#!/usr/bin/env python3
import argparse
import csv
import math
import os
import random
import signal
import subprocess
import sys
import tempfile
import datetime
import json
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
import threading
from pathlib import Path
import lib.serialize_result as serialize_result

try:
    import tomllib  # Python 3.11+
except ImportError:  # pragma: no cover
    import tomli as tomllib  # type: ignore

KILL_GRACE = 5  # seconds beyond the jar's own timeout before the script kills the process

DEFAULTS: dict[str, str | Path | int | bool] = {
    "TIMEOUT": "30",
    "JOBS": os.cpu_count() or 1,
    "EXTENSION": "ari",
    "RAW_RESULT": False,
    "LOCAL": False,
    "LOCAL_JAVA": "java",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run AProVE over a directory of problem files in parallel (via Docker or locally)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
        argument_default=argparse.SUPPRESS,
    )
    parser.add_argument("-c", "--config", type=Path, help="TOML config file (keys like FOLDER, SUBDIR, CATEGORY)")
    parser.add_argument("-f", "--folder", type=Path, help="Base folder (mount point inside container)")
    parser.add_argument("-s", "--subdir", type=Path, help="Subdirectory under folder to scan (e.g. PTRS_Standard)")
    parser.add_argument("-C", "--category", help="AProVE category (e.g. PTRS_AST_INNERMOST)")
    parser.add_argument("-t", "--timeout", help=f"Solver timeout per file (seconds) (default: {DEFAULTS['TIMEOUT']})")
    parser.add_argument("-i", "--image", help="Docker image/tag/ID (required unless --local)")
    parser.add_argument("-J", "--aprove-jar", type=Path, help="Path to aprove.jar (required with --local; mounts into container otherwise)")
    parser.add_argument("--local", action="store_true", default=argparse.SUPPRESS,
                        help="Run AProVE directly via java instead of Docker. Requires --aprove-jar.")
    parser.add_argument("--java", dest="local_java", metavar="PATH",
                        help="Java executable to use with --local (default: java)")
    parser.add_argument("-o", "--outdir", type=Path, help="Output directory for per-file .out files and summary.csv. Optional if --flat-csv is set.")
    parser.add_argument("-m", "--memory", help="Memory cap for container (e.g. 2g). Disables swap.")
    parser.add_argument("-j", "--jobs", type=int, help=f"Parallelism (default: {DEFAULTS['JOBS']})")
    parser.add_argument("-x", "--extension", help=f"File extension to search for (without dot) (default: {DEFAULTS['EXTENSION']})")
    parser.add_argument("-r", "--raw-result", action="store_true", default=argparse.SUPPRESS,
                        help="Record the raw first output line in the CSV instead of normalising to YES/NO/MAYBE/KILLED/ERROR. "
                             "Useful for complexity categories where the first line carries a complexity bound (e.g. WORST_CASE(O(1),O(n^2))).")
    parser.add_argument("-F", "--flat-csv", type=Path,
                        help="Append results to a single flat CSV (Timestamp;Problem;Result;Timeout;Category;CommitID). "
                             "Can be used alongside --outdir.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--resume", action="store_true", default=argparse.SUPPRESS,
                      help="Skip files that already have a result in the existing summary.csv.")
    mode.add_argument("--rerun", metavar="RESULTS",
                      help="Only run files whose result in the existing summary.csv matches one of the "
                           "comma-separated values (e.g. MAYBE,KILLED,ERROR).")
    parser.add_argument("--sample", type=int, metavar="N",
                        help="Randomly sample N files from the (filtered) problem set.")
    parser.add_argument("--sample-pct", type=int, metavar="PCT",
                        help="Randomly sample PCT%% of the (filtered) problem set (1-100). Ignored if --sample is set.")
    parser.add_argument("--runall", type=Path, metavar="DIR",
                        help="Run every *.toml config found in DIR, forwarding all other flags to each run.")
    parser.add_argument("--cert", action="store_true", default=argparse.SUPPRESS,
                        help="Pass --cert to the solver, requesting CPF certificate output.")
    return parser.parse_args()


def load_config(path: Path) -> dict[str, object]:
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    # Allow either top-level keys or a [config] table
    if isinstance(data, dict) and "config" in data and isinstance(data["config"], dict):
        data = data["config"]
    cfg: dict[str, object] = {}
    if isinstance(data, dict):
        for k, v in data.items():
            cfg[str(k).upper()] = v
    return cfg


def build_config(cli: argparse.Namespace) -> dict[str, str | Path]:
    cfg: dict[str, str | Path] = DEFAULTS.copy()
    config_path = getattr(cli, "config", None)
    if config_path:
        cfg.update(load_config(config_path))
    # CLI overrides config only when provided
    for key, attr in [
        ("FOLDER", "folder"),
        ("SUBDIR", "subdir"),
        ("CATEGORY", "category"),
        ("TIMEOUT", "timeout"),
        ("IMAGE", "image"),
        ("APROVE_JAR", "aprove_jar"),
        ("OUTDIR", "outdir"),
        ("MEMORY", "memory"),
        ("JOBS", "jobs"),
        ("EXTENSION", "extension"),
        ("RAW_RESULT", "raw_result"),
        ("FLAT_CSV", "flat_csv"),
        ("RESUME", "resume"),
        ("RERUN", "rerun"),
        ("SAMPLE", "sample"),
        ("SAMPLE_PCT", "sample_pct"),
        ("LOCAL", "local"),
        ("LOCAL_JAVA", "local_java"),
        ("CERT", "cert"),
    ]:
        if hasattr(cli, attr):
            val = getattr(cli, attr)
            if val is None:
                continue
            cfg[key] = val
    return cfg


def require(cfg: dict[str, str | Path], key: str) -> str:
    val = cfg.get(key)
    if val is None or str(val) == "":
        raise SystemExit(f"{key} is required (via config or CLI)")
    return str(val)


def docker_image_exists(image: str) -> bool:
    try:
        subprocess.run(["docker", "image", "inspect", image], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return True
    except subprocess.CalledProcessError:
        return False


def get_commit_id(image: str, jar_path: Path | None) -> str:
    """Read the first token of the VERSION file embedded in aprove.jar."""
    try:
        if jar_path:
            result = subprocess.run(
                ["unzip", "-p", str(jar_path), "VERSION"],
                check=True, capture_output=True, text=True,
            )
        else:
            result = subprocess.run(
                ["docker", "run", "--rm", image, "unzip", "-p", "/opt/bundle/aprove.jar", "VERSION"],
                check=True, capture_output=True, text=True,
            )
        return result.stdout.split()[0]
    except Exception:  # noqa: BLE001
        return "unknown"


def _kill_pgroup(pgid: int) -> None:
    try:
        os.killpg(pgid, signal.SIGKILL)
    except OSError:
        pass


def _docker_kill(cid_file: Path) -> None:
    """Kill the container whose ID was written to cid_file by docker run --cidfile."""
    try:
        cid = cid_file.read_text().strip()
        if cid:
            subprocess.run(["docker", "kill", cid], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception:  # noqa: BLE001
        pass


def _maybe_append_flat(cfg: dict[str, str | Path], file_path: Path, root: Path, result: str) -> None:
    flat_csv = cfg.get("FLAT_CSV")
    if not flat_csv:
        return
    try:
        rel = str(file_path.relative_to(root))
    except ValueError:
        rel = file_path.name
    serialize_result.append_flat(
        Path(str(flat_csv)),
        problem=rel,
        result=result,
        timeout=str(cfg.get("TIMEOUT", "")),
        category=str(cfg.get("CATEGORY", "")),
        commit_id=str(cfg.get("COMMIT_ID", "unknown")),
    )


def run_file(cfg: dict[str, str | Path], file_path: Path, root: Path, outdir: Path, mem_flags: list[str]) -> tuple[Path, str, str]:
    if STOP_EVENT.is_set():
        return file_path, "", "cancelled"
    clean_file = Path(str(file_path)).as_posix().replace("//", "/")
    cid_file = Path(tempfile.mktemp(suffix=".cid", prefix="aprove_"))
    cmd = [
        "docker",
        "run",
        "--rm",
        "--cidfile", str(cid_file),
        *mem_flags,
        "-v",
        f"{cfg['FOLDER']}:{cfg['FOLDER']}",
        cfg["IMAGE"],
        f"--timeout={cfg['TIMEOUT']}",
        f"--category={cfg['CATEGORY']}",
        *( ["--cert"] if cfg.get("CERT") else []),
        clean_file,
    ]
    try:
        deadline = time.monotonic() + int(cfg["TIMEOUT"]) + KILL_GRACE
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, preexec_fn=os.setsid if hasattr(os, "setsid") else None)
        killed_by_script = False
        try:
            while True:
                try:
                    stdout, stderr = proc.communicate(timeout=0.5)
                    break
                except subprocess.TimeoutExpired:
                    if STOP_EVENT.is_set():
                        _docker_kill(cid_file)
                        proc.terminate()
                        try:
                            stdout, stderr = proc.communicate(timeout=2)
                        except subprocess.TimeoutExpired:
                            proc.kill()
                            stdout, stderr = proc.communicate()
                        return file_path, stdout or "", "cancelled"
                    if time.monotonic() >= deadline:
                        _docker_kill(cid_file)
                        proc.kill()
                        stdout, stderr = proc.communicate()
                        killed_by_script = True
                        break
        finally:
            cid_file.unlink(missing_ok=True)
        output = stdout or ""
        if killed_by_script:
            if outdir:
                serialize_result.serialize(outdir, root, file_path, "KILLED", False)
            _maybe_append_flat(cfg, file_path, root, "KILLED")
            return file_path, "KILLED", ""
        if stderr and outdir:
            (outdir / "error.log").open("a", encoding="utf-8").write(f"=== {datetime.datetime.now().isoformat(timespec='seconds')} {clean_file} ===\n{stderr}\n\n")
    except Exception as exc:  # noqa: BLE001
        return file_path, "", f"error invoking docker: {exc}"

    raw_first_line = bool(cfg.get("RAW_RESULT", False))
    if outdir:
        serialize_result.serialize(outdir, root, file_path, output, raw_first_line)
    first_line = output.splitlines()[0] if output else ""
    normalised = first_line if (raw_first_line or first_line in serialize_result.VALID_RESULTS) else "ERROR"
    _maybe_append_flat(cfg, file_path, root, normalised)
    return file_path, output, ""


def run_file_local(cfg: dict[str, str | Path], file_path: Path, root: Path, outdir: Path) -> tuple[Path, str, str]:
    if STOP_EVENT.is_set():
        return file_path, "", "cancelled"
    clean_file = str(file_path)
    solver = Path(__file__).resolve().parent / "solver"
    env = os.environ.copy()
    env["APROVE"] = str(cfg["APROVE_JAR"])
    env["JAVA"] = str(cfg.get("LOCAL_JAVA", "java"))
    env["SOLVER_ROOT"] = str(Path(__file__).resolve().parent)
    cmd = [
        sys.executable, str(solver),
        f"--timeout={cfg['TIMEOUT']}",
        f"--category={cfg['CATEGORY']}",
        *( ["--cert"] if cfg.get("CERT") else []),
        clean_file,
    ]
    try:
        deadline = time.monotonic() + int(cfg["TIMEOUT"]) + KILL_GRACE
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                                env=env, preexec_fn=os.setsid if hasattr(os, "setsid") else None)
        pgid = os.getpgid(proc.pid) if hasattr(os, "getpgid") else None
        killed_by_script = False
        try:
            while True:
                try:
                    stdout, stderr = proc.communicate(timeout=0.5)
                    break
                except subprocess.TimeoutExpired:
                    if STOP_EVENT.is_set():
                        if pgid is not None:
                            _kill_pgroup(pgid)
                        proc.kill()
                        try:
                            stdout, stderr = proc.communicate(timeout=2)
                        except subprocess.TimeoutExpired:
                            proc.kill()
                            stdout, stderr = proc.communicate()
                        return file_path, stdout or "", "cancelled"
                    if time.monotonic() >= deadline:
                        if pgid is not None:
                            _kill_pgroup(pgid)
                        proc.kill()
                        stdout, stderr = proc.communicate()
                        killed_by_script = True
                        break
        finally:
            if pgid is not None:
                _kill_pgroup(pgid)
        output = stdout or ""
        if killed_by_script:
            if outdir:
                serialize_result.serialize(outdir, root, file_path, "KILLED", False)
            _maybe_append_flat(cfg, file_path, root, "KILLED")
            return file_path, "KILLED", ""
        if stderr and outdir:
            (outdir / "error.log").open("a", encoding="utf-8").write(f"=== {datetime.datetime.now().isoformat(timespec='seconds')} {clean_file} ===\n{stderr}\n\n")
    except Exception as exc:  # noqa: BLE001
        return file_path, "", f"error invoking solver: {exc}"

    raw_first_line = bool(cfg.get("RAW_RESULT", False))
    if outdir:
        serialize_result.serialize(outdir, root, file_path, output, raw_first_line)
    first_line = output.splitlines()[0] if output else ""
    normalised = first_line if (raw_first_line or first_line in serialize_result.VALID_RESULTS) else "ERROR"
    _maybe_append_flat(cfg, file_path, root, normalised)
    return file_path, output, ""


def monitor_progress(total: int, done_ref: dict[str, int], lock: threading.Lock) -> None:
    while True:
        with lock:
            done = done_ref["count"]
        pct = int((done / total) * 100) if total else 100
        sys.stderr.write(f"\r[{done}/{total} ({pct}%)]")
        sys.stderr.flush()
        if done >= total:
            break
        if STOP_EVENT.wait(0.2):
            with lock:
                done = done_ref["count"]
            pct = int((done / total) * 100) if total else 100
            sys.stderr.write(f"\r[{done}/{total} ({pct}%)]")
            sys.stderr.flush()
            break
    sys.stderr.write("\n")


def filter_files(files: list[Path], root: Path, outdir: Path | None, resume: bool, rerun: list[str]) -> list[Path]:
    if not outdir:
        if rerun:
            print("ERROR: --rerun requires --outdir.", file=sys.stderr)
            return []
        return files
    summary_path = outdir / "summary.csv"
    if not summary_path.exists():
        if rerun:
            print(f"No summary.csv found in {outdir} — nothing to rerun.", file=sys.stderr)
            return []
        return files

    with summary_path.open(encoding="utf-8", newline="") as fh:
        done: dict[str, str] = {
            row["File"].strip(): row["Result"].strip()
            for row in csv.DictReader(fh, delimiter=";")
            if row.get("File")
        }

    if resume:
        filtered = [f for f in files if str(f.relative_to(root)) not in done]
        print(f"Resume: skipping {len(files) - len(filtered)} already-completed file(s), running {len(filtered)}.")
        return filtered

    if rerun:
        target = {r.strip().upper() for r in rerun}
        filtered = [f for f in files if done.get(str(f.relative_to(root)), "").upper() in target]
        print(f"Rerun: {len(filtered)} file(s) with result in {{{', '.join(sorted(target))}}}.")
        return filtered

    return files


_DEFAULT_RESULT_LABELS = ["YES", "NO", "MAYBE", "KILLED", "ERROR"]


def _query_result_labels(cfg: dict, category: str, local: bool, extra_docker_flags: list[str]) -> list[str]:
    try:
        if local:
            solver = Path(__file__).resolve().parent / "solver"
            result = subprocess.run(
                [sys.executable, str(solver), "--category", category, "--meta"],
                capture_output=True, text=True,
            )
        else:
            result = subprocess.run(
                ["docker", "run", "--rm", *extra_docker_flags, cfg["IMAGE"],
                 "--category", category, "--meta"],
                capture_output=True, text=True,
            )
        if result.returncode == 0:
            return json.loads(result.stdout).get("result_labels", _DEFAULT_RESULT_LABELS)
    except Exception:  # noqa: BLE001
        pass
    return _DEFAULT_RESULT_LABELS


def run_all_configs(runall_dir: Path) -> int:
    configs = sorted(p for p in runall_dir.glob("*.toml") if not p.name.startswith("_"))
    if not configs:
        print(f"ERROR: no *.toml files found in {runall_dir}", file=sys.stderr)
        return 2

    # Forward all argv except --runall (and its value) and -c/--config (and its value)
    passthrough: list[str] = []
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg in ("--runall", "-c", "--config"):
            i += 2
        elif arg.startswith(("--runall=", "--config=")):
            i += 1
        else:
            passthrough.append(arg)
            i += 1

    failures = 0
    for cfg_path in configs:
        print(f"\n{'='*60}\nConfig: {cfg_path.name}\n{'='*60}", flush=True)
        try:
            ret = subprocess.run(
                [sys.executable, __file__, "-c", str(cfg_path), *passthrough]
            ).returncode
        except KeyboardInterrupt:
            return 130
        if ret == 130:
            return 130
        if ret != 0:
            failures += 1

    total = len(configs)
    print(f"\nFinished {total} config(s): {total - failures} OK, {failures} failed.")
    return 1 if failures else 0


def main() -> int:
    cli = parse_args()

    runall_dir = getattr(cli, "runall", None)
    if runall_dir:
        return run_all_configs(Path(runall_dir))

    if not hasattr(cli, "config"):
        print("ERROR: no config file provided. Use -c/--config to supply a TOML configuration.", file=sys.stderr)
        return 2
    cfg = build_config(cli)

    folder = Path(os.path.expandvars(require(cfg, "FOLDER"))).expanduser().resolve()
    subdir = Path(require(cfg, "SUBDIR"))
    category = require(cfg, "CATEGORY")
    timeout = require(cfg, "TIMEOUT")
    outdir = Path(str(cfg["OUTDIR"])) if cfg.get("OUTDIR") else None
    aprove_jar = cfg.get("APROVE_JAR")
    extension = str(cfg.get("EXTENSION", "ari")).lstrip(".")
    local = bool(cfg.get("LOCAL", False))

    flat_csv_raw = cfg.get("FLAT_CSV")
    if not outdir and not flat_csv_raw:
        print("ERROR: at least one of --outdir or --flat-csv must be specified.", file=sys.stderr)
        return 2

    cfg["FOLDER"] = folder
    cfg["SUBDIR"] = subdir
    cfg["CATEGORY"] = category
    cfg["TIMEOUT"] = timeout
    if outdir:
        cfg["OUTDIR"] = outdir
    cfg["EXTENSION"] = extension

    jobs = int(cfg.get("JOBS", os.cpu_count() or 1))

    if local:
        jar_path = Path(os.path.expandvars(require(cfg, "APROVE_JAR"))).expanduser().resolve()
        if not jar_path.exists():
            print(f"ERROR: APROVE_JAR does not exist: {jar_path}", file=sys.stderr)
            return 1
        cfg["APROVE_JAR"] = jar_path
        cfg["COMMIT_ID"] = get_commit_id("", jar_path)
        mem_flags: list[str] = []
        jar_mount: list[str] = []
        print(f"Mode: local (java={cfg.get('LOCAL_JAVA', 'java')})")
    else:
        image = require(cfg, "IMAGE")
        cfg["IMAGE"] = image
        memory = cfg.get("MEMORY")
        mem_flags = []
        if memory:
            mem_flags = [f"--memory={memory}", f"--memory-swap={memory}"]
        jar_mount = []
        if aprove_jar:
            jar_path = Path(os.path.expandvars(str(aprove_jar))).expanduser().resolve()
            if not jar_path.exists():
                print(f"ERROR: APROVE_JAR does not exist: {jar_path}", file=sys.stderr)
                return 1
            cfg["APROVE_JAR"] = jar_path
            jar_mount = ["-v", f"{jar_path}:/opt/bundle/aprove.jar:ro"]
        if not docker_image_exists(image):
            print(f"ERROR: invalid docker image reference: {image}", file=sys.stderr)
            return 1
        jar_path_for_version = cfg.get("APROVE_JAR")
        cfg["COMMIT_ID"] = get_commit_id(image, Path(str(jar_path_for_version)) if jar_path_for_version else None)
        print(f"Mode: docker (image={image})")

    result_labels = _query_result_labels(cfg, category, local, mem_flags + jar_mount if not local else [])

    print(f"Testing all *.{extension} in {folder}/{subdir}")
    print(f"Under the {category} category using {cfg.get('APROVE_JAR', 'jar from image')}")
    if outdir:
        print(f"Exporting result to {outdir}")
    print(f"Jar commit ID: {cfg['COMMIT_ID']}")

    flat_csv = cfg.get("FLAT_CSV")
    if flat_csv:
        cfg["FLAT_CSV"] = Path(os.path.expandvars(str(flat_csv))).expanduser()

    resume = bool(cfg.get("RESUME", False))
    rerun_raw = cfg.get("RERUN")
    rerun = [r.strip() for r in str(rerun_raw).split(",")] if rerun_raw else []

    root = folder / subdir
    files = sorted(root.rglob(f"*.{extension}"))
    if outdir:
        outdir.mkdir(parents=True, exist_ok=True)
        (outdir / "results").mkdir(parents=True, exist_ok=True)
        if not resume and not rerun:
            (outdir / "summary.csv").write_text("File;Result;FullResult;InputPath\n", encoding="utf-8")

    files = filter_files(files, root, outdir, resume, rerun)

    sample = cfg.get("SAMPLE")
    if not sample and cfg.get("SAMPLE_PCT"):
        pct = max(1, min(100, int(cfg["SAMPLE_PCT"])))
        sample = max(1, math.ceil(len(files) * pct / 100))
    if sample:
        n = int(sample)
        if n < len(files):
            total_before = len(files)
            files = sorted(random.sample(files, n))
            print(f"Sample: randomly selected {n} of {total_before} file(s).")

    total = len(files)

    done_ref = {"count": 0}
    lock = threading.Lock()
    monitor = threading.Thread(target=monitor_progress, args=(total, done_ref, lock), daemon=True)
    monitor.start()

    pool = ThreadPoolExecutor(max_workers=jobs)
    try:
        if local:
            futures = {pool.submit(run_file_local, cfg, f, root, outdir): f for f in files}
        else:
            futures = {pool.submit(run_file, cfg, f, root, outdir, mem_flags + jar_mount): f for f in files}
        for fut in as_completed(futures):
            with lock:
                done_ref["count"] += 1
            try:
                _, _, err = fut.result()
                if err and err != "cancelled":
                    print(err, file=sys.stderr)
            except Exception as exc:  # noqa: BLE001
                print(f"error processing {futures[fut]}: {exc}", file=sys.stderr)
    except KeyboardInterrupt:
        STOP_EVENT.set()
        sys.stderr.write("\nInterrupted, cancelling pending jobs...\n")
        pool.shutdown(wait=False, cancel_futures=True)
        monitor.join()
        exit_code = 130
    else:
        exit_code = 0
    finally:
        pool.shutdown(wait=True)
        STOP_EVENT.set()
        monitor.join()

    raw_result = bool(cfg.get("RAW_RESULT", False))
    counts: dict[str, int] = {} if raw_result else {"YES": 0, "NO": 0, "MAYBE": 0, "AST": 0, "SAST": 0, "KILLED": 0, "ERROR": 0}
    if outdir:
        summary_path = outdir / "summary.csv"
        if summary_path.exists():
            with summary_path.open(encoding="utf-8", newline="") as fh:
                for row in csv.DictReader(fh, delimiter=";"):
                    result = row.get("Result", "").strip()
                    counts[result] = counts.get(result, 0) + 1

    if raw_result:
        labels = sorted(counts, key=lambda k: (-counts[k], k))
        col_w = max((len(l) for l in labels), default=6)
    else:
        labels = result_labels
        col_w = max(len(l) for l in labels)
    print(f"\n{'Result':<{col_w}} {'Count':>6}")
    print(f"{'-'*col_w} {'-'*6}")
    for label in labels:
        print(f"{label:<{col_w}} {counts.get(label, 0):>6}")

    flat_csv = cfg.get("FLAT_CSV")
    if flat_csv:
        flat_path = Path(str(flat_csv))
        contra, bad, good, breaking = 0, 0, 0, 0
        contra_rows: list[str] = []
        bad_rows: list[str] = []
        breaking_rows: list[str] = []
        if flat_path.exists():
            with flat_path.open(encoding="utf-8", newline="") as fh:
                for row in csv.DictReader(fh, delimiter=";"):
                    conflict = row.get("Conflict", "").strip()
                    entry = f"  {row.get('Problem', '')}  [{row.get('Category', '')}]  {row.get('Result', '')}"
                    if conflict == "CONTRA":
                        contra += 1
                        contra_rows.append(entry)
                    elif conflict == "BAD":
                        bad += 1
                        bad_rows.append(entry)
                    elif conflict == "GOOD":
                        good += 1
                    elif conflict == "BROKEN":
                        breaking += 1
                        breaking_rows.append(entry)
        if contra or bad or good or breaking:
            print(f"\n{'Conflict':<10} {'Rows':>6}")
            print(f"{'-'*10} {'-'*6}")
            print(f"{'BROKEN':<10} {breaking:>6}")
            print(f"{'CONTRA':<10} {contra:>6}")
            print(f"{'BAD':<10} {bad:>6}")
            print(f"{'GOOD':<10} {good:>6}")
            for label, rows in [("BROKEN", breaking_rows), ("CONTRA", contra_rows), ("BAD", bad_rows)]:
                if rows:
                    seen: set[str] = set()
                    unique = [r for r in rows if not (r in seen or seen.add(r))]  # type: ignore[func-returns-value]
                    print(f"\n{label} conflicts ({len(unique)} problem(s)):")
                    for r in unique:
                        print(r)

    return exit_code


if __name__ == "__main__":
    STOP_EVENT = threading.Event()
    raise SystemExit(main())
