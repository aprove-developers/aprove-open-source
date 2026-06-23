import os
import subprocess
import sys
import tempfile
from pathlib import Path

APROVE = os.environ.get("APROVE", "/opt/bundle/aprove.jar")
CPF_CONVERTER = os.environ.get("CPF_CONVERTER", "/opt/bundle/cpfconverter/cpf2_to_3.sh")
JAVA = os.environ.get("JAVA", "java")
# -ea for "enable assertions"
JAVA_OPTS: list[str] = os.environ.get("JAVA_OPTS", "-ea").split()
# Max JVM heap (-Xmx) for memory-heavy analyses, taken from the JVM_MEMORY config
# (e.g. "8G"); empty -> JVM default heap.
_JVM_MEMORY: str = os.environ.get("JVM_MEMORY", "").strip()
_HEAP_OPTS: list[str] = [f"-Xmx{_JVM_MEMORY}"] if _JVM_MEMORY else []
LOAT_PATH = os.environ.get("LOAT_PATH", "/opt/bundle/bin")
KOAT2_PATH = os.environ.get("KOAT2_PATH", "/opt/bundle/bin")


def mkinput(out: Path, *lines: str, benchmark: Path) -> None:
    with out.open("w") as f:
        for line in lines:
            f.write(line + "\n")
        f.write(benchmark.read_text())


def eff_timeout(timeout: int, subtract: int) -> int:
    return timeout - subtract if timeout > subtract + 5 else timeout


def _print_input(path: Path, label: str) -> None:
    if os.environ.get("PRINT_INPUT", "0") == "1":
        print(f"---BEGIN INPUT ({label})---", file=sys.stderr)
        print(path.read_text(), end="", file=sys.stderr)
        print("---END INPUT---", file=sys.stderr)


def _solver_env(env: dict[str, str] | None = None) -> dict[str, str]:
    base = dict(os.environ) if env is None else dict(env)
    base.setdefault("LOAT_PATH", LOAT_PATH)
    base.setdefault("KOAT2_PATH", KOAT2_PATH)
    return base


def start_plain(
    input_file: Path,
    *,
    heavy: bool = False,
    mode: str = "wst",
    timeout: int | None = None,
    env: dict[str, str] | None = None,
    extra_args: list[str] | None = None,
) -> subprocess.Popen:
    """Start AProVE in 'plain' mode and return the still-running process.

    The process is placed in its own session (where supported) so callers that
    run several solvers concurrently can kill a whole group if it overruns.

    ``extra_args`` are passed verbatim to AProVE before the input file.
    """
    opts = (_HEAP_OPTS + JAVA_OPTS) if heavy else JAVA_OPTS
    t_args = ["-t", str(timeout)] if timeout is not None else []
    cmd = [JAVA, *opts, "-jar", APROVE, "-m", mode, "-p", "plain", *(extra_args or []), *t_args, str(input_file)]
    return subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        text=True,
        env=_solver_env(env),
        preexec_fn=os.setsid if hasattr(os, "setsid") else None,
    )


def _warn_if_killed(returncode: int | None, context: str) -> None:
    """Log to stderr if AProVE was killed by a signal (e.g. the cgroup OOM-killer).

    A container's OOM-killer sends SIGKILL to the JVM, which surfaces here as a
    negative returncode (-9) or 137 (128+9). Without this the empty stdout is
    silently returned and the container still exits 0, so the harness can only
    tell "no output" but not that it was an out-of-memory kill. benchmark.py copies
    solver stderr into error.log, so this makes the OOM explicit there.
    """
    if returncode is None or 0 <= returncode < 128:
        return
    sig = -returncode if returncode < 0 else returncode - 128
    cause = "OUT OF MEMORY (heap too large for the container)" if sig in (6, 9) else f"killed by signal {sig}"
    print(f"[solver] AProVE ({context}) produced no result: {cause} [exit={returncode}]. "
          f"Lower JVM_MEMORY/-Xmx or raise the container RAM.", file=sys.stderr, flush=True)


def run_plain(
    input_file: Path,
    *,
    heavy: bool = False,
    mode: str = "wst",
    timeout: int | None = None,
    env: dict[str, str] | None = None,
    extra_args: list[str] | None = None,
) -> str:
    proc = start_plain(input_file, heavy=heavy, mode=mode, timeout=timeout, env=env, extra_args=extra_args)
    out = proc.communicate()[0] or ""
    _warn_if_killed(proc.returncode, f"-m {mode}")
    return out


def run_cpf_convert(
    input_file: Path,
    *,
    mode: str = "wst",
    timeout: int | None = None,
    extra_args: list[str] | None = None,
) -> str:
    t_args = ["-t", str(timeout)] if timeout is not None else []
    cmd = [JAVA, *JAVA_OPTS, "-jar", APROVE, "-m", mode, "-p", "cpf", "-C", "ceta", *(extra_args or []), *t_args, str(input_file)]
    result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True, env=_solver_env())
    lines = result.stdout.splitlines(keepends=True)
    if not lines:
        return ""
    decision = lines[0].rstrip("\r\n")
    if decision not in ("YES", "NO"):
        return result.stdout
    rest = "".join(lines[1:])
    with tempfile.NamedTemporaryFile(mode="w", suffix=".cpf", delete=False) as f:
        f.write(rest)
        tmp_path = f.name
    try:
        conv = subprocess.run([CPF_CONVERTER, tmp_path], stdout=subprocess.PIPE, text=True)
        return lines[0] + conv.stdout
    finally:
        Path(tmp_path).unlink(missing_ok=True)


def run_complexity(
    benchmark: Path,
    timeout: int,
    cert: bool,
    *,
    goal_lines: list[str],
    mode: str = "wst",
) -> str:
    to = eff_timeout(timeout, 10)
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir) / "input.ari"
        mkinput(tmp, *goal_lines, benchmark=benchmark)
        _print_input(tmp, f"complexity({mode})")
        base_cmd = [JAVA, *_HEAP_OPTS, *JAVA_OPTS, "-jar", APROVE, "-m", mode, "-w", "4", "-t", str(to)]
        if cert:
            result = subprocess.run(
                [*base_cmd, "-p", "cpf", "-C", "ceta", str(tmp)],
                stdout=subprocess.PIPE, text=True, env=_solver_env(),
            )
            _warn_if_killed(result.returncode, f"complexity cert -m {mode}")
            lines = result.stdout.splitlines(keepends=True)
            if not lines:
                return ""
            rest = "".join(lines[1:])
            with tempfile.NamedTemporaryFile(mode="w", suffix=".cpf", delete=False) as f:
                f.write(rest)
                tmp2 = f.name
            try:
                conv = subprocess.run([CPF_CONVERTER, tmp2], stdout=subprocess.PIPE, text=True)
                return lines[0] + conv.stdout
            finally:
                Path(tmp2).unlink(missing_ok=True)
        result = subprocess.run(
            [*base_cmd, "-p", "plain", str(tmp)],
            stdout=subprocess.PIPE, text=True, env=_solver_env(),
        )
        _warn_if_killed(result.returncode, f"complexity -m {mode}")
        return result.stdout
