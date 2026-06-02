import os
import subprocess
import sys
import tempfile
from pathlib import Path

APROVE = os.environ.get("APROVE", "/opt/bundle/aprove.jar")
CPF_CONVERTER = os.environ.get("CPF_CONVERTER", "/opt/bundle/cpfconverter/cpf2_to_3.sh")
JAVA = os.environ.get("JAVA", "java")
JAVA_PLAIN_OPTS: list[str] = os.environ.get("JAVA_PLAIN_OPTS", "-ea").split()
JAVA_HEAVY_OPTS: list[str] = os.environ.get("JAVA_HEAVY_OPTS", "-Xmx14G -Xms14G -ea").split()
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


def run_plain(
    input_file: Path,
    *,
    heavy: bool = False,
    mode: str = "wst",
    timeout: int | None = None,
    env: dict[str, str] | None = None,
) -> str:
    opts = JAVA_HEAVY_OPTS if heavy else JAVA_PLAIN_OPTS
    t_args = ["-t", str(timeout)] if timeout is not None else []
    cmd = [JAVA, *opts, "-jar", APROVE, "-m", mode, "-p", "plain", *t_args, str(input_file)]
    return subprocess.run(cmd, stdout=subprocess.PIPE, text=True, env=_solver_env(env)).stdout


def run_cpf_convert(
    input_file: Path,
    *,
    mode: str = "wst",
    timeout: int | None = None,
) -> str:
    t_args = ["-t", str(timeout)] if timeout is not None else []
    cmd = [JAVA, *JAVA_PLAIN_OPTS, "-jar", APROVE, "-m", mode, "-p", "cpf", "-C", "ceta", *t_args, str(input_file)]
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
        base_cmd = [JAVA, *JAVA_HEAVY_OPTS, "-jar", APROVE, "-m", mode, "-w", "4", "-t", str(to)]
        if cert:
            result = subprocess.run(
                [*base_cmd, "-p", "cpf", "-C", "ceta", str(tmp)],
                stdout=subprocess.PIPE, text=True, env=_solver_env(),
            )
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
        return subprocess.run(
            [*base_cmd, "-p", "plain", str(tmp)],
            stdout=subprocess.PIPE, text=True, env=_solver_env(),
        ).stdout
