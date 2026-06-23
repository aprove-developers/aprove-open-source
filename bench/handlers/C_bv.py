from pathlib import Path
import lib.solver as s

BV_ARGS = ["-b", "--bit-width", "64"]


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    if cert:
        return s.run_cpf_convert(benchmark, extra_args=BV_ARGS)
    return s.run_plain(benchmark, extra_args=BV_ARGS)
