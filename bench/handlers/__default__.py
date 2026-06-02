from pathlib import Path
import lib.solver as s


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    if cert:
        return s.run_cpf_convert(benchmark)
    return s.run_plain(benchmark)
