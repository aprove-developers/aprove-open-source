from pathlib import Path
import tempfile
import lib.solver as s

RESULT_LABELS = ["YES", "NO", "MAYBE", "KILLED", "ERROR"]


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir) / "input.ari"
        s.mkinput(tmp, "(GOAL SAST)", "(STRATEGY INNERMOST)", benchmark=benchmark)
        s._print_input(tmp, "PTRS_SAST_INNERMOST")
        if cert:
            return s.run_cpf_convert(tmp)
        return s.run_plain(tmp, timeout=timeout)
