from pathlib import Path
import tempfile
import lib.solver as s


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir) / "input.ari"
        s.mkinput(tmp, "(STRATEGY OUTERMOST)", benchmark=benchmark)
        s._print_input(tmp, "TRS_Outermost")
        if cert:
            return s.run_cpf_convert(tmp)
        return s.run_plain(tmp)
