import os
import re
import sys
import tempfile
from pathlib import Path

import lib.solver as s

RESULT_LABELS = ["AST", "SAST", "NO", "MAYBE", "KILLED", "ERROR"]

_SAST_BOUND = re.compile(r'^(.*O\(1\).*|.*O\(n\^\d+\).*|.*EXP.*|.*2-EXP.*)$')


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    to = s.eff_timeout(timeout, 2)
    with tempfile.TemporaryDirectory() as ast_dir, tempfile.TemporaryDirectory() as sast_dir:
        ast_trs = Path(ast_dir) / "ast.ari"
        sast_trs = Path(sast_dir) / "sast.ari"
        s.mkinput(ast_trs, "(GOAL AST)", "(STRATEGY INNERMOST)", benchmark=benchmark)
        s.mkinput(sast_trs, "(GOAL COMPLEXITY)", "(STRATEGY INNERMOST)", benchmark=benchmark)

        if os.environ.get("PRINT_INPUT", "0") == "1":
            print("---BEGIN AST INPUT---", file=sys.stderr)
            print(*ast_trs.read_text().splitlines()[:20], sep="\n", file=sys.stderr)
            print("---BEGIN SAST INPUT---", file=sys.stderr)
            print(*sast_trs.read_text().splitlines()[:20], sep="\n", file=sys.stderr)
            print("---END---", file=sys.stderr)

        ans_ast = s.run_plain(ast_trs, mode="wst", timeout=to)

        sast_env = os.environ.copy()
        sast_env["LD_LIBRARY_PATH"] = "../lib:" + sast_env.get("LD_LIBRARY_PATH", "")
        sast_env["PATH"] = ".:" + sast_env["PATH"]
        ans_sast = s.run_plain(sast_trs, mode="benchmark", timeout=to, env=sast_env)

    first_ast = ans_ast.splitlines()[0] if ans_ast.strip() else ""
    first_sast = ans_sast.splitlines()[0] if ans_sast.strip() else ""
    sast_rest = "".join(ans_sast.splitlines(keepends=True)[1:])
    ast_rest = "".join(ans_ast.splitlines(keepends=True)[1:])

    if _SAST_BOUND.match(first_sast):
        return "SAST\n" + sast_rest
    if first_ast == "YES":
        return "AST\n" + ast_rest
    return "MAYBE\n"
