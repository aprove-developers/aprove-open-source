import os
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

import lib.solver as s

# Seconds to keep waiting after a solver's own -t budget should have expired,
# to let it tear down before we force-kill it. Must stay below the harness
# KILL_GRACE (benchmark.py) so there is still time to combine and print an
# answer instead of being reported as KILLED.
_TEARDOWN_GRACE = 3

# The competition output is WORST_CASE(f,g) with the lower bound f and upper bound g:
#   f in {? < Non-SAST < Non-AST}   (lower bound)
#   g in {? < AST < SAST}           (upper bound)
# These strings are dynamic, so the category must run with RAW_RESULT=true.
RESULT_LABELS = ["WORST_CASE", "MAYBE", "KILLED", "ERROR"]

# SAST is derived from a COMPLEXITY run instead of a dedicated (GOAL SAST) run:
# a finite expected-runtime upper bound proves SAST, an INF lower bound disproves it. 
# AProVE prints WORST_CASE(<lower>,<upper>); the regex is matched against the
# upper bound (with its surrounding delimiters) and accepts O(1)/O(n)/O(n^k)/EXP/2-EXP.
_SAST_UPPER_RE = re.compile(r'^(.O\(1\).|.O\(n\).|.*O\(n\^\d+\).|.EXP.|.2-EXP.*)$')
_WORST_CASE_RE = re.compile(r"WORST_CASE\(([^,]*),(.*)\)\s*$")


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    return _run(timeout, benchmark, extra_goal_lines=())


def _run(timeout: int, benchmark: Path, extra_goal_lines: tuple[str, ...]) -> str:
    # The AST and COMPLEXITY analyses run in parallel, so each gets (almost) the
    # full timeout via AProVE's own -t rather than half of it.
    to = s.eff_timeout(timeout, 2)
    with tempfile.TemporaryDirectory() as ast_dir, tempfile.TemporaryDirectory() as cpx_dir:
        ast_trs = Path(ast_dir) / "ast.ari"
        cpx_trs = Path(cpx_dir) / "cpx.ari"
        s.mkinput(ast_trs, "(GOAL AST)", *extra_goal_lines, benchmark=benchmark)
        s.mkinput(cpx_trs, "(GOAL COMPLEXITY)", *extra_goal_lines, benchmark=benchmark)

        if os.environ.get("PRINT_INPUT", "0") == "1":
            print("---BEGIN AST INPUT---", file=sys.stderr)
            print(*ast_trs.read_text().splitlines()[:20], sep="\n", file=sys.stderr)
            print("---BEGIN COMPLEXITY INPUT---", file=sys.stderr)
            print(*cpx_trs.read_text().splitlines()[:20], sep="\n", file=sys.stderr)
            print("---END---", file=sys.stderr)

        # Deadline for collecting both answers.
        deadline = time.monotonic() + to + _TEARDOWN_GRACE
        ans_ast, ans_cpx = _run_parallel(ast_trs, cpx_trs, to, deadline)

    return _combine(ans_ast, _sast_from_complexity(ans_cpx))


def _run_parallel(ast_trs: Path, cpx_trs: Path, to: int, deadline: float) -> tuple[str, str]:
    """Run the AST and COMPLEXITY solvers concurrently and return their stdout.

    Both processes are given AProVE's full ``-t`` budget so they normally
    self-terminate together shortly before ``deadline``. Any solver still alive
    at ``deadline`` is killed so we can still emit the best answer found so far.
    """
    procs = {
        "ast": s.start_plain(ast_trs, mode="wst", timeout=to),
        "cpx": s.start_plain(cpx_trs, mode="benchmark", timeout=to),
    }
    outs: dict[str, str] = {"ast": "", "cpx": ""}

    def _collect(key: str) -> None:
        outs[key] = procs[key].communicate()[0] or ""

    threads = {k: threading.Thread(target=_collect, args=(k,)) for k in procs}
    for t in threads.values():
        t.start()

    for t in threads.values():
        remaining = deadline - time.monotonic()
        if remaining > 0:
            t.join(remaining)

    # Kill anything that overran the deadline, then make sure the collector
    # threads have stored whatever output was produced before the kill.
    for proc in procs.values():
        if proc.poll() is None:
            _kill(proc)
    for t in threads.values():
        t.join()

    return outs["ast"], outs["cpx"]


def _sast_from_complexity(ans_cpx: str) -> str:
    """Derive a SAST yes/no answer from a complexity WORST_CASE(lower,upper) run.

    A finite expected-runtime upper bound (O(1)/O(n)/O(n^k)/EXP/2-EXP) proves SAST; 
    an INF lower bound disproves it. The returned string has the SAST
    verdict ("YES"/"NO"/"MAYBE") as its first line followed by the complexity proof, 
    so it can be fed straight into _combine.
    """
    lines = ans_cpx.splitlines(keepends=True)
    first = lines[0].strip() if ans_cpx.strip() else ""
    proof = "".join(lines[1:])

    verdict = "MAYBE"
    m = _WORST_CASE_RE.match(first)
    if m:
        lower, upper = m.group(1).strip(), m.group(2).strip()
        # The regex expects the upper bound flanked by delimiters, so wrap it.
        if _SAST_UPPER_RE.match(f"({upper})"):
            verdict = "YES"
        elif lower == "INF":
            verdict = "NO"
    return verdict + "\n" + proof


def _kill(proc: subprocess.Popen) -> None:
    try:
        if hasattr(os, "killpg"):
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        else:
            proc.kill()
    except (ProcessLookupError, PermissionError):
        proc.kill()


def _combine(ans_ast: str, ans_sast: str) -> str:
    """Turn the AST and SAST yes/no answers into a WORST_CASE(f,g) verdict."""
    ast_lines = ans_ast.splitlines(keepends=True)
    sast_lines = ans_sast.splitlines(keepends=True)
    first_ast = ast_lines[0].strip() if ans_ast.strip() else ""
    first_sast = sast_lines[0].strip() if ans_sast.strip() else ""
    ast_proof = "".join(ast_lines[1:])
    sast_proof = "".join(sast_lines[1:])

    # Upper bound g: SAST (YES) is stronger than AST (YES).
    if first_sast == "YES":
        upper, upper_proof = "SAST", sast_proof
    elif first_ast == "YES":
        upper, upper_proof = "AST", ast_proof
    else:
        upper, upper_proof = "?", ""

    # Lower bound f: Non-AST (AST disproven) is stronger than Non-SAST.
    if first_ast == "NO":
        lower, lower_proof = "Non-AST", ast_proof
    elif first_sast == "NO":
        lower, lower_proof = "Non-SAST", sast_proof
    else:
        lower, lower_proof = "?", ""

    proofs = [p for p in (upper_proof, lower_proof) if p]
    # The two proofs may coincide (same run justified both bounds); keep one.
    if len(proofs) == 2 and proofs[0] == proofs[1]:
        proofs = proofs[:1]
    return f"WORST_CASE({lower},{upper})\n" + "".join(proofs)
