from pathlib import Path

from handlers.PTRS_Standard import _run

# The competition output is WORST_CASE(f,g) with the lower bound f and upper
# bound g, see TermCompRules/ptrs.tex:
#   f in {? < Non-SAST < Non-AST}   (lower bound)
#   g in {? < AST < SAST}           (upper bound)
# These strings are dynamic, so the category must run with RAW_RESULT=true.
RESULT_LABELS = ["WORST_CASE", "MAYBE", "KILLED", "ERROR"]


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    # Same pipeline as PTRS_Standard, but restricted to the innermost strategy.
    return _run(timeout, benchmark, extra_goal_lines=("(STRATEGY INNERMOST)",))
