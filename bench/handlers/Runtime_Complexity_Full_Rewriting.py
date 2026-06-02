from pathlib import Path
import lib.solver as s


def run(timeout: int, benchmark: Path, cert: bool) -> str:
    return s.run_complexity(benchmark, timeout, cert,
                            goal_lines=["(GOAL COMPLEXITY)", "(STARTTERM BASIC)"],
                            mode="wst")
