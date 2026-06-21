#!/usr/bin/env python3
"""
Serialize solver output:
  - Writes full stdout to results/<relative>.out
  - Appends a summary CSV row: relative path, first line, results/<relative>.out, absolute input path
Usage (stdin carries solver stdout):
  python serialize_result.py OUTDIR ROOT_PREFIX FILEPATH
"""

from __future__ import annotations

import csv
import datetime
import sys
import time
from pathlib import Path

VALID_RESULTS = ["YES", "NO", "MAYBE", "AST", "SAST", "ERROR", "KILLED"]

def _rel_path(root_prefix: Path, file_path: Path) -> str:
    try:
        return str(file_path.relative_to(root_prefix))
    except ValueError:
        return file_path.name


def _append_summary(summary: Path, rel: str, first_line: str, result_path: str, input_path: str, time_ms: int | None = None) -> None:
    lock = summary.with_suffix(summary.suffix + ".lock")
    while True:
        try:
            lock.mkdir()
            break
        except FileExistsError:
            time.sleep(0.01)
    try:
        header = ["File", "Result", "FullResult", "InputPath", "Time_ms"]
        rows: list[list[str]] = []
        if summary.exists():
            with summary.open("r", encoding="utf-8", newline="") as fh:
                rows = list(csv.reader(fh, delimiter=";"))
        # ensure header
        if not rows or rows[0] != header:
            rows = [header]

        data_rows = rows[1:]

        new_row = [rel, first_line, result_path, input_path, str(time_ms) if time_ms is not None else ""]

        replaced = False
        for idx, row in enumerate(data_rows):
            if row and row[0] == rel:
                data_rows[idx] = new_row
                replaced = True
                break
        if not replaced:
            data_rows.append(new_row)
            data_rows.sort(key=lambda r: r[0])

        rows = [header] + data_rows
        with summary.open("w", encoding="utf-8", newline="") as fh:
            writer = csv.writer(fh, delimiter=";")
            writer.writerows(rows)
    finally:
        lock.rmdir()


def serialize(outdir: Path, root_prefix: Path, file_path: Path, content: str, raw_first_line: bool = False, time_ms: int | None = None) -> None:
    rel = _rel_path(root_prefix, file_path)
    results_dir = outdir / "results"
    outfile = results_dir / f"{rel}.out"
    outfile.parent.mkdir(parents=True, exist_ok=True)
    results_dir.mkdir(parents=True, exist_ok=True)

    outfile.write_text(content, encoding="utf-8")
    first_line = content.splitlines()[0] if content else ""
    if not raw_first_line and first_line not in VALID_RESULTS:
        first_line = "ERROR"
    summary = outdir / "summary.csv"
    _append_summary(summary, rel, first_line, f"results/{rel}.out", str(file_path), time_ms=time_ms)


_POSITIVE = {"YES", "NO", "AST", "SAST"}
_WEAK = {"MAYBE", "KILLED"}


def _conflict_type(old: str, new: str) -> str | None:
    """Return a conflict type string or None.

    BROKEN: any -> ERROR
    CONTRA: positive -> different positive  (YES<->NO, AST<->SAST, YES<->AST, etc.)
    BAD:    positive -> MAYBE/KILLED
    GOOD:   MAYBE/KILLED -> positive  |  ERROR -> any non-ERROR
    None:   same result or no meaningful disagreement (most recent wins)
    """
    if old == new:
        return None
    if new == "ERROR":
        return "BROKEN"
    if old in _POSITIVE and new in _POSITIVE:
        return "CONTRA"
    if old in _POSITIVE and new in _WEAK:
        return "BAD"
    if old in _WEAK and new in _POSITIVE:
        return "GOOD"
    if old == "ERROR" and new != "ERROR":
        return "GOOD"
    return None


def append_flat(csv_path: Path, problem: str, result: str, timeout: str, category: str, commit_id: str, time_ms: int | None = None) -> None:
    """Write a result row to the flat benchmark CSV.

    Deduplication by (Problem, Category):
    - No conflict with existing row(s) -> replace all matching rows with the new one (Conflict=NONE).
    - Any conflict -> keep all existing rows (tagged with conflict type) and append the new row.
    """
    lock = csv_path.with_suffix(csv_path.suffix + ".lock")
    while True:
        try:
            lock.mkdir()
            break
        except FileExistsError:
            time.sleep(0.01)
    try:
        header = ["Timestamp", "Problem", "Result", "Timeout", "Category", "CommitID", "Conflict", "Time_ms"]
        COL_PROBLEM, COL_RESULT, COL_CATEGORY, COL_CONFLICT = 1, 2, 4, 6

        data_rows: list[list[str]] = []
        if csv_path.exists():
            with csv_path.open("r", encoding="utf-8", newline="") as fh:
                rows = list(csv.reader(fh, delimiter=";"))
            data_rows = rows[1:] if rows and rows[0] and rows[0][0] == "Timestamp" else rows
            # Pad rows that predate the Conflict column (6→7) and/or Time_ms column (7→8)
            data_rows = [
                r + ["NONE"] * max(0, 7 - len(r)) + [""] * max(0, 8 - max(7, len(r)))
                for r in data_rows
            ]

        new_row = [
            datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
            problem,
            result,
            timeout,
            category,
            commit_id,
            "NONE",
            str(time_ms) if time_ms is not None else "",
        ]

        matches = [(i, r) for i, r in enumerate(data_rows)
                   if len(r) > COL_CATEGORY and r[COL_PROBLEM] == problem and r[COL_CATEGORY] == category]

        if matches:
            conflict = next((_conflict_type(r[COL_RESULT], result) for _, r in matches if _conflict_type(r[COL_RESULT], result)), None)
            if conflict:
                # Tag all existing matching rows with the conflict type (upgrade NONE if needed)
                for i, r in matches:
                    if r[COL_CONFLICT] == "NONE":
                        data_rows[i] = r[:COL_CONFLICT] + [conflict] + r[COL_CONFLICT + 1:]
                new_row[COL_CONFLICT] = conflict
                data_rows.append(new_row)
            else:
                # No result conflict: check for runtime improvement
                faster = False
                if time_ms is not None:
                    try:
                        old_ms = int(matches[-1][1][7] if len(matches[-1][1]) > 7 else "")
                        if time_ms < old_ms:
                            faster = True
                    except (ValueError, TypeError):
                        pass
                if faster:
                    # Keep existing rows, append new row tagged FASTER
                    new_row[COL_CONFLICT] = "FASTER"
                    data_rows.append(new_row)
                else:
                    # No change: drop all matching rows, append the new one
                    data_rows = [r for r in data_rows if not (len(r) > COL_CATEGORY and r[COL_PROBLEM] == problem and r[COL_CATEGORY] == category)]
                    data_rows.append(new_row)
        else:
            data_rows.append(new_row)

        csv_path.parent.mkdir(parents=True, exist_ok=True)
        with csv_path.open("w", encoding="utf-8", newline="") as fh:
            writer = csv.writer(fh, delimiter=";")
            writer.writerow(header)
            writer.writerows(data_rows)
    finally:
        lock.rmdir()


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write("Usage: serialize_result.py OUTDIR ROOT_PREFIX FILEPATH\n")
        return 2
    outdir = Path(argv[0])
    root_prefix = Path(argv[1])
    file_path = Path(argv[2])
    content = sys.stdin.read()
    serialize(outdir, root_prefix, file_path, content)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
