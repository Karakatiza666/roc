#!/usr/bin/env python3
"""Run the script `roc main.roc` prints against SQLite, and compare each query
that carries a `-- roc:` line with the rows Roc computed from the same
functions over the same seed rows.

    python3 examples/reifying/sql/check.py [path/to/roc]
"""

import json
import pathlib
import sqlite3
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent
ROC = sys.argv[1] if len(sys.argv) > 1 else str(HERE.parents[2] / "zig-out" / "bin" / "roc")


def normalized(rows):
    # SQLite computes NUMERIC arithmetic in floating point, and Roc in Dec, so
    # a total can differ in the last few bits. Order is compared separately.
    return [{k: round(v, 6) if isinstance(v, float) else v for k, v in row.items()} for row in rows]


def main():
    script = subprocess.run([ROC, str(HERE / "main.roc")], capture_output=True, text=True, check=True).stdout
    db = sqlite3.connect(":memory:")
    db.execute("PRAGMA foreign_keys = ON")
    failures = 0
    for block in script.split("\n\n"):
        lines = block.strip().split("\n")
        header = lines[0]
        if "unsupported" in header or "bad schema" in header:
            print(f"FAIL {header}")
            failures += 1
            continue
        if not header.startswith("-- query: "):
            db.executescript("\n".join(lines))
            continue
        name = header.removeprefix("-- query: ")
        # A statement with `?` placeholders carries its values on a line of
        # their own, and the driver binds them.
        params = [json.loads(line.removeprefix("-- params: ")) for line in lines[1:] if line.startswith("-- params: ")]
        sql = "\n".join(line for line in lines[1:] if not line.startswith("-- roc:") and not line.startswith("-- params: "))
        cursor = db.execute(sql, params[0] if params else ())
        columns = [c[0] for c in cursor.description]
        got = normalized([dict(zip(columns, row)) for row in cursor.fetchall()])
        print(f"-- {name}")
        for row in got:
            print(f"   {row}")
        reference = [line.removeprefix("-- roc: ") for line in lines if line.startswith("-- roc: ")]
        if reference and reference[0]:
            want = normalized(json.loads(reference[0]))
            key = lambda row: json.dumps(row, sort_keys=True)
            if sorted(got, key=key) == sorted(want, key=key):
                print("   agrees with Roc")
            else:
                print(f"   FAIL: Roc computed {want}")
                failures += 1
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
