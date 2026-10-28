#!/usr/bin/env python3
"""Run the scripts `roc main.roc` and `roc builtins.roc` print against SurrealDB and check every block.

Blocks are separated by one blank line; a block has no blank line inside.
Line 1 of a block is its header, then directive lines, then SurrealQL:
  -- schema | -- seed: T | -- accepts: N      all statements must be OK
  -- query: N | -- write: N                   last statement result is compared
       `-- roc: <SurrealQL literal>` (one line), `-- ordered` (else multiset)
  -- rejects: N  with `-- error: <substring>`  some statement must be ERR
Both scripts run, one after the other, in the same fresh database.
Runs `check_cuts.py` first.
Usage: check.py [path/to/roc] [--script FILE]... [--url U] [--user X] [--pass Y]
Env: SURREAL_URL (default http://localhost:8000), SURREAL_USER, SURREAL_PASS.
"""

import argparse
import base64
import decimal
import json
import os
import pathlib
import struct
import subprocess
import sys
import urllib.error
import urllib.request

HERE = pathlib.Path(__file__).resolve().parent
APPS = ["main.roc", "builtins.roc"]
NS, DB = "roc", "roc_surreal"
DOCKER = "docker run --rm -d -p 8000:8000 surrealdb/surrealdb:v3.3.4 start --user root --pass root memory"


class Server:
    def __init__(self, url, user, password):
        self.url = url.rstrip("/")
        self.auth = "Basic " + base64.b64encode(f"{user}:{password}".encode()).decode()

    def run(self, text, db=DB):
        """One HTTP request. Returns (statements, None) or (None, error text).

        The reply is CBOR, not JSON: JSON prints a decimal as a string, so
        it cannot tell the decimal 42 from the string "42". CBOR tags it.
        """
        headers = {"Accept": "application/cbor", "Content-Type": "text/plain",
                   "Authorization": self.auth, "surreal-ns": NS}
        if db:
            headers["surreal-db"] = db
        request = urllib.request.Request(self.url + "/sql", text.encode(), headers)
        try:
            return cbor(urllib.request.urlopen(request).read()), None
        except urllib.error.HTTPError as e:
            return None, f"HTTP {e.code} {e.read().decode()}"


def cbor(data):
    """Decodes one CBOR value. Only what SurrealDB sends is supported."""
    value, end = cbor_item(data, 0)
    assert end == len(data), "trailing bytes in the CBOR reply"
    return value


def cbor_item(data, at):
    major, info = data[at] >> 5, data[at] & 31
    at += 1
    if major == 7 and info in (25, 26, 27):
        size = {25: 2, 26: 4, 27: 8}[info]
        return struct.unpack(">" + {2: "e", 4: "f", 8: "d"}[size], data[at:at + size])[0], at + size
    if info < 24:
        arg = info
    else:
        size = {24: 1, 25: 2, 26: 4, 27: 8}[info]
        arg, at = int.from_bytes(data[at:at + size], "big"), at + size
    if major == 0:
        return arg, at
    if major == 1:
        return -1 - arg, at
    if major in (2, 3):
        raw = data[at:at + arg]
        return (raw if major == 2 else raw.decode()), at + arg
    if major == 4:
        items = []
        for _ in range(arg):
            item, at = cbor_item(data, at)
            items.append(item)
        return items, at
    if major == 5:
        pairs = {}
        for _ in range(arg):
            name, at = cbor_item(data, at)
            pairs[name], at = cbor_item(data, at)
        return pairs, at
    if major == 6:
        inner, at = cbor_item(data, at)
        if arg == 10:  # a decimal, sent as its text
            # -0 equals 0 in SurrealQL (`math::ceil(-0.5dec)` is -0), so one text stands for both.
            number = decimal.Decimal(inner).normalize()
            return {"$decimal": "0" if number == 0 else str(number)}, at
        if arg == 6:  # NONE
            return None, at
        return {"$tag": arg, "value": inner}, at
    return {20: False, 21: True, 22: None, 23: None}[arg], at


def normal(value):
    # NONE is a missing key or null, so a null field is dropped before comparing.
    # A decimal is already normalised by `cbor`, so "42" and 42dec stay apart.
    if isinstance(value, dict):
        return {k: normal(v) for k, v in value.items() if v is not None}
    if isinstance(value, list):
        return [normal(v) for v in value]
    return value


def key(value):
    return json.dumps(value, sort_keys=True)


def split_block(block):
    """Returns (header, directives, body) for one block."""
    lines = block.strip().split("\n")
    directives = {}
    body = []
    for line in lines[1:]:
        if line == "-- ordered":
            directives["ordered"] = True
        elif line.startswith("-- roc: "):
            directives["roc"] = line.removeprefix("-- roc: ")
        elif line.startswith("-- error: "):
            directives["error"] = line.removeprefix("-- error: ")
        else:
            body.append(line)
    return lines[0], directives, "\n".join(body)


def check_block(server, header, directives, body):
    """Returns None when the block agrees, else a failure text."""
    kind, _, name = header.removeprefix("-- ").partition(": ")
    if kind not in ("schema", "seed", "query", "write", "rejects", "accepts"):
        return "unknown block header"
    statements, error = server.run(body)
    if error:
        return error
    errors = [s["result"] for s in statements if s["status"] != "OK"]
    if kind == "rejects":
        if not errors:
            return "the database accepted this write"
        want = directives.get("error")
        if want and not any(want in str(e) for e in errors):
            return f"error does not contain {want!r}; got {errors}"
        return None
    if errors:
        return f"database error: {errors[0]}"
    if kind in ("query", "write") and "roc" in directives:
        # The server evaluates the Roc literal, so both sides share a serialiser.
        reference, error = server.run(f"RETURN {directives['roc']};")
        if error or reference[0]["status"] != "OK":
            return f"bad -- roc literal: {error or reference[0]['result']}"
        got, want = normal(statements[-1]["result"]), normal(reference[0]["result"])
        if not directives.get("ordered") and isinstance(got, list) and isinstance(want, list):
            got, want = sorted(got, key=key), sorted(want, key=key)
        if got != want:
            if isinstance(got, list) and isinstance(want, list):
                # A long result: show only the rows that differ.
                got_keys, want_keys = {key(v) for v in got}, {key(v) for v in want}
                if got_keys != want_keys:
                    return (f"Roc computed {json.dumps([v for v in want if key(v) not in got_keys])}, "
                            f"database returned {json.dumps([v for v in got if key(v) not in want_keys])} (rows that differ)")
            return f"Roc computed {json.dumps(want)}, database returned {json.dumps(got)}"
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("roc", nargs="?", default=str(HERE.parents[2] / "zig-out" / "bin" / "roc"))
    parser.add_argument("--script", action="append", help="run this script file instead of calling roc (repeatable)")
    parser.add_argument("--url", default=os.environ.get("SURREAL_URL", "http://localhost:8000"))
    parser.add_argument("--user", default=os.environ.get("SURREAL_USER", "root"))
    parser.add_argument("--pass", dest="password", default=os.environ.get("SURREAL_PASS", "root"))
    args = parser.parse_args()

    # The cut lists first: a list that lacks a name shows only as a refusal in one nominal.
    if subprocess.run([sys.executable, str(HERE / "check_cuts.py")]).returncode:
        sys.exit(1)

    server = Server(args.url, args.user, args.password)
    try:
        urllib.request.urlopen(server.url + "/health")
    except OSError as e:
        print(f"Cannot reach SurrealDB at {server.url}: {e}\nStart one with:\n  {DOCKER}")
        sys.exit(2)

    if args.script:
        scripts = [pathlib.Path(f).read_text() for f in args.script]
    else:
        scripts = [subprocess.run([args.roc, str(HERE / app)], capture_output=True, text=True, check=True).stdout
                   for app in APPS]
    script = "\n\n".join(text.strip("\n") for text in scripts)

    # A fresh database for every run.
    _, error = server.run(f"DEFINE NAMESPACE IF NOT EXISTS {NS};", db=None)
    if not error:
        _, error = server.run(f"DEFINE DATABASE IF NOT EXISTS {DB}; REMOVE DATABASE {DB}; DEFINE DATABASE {DB};", db=None)
    if error:
        print(f"Cannot prepare the database: {error}")
        sys.exit(2)

    failures = 0
    total = 0
    for block in script.split("\n\n"):
        if not block.strip():
            continue
        header, directives, body = split_block(block)
        total += 1
        if "unsupported" in header or "bad schema" in header:
            problem = "the Roc program reported an error"
        elif not header.startswith("-- "):
            problem = "block does not start with a `-- ` header"
        else:
            problem = check_block(server, header, directives, body)
        print(f"{'FAIL' if problem else 'ok  '} {header.removeprefix('-- ')}")
        if problem:
            print(f"     {problem}")
            failures += 1
    print(f"{total - failures}/{total} blocks agree")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
