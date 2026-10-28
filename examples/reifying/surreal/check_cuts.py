#!/usr/bin/env python3
"""Check that every `code_primitives` list of the library holds the same names.

The reifier reads the cut of the nominal that owns the method with the `Code`
parameter (see `Surreal.code_primitives`), so `Surreal.roc` repeats the list
in each such nominal, and `TranslateTest.roc` has one more. The compiler does
not compare them: a name missing from one list shows only as a refusal where
a method of that nominal calls the function.

Fails when two lists differ, or when a nominal with a `Code` method has no
list. Usage: check_cuts.py
"""

import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
FILES = ["Surreal.roc", "TranslateTest.roc"]
# A nominal that takes `Code` and has no cut. An ordering names a result column, so it calls no function of the cut.
NO_CUT = {"Selected"}

LIST = re.compile(r"^(\t*)code_primitives = \((.*)\)$")
HEADER = re.compile(r"^\t([A-Z]\w*)(\([^)]*\))? ::?=? ")
FUNCTION = re.compile(r"^(\t+)[a-z_]\w* : (.*)$")


def names_of(text):
    """The names of one tuple, without the `Surreal.` prefix."""
    return {part.strip().removeprefix("Surreal.") for part in text.split(",")}


def read(file):
    """Each list as (owner, line number, names), and the nominals that have a `Code` method."""
    lists, coded = [], set()
    owner = "TranslateTest" if file == "TranslateTest.roc" else "Surreal"
    for number, line in enumerate((HERE / file).read_text().split("\n"), 1):
        header = HEADER.match(line)
        if header and file == "Surreal.roc":
            owner = header.group(1)
        found = LIST.match(line)
        if found:
            lists.append((owner, number, names_of(found.group(2))))
        method = FUNCTION.match(line)
        if method and file == "Surreal.roc" and re.search(r"\bCode[.(]", method.group(2)):
            # A method one tab deep belongs to `Surreal`, one two tabs deep to the nominal above it.
            coded.add(owner if len(method.group(1)) == 2 else "Surreal")
    return lists, coded


def main():
    found, coded = [], set()
    for file in FILES:
        lists, with_code = read(file)
        found += [(file, *item) for item in lists]
        coded |= with_code
    problems = []
    everything = set().union(*(names for *_, names in found))
    for file, owner, number, names in found:
        for name in sorted(everything - names):
            problems.append(f"{file}:{number} ({owner}) lacks {name}")
    listed = {owner for _, owner, _, _ in found}
    for owner in sorted(coded - listed - NO_CUT):
        problems.append(f"Surreal.roc: {owner} has a method that takes `Code` and no `code_primitives` list")
    if len(found) < 2:
        problems.append("fewer than two lists found; the pattern of a list changed")
    for problem in problems:
        print(problem)
    print(f"{len(found)} lists, {len(everything)} names, {len(problems)} problems")
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
