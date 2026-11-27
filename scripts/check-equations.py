#!/usr/bin/env python3
"""Check that the book takes its equations and equation numbers from the paper's table.

Usage:  python3 -I scripts/check-equations.py            (exit 1 on a problem)
        python3 -I scripts/check-equations.py --changed OLD.json
            (after regenerating docs/site/gp-equations.json for a new paper version: list the
            equations whose TeX changed and the chapters that use them)

The book's chapters (`docs/site/Companion/*.lean`) show the paper's equations with `{gpeq "6.24"}`
and cite numbers with ``{eq}`6.24` `` (both read `docs/site/gp-equations.json`, generated from the
paper's TeX by `scripts/gen_equations.py`, and fail the build on an unknown number). This check
keeps hand-typed numbers out:

* a hand-written display (`$$`…``) that carries an equation number (`\\text{(6.24)}`) must follow a
  `{transcribed "6.24" "<fingerprint>"}` paragraph naming the same numbers; that marker fails the
  build when the paper's equation changes;
* a number like "(6.24)" or "(14.6–14.8)" in prose, outside code and math, must be written
  ``{eq}`6.24` `` (a range: ``{eq}`14.6`–{eq}`14.8` ``);
* a heading stays plain text, but every equation number in it must exist in the paper.
"""

import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
NUM = r"(?:[1-9]\d?|[A-H])\.\d+"
TAG = re.compile(r"\\text\{\((" + NUM + r"(?:\s*,\s*" + NUM + r")*)\)\}")
PROSE = re.compile(r"\((" + NUM + r"(?:\s*(?:,|–|-)\s*" + NUM + r")*)\)")
HEADING_NUM = re.compile(r"(?<![\w.])" + NUM + r"(?![\w.]*\d)")
SKIP = ("Paper.lean", "Source.lean", "Docstring.lean")


def chapters():
    return [f for f in sorted(glob.glob(os.path.join(ROOT, "docs", "site", "Companion", "*.lean")))
            if not f.endswith(SKIP)]


def numbers_used(src):
    used = set()
    for m in re.finditer(r'\{(?:gpeq|transcribed) "([^"]*)"', src):
        used |= {n.strip() for n in m.group(1).split(",")}
    for m in re.finditer(r"\{eq\}`([^`]*)`", src):
        used |= {n.strip() for n in m.group(1).split(",")}
    return used


def changed(old_path):
    old = json.load(open(old_path, encoding="utf-8"))["equations"]
    new = json.load(open(os.path.join(ROOT, "docs", "site", "gp-equations.json"), encoding="utf-8"))["equations"]
    old_by_hash = {e["hash"]: n for n, e in old.items()}
    moved = {n: old_by_hash[e["hash"]] for n, e in new.items() if e["hash"] in old_by_hash and old_by_hash[e["hash"]] != n}
    gone = sorted(n for n, e in old.items() if e["hash"] not in {x["hash"] for x in new.values()})
    print(f"{len(gone)} equation(s) of the old version whose TeX changed or which were removed:")
    users = {}
    for f in chapters():
        used = numbers_used(open(f, encoding="utf-8").read())
        for n in used:
            users.setdefault(n, []).append(os.path.relpath(f, ROOT))
    for n in gone:
        print(f"  ({n})" + (f"  used by {', '.join(users[n])}" if n in users else ""))
    print(f"{len(moved)} equation(s) with unchanged TeX under a new number (old → new):")
    for n, o in sorted(moved.items()):
        print(f"  ({o}) → ({n})" + (f"  used by {', '.join(users[o])}" if o in users else ""))


def main():
    if sys.argv[1:2] == ["--changed"]:
        changed(sys.argv[2])
        return
    table = json.load(open(os.path.join(ROOT, "docs", "site", "gp-equations.json"), encoding="utf-8"))["equations"]
    bad = []
    for f in chapters():
        lines = open(f, encoding="utf-8").read().split("\n")
        inblock = False
        for k, line in enumerate(lines):
            rel = f"{os.path.relpath(f, ROOT)}:{k + 1}"
            if line.startswith("```"):
                inblock = not inblock
                continue
            if inblock:
                continue
            if line.lstrip().startswith("$$`"):
                tags = [n.strip() for m in TAG.finditer(line) for n in m.group(1).split(",")]
                if not tags:
                    continue
                prev = next((lines[j] for j in range(k - 1, -1, -1) if lines[j].strip()), "")
                pm = re.match(r'\{transcribed "([^"]*)"', prev)
                marked = {n.strip() for n in pm.group(1).split(",")} if pm else set()
                if marked != set(tags):
                    bad.append(f"{rel}: hand-written display of ({', '.join(tags)}): use {{gpeq \"{', '.join(tags)}\"}}, "
                               "or mark it {transcribed …} with the equation's fingerprint")
                continue
            if line.startswith("#"):
                # Headings stay plain text: their equation numbers must exist in the table.
                for n in HEADING_NUM.findall(re.sub(r"§\S+", "", line)):
                    if n not in table:
                        bad.append(f"{rel}: heading cites equation ({n}), which the paper does not have")
                continue
            if line.startswith(("{", "import", "open", "%%%", "set_option")):
                continue
            text = re.sub(r"\$?`[^`]*`", "", line)
            for m in PROSE.finditer(text):
                bad.append(f"{rel}: hand-typed equation number {m.group(0)}: write {{eq}}`N` (a range: {{eq}}`N`–{{eq}}`M`)")
    for b in bad:
        print(b)
    print(f"check-equations: {len(bad)} problem(s)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
