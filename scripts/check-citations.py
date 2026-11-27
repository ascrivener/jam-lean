#!/usr/bin/env python3
"""Check that every note the book and the model cite exists in docs/upstream-candidates.md.

Usage:  python3 -I scripts/check-citations.py        (exit 1 on a bad citation)

A note is a row of one of the tables in `docs/upstream-candidates.md`; its id is the row's first
cell, a number (`| 27 | …`, also `| 23 (first part) | …`) or a v0.8.1 id (`| v0.8.1-A18 | …`).
A row whose text says "withdrawn" or "retired" is withdrawn.

Scanned: the book's chapters (`docs/site/Companion.lean`, `docs/site/Companion/*.lean`) and every
`.lean` file of `JAM/`, `PVM/` and `JamCrypto/`. A citation is `v0.8.1-A<n>`, or "note <n>" /
"notes <n>, <m> and <k>". A line that mentions the README is skipped: the README's own list of notes
on the paper (section "Notes on the paper and the vectors") has a few entries of its own.
Each citation must name an existing, not withdrawn, note.
"""

import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def notes():
    ids, withdrawn = set(), set()
    for line in open(os.path.join(ROOT, "docs", "upstream-candidates.md"), encoding="utf-8"):
        m = re.match(r"\|\s*(v0\.8\.1-A\d+|\d+)\b", line)
        if not m:
            continue
        ids.add(m.group(1))
        if re.search(r"(?i)\b(withdrawn|retired)\b", line):
            withdrawn.add(m.group(1))
    return ids, withdrawn


def citations(line):
    for m in re.finditer(r"v0\.8\.1-A\d+", line):
        yield m.group(0)
    for m in re.finditer(r"\b[Nn]otes?\s+((?:\d+|v0\.8\.1-A\d+)(?:(?:,\s*|\s+and\s+)(?:\d+|v0\.8\.1-A\d+))*)", line):
        for n in re.findall(r"\b\d+\b", re.sub(r"v0\.8\.1-A\d+", "", m.group(1))):
            yield n


def main():
    ids, withdrawn = notes()
    files = [os.path.join(ROOT, "docs", "site", "Companion.lean")]
    files += sorted(glob.glob(os.path.join(ROOT, "docs", "site", "Companion", "*.lean")))
    for d in ["JAM", "PVM", "JamCrypto"]:
        files += sorted(glob.glob(os.path.join(ROOT, d, "**", "*.lean"), recursive=True))
    bad = 0
    for f in files:
        for k, line in enumerate(open(f, encoding="utf-8"), 1):
            if "README" in line:
                continue
            for c in citations(line):
                why = "no such note" if c not in ids else "withdrawn" if c in withdrawn else None
                if why:
                    bad += 1
                    print(f"{os.path.relpath(f, ROOT)}:{k}: note {c}: {why} in docs/upstream-candidates.md")
    print(f"check-citations: {len(ids)} notes, {bad} bad citation(s)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
