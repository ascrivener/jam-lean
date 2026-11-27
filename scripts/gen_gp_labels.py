#!/usr/bin/env python3
"""Generate `docs/site/gp-labels.json`: the Gray Paper's version and its section labels with their
printed numbers, the one source of every paper link and number in the companion book.

Usage:  python3 -I scripts/gen_gp_labels.py <path/to/graypaper> <out.json>

Sections are numbered as LaTeX numbers them: `graypaper.tex`'s `\\input` files in order, counting
`\\section`, `\\subsection` and `\\subsubsection` (starred forms are unnumbered), with letters after
`\\appendix`. A `\\label{sec:…}` that follows a heading (before the next heading or paragraph of
text) names it. The version and commit are those of the pinned paper (`scripts/fetch-paper.sh`).

The book's `Companion/Paper.lean` reads this table (``{gpsec}`sec:epochmarker` `` renders "§6.6",
``{gpchapter}`…` `` a chapter's section with its title); an unknown label fails the build. Moving to a
new paper version: update `VERSION`/`COMMIT` below with the pin, regenerate, and rebuild the book
(CLAUDE.md's version-change checklist).
"""

import json
import os
import re
import string
import sys

VERSION = "0.8.1"
COMMIT = "b7044ad"  # tag v0.8.1 of gavofyork/graypaper (b7044addaf48a09f235531f6188c5e7418bed410)

HEAD = re.compile(r"\\(section|subsection|subsubsection)(\*?)\s*(?:\[[^\]]*\])?\s*\{")


def strip_comments(src):
    return "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in src.split("\n"))


def main():
    if len(sys.argv) != 3:
        sys.exit("usage: gen_gp_labels.py <graypaper dir> <out.json>")
    root = sys.argv[1]
    main_tex = strip_comments(open(os.path.join(root, "graypaper.tex"), encoding="utf-8").read())
    body = main_tex.split("\\begin{document}", 1)[1]
    events = []  # ("appendix",) or ("file", path) in document order
    for m in re.finditer(r"\\appendix\b|\\input\{([^}]*)\}", body):
        events.append(("appendix", None) if m.group(0) == "\\appendix" else ("file", m.group(1)))

    counters = [0, 0, 0]
    appendix = False
    labels, titles = {}, {}
    for kind, path in events:
        if kind == "appendix":
            appendix, counters = True, [0, 0, 0]
            continue
        f = os.path.join(root, path if path.endswith(".tex") else path + ".tex")
        src = strip_comments(open(f, encoding="utf-8").read())
        heads = list(HEAD.finditer(src))
        for i, m in enumerate(heads):
            level = ["section", "subsection", "subsubsection"].index(m.group(1))
            if m.group(2) == "*":
                continue
            counters[level] += 1
            for k in range(level + 1, 3):
                counters[k] = 0
            top = string.ascii_uppercase[counters[0] - 1] if appendix else str(counters[0])
            number = ".".join([top] + [str(c) for c in counters[1:level + 1]])
            # the title (balanced braces) and the labels right after the heading
            depth, j = 1, m.end()
            while depth:
                depth += {"{": 1, "}": -1}.get(src[j], 0)
                j += 1
            title = re.sub(r"\s+", " ", src[m.end():j - 1]).strip()
            end = heads[i + 1].start() if i + 1 < len(heads) else len(src)
            after = src[j:end]
            para = re.search(r"\n\s*\n", after)
            window = after[:para.start()] if para else after
            for lab in re.findall(r"\\label\{(sec:[^}]*)\}", window[:400]):
                if lab in labels:
                    sys.exit(f"gen_gp_labels: label {lab} defined twice")
                labels[lab] = number
            titles[number] = title
    out = {
        "generator": "scripts/gen_gp_labels.py",
        "version": VERSION,
        "commit": COMMIT,
        "sections": labels,
        "titles": titles,
    }
    with open(sys.argv[2], "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1, sort_keys=True)
        fh.write("\n")


if __name__ == "__main__":
    main()
