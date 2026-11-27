#!/usr/bin/env python3
"""Build `scripts/gp-labels.json`: the printed number of each `\\ref` label used by the constants in
the Gray Paper's `text/definitions.tex`, for `scripts/gen_constants.py`.

Usage:  pdftotext -layout graypaper-0.8.1.pdf gp.txt
        python3 -I scripts/gp_labels_from_pdf.py <definitions.tex> <gp.txt> <out.json>

LaTeX numbers sections and equations when it typesets the paper; the TeX sources alone do not say
which number a label gets. The paper's appendix of constants prints each constant's description
with its references resolved ("See equation 9.8."), so this script finds each constant's
description in the text of the release PDF (the v0.8.1 release asset) and reads the numbers in
order. A description that cannot be found, or whose count of numbers does not match its count of
`\\ref`s, is an error. Run it once per paper version and commit the result.
"""

import json
import re
import sys

NUM = r"((?:[A-Z]|\d+)(?:\.\d+)+|\d+)"


def plain(tex):
    """The leading plain-text part of a description, as the PDF prints it."""
    t = re.split(r"\$|\\ref", tex, maxsplit=1)[0]
    t = re.sub(r"\\(?:textsc|texttt|emph|textit|textbf)\{([^}]*)\}", r"\1", t)
    t = t.replace("\\,", " ").replace("~", " ")
    t = re.split(r"\bSee\b", t, maxsplit=1)[0]  # keep "See equation" for the number search
    return re.sub(r"\s+", " ", t).strip()


def main():
    if len(sys.argv) != 4:
        sys.exit("usage: gp_labels_from_pdf.py <definitions.tex> <gp.txt> <out.json>")
    src = open(sys.argv[1], encoding="utf-8").read()
    pdf = re.sub(r"\s+", " ", open(sys.argv[2], encoding="utf-8").read())
    labels = {}
    for m in re.finditer(r"\\item\[\$(\\C[A-Za-z]+.*?)\$\]\s*(.*)", src):
        desc = m.group(2)
        refs = re.findall(r"\\ref\{([^}]*)\}", desc)
        if not refs:
            continue
        key = plain(desc)
        if len(key) < 15:
            sys.exit(f"gp_labels_from_pdf: description too short to locate: {desc[:60]!r}")
        hits = [h.start() for h in re.finditer(re.escape(key), pdf)]
        if not hits:
            sys.exit(f"gp_labels_from_pdf: not found in the PDF text: {key!r}")
        # The appendix of constants is the last place the paper prints the description.
        tail = pdf[hits[-1] + len(key):hits[-1] + len(key) + 400]
        # The numbers of each "See …" sentence (a dot ends it unless a digit follows).
        nums = [n for sent in re.findall(r"\bSee\b((?:[^.]|\.(?=\d))*)", tail)
                for n in re.findall(r"(?<![\w.])" + NUM + r"(?![\w])", sent)]
        if len(nums) < len(refs):
            sys.exit(f"gp_labels_from_pdf: {len(refs)} refs but {len(nums)} numbers after {key!r}")
        for r, n in zip(refs, nums):
            if labels.get(r, n) != n:
                sys.exit(f"gp_labels_from_pdf: {r} read as both {labels[r]} and {n}")
            labels[r] = n
    with open(sys.argv[3], "w", encoding="utf-8") as fh:
        json.dump({"source": "Gray Paper v0.8.1 release PDF, appendix of constants",
                   "generator": "scripts/gp_labels_from_pdf.py", "labels": labels},
                  fh, indent=1, sort_keys=True)
        fh.write("\n")


if __name__ == "__main__":
    main()
