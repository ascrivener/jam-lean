#!/usr/bin/env python3
"""Generate `JAM/Constants.lean` from the Gray Paper's `text/definitions.tex`.

Usage:  python3 -I scripts/gen_constants.py <path/to/graypaper/text/definitions.tex> <output.lean>

Reads every `\\item[$\\NAME = value$]` whose NAME is a constant macro (`\\C…`), including the
host-call gas constants (`\\Cgas…`, §I.4.4 "Host-call gas") and the per-case `fetch` constants
(`\\CgasYc{n} = a, \\CgasYl{n} = b`, and `\\CgasYunknown = a` for an unknown case, which v0.8.1
writes instead of v0.8.0's `\\CgasYc{\\none} = a, \\CgasYl{\\none} = 0`). The Lean names are the paper's macro names, so each value can be
traced back to its definition. Anything unrecognised is an error.

The descriptions are the paper's, with its cross-references resolved: `\\ref{sec:…}` becomes §N
and `\\ref{eq:…}` eq. (N), the numbers the v0.8.1 PDF prints (`scripts/gp-labels.json`, built by
`scripts/gp_labels_from_pdf.py`); a label missing from that table is dropped. `\\texttt{x}` becomes
`x` in backticks and `\\,` a space. Math stays as the paper writes it, with the paper's macros, which
the docs site renders (`docs/site/gp-macros.js`).
"""

import json
import os

import re
import sys

LABELS = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "gp-labels.json"),
                        encoding="utf-8"))["labels"]


def resolve_refs(desc):
    """The paper's \\ref{…} as the PDF prints them: §N for a section, eq. (N) for an equation."""
    d = re.sub(r"\b(?:[Ss]ections?|[Ee]quations?)\s+(?=\\ref\{sec:)", "", desc)
    d = re.sub(r"\b[Ee]quation\s+(?=\\ref\{eq:)", "eq. ", d)
    d = re.sub(r"\b[Ee]quations\s+(?=\\ref\{eq:)", "eqs. ", d)

    def one(m):
        n = LABELS.get(m.group(1))
        if n is None:
            return ""
        return "§" + n if m.group(1).startswith("sec:") else "(" + n + ")"
    d = re.sub(r"\\ref\{([^}]*)\}", one, d)
    d = re.sub(r"\\texttt\{([^}]*)\}", r"`\1`", d)
    return d.replace("\\,", " ")


def fail(msg):
    sys.stderr.write(f"gen_constants: {msg}\n")
    sys.exit(1)


def value(expr, name):
    """Evaluate a constant's right-hand side: digits with thousands commas, `a\\cdot2^{b}`, or a
    derived expression whose final `= N` gives the value."""
    expr = expr.strip()
    if "=" in expr:
        expr = expr.rsplit("=", 1)[1].strip()
    expr = expr.replace(",", "").replace("\\cdot", "*").replace(" ", "")
    expr = re.sub(r"\^\{(\d+)\}", r"**\1", expr)
    expr = re.sub(r"\^(\d+)", r"**\1", expr)
    if not re.fullmatch(r"[0-9*]+", expr):
        return None
    return eval(expr)  # only digits and * at this point


def main():
    if len(sys.argv) != 3:
        fail("usage: gen_constants.py <definitions.tex> <out.lean>")
    src = open(sys.argv[1], encoding="utf-8").read()
    consts, fetch = [], {}
    for m in re.finditer(r"\\item\[\$(.*?)\$\]\s*(.*)", src):
        head, desc = m.group(1), m.group(2).strip()
        fm = re.fullmatch(r"\\CgasYc\{(\\none|\d+)\}\s*=\s*(\d+),\s*\\CgasYl\{(\\none|\d+)\}\s*=\s*(\d+)", head)
        if fm:
            key = "none" if fm.group(1) == "\\none" else int(fm.group(1))
            fetch[key] = (int(fm.group(2)), int(fm.group(4)))
            continue
        um = re.fullmatch(r"\\CgasYunknown\s*=\s*(\d+)", head)
        if um:
            fetch["none"] = (int(um.group(1)), 0)
        cm = re.fullmatch(r"\\(C[A-Za-z]+)\s*=\s*(.*)", head)
        if not cm:
            continue
        name, rhs = cm.group(1), cm.group(2)
        v = value(rhs, name)
        if v is None:
            # Non-numeric constants (e.g. byte strings) are out of scope here.
            continue
        desc = resolve_refs(re.sub(r"\s+", " ", desc))
        consts.append((name, v, desc))
    names = [n for n, _, _ in consts]
    if len(set(names)) != len(names):
        fail("duplicate constant")
    expected_fetch = set(range(16)) | {"none"}
    if set(fetch) != expected_fetch:
        fail(f"fetch gas cases: {sorted(map(str, fetch))}")
    for required in ["Citemdeposit", "Cbytedeposit", "Cbasedeposit", "CgasG", "CgasRconst",
                     "CgasWconst", "CgasI", "CgasLconst", "CgasGeminiconst", "Ccorecount"]:
        if required not in names:
            fail(f"missing constant {required}")

    L = ["/-",
         "  GENERATED FILE: do not edit by hand.",
         "  Produced by `scripts/gen_constants.py` from the Gray Paper v0.8.1, `text/definitions.tex`.",
         "  CI regenerates it from the pinned paper and fails on any difference.",
         "-/",
         "",
         "namespace JAM.Constants",
         ""]
    for name, v, desc in consts:
        d = desc.replace("-/", "- /")
        if len(d) > 300:
            d = d[:297] + "..."
        L.append(f"/-- {d} -/")
        L.append(f"def {name} : Nat := {v}")
        L.append("")
    L.append("/-- 𝖬_{Y,c,c} and 𝖬_{Y,c,ℓ}: the constant and per-1024-octet gas of `fetch` case `c`")
    L.append("    (`none` for an unknown case). -/")
    L.append("def CgasY : Option Nat → Nat × Nat")
    for k in range(16):
        L.append(f"  | some {k} => ({fetch[k][0]}, {fetch[k][1]})")
    L.append(f"  | _ => ({fetch['none'][0]}, {fetch['none'][1]})")
    L.append("")
    L.append("end JAM.Constants")
    L.append("")
    open(sys.argv[2], "w", encoding="utf-8").write("\n".join(L))


if __name__ == "__main__":
    main()
