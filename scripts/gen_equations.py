#!/usr/bin/env python3
"""Generate `docs/site/gp-equations.json`: every numbered equation of the pinned Gray Paper, with its
printed number, its label (if the paper gives one) and a fingerprint of its TeX.

Usage:  python3 -I scripts/gen_equations.py <path/to/graypaper> <out.json> [--aux graypaper.aux]

Numbering is LaTeX's, recomputed from the sources: `graypaper.tex`'s `\\input` files in order;
`\\numberwithin{equation}{section}`, so each `\\section` (letters after `\\appendix`) restarts the
count; `equation` takes one number, and `align` and `gather` one per row (rows split at top-level
`\\\\`), except rows with
`\\nonumber` or `\\notag`. An `eq:` label outside a numbered environment takes the number of the last heading
(as in LaTeX, where an equation's counter step is local to its environment). Starred environments take none.

`--aux FILE` checks the result against LaTeX's own numbering: the `.aux` of a build of the same tag
(`xelatex graypaper.tex` in a checkout of it). Every `\\newlabel{eq:…}` must have the number computed
here, or the script fails. CI runs without it (no TeX there) and only checks that the table matches
the sources; run it with `--aux` once per paper version, when the pin moves.

Each entry's `body` is the equation's TeX as the paper writes it (labels removed, a `\\ref` replaced by
the printed number), for the book to render with the paper's macros (`docs/site/gp-macros.js`).

The fingerprint is a short hash of the equation's TeX (the row's, for `align`/`gather`), with
labels and whitespace removed. A version move can remap the book's equation numbers through it:
an equation whose TeX is unchanged keeps its identity under a new number, and one whose TeX changed
needs a look.
"""

import hashlib
import json
import os
import re
import string
import sys

VERSION = "0.8.1"
COMMIT = "b7044ad"
ENVS = ("equation", "align", "gather")
TOKEN = re.compile(r"\\(?:sub)*section(\*?)\s*(?:\[[^\]]*\])?\s*\{|\\begin\{(equation|align|gather)(\*?)\}|\\label\{(eq:[^}]*)\}")


def strip_comments(src):
    return "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in src.split("\n"))


def env_body(src, start, env):
    """The body of the environment whose \\begin ends at `start`, and the index after its \\end."""
    end = src.index("\\end{" + env + "}", start)
    return src[start:end], end + len("\\end{" + env + "}")


def rows(body):
    """Split an align/gather body at top-level \\\\ (outside braces and nested environments)."""
    out, cur, depth, i = [], [], 0, 0
    while i < len(body):
        if body.startswith("\\begin{", i):
            depth += 1
        elif body.startswith("\\end{", i):
            depth -= 1
        c = body[i]
        if c == "\\" and body.startswith("\\\\", i) and depth == 0:
            out.append("".join(cur))
            cur = []
            i += 2
            continue
        if c == "\\" and i + 1 < len(body):
            cur.append(body[i:i + 2])
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
        cur.append(c)
        i += 1
    out.append("".join(cur))
    # A trailing \\ leaves an empty last row, which amsmath's align still numbers.
    return out


def fingerprint(tex):
    t = re.sub(r"\\label\{[^}]*\}", "", tex)
    t = re.sub(r"\s+", "", t)
    return hashlib.sha256(t.encode("utf-8")).hexdigest()[:10]


def main():
    args = sys.argv[1:]
    aux = None
    if "--aux" in args:
        k = args.index("--aux")
        aux = args[k + 1]
        args = args[:k] + args[k + 2:]
    if len(args) != 2:
        sys.exit("usage: gen_equations.py <graypaper dir> <out.json> [--aux graypaper.aux]")
    root, out_path = args
    main_tex = strip_comments(open(os.path.join(root, "graypaper.tex"), encoding="utf-8").read())
    body = main_tex.split("\\begin{document}", 1)[1]
    events = [("appendix", None) if m.group(0) == "\\appendix" else ("file", m.group(1))
              for m in re.finditer(r"\\appendix\b|\\input\{([^}]*)\}", body)]

    sec, eqn, appendix = 0, 0, False
    sub = [0, 0]   # subsection, subsubsection counters
    last = [None]  # the last \\refstepcounter's value, as a \\label outside an equation sees it
    equations, labels = {}, {}

    def number():
        top = string.ascii_uppercase[sec - 1] if appendix else str(sec)
        return f"{top}.{eqn}"

    for kind, path in events:
        if kind == "appendix":
            appendix, sec, eqn = True, 0, 0
            continue
        f = os.path.join(root, path if path.endswith(".tex") else path + ".tex")
        src = strip_comments(open(f, encoding="utf-8").read())
        i = 0
        while True:
            m = TOKEN.search(src, i)
            if not m:
                break
            if m.group(4):
                # an eq: label outside a numbered environment: LaTeX gives it the last heading's
                # number (an equation's \refstepcounter is local to its environment's group)
                if m.group(4) in labels:
                    sys.exit(f"gen_equations: label {m.group(4)} twice")
                labels[m.group(4)] = last[0]
                if last[0] in equations:
                    equations[last[0]].setdefault("labels", []).append(m.group(4))
                i = m.end()
                continue
            if re.match(r"\\(?:sub)*section", m.group(0)):
                if m.group(1) != "*":
                    if m.group(0).startswith("\\section"):
                        sec, eqn, sub = sec + 1, 0, [0, 0]
                        last[0] = string.ascii_uppercase[sec - 1] if appendix else str(sec)
                    else:
                        base = string.ascii_uppercase[sec - 1] if appendix else str(sec)
                        if m.group(0).startswith("\\subsubsection"):
                            sub[1] += 1
                        else:
                            sub = [sub[0] + 1, 0]
                        last[0] = f"{base}.{sub[0]}" + (f".{sub[1]}" if m.group(0).startswith("\\subsubsection") else "")
                i = m.end()
                continue
            env, star = m.group(2), m.group(3)
            inner, i = env_body(src, m.end(), env + star)
            if star:
                continue
            parts = [inner] if env == "equation" else rows(inner)
            for part in parts:
                if re.search(r"\\(nonumber|notag)\b", part):
                    continue
                eqn += 1
                n = number()
                labs = re.findall(r"\\label\{([^}]*)\}", part)
                body = re.sub(r"\\label\{[^}]*\}", "", part).strip()
                entry = {"hash": fingerprint(part), "file": path, "env": env, "body": body}
                eqlabs = [l for l in labs if l.startswith("eq:")]
                if eqlabs:
                    entry["labels"] = eqlabs
                for l in eqlabs:
                    if l in labels:
                        sys.exit(f"gen_equations: label {l} twice")
                    labels[l] = n
                equations[n] = entry

    # \ref inside a body: the printed number (equations from here, sections from gp-labels.json)
    secs = {}
    gl = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "docs", "site", "gp-labels.json")
    if os.path.exists(gl):
        secs = json.load(open(gl, encoding="utf-8"))["sections"]
    for n, e in equations.items():
        def ref(m):
            lab = m.group(1)
            num = labels.get(lab) or secs.get(lab)
            if num is None:
                sys.exit(f"gen_equations: equation {n} refers to unknown label {lab}")
            return "\\text{" + num + "}"
        e["body"] = re.sub(r"\\ref\{([^}]*)\}", ref, e["body"])

    if aux:
        txt = open(aux, encoding="utf-8", errors="replace").read()
        bad = []
        for m in re.finditer(r"\\newlabel\{(eq:[^}]*)\}\{\{([^}]*)\}", txt):
            if labels.get(m.group(1)) != m.group(2):
                bad.append(f"{m.group(1)}: LaTeX {m.group(2)}, computed {labels.get(m.group(1))}")
        if bad:
            sys.exit("gen_equations: numbering differs from the .aux:\n  " + "\n  ".join(bad))
        print(f"gen_equations: all {len(re.findall(r'newlabel.eq:', txt))} labelled equations agree with the .aux")

    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump({"generator": "scripts/gen_equations.py", "version": VERSION, "commit": COMMIT,
                   "equations": equations, "labels": labels}, fh, indent=1, sort_keys=True)
        fh.write("\n")


if __name__ == "__main__":
    main()
