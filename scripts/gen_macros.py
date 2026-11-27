#!/usr/bin/env python3
"""Generate the Gray Paper macro table for the docs site from the paper's TeX sources.

Usage:  python3 -I scripts/gen_macros.py <path/to/graypaper> <out.json> <out.js>

Reads every `\\newcommand` / `\\renewcommand` (starred or not) in `preamble.tex` and `text/*.tex` of
the pinned paper (tag v0.8.1) and writes a JSON table that both renderers load: the book's KaTeX
(`docs/site/CompanionMain.lean`) and doc-gen4's MathJax (`docs/site/build-site.sh`).

Names. Write the paper's names, `¬` included (`\\wp¬authcode`). KaTeX and MathJax accept only
ASCII letters in a macro name, so the table keys replace each `¬` with the sentinel `QQ`
(`\\wpQQauthcode`), and both renderers apply the same rewrite to every formula before parsing it
(`gpMacroName` in the site scripts). No paper macro contains `QQ`, which this script checks.

Packages. A few bodies use commands of LaTeX packages that neither renderer has. `SUBST` maps
them to supported equivalents (applied to every body, longest first). A macro whose body still
uses something unsupported after that is left out of the table and listed under "unmapped" in the
output, with the reason; `UNMAPPED_OK` lists the ones known to be layout-only (not notation).

Optional arguments. KaTeX's macro table has no optional arguments, so a macro declared
`[n][default]` is entered for KaTeX with the default substituted for `#1` and n - 1 arguments; MathJax
gets the real optional argument. Such macros are listed under "optional".

`<out.js>` is the same table as a script for the site (`window.gpMacros`): `katex` (a preamble
of `\\newcommand`s, run once into a macro object, so each macro takes exactly its declared number of
arguments), `mathjax` (MathJax's `tex.macros` form) and `name` (the `¬` rewrite of a formula).

The output is deterministic (sorted keys), so CI can regenerate it and compare (scripts/check-tables.sh).
"""

import glob
import json
import os
import re
import sys


def fail(msg):
    sys.stderr.write(f"gen_macros: {msg}\n")
    sys.exit(1)


# Commands of LaTeX packages that KaTeX and MathJax lack, with supported equivalents.
SUBST = {
    r"\accentset": r"\overset",          # accents: \accentset{a}{b} puts a over b
    r"\bm": r"\boldsymbol",              # bm
    r"\nicefrac": r"\tfrac",             # nicefrac: a slanted fraction; an upright one reads the same
    r"\xspace": "",                      # xspace: spacing after text macros
    r"\left\lsem": r"[\![",              # \lsem/\rsem (sequence brackets): no such delimiters
    r"\right\rsem": r"]\!]",
    r"\lsem": r"[\![",
    r"\rsem": r"]\!]",
    r"\llbracket": r"[\![",              # stmaryrd; MathJax's TeX input lacks it
    r"\rrbracket": r"]\!]",
    r"\originalleft": r"\left",          # preamble.tex: \let\originalleft\left
    r"\originalright": r"\right",
    r"\textsc": r"\text",                # small caps: plain text
    r"\smaller": "",                     # relsize
    r"\larger": "",
    r"\textsmaller": r"\text",
    r"\lightning": r"\text{☇}",          # mathabx / stmaryrd
    r"\ensuremath": "",                  # always in math here; leaves the argument group
    r"\@": "",                           # end-of-sentence spacing in prose macros
    r"@{}": "",                           # array column specs: KaTeX has no @{…}
    r"\Aries": r"\text{♈}",              # marvosym zodiac signs (host-call gas names)
    r"\Taurus": r"\text{♉}",
    r"\Gemini": r"\text{♊}",
    r"\wideparen": r"\overparen",        # mathabx; KaTeX gets \overparen as \overgroup (KATEX_SHIMS)
    r"\left\langlebar": r"\left\langle",  # mathabx's barred angle brackets: plain angle brackets
    r"\right\ranglebar": r"\right\rangle",
    r"\langlebar": r"\langle",
    r"\ranglebar": r"\rangle",
}

# Symbols of LaTeX packages that the paper uses directly in its text (not through a macro of its
# own), entered in the table so formulas can write them as the paper does. Listed under "package".
PACKAGE_SYMBOLS = {
    "Aries": r"\text{♈}",                # marvosym: the host-call gas constants' signs
    "Taurus": r"\text{♉}",
    "Gemini": r"\text{♊}",
}

# Substitutions that print a close but not identical glyph; listed under "approximate".
APPROXIMATE_SUBST = (r"\wideparen", r"\langlebar", r"\ranglebar", r"\left\langlebar", r"\right\ranglebar")

# Definitions KaTeX needs before the table (MathJax has these natively).
KATEX_SHIMS = [r"\def\overparen#1{\overgroup{#1}}"]

# Macros whose paper body draws its glyph with TeX primitives (boxes, rules, rotation) that neither
# renderer has: the supported form that prints the same symbol. Keyed by the paper's name.
OVERRIDES = {
    r"\doubleplus": r"\mathbin{+\!\!+}",        # drawn ++ (\drawplusplus)
    r"\orderedin": r"\mathrel{<\!\!\!-}",       # < overlapping a short rule
    r"\fault": r"\Finv",                         # a rotated sans-serif F
    r"\concat": r"\frown",                       # \ensuremath{\frown}
    r"\tricolon": r"\mathrel{\vdots}",           # three small stacked triangles (approximate)
    r"\remainder": r"\mathbin{\mathsf{R}}",       # \text{\footnotesize\textsf{R}}: MathJax's \text takes no macros
    r"\append": r"\doubleplus",                  # \ensuremath{\doubleplus}
}

# Paper macros that are LaTeX plumbing rather than notation, and must not reach the renderers: the
# paper's \\left/\\right wrappers (spacing tricks with \\bgroup/\\aftergroup), equation numbering and
# table rules. They are listed under "unmapped".
EXCLUDE = {"left", "right", "theequation", "mrule", "stacktype", "stackgap"}

# Macros that are page layout or prose helpers, not notation: their absence is expected.
UNMAPPED_OK_PREFIXES = ("draw", "the", "pdf", "color")

# Primitives that are not available in KaTeX or MathJax at all; a body using one is left out.
UNSUPPORTED = [
    r"\hbox", r"\vrule", r"\hfill", r"\raisebox", r"\scalebox", r"\resizebox", r"\tikz",
    r"\includegraphics", r"\stackunder", r"\stackon", r"\stackrel@", r"\ifthenelse", r"\rotatebox", r"\vcenter", r"\offinterlineskip", r"\vskip",
    r"\cite", r"\ref", r"\label", r"\url", r"\href", r"\emph", r"\section", r"\subsection",
    r"\textit", r"\textbf", r"\begin{tikzpicture}", r"\definecolor", r"\setlength", r"\addtolength",
    r"\newline", r"\par", r"\vspace", r"\hspace*", r"\makebox", r"\parbox", r"\fbox@", r"\rule",
    r"\mathlarger", r"\mathsmaller",
    # MnSymbol / mathabx glyphs with no counterpart in either renderer
    r"\downspoon", r"\nwspoon", r"\sespoon", r"\lwavy", r"\lWavy", r"\ooalign", r"\jamdraftversionraw", r"\relscale", r"\Shortstack", r"\stackengine",
]


def read_group(s, i):
    """s[i] == '{': return (content, index after the matching '}')."""
    assert s[i] == "{"
    depth, j = 0, i
    while j < len(s):
        c = s[j]
        if c == "\\":
            j += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return s[i + 1:j], j + 1
        j += 1
    raise ValueError("unbalanced braces")


def strip_comments(src):
    out = []
    for line in src.split("\n"):
        k = 0
        while True:
            k = line.find("%", k)
            if k < 0:
                break
            # an escaped \% is not a comment (count the backslashes before it)
            b = k
            while b > 0 and line[b - 1] == "\\":
                b -= 1
            if (k - b) % 2 == 0:
                line = line[:k]
                break
            k += 1
        out.append(line)
    return "\n".join(out)


DEF = re.compile(r"\\(?:re)?newcommand\*?\s*")
NAME = re.compile(r"\\([A-Za-z¬]+)")


def parse(src, where, out):
    src = strip_comments(src)
    for m in DEF.finditer(src):
        i = m.end()
        if src[i] == "{":
            name_s, i = read_group(src, i)
        else:
            nm = NAME.match(src, i)
            if not nm:
                continue
            name_s, i = nm.group(0), nm.end()
        name_s = name_s.strip()
        nm = NAME.fullmatch(name_s)
        if not nm:
            continue
        name = nm.group(1)
        nargs, default = 0, None
        am = re.match(r"\s*\[(\d)\]", src[i:])
        if am:
            nargs = int(am.group(1))
            i += am.end()
            dm = re.match(r"\s*\[", src[i:])
            if dm:
                j = i + dm.end()
                depth = 0
                k = j
                while k < len(src):
                    if src[k] == "{":
                        depth += 1
                    elif src[k] == "}":
                        depth -= 1
                    elif src[k] == "]" and depth == 0:
                        break
                    k += 1
                default = src[j:k]
                i = k + 1
        while src[i].isspace():
            i += 1
        if src[i] != "{":
            fail(f"{where}: \\{name}: body is not a group")
        body, _ = read_group(src, i)
        body = body.strip()
        if body.endswith("\\"):  # a trailing control space "\ "
            body += " "
        out[name] = (nargs, default, body, where)


SENTINEL = "QQ"


def ascii_name(name):
    return name.replace("¬", SENTINEL)


def rename_refs(body):
    return re.sub(r"\\([A-Za-z]*¬[A-Za-z¬]*)", lambda m: "\\" + ascii_name(m.group(1)), body)


def lower_bb(body):
    """\\mathbb of a lowercase letter: KaTeX prints a plain italic letter, so use the Unicode
    double-struck letter (U+1D552 …) in \\text, the same glyph."""
    return re.sub(r"\\mathbb\{([a-z])\}", lambda m: "\\text{" + chr(0x1D552 + ord(m.group(1)) - ord("a")) + "}", body)


def apply_subst(body):
    for k in sorted(SUBST, key=len, reverse=True):
        guard = r"(?![A-Za-z])" if k[-1].isalpha() else ""
        body = re.sub(re.escape(k) + guard, lambda _m, v=SUBST[k]: v, body)
    return body


def main():
    if len(sys.argv) != 4:
        fail("usage: gen_macros.py <graypaper dir> <out.json> <out.js>")
    root = sys.argv[1]
    defs = {}
    parse(open(os.path.join(root, "preamble.tex"), encoding="utf-8").read(), "preamble.tex", defs)
    for f in sorted(glob.glob(os.path.join(root, "text", "*.tex"))):
        parse(open(f, encoding="utf-8").read(), "text/" + os.path.basename(f), defs)

    for name in defs:
        if SENTINEL in name:
            fail(f"\\{name} contains the sentinel {SENTINEL}")

    macros, unmapped, optional, approx = {}, {}, {}, {}
    for name in sorted(defs, key=ascii_name):
        nargs, default, body, where = defs[name]
        body = OVERRIDES.get("\\" + name, body)
        a = ascii_name(name)
        b = lower_bb(apply_subst(rename_refs(body)))
        b = re.sub(r"(?<!\\)\$", "", b)  # math inside a text-mode macro: already in math here
        if name in EXCLUDE:
            unmapped[a] = {"paper": "\\" + name, "where": where, "uses": ["LaTeX plumbing (EXCLUDE)"]}
            continue
        bad = [u for u in UNSUPPORTED if u.rstrip("@") in b and re.search(re.escape(u.rstrip("@")) + r"(?![A-Za-z])", b)]
        if "&" in b.replace("\\&", "") and "\\begin" not in b:
            bad = bad + ["a table row (& cells)"]
        if bad or "\n\n" in b:
            if not a.startswith(UNMAPPED_OK_PREFIXES):
                unmapped[a] = {"paper": "\\" + name, "where": where, "uses": bad or ["paragraph break"]}
            continue
        entry = {"paper": "\\" + name, "body": b, "args": nargs}
        if name == "tricolon" or any(re.search(re.escape(k) + r"(?![A-Za-z])", body) for k in APPROXIMATE_SUBST):
            approx[a] = "\\" + name
        if default is not None:
            entry["default"] = apply_subst(rename_refs(default))
            optional[a] = "\\" + name
        macros[a] = entry

    package = {}
    for a, b in sorted(PACKAGE_SYMBOLS.items()):
        if a not in macros:
            macros[a] = {"paper": "\\" + a, "body": b, "args": 0}
            package[a] = "\\" + a

    # A macro that uses an unmapped one cannot render either.
    changed = True
    while changed:
        changed = False
        for a in list(macros):
            refs = set(re.findall(r"\\([A-Za-z]+)", macros[a]["body"]))
            gone = sorted(r for r in refs if r in unmapped and r not in EXCLUDE)
            if gone:
                e = macros.pop(a)
                optional.pop(a, None)
                approx.pop(a, None)
                unmapped[a] = {"paper": e["paper"], "where": defs[e["paper"][1:]][3], "uses": ["\\" + g for g in gone]}
                changed = True

    # A macro that uses an approximate one is approximate too.
    changed = True
    while changed:
        changed = False
        for a2 in macros:
            if a2 in approx:
                continue
            refs = set(re.findall(r"\\([A-Za-z]+)", macros[a2]["body"]))
            if refs & set(approx):
                approx[a2] = macros[a2]["paper"]
                changed = True

    out = {
        "source": "gavofyork/graypaper tag v0.8.1: preamble.tex and text/*.tex",
        "sentinel": SENTINEL,
        "generator": "scripts/gen_macros.py",
        "macros": macros,
        "optional": optional,
        "approximate": approx,
        "package": package,
        "unmapped": unmapped,
    }
    with open(sys.argv[2], "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False, indent=1, sort_keys=True)
        fh.write("\n")
    with open(sys.argv[3], "w", encoding="utf-8") as fh:
        fh.write(site_js(macros))


def katex_form(e):
    """(body, nargs) for KaTeX: an optional first argument becomes its default."""
    body, n = e["body"], e["args"]
    if "default" in e:
        d = e["default"]
        body = body.replace("#1", "{" + d + "}")
        body = re.sub(r"#(\d)", lambda m: "#" + str(int(m.group(1)) - 1), body)
        n -= 1
    return body, n


def site_js(macros):
    pre = list(KATEX_SHIMS)
    mj = {}
    for a in sorted(macros):
        e = macros[a]
        body, n = katex_form(e)
        # \def, not \newcommand: the paper redefines a few built-ins (\N, \Z, \S, \H, \set, \sub).
        pre.append("\\def\\" + a + "".join(f"#{i}" for i in range(1, n + 1)) + "{" + body + "}")
        if "default" in e:
            mj[a] = [e["body"], e["args"], e["default"]]
        elif e["args"]:
            mj[a] = [e["body"], e["args"]]
        else:
            mj[a] = e["body"]
    lines = [
        "// Generated by scripts/gen_macros.py from the Gray Paper v0.8.1 TeX; do not edit.",
        "// Write the paper's macro names, ¬ included; gpMacros.name rewrites ¬ before parsing.",
        "window.gpMacros = (function () {",
        "  var name = function (s) {",
        "    return s.replace(/\\\\[A-Za-z]*¬[A-Za-z¬]*/g, function (m) { return m.replace(/¬/g, " + json.dumps(SENTINEL) + "); });",
        "  };",
        "  var preamble = [\n    " + ",\n    ".join(json.dumps(p, ensure_ascii=False) for p in pre) + "\n  ];",
        "  var mathjax = " + json.dumps(mj, ensure_ascii=False, sort_keys=True) + ";",
        "  var katexMacros = null;",
        "  // The macro object for katex.render: the definitions run once, then reused (copied per call).",
        "  var katex = function (k) {",
        "    if (katexMacros === null) {",
        "      katexMacros = {};",
        "      // One definition at a time, in order, so a definition KaTeX rejects costs only itself.",
        "      for (var i = 0; i < preamble.length; i++) {",
        "        try { k.renderToString(preamble[i], { macros: katexMacros, globalGroup: true, throwOnError: true, strict: 'ignore' }); }",
        "        catch (e) { /* see docs/site/check-macros.js */ }",
        "      }",
        "      // KaTeX's \\\\def has no optional argument: those macros are functions that read [..] if present.",
        "      Object.keys(mathjax).forEach(function (n) {",
        "        var m = mathjax[n];",
        "        if (!Array.isArray(m) || m.length < 3) return;",
        "        katexMacros['\\\\' + n] = function (ctx) {",
        "          var text = function (toks) {",
        "            return toks.map(function (t) { return /^\\\\[A-Za-z]+$/.test(t.text) ? t.text + ' ' : t.text; }).join('');",
        "          };",
        "          var opt = m[2];",
        "          if (ctx.future().text === '[') {",
        "            ctx.popToken();",
        "            var depth = 0, toks = [];",
        "            for (;;) {",
        "              var t = ctx.popToken();",
        "              if (t.text === 'EOF') break;",
        "              if (t.text === '{') depth++;",
        "              if (t.text === '}') depth--;",
        "              if (t.text === ']' && depth === 0) break;",
        "              toks.push(t);",
        "            }",
        "            opt = text(toks);",
        "          }",
        "          var args = m[1] > 1 ? ctx.consumeArgs(m[1] - 1) : [];",
        "          return m[0].replace(/#(\\d)/g, function (_, d) {",
        "            return d === '1' ? '{' + opt + '}' : '{' + text(args[+d - 2].slice().reverse()) + '}';",
        "          });",
        "        };",
        "      });",
        "    }",
        "    return Object.assign({}, katexMacros);",
        "  };",
        "  return { name: name, katex: katex, mathjax: mathjax, preamble: preamble };",
        "})();",
        "",
    ]
    return "\n".join(lines)


if __name__ == "__main__":
    main()
