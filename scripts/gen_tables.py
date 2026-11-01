#!/usr/bin/env python3
"""Generate `PVM/Tables.lean` from the Gray Paper's LaTeX source.

Usage:  python3 -I scripts/gen_tables.py <path/to/graypaper/text/pvm.tex> <output.lean>

Everything in the output is read from `text/pvm.tex` (Gray Paper v0.8.0, Appendix A):

* the opcode numbers, names and argument formats, from the instruction tables
  (§A.5, `sec:instructiontables`): one Lean enumeration per argument format;
* the block-termination set T, from §A.3 (`sec:basicblocks`);
* the memory-access cost 𝔪 and the per-instruction gas cost rows
  (č, ď, x̌_A, x̌_L, x̌_S, x̌_M, x̌_D), from §A.10 (`sec:gascosttables`), with the
  table's macros expanded.

The script is deliberately strict: anything it does not recognise is an error, so
a change in the paper's source makes CI fail rather than silently produce a
different table.
"""

import re
import sys

# Argument formats, in the order of §A.5's subsubsections. The key is the
# subsubsection title as written in the LaTeX source; the value is the Lean name
# of the format (and the prefix of its opcode enumeration).
FORMATS = [
    ("Instructions without Arguments", "NoArgs"),
    ("Instructions with Arguments of One Immediate", "OneImm"),
    ("Instructions with Arguments of One Register and One Extended Width Immediate", "RegExtImm"),
    ("Instructions with Arguments of Two Immediates", "TwoImm"),
    ("Instructions with Arguments of One Offset", "OneOffset"),
    ("Instructions with Arguments of One Register \\& One Immediate", "RegImm"),
    ("Instructions with Arguments of One Register \\& Two Immediates", "RegTwoImm"),
    ("Instructions with Arguments of One Register, One Immediate and One Offset", "RegImmOffset"),
    ("Instructions with Arguments of Two Registers", "TwoReg"),
    ("Instructions with Arguments of Two Registers \\& One Immediate", "TwoRegImm"),
    ("Instructions with Arguments of Two Registers \\& One Offset", "TwoRegOffset"),
    ("Instruction with Arguments of Two Registers and Two Immediates", "TwoRegTwoImm"),
    ("Instructions with Arguments of Three Registers", "ThreeReg"),
]

# Lean keywords / existing identifiers we must not use bare as constructor names.
RESERVED = set()


def fail(msg):
    sys.stderr.write(f"gen_tables: {msg}\n")
    sys.exit(1)


def lean_name(token):
    """`shlo_l_imm_alt_32` -> `shloLImmAlt32`; reserved words get a trailing underscore-free escape."""
    parts = token.split("_")
    name = parts[0] + "".join(p[:1].upper() + p[1:] for p in parts[1:])
    if name in RESERVED:
        return f"«{name}»"
    return name


def token_name(tex):
    """`\\token{shlo\\_l\\_32}` contents -> `shlo_l_32`."""
    return tex.replace("\\_", "_").strip()


def section(src, start_pat, end_pat):
    s = src.find(start_pat)
    if s < 0:
        fail(f"cannot find {start_pat!r}")
    e = src.find(end_pat, s + len(start_pat))
    if e < 0:
        fail(f"cannot find {end_pat!r} after {start_pat!r}")
    return src[s:e]


def parse_instruction_tables(src):
    body = section(src, "\\subsection{Instruction Tables}", "\\subsection{Host Call Definition}")
    parts = re.split(r"\\subsubsection\{(.*?)\}\n", body)
    # parts = [preamble, title1, body1, title2, body2, ...]
    titles = parts[1::2]
    bodies = parts[2::2]
    if [t for t, _ in FORMATS] != titles:
        fail(f"unexpected instruction-table subsections: {titles}")
    out = []
    seen_ops, seen_names = set(), set()
    for (title, fmt), tbody in zip(FORMATS, bodies):
        rows = re.findall(r"^\s*(\d+)\s*&\s*\\token\{([^}]*)\}\s*&", tbody, re.M)
        if not rows:
            fail(f"no rows in {title}")
        ops = []
        for num, tok in rows:
            n, name = int(num), token_name(tok)
            if n in seen_ops or name in seen_names:
                fail(f"duplicate opcode {n} / {name}")
            seen_ops.add(n)
            seen_names.add(name)
            ops.append((n, name))
        out.append((fmt, title, ops))
    return out


def parse_terminators(src):
    body = section(src, "\\subsection{Basic Blocks and Termination Instructions}", "We denote this set")
    items = section(body, "\\begin{itemize}", "\\end{itemize}")
    return [token_name(t) for t in re.findall(r"\\token\{([^}]*)\}", items)]


def parse_costs(src):
    body = section(src, "\\subsection{Gas Cost Tables}", "\\end{longtable}")
    m = re.search(r"\\mathfrak\{m\}\s*\\equiv\s*(\d+)", body)
    if not m:
        fail("cannot find the definition of 𝔪")
    mem_cost = int(m.group(1))
    # Macro definitions with no arguments: \newcommand*{\name}{body}. Bodies may
    # contain one level of braces (e.g. \ifdstandsrcoverlap{1}{2}).
    macros = {}
    for name, nargs, mbody in re.findall(
        r"\\newcommand\*\{\\(\w+)\}(\[\d\])?\{((?:[^{}]|\{[^{}]*\})*)\}", body
    ):
        macros[name] = (nargs, mbody)

    def expand(cell):
        # Expand zero-argument macros repeatedly (they may nest).
        for _ in range(10):
            changed = False
            for name, (nargs, mbody) in macros.items():
                pat = re.escape("\\" + name) + r"(?![A-Za-z])"
                if nargs:
                    k = int(nargs[1:-1])
                    pat += r"\{([^{}]*)\}" * k

                    def sub(m, mbody=mbody, k=k):
                        out = mbody
                        for i in range(k):
                            out = out.replace(f"#{i + 1}", m.group(i + 1))
                        return out

                    new = re.sub(pat, sub, cell)
                else:
                    new = re.sub(pat, lambda _m, mbody=mbody: mbody, cell)
                if new != cell:
                    cell, changed = new, True
            if not changed:
                return cell
        fail(f"macro expansion did not converge: {cell}")

    table = section(body, "\\begin{longtable}", "\\bottomrule")
    table = table.split("\\endhead", 1)[1]
    rows = []
    for line in table.split("\\\\"):
        line = line.replace("\\mrule", "").strip()
        if not line:
            continue
        m = re.match(r"\\token\{([^}]*)\}\s*&(.*)$", line, re.S)
        if not m:
            fail(f"unrecognised cost-table row: {line!r}")
        name = token_name(m.group(1))
        cells = [c.strip() for c in expand(m.group(2)).split("&")]
        if len(cells) != 7:
            fail(f"row {name}: expected 7 cells, got {cells}")
        rows.append((name, [cost_expr(c, name) for c in cells]))
    return mem_cost, rows


def cost_expr(cell, name):
    """Translate one expanded cost cell into a Lean `CostExpr` term."""
    if re.fullmatch(r"\d+", cell):
        return f"(.const {cell})"
    m = re.fullmatch(r"\$\\mathfrak\{P\}\((\d+),\s*(\d+)\)\$", cell)
    if m:
        return f"(.overlap {m.group(1)} {m.group(2)})"
    m = re.fullmatch(r"\$\\mathfrak\{P\}_\{S\}\((\d+),\s*(\d+)\)\$", cell)
    if m:
        return f"(.overlapShift {m.group(1)} {m.group(2)})"
    if cell == "$\\mathfrak{m}$":
        return ".memory"
    if cell == "$\\mathfrak{b}$":
        return ".branch"
    fail(f"row {name}: unrecognised cost cell {cell!r}")


HEADER = """\
/-
  GENERATED FILE: do not edit by hand.
  Produced by `scripts/gen_tables.py` from the Gray Paper v0.8.0, `text/pvm.tex`.
  CI regenerates it from the pinned paper and fails on any difference.
-/
import PVM.CostExpr

namespace PVM
"""


def main():
    if len(sys.argv) != 3:
        fail("usage: gen_tables.py <pvm.tex> <out.lean>")
    src = open(sys.argv[1], encoding="utf-8").read()
    formats = parse_instruction_tables(src)
    terms = parse_terminators(src)
    mem_cost, costs = parse_costs(src)

    by_name = {}
    for fmt, _, ops in formats:
        for n, name in ops:
            by_name[name] = (n, fmt)
    for t in terms:
        if t not in by_name:
            fail(f"terminator {t} is not an instruction")
    cost_names = [n for n, _ in costs]
    if len(set(cost_names)) != len(cost_names):
        fail("duplicate rows in the gas cost table")
    missing = sorted(set(by_name) - set(cost_names))
    extra = sorted(set(cost_names) - set(by_name))
    if missing or extra:
        fail(f"cost table mismatch: missing {missing}, unknown {extra}")

    L = [HEADER]
    for fmt, title, ops in formats:
        L.append(f"/-- Opcodes of GP §A.5 \"{title.replace(chr(92) + '&', '&')}\". -/")
        L.append(f"inductive {fmt}Op where")
        for n, name in ops:
            L.append(f"  /-- `{name}` (opcode {n}). -/")
            L.append(f"  | {lean_name(name)}")
        L.append("  deriving DecidableEq, Repr, Inhabited")
        L.append("")
        L.append(f"/-- The opcode number of each `{fmt}Op`, as in GP §A.5. -/")
        L.append(f"def {fmt}Op.opcode : {fmt}Op → Nat")
        for n, name in ops:
            L.append(f"  | .{lean_name(name)} => {n}")
        L.append("")
        L.append(f"/-- The paper's name for each `{fmt}Op`. -/")
        L.append(f"def {fmt}Op.name : {fmt}Op → String")
        for n, name in ops:
            L.append(f"  | .{lean_name(name)} => \"{name}\"")
        L.append("")
        L.append(f"/-- Inverse of `{fmt}Op.opcode`. -/")
        L.append(f"def {fmt}Op.ofOpcode? : Nat → Option {fmt}Op")
        for n, name in ops:
            L.append(f"  | {n} => some .{lean_name(name)}")
        L.append("  | _ => none")
        L.append("")

    L.append("/-- The argument formats of GP §A.5, one per subsubsection of the instruction tables. -/")
    L.append("inductive ArgFormat where")
    for fmt, _, _ in formats:
        L.append(f"  | {fmt[0].lower() + fmt[1:]}")
    L.append("  deriving DecidableEq, Repr")
    L.append("")
    L.append("/-- The argument format of each opcode in U (GP §A.5); `none` for octets not in U. -/")
    L.append("def formatOf? : Nat → Option ArgFormat")
    for fmt, _, ops in formats:
        for n, name in ops:
            L.append(f"  | {n} => some .{fmt[0].lower() + fmt[1:]}")
    L.append("  | _ => none")
    L.append("")
    L.append("/-- The opcodes U of all valid instructions (GP §A.3), in increasing order. -/")
    allops = sorted(by_name.values())
    L.append("def validOpcodes : List Nat :=")
    L.append("  [" + ", ".join(str(n) for n, _ in allops) + "]")
    L.append("")
    L.append("/-- The paper's name of each opcode in U. -/")
    L.append("def opcodeName? : Nat → Option String")
    for name, (n, _) in sorted(by_name.items(), key=lambda kv: kv[1][0]):
        L.append(f"  | {n} => some \"{name}\"")
    L.append("  | _ => none")
    L.append("")
    L.append("/-- The block-termination opcodes T (GP §A.3, `sec:basicblocks`), in the paper's order:")
    L.append("    " + ", ".join(f"`{t}`" for t in terms) + ". -/")
    L.append("def terminatorOpcodes : List Nat :=")
    L.append("  [" + ", ".join(str(by_name[t][0]) for t in terms) + "]")
    L.append("")
    L.append("/-- The opcode of `trap`. -/")
    L.append(f"def trapOpcode : Nat := {by_name['trap'][0]}")
    L.append("/-- The opcode of `unlikely`. -/")
    L.append(f"def unlikelyOpcode : Nat := {by_name['unlikely'][0]}")
    L.append("/-- The opcode of `move_reg`. -/")
    L.append(f"def moveRegOpcode : Nat := {by_name['move_reg'][0]}")
    L.append("")
    L.append("/-- The memory-access cost 𝔪 (GP §A.10). -/")
    L.append(f"def memoryCost : Nat := {mem_cost}")
    L.append("")
    L.append("/-- The gas cost table of GP §A.10 (`sec:gascosttables`), keyed by opcode:")
    L.append("    `(č, ď, x̌_A, x̌_L, x̌_S, x̌_M, x̌_D)` as written in the paper, before evaluation. -/")
    L.append("def costRow? : Nat → Option CostRow")
    for name, cells in sorted(costs, key=lambda r: by_name[r[0]][0]):
        n = by_name[name][0]
        L.append(f"  | {n} => some ⟨{', '.join(cells)}⟩ -- {name}")
    L.append("  | _ => none")
    L.append("")
    L.append("end PVM")
    L.append("")
    open(sys.argv[2], "w", encoding="utf-8").write("\n".join(L))


if __name__ == "__main__":
    main()
