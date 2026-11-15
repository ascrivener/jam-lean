#!/usr/bin/env python3
"""Convert Lean files to the module system (docs/module-system.md).

Usage: scripts/to-module.py [--check] FILE...   (run from the repository root)

For each FILE that is not yet a module, it:
  * puts `module` on the first line;
  * turns each `import X` into `public import X`, keeping existing `public` and `meta` imports;
  * opens `@[expose] public section` after the imports. Every definition stays transparent, so
    `decide`, `rfl`, `unfold`, `simp [d]` and kernel reflection keep working downstream. Only proof
    bodies leave the public interface.

It refuses a file that imports a repository file that is neither a module nor among the FILEs: a
module cannot import a non-module, so convert bottom-up. `--check` only reports what it would do.
Meta code (simprocs, elaborators, and macros that run definitions from imports) needs
`public meta import` added by hand; the build says which.
"""
import os
import re
import sys

args = sys.argv[1:]
check = "--check" in args
files = [a for a in args if a != "--check"]
IMP = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def mod_path(m):
    return m.replace(".", "/") + ".lean"


def is_module(text):
    for line in text.split("\n"):
        s = line.strip()
        if s == "" or s.startswith("--"):
            continue
        return s == "module"
    return False


converting = {os.path.normpath(f) for f in files}
bad = []
for f in files:
    for m in IMP.findall(open(f, encoding="utf-8").read()):
        p = mod_path(m)
        if os.path.exists(p) and os.path.normpath(p) not in converting:
            if not is_module(open(p, encoding="utf-8").read()):
                bad.append(f"{f}: imports non-module {m}")
if bad:
    print("\n".join(bad))
    print("convert those first (bottom-up), or pass them too")
    sys.exit(1)

for f in files:
    text = open(f, encoding="utf-8").read()
    if is_module(text):
        continue
    lines = text.split("\n")
    idx = [i for i, l in enumerate(lines) if IMP.match(l)]
    last = idx[-1] if idx else -1
    lines = [("public " + l if l.startswith("import ") else l) for l in lines]
    lines.insert(last + 1, "\n@[expose] public section\n")
    lines.insert(0, "module\n")
    if check:
        print(f"would convert {f}")
    else:
        open(f, "w", encoding="utf-8").write("\n".join(lines))
