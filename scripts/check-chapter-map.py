#!/usr/bin/env python3
"""Warn when a PR changes a model module but not the companion chapter that discusses it.

Usage:  python3 -I scripts/check-chapter-map.py <base-ref>   (always exits 0; warnings only)
        python3 -I scripts/check-chapter-map.py --seed       (print a map seeded from the chapters' imports)

`docs/site/chapter-map.json` maps each model module (`JAM.Safrole`) to the chapters
(`docs/site/Companion/Safrole.lean`) that discuss it; it was seeded from the chapters' `import`
lines and may be edited by hand. For the files changed between `<base-ref>` and HEAD, a mapped
module whose chapters are all unchanged gets a warning, in the GitHub job summary when
`$GITHUB_STEP_SUMMARY` is set and on stdout. A PR that changes a modelled function's behaviour
updates its chapter in the same PR (CLAUDE.md, Rules); a change that does not alter what the
chapter says (a proof, a refactor, a docstring) can ignore the warning.
"""

import glob
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
MAP = os.path.join(ROOT, "docs", "site", "chapter-map.json")


def seed():
    m = {}
    for f in sorted(glob.glob(os.path.join(ROOT, "docs", "site", "Companion", "*.lean"))):
        rel = os.path.relpath(f, ROOT)
        for line in open(f, encoding="utf-8"):
            im = re.match(r"import ((?:JAM|PVM|JamCrypto)(?:\.\w+)+)\s*$", line)
            if im:
                m.setdefault(im.group(1), []).append(rel)
    return {k: sorted(set(v)) for k, v in sorted(m.items())}


def main():
    if sys.argv[1:] == ["--seed"]:
        print(json.dumps(seed(), indent=1))
        return
    if len(sys.argv) != 2:
        sys.exit("usage: check-chapter-map.py <base-ref> | --seed")
    cmap = json.load(open(MAP, encoding="utf-8"))
    out = subprocess.run(["git", "-C", ROOT, "diff", "--name-only", f"{sys.argv[1]}...HEAD"],
                         capture_output=True, text=True)
    if out.returncode != 0:
        print(f"check-chapter-map: git diff failed: {out.stderr.strip()}")
        return
    changed = set(out.stdout.split())
    warn = []
    for f in sorted(changed):
        if not f.endswith(".lean"):
            continue
        mod = f[:-len(".lean")].replace("/", ".")
        chapters = cmap.get(mod)
        if chapters and not any(c in changed for c in chapters):
            warn.append(f"`{f}` changed, but not its chapter: " + ", ".join(f"`{c}`" for c in chapters))
    text = ["### Companion chapters", ""]
    if warn:
        text += ["If this PR changes what a modelled function does, update its chapter too "
                 "(CLAUDE.md, Rules). Proof-only, refactoring or docstring changes can ignore this.", ""]
        text += [f"- {w}" for w in warn]
    else:
        text += ["No mapped model module changed without its chapter."]
    print("\n".join(text))
    summary = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as fh:
            fh.write("\n".join(text) + "\n")


if __name__ == "__main__":
    main()
