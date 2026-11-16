#!/usr/bin/env python3
"""Decide whether a change can affect the `Services` proofs (CI's "changes" job; docs/BUILD-INFRA.md).

Usage: scripts/services-affected.py [BASE]

Prints `affected=true` or `affected=false`, and appends the same line to $GITHUB_OUTPUT when that is
set. With BASE, the change is `git diff BASE...HEAD`; without it (a push to main) the answer is true.

A change affects Services when a changed path is
  * under `Services/` or `services/` (the vendored blobs), or `Services.lean`;
  * build configuration: `lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, `.github/`;
  * under `scripts/`, except the scripts listed in MODEL_ONLY_SCRIPTS;
  * a Lean module that a Services module, or one of the Services checks in PROOF_ROOTS, imports
    (directly or transitively), found by scanning `import` lines.
Any error also gives `affected=true`: a wrong `true` costs a long build, a wrong `false` a broken main.
If main's proofs ever fail after a PR merged with `affected=false`, fix this script.
"""
import os
import re
import subprocess
import sys

# Scripts the proofs chain never runs.
MODEL_ONLY_SCRIPTS = {
    "scripts/check-tables.sh",
    "scripts/fetch-vectors.sh",
    "scripts/fetch-jam-vectors.sh",
    "scripts/fetch-trace-vectors.sh",
    "scripts/fetch-lake.sh",
    "scripts/fetch-paper.sh",
    "scripts/CheckAxiomsModel.lean",
}

# Modules outside `Services` that the proofs chain builds and runs.
PROOF_ROOTS = ["Tests.WitnessCheck", "Tests.BootstrapCheck", "Tests.GenWitnessSteps"]

IMPORT = re.compile(r"^import\s+(\S+)", re.M)


def module_path(m):
    return m.replace(".", "/") + ".lean"


def imports_of(m):
    p = module_path(m)
    if not os.path.exists(p):
        return []
    with open(p, encoding="utf-8") as f:
        return IMPORT.findall(f.read())


def proof_closure():
    """Every module the Services proofs import, transitively (as paths)."""
    roots = list(PROOF_ROOTS) + ["Services"]
    for dp, _, fs in os.walk("Services"):
        roots += [os.path.join(dp, f)[:-5].replace("/", ".") for f in fs if f.endswith(".lean")]
    seen = set()
    stack = roots
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(imports_of(m))
    return {module_path(m) for m in seen}


def affected_by(path, closure):
    if path == "Services.lean" or path.startswith(("Services/", "services/", ".github/")):
        return True
    if path in ("lakefile.lean", "lean-toolchain", "lake-manifest.json"):
        return True
    if path.startswith("scripts/"):
        return path not in MODEL_ONLY_SCRIPTS
    return path in closure


def decide(base):
    if not base:
        return True, "no base: a push to main always runs the proofs"
    out = subprocess.run(["git", "diff", "--name-only", f"{base}...HEAD"],
                         check=True, capture_output=True, text=True).stdout
    changed = [l for l in out.splitlines() if l]
    closure = proof_closure()
    hits = [p for p in changed if affected_by(p, closure)]
    if hits:
        return True, "affects Services: " + ", ".join(hits[:20]) + (" …" if len(hits) > 20 else "")
    return False, f"{len(changed)} changed paths, none in the Services proofs' imports"


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else ""
    try:
        affected, why = decide(base)
    except Exception as e:  # fail safe
        affected, why = True, f"error ({e}); assuming Services are affected"
    print(why, file=sys.stderr)
    line = f"affected={'true' if affected else 'false'}"
    print(line)
    out = os.environ.get("GITHUB_OUTPUT")
    if out:
        with open(out, "a") as f:
            f.write(line + "\n")


if __name__ == "__main__":
    main()
