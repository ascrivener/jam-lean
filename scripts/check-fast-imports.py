#!/usr/bin/env python3
"""Fail if a spec or proof module imports a fast module, except where allowed.

A *fast module* is any module with a `Fast` component (`PVM.Fast`, `PVM.Fast.Step`, `JAM.Fast.Trie`,
`JamCrypto.Fast.*`, ...): it holds faster implementations of spec definitions, each proved equal and
registered with `@[csimp]`. Spec modules hold no fast code and import no fast module, except the
ones in ALLOW below: a `@[csimp]` replacement applies where a caller is compiled with the lemma
imported, so these spec modules import the specific fast modules that their own compiled code calls
through. Imports never change what the kernel or any proof sees. Proof modules (`Theorems`, `Logic`,
`SymExec`, `Services`) may import no fast module at all. Tests and other executables may import
anything. See docs/fast-paths.md.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBS = ["PVM", "JAM", "JamCrypto", "Services"]

BLAKE = {"JAM.Fast.Blake2b"}
ALLOW = {
    # library roots
    "PVM": {"PVM.Fast"},
    "JAM": {"JAM.Fast"},
    # Ψ, Ψ_M and the blob parsers called from compiled spec code
    "PVM.Invocation": {"PVM.Fast.Basic"},
    "JAM.Refine": {"PVM.Fast.Host", "JAM.Fast.HostGeneral"} | BLAKE,
    "JAM.Accumulate": {"PVM.Fast.Host", "JAM.Fast.HostGeneral"} | BLAKE,
    "JAM.Host.General": {"PVM.Fast.Parse"},
    # ℋ (Blake2b-256)
    "JAM.Account": BLAKE,
    "JAM.Assurances": BLAKE,
    "JAM.Auditing": BLAKE,
    "JAM.BlockImport": BLAKE,
    "JAM.Disputes": BLAKE,
    "JAM.Preimages": BLAKE,
    "JAM.Reports": BLAKE,
    "JAM.Safrole": BLAKE,
    "JAM.Shuffle": BLAKE,
    "JAM.StateDecode": BLAKE,
    # ℋ and ℋ_K (Keccak-256)
    "JAM.Accumulation": BLAKE | {"JAM.Fast.Keccak"},
    "JAM.History": {"JAM.Fast.Keccak"},
    # M_σ (the state trie root)
    "JAM.State": {"JAM.Fast.Trie"},
}
PROOF_PARTS = {"Theorems", "Logic", "SymExec"}


def is_fast(mod: str) -> bool:
    return "Fast" in mod.split(".")


def module_of(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def main() -> int:
    files = []
    for lib in LIBS:
        if (ROOT / f"{lib}.lean").exists():
            files.append(ROOT / f"{lib}.lean")
        files += sorted((ROOT / lib).rglob("*.lean")) if (ROOT / lib).is_dir() else []
    bad = []
    for f in files:
        mod = module_of(f)
        if is_fast(mod):
            continue
        parts = mod.split(".")
        proof = parts[0] == "Services" or bool(PROOF_PARTS & set(parts))
        for line in f.read_text(encoding="utf-8").splitlines():
            m = re.match(r"import\s+(\S+)", line)
            if not m:
                if line.strip() and not line.startswith("import") and not line.startswith("--"):
                    if not line.startswith("prelude") and not line.startswith("module"):
                        break
                continue
            imp = m.group(1)
            if not is_fast(imp):
                continue
            if proof:
                bad.append(f"{mod}: proof module imports fast module {imp}")
            elif imp not in ALLOW.get(mod, set()):
                bad.append(f"{mod}: imports fast module {imp} (not in the allowlist)")
    for b in bad:
        print(b)
    if bad:
        print(f"check-fast-imports: {len(bad)} disallowed import(s); see docs/fast-paths.md")
        return 1
    print(f"check-fast-imports: {len(files)} modules checked, spec/fast separation holds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
