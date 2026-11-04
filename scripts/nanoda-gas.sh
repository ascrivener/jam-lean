#!/usr/bin/env bash
# Attest-mode gas of the batches that hold DECLs, in witness's simulator (PolkaVM, PolkaJam's gas),
# after scripts/nanoda-profile.sh OUT_DIR ... has converted their closure.
#   scripts/nanoda-gas.sh OUT_DIR DECL...
# Needs WITNESS_LEAN (lean-host built, and `cargo jam-build --out-dir out` run there) and WITNESS
# (a witness checkout with `cargo build --release -p witness-sim`). Batches are planned by
# witness-lean's lean_plan.py: one dependency depth each, trusting everything they import.
set -euo pipefail
OUT=$1; shift
WL=${WITNESS_LEAN:?set WITNESS_LEAN}; SIM=${WITNESS:?set WITNESS}/target/release/witness-sim
# The recompiler needs userfaultfd; the interpreter gives the same gas.
export POLKAVM_BACKEND=${POLKAVM_BACKEND:-interpreter}
python3 "$WL/tools/lean/lean_plan.py" "$OUT/pack" --max-proof 100000000 >"$OUT/plan.json" 2>/dev/null
python3 - "$OUT" "$@" <<'PY' | while read -r n name; do
import json, sys
out, names = sys.argv[1], set(sys.argv[2:])
m = {e["hash"]: e for e in json.load(open(f"{out}/pack/manifest.json"))}
for i, b in enumerate(json.load(open(f"{out}/plan.json"))):
    for h in b.get("subjects", []):
        if m[h]["names"][0] in names:
            print(i, m[h]["names"][0])
PY
  "$WL/target/release/lean-host" args "$OUT/pack" "$OUT/plan.json" "$n" "$OUT/args-$n" >/dev/null
  echo "$name (batch $n, $(stat -c %s "$OUT/args-$n") bytes of args): $("$SIM" check "$WL/out/lean-check.jam" "$OUT/args-$n" 100000000000 2>&1)"
done
