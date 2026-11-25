#!/usr/bin/env python3
"""Ring-root vectors from real JAM states: every (gamma_k, gamma_z) of the jam-test-vectors
safrole STF vectors (pre and post states), and gamma_P/gamma_Z of the 0.8.0 fuzzer genesis state.

usage: jam_roots.py JAM_TEST_VECTORS_DIR JAM_FUZZING_DIR > JamCryptoTest/ring/ring-root-jam.txt"""
import glob, json, os, sys

tv, fz = sys.argv[1], sys.argv[2]
seen = set()
def emit(size, keys, root, src):
    k = (size, tuple(keys), root)
    if k in seen: return
    seen.add(k)
    print(f"# {src}")
    print("root", size, root, " ".join(keys))

V = {"tiny": 6, "full": 1023}  # the ring size is the spec's validator count
for spec in ["tiny", "full"]:
    for f in sorted(glob.glob(os.path.join(tv, "stf/safrole", spec, "*.json"))):
        d = json.load(open(f))
        for st in ["pre_state", "post_state"]:
            s = d[st]
            emit(V[spec], [k["bandersnatch"] for k in s["gamma_k"]], s["gamma_z"], f"safrole/{spec}/{os.path.basename(f)} {st}")

# gamma (C(4), key 0x04…): |gamma_P| (one octet for <128), 336-octet validator keys, gamma_Z
f = os.path.join(fz, "fuzz-proto/examples/0.8.0/no_forks/00000001_fuzzer_initialize.json")
for kv in json.load(open(f))["initialize"]["state"]:
    if kv["key"].startswith("0x04"):
        v = bytes.fromhex(kv["value"][2:])
        n = v[0]
        assert n < 128
        keys = ["0x" + v[1 + 336 * i: 33 + 336 * i].hex() for i in range(n)]
        root = "0x" + v[1 + 336 * n: 1 + 336 * n + 144].hex()
        emit(6, keys, root, "jam-fuzzing 0.8.0 no_forks genesis")
