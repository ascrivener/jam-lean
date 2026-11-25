#!/usr/bin/env python3
"""Ticket ring VRF signatures from the jam-test-vectors safrole STF vectors, as unlabelled
`proof V ROOT CTX - SIG ? ?` lines (context "jam_ticket_seal" (the GP writes $jam_ticket_seal) ++ eta'_2 ++ attempt, empty
message, ring root gamma_Z'). Label them with ark-vrf: `gen label < unlabelled > labelled`.

usage: jam_tickets.py JAM_TEST_VECTORS_DIR | SRS=... gen label > JamCryptoTest/ring/ring-proof-jam.txt"""
import glob, json, os, sys

tv = sys.argv[1]
V = {"tiny": 6, "full": 1023}
E = {"tiny": 12, "full": 600}
for spec in ["tiny", "full"]:
    for f in sorted(glob.glob(os.path.join(tv, "stf/safrole", spec, "*.json"))):
        d = json.load(open(f))
        pre, post = d["pre_state"], d["post_state"]
        change = d["input"]["slot"] // E[spec] > pre["tau"] // E[spec]
        eta2 = pre["eta"][1] if change else pre["eta"][2]
        for t in d["input"]["extrinsic"]:
            ctx = b"jam_ticket_seal".hex() + eta2[2:] + "%02x" % t["attempt"]
            print(f"# {spec}/{os.path.basename(f)} attempt {t['attempt']}")
            print("proof", V[spec], post["gamma_z"][2:], ctx, "-", t["signature"][2:], "?", "?")
