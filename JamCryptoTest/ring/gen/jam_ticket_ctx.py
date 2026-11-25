#!/usr/bin/env python3
"""Ticket-context vectors: `ticket V ROOT ETA2 ATTEMPT SIG` for the first ticket of some
jam-test-vectors 0.8.0 safrole vectors that accept it. ringtest builds the context itself and
checks that "jam_ticket_seal" ++ eta'_2 ++ attempt verifies and "$jam_ticket_seal" ++ … does not.

usage: jam_ticket_ctx.py JAM_TEST_VECTORS_DIR > JamCryptoTest/ring/ring-ticket-jam.txt"""
import json, os, sys

tv = sys.argv[1]
E = {"tiny": 12, "full": 600}
V = {"tiny": 6, "full": 1023}
for spec, name in [("tiny", "publish-tickets-no-mark-2"), ("tiny", "publish-tickets-with-mark-3"),
                   ("full", "publish-tickets-no-mark-2")]:
    f = os.path.join(tv, "stf/safrole", spec, name + ".json")
    d = json.load(open(f))
    assert "ok" in d["output"], f
    pre, post = d["pre_state"], d["post_state"]
    change = d["input"]["slot"] // E[spec] > pre["tau"] // E[spec]
    eta2 = pre["eta"][1] if change else pre["eta"][2]
    t = d["input"]["extrinsic"][0]
    print(f"# {spec}/{name}.json first ticket")
    print("ticket", V[spec], post["gamma_z"][2:], eta2[2:], t["attempt"], t["signature"][2:])
