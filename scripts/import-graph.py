#!/usr/bin/env python3
"""Import-graph and build-time report for build profiling (docs/BUILD-INFRA.md).

Usage: scripts/import-graph.py [build-times.tsv]

Scans the `import` lines of PVM/, JAM/, Services/ and Tests/ and prints, per module:
  * fan-out: how many modules depend on it, directly or transitively (what a change rebuilds);
  * the build seconds of those dependents, when a build-times TSV (module<TAB>seconds) is given;
  * its own size and build time.
"""
import collections
import os
import re
import sys

mods = {}
for d in ["PVM", "JAM", "Services", "Tests"]:
    for dp, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mods[p[:-5].replace("/", ".")] = p
for f in ["PVM.lean", "JAM.lean", "Services.lean"]:
    mods[f[:-5]] = f
imp = {m: [x for x in re.findall(r"^import\s+(\S+)", open(p, encoding="utf-8").read(), re.M) if x in mods]
       for m, p in mods.items()}
size = {m: os.path.getsize(p) for m, p in mods.items()}
rev = collections.defaultdict(set)
for m, l in imp.items():
    for x in l:
        rev[x].add(m)

def dependents(m):
    seen, st = set(), [m]
    while st:
        for z in rev.get(st.pop(), ()):
            if z not in seen:
                seen.add(z)
                st.append(z)
    return seen

secs = {}
if len(sys.argv) > 1:
    for line in open(sys.argv[1]):
        if line.startswith("#") or not line.strip():
            continue
        m, s = line.split("\t")[:2]
        secs[m] = float(s)

dn = {m: dependents(m) for m in mods}
cost = {m: sum(secs.get(x, 0) for x in dn[m]) for m in mods}
print(f"{len(mods)} modules, {sum(size.values()) // 1024} KiB of source, "
      f"{sum(secs.values()) / 3600:.1f} h of serial build time in the TSV")
key = (lambda m: -cost[m]) if secs else (lambda m: -len(dn[m]))
print("\n# rebuild cost of a change: dependents, their build minutes, own KiB, own seconds, module")
for m in sorted(mods, key=key)[:40]:
    print(f"{len(dn[m])}\t{cost[m] / 60:.0f}\t{size[m] // 1024}\t{secs.get(m, 0):.0f}\t{m}")
if secs:
    print("\n# slowest modules: seconds, dependents, own KiB, module")
    for m in sorted(secs, key=lambda m: -secs[m])[:40]:
        print(f"{secs[m]:.0f}\t{len(dn.get(m, ()))}\t{size.get(m, 0) // 1024}\t{m}")
