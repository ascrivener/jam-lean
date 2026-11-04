"""Summarize `lean-host profile` output for the pvm-lean closure: nanoda time per node, gas at
~80M gas per native ms (witness-lean's budgeting figure; machine-dependent), and sizes."""
import json, struct, sys, collections

R = sys.argv[1] if len(sys.argv) > 1 else '.'
GAS_PER_MS = 80e6
REFINE_MS = 5e9 / GAS_PER_MS  # ~62 ms; witness-lean budgets a check ~55 ms

ents = [json.loads(l) for l in open(f'{R}/pack/manifest.jsonl')]
data = open(f'{R}/profile', 'rb').read()
times, off = [], 0
for _ in ents:
    us, n = struct.unpack_from('<II', data, off)
    off += 8 + 4 * n
    times.append(us)

def group(name):
    for p in ('Services.Witness.', 'Services.Bootstrap.', 'Services.', 'PVM.', 'JAM.'):
        if name.startswith(p):
            rest = name[len(p):]
            return p + rest.split('.')[0] if p.startswith('Services') else p.rstrip('.')
    return 'core/Std'

rows = []
for e, us in zip(ents, times):
    rows.append((us, e['names'][0], e['kind'], e['size'], e.get('proof_size', 0)))
failed = [r for r in rows if r[0] == 0xFFFFFFFF]
ok = [r for r in rows if r[0] != 0xFFFFFFFF]
print(f'{len(rows)} nodes, {len(failed)} failed')
for r in failed[:20]:
    print('  FAILED', r[1], r[2], 'proof', r[4])
tot = sum(r[0] for r in ok) / 1e3
print(f'total nanoda time {tot/1e3:.1f} s, ~{tot*GAS_PER_MS:.2e} gas')
over = [r for r in ok if r[0] / 1e3 > REFINE_MS]
print(f'over one refine (> {REFINE_MS:.0f} ms): {len(over)}')
print('\nheaviest 40 (ms, refines, kind, statement KB, proof KB):')
for us, n, k, s, p in sorted(ok, reverse=True)[:40]:
    print(f'  {us/1e3:9.1f} {us/1e3/REFINE_MS:7.1f}  {k:6} {s/1e3:8.1f} {p/1e3:9.1f}  {n}')
print('\nproof size > 2 MiB:', sum(1 for r in rows if r[4] > 2 * 2**20),
      ' > 64 KiB:', sum(1 for r in rows if r[4] > 65536))
print('\nlargest proofs (KB, ms):')
for us, n, k, s, p in sorted(rows, key=lambda r: -r[4])[:15]:
    print(f'  {p/1e3:9.1f} {us/1e3 if us != 0xFFFFFFFF else -1:9.1f}  {n}')
agg = collections.defaultdict(lambda: [0, 0, 0, 0.0])
for us, n, k, s, p in rows:
    g = agg[group(n)]
    g[0] += 1; g[1] += s; g[2] += p; g[3] += (us if us != 0xFFFFFFFF else 0) / 1e3
print('\nby module group (nodes, statements MB, proofs MB, nanoda s):')
for g, (c, s, p, ms) in sorted(agg.items(), key=lambda kv: -kv[1][3])[:45]:
    print(f'  {c:6} {s/1e6:7.2f} {p/1e6:8.2f} {ms/1e3:8.2f}  {g}')
