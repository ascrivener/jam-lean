#!/usr/bin/env python3
"""Convert a generated cut chain (`lake exe genwitnesssteps … cut … frame`) to the symbolic executor
(`PVM/SymExec`, `docs/symexec-spike.md`, "Generator interface").

Run it right after `genwitnesssteps` has written the chain: it reads `<Chain>/St.lean`, the segment
files `<Chain>/S<i>.lean` and the composition `<Chain>.lean`, and rewrites them so that

* every maximal run `S_b … S_{e-1}` of segments the executor follows becomes one file
  `<Chain>/E<b>.lean`, whose `run` has exactly the statement of the composed `S_b.run … S_{e-1}.run`
  (`St_b → ∃ ω' μ', FreeStepsH … ∧ St_e`). Inside, the run is cut every `every` segments into `Cut`
  data, one `seg_sound` line (`by decide +kernel`) per piece, bridged from `St_b` and to `St_e`;
* segments the executor cannot follow (host calls, or those listed in `keep=`) stay as generated;
* `<Chain>.lean` composes the `E` and kept `S` runs; its theorems' statements are unchanged;
* `<Chain>/St.lean` keeps only the states the composition names (all frame conditions `C_i` stay);
* the replaced `S<i>.lean` are deleted.

Usage: gen_exec_chain.py <chain dir> [every=16] [keep=i,j,…] [nopc=pc,…] [cutat=i,…] [maxchecks=4] [spike] [dry]
  e.g. scripts/gen_exec_chain.py Services/Bootstrap/BTail1
"""
import os, re, sys

args = sys.argv[1:]
chain_dir = args[0].rstrip('/')
every = 16
keep = set()
# pcs the executor cannot follow (e.g. a table read at a symbolic index): segments stepping them stay
nopc = {60553}
# extra cut points (where the executor loses a fact it needs, e.g. after an aliasing write)
cutat = set()
# checks per E file (files build in parallel)
maxchecks = 4
dry = False
# the binary's code table for the executor: the wiring layout by default, `spike` for the spike's
prog_mod, prog_hyp = 'Services.Bootstrap.SymExec.Prog', 'Services.Bootstrap.SymExec.hyp'
for a in args[1:]:
    if a == 'spike': prog_mod, prog_hyp = 'PVM.SymExec.Bootstrap.Prog', 'PVM.SymExec.Bootstrap.hyp'
    if a.startswith('every='): every = int(a[6:])
    elif a.startswith('keep='): keep = {int(x) for x in a[5:].split(',') if x}
    elif a.startswith('nopc='): nopc = {int(x) for x in a[5:].split(',') if x}
    elif a.startswith('cutat='): cutat = {int(x) for x in a[6:].split(',') if x}
    elif a.startswith('maxchecks='): maxchecks = int(a[10:])
    elif a == 'dry': dry = True
chain_file = chain_dir + '.lean'
ns = chain_dir.replace('/', '.')
cname = os.path.basename(chain_dir)
stsrc = open(f'{chain_dir}/St.lean').read()
csrc = open(chain_file).read()

# ---------------------------------------------------------------- the states
def st_block(i):
    m = re.search(rf'^((?:/--.*?-/\n)?structure St{i} .*? where\n.*?)(?:\n\n|\Z)', stsrc, re.S | re.M)
    return m

def fields(i):
    body = re.search(rf'^structure St{i} .*? where\n(.*?)(?:\n\n|\Z)', stsrc, re.S | re.M).group(1)
    return [m.groups() for m in (re.match(r'  (\w+) : (.*)$', l) for l in body.split('\n')) if m]

def frame_of(j):
    m = re.search(rf'^def C{j} \(a : Nat\) : Bool := (.*)$', stsrc, re.M).group(1)
    return [(int(a), int(b)) for a, b in re.findall(r'decide \((\d+) ≤ a ∧ a < (\d+)\)', m)]

def frame_between(b, j):
    out = []
    for k in range(b + 1, j + 1):
        for r in frame_of(k):
            if r not in out: out.append(r)
    return out

# ---------------------------------------------------------------- the segments
segs = []
i = 0
while os.path.exists(f'{chain_dir}/S{i}.lean'):
    s = open(f'{chain_dir}/S{i}.lean').read()
    m = re.search(r"theorem run (.*?) \(h : St(\d+) ([^)]*)\) :\n\s*∃ ω' μ', FreeStepsH p \((.*?)\) (\d+) ω μ x (\d+) ω' μ' x (\d+) ∧ St(\d+) ", s, re.S)
    assert m and int(m.group(2)) == i and int(m.group(8)) == i + 1, f'S{i}: unexpected run statement'
    host = bool(re.search(r'pvm_host|ecalli|growHeap|host_decode', s)) or \
        any(re.search(rf'\(d_{pc} ', s) for pc in nopc)
    imports = [l for l in s.split('\n') if l.startswith('import ') and not l.endswith('.St')]
    opens = re.search(r'^open (.*)$', s, re.M).group(1)
    segs.append(dict(i=i, sig=m.group(1), targs=m.group(3), contr=m.group(4), start=int(m.group(5)),
                     end=int(m.group(6)), n=int(m.group(7)), host=host, imports=imports, opens=opens))
    i += 1
N = len(segs)
sig, targs, contr = segs[0]['sig'], segs[0]['targs'], segs[0]['contr']
for s in segs:
    assert s['sig'] == sig and s['targs'] == targs and s['contr'] == contr, f"S{s['i']}: signature differs"

# the named naturals and their bounds, from the run signature
# accumulate chains (`accContract`) run through CodeX/CodeA code: the merged table
acc = contr.startswith('accContract')
if acc and prog_mod == 'Services.Bootstrap.SymExec.Prog':
    prog_mod, prog_hyp = 'Services.Bootstrap.SymExec.ProgAll', 'Services.Bootstrap.SymExec.hypAll'
inst = ('[Services.Bootstrap.Code.HasCode p P] [Services.Bootstrap.CodeX.HasCodeX p P] [Services.Bootstrap.CodeA.HasCodeA p P]'
        if acc else '[Services.Bootstrap.Code.HasCode p P]')
vars_, ub, lb, bpf, lpf = [], [], [], [], []
for name, h, ty in re.findall(r'\((\w+) : Nat\) \((h\w+) : ([^)]*)\)', sig):
    parts = [p.strip() for p in ty.split('∧')]
    u = l = None; up = lp = None
    for k, p in enumerate(parts):
        pr = h if len(parts) == 1 else (f'{h}.1' if k == 0 else f'{h}.2')
        if (mm := re.fullmatch(rf'{name} < (\d+)', p)): u, up = int(mm.group(1)), pr
        elif (mm := re.fullmatch(rf'{name} ≤ (\d+)', p)): u, up = int(mm.group(1)) + 1, f'(Nat.lt_succ_of_le {pr})'
        elif (mm := re.fullmatch(rf'(\d+) ≤ {name}', p)): l, lp = int(mm.group(1)), pr
        elif (mm := re.fullmatch(rf'(\d+) < {name}', p)): l, lp = int(mm.group(1)) + 1, pr
    assert u is not None, f'no upper bound for {name}'
    vars_.append(name); ub.append(u); bpf.append(up)
    lb.append(l or 0); lpf.append(lp if l else 'Nat.zero_le _')
vidx = {v: k for k, v in enumerate(vars_)}
vl = '[' + ', '.join(vars_) + ']'
vbind = ' '.join(f'({v} : Nat)' for v in vars_)

def sval(e):
    e = e.strip()
    return f'.const {e}' if re.fullmatch(r'\d+', e) else f'.var {vidx[e]}'

def spec(j):
    regs, cells, rd, wr, regn, celln, rdn, wrn = [], [], [], [], [], [], [], []
    for n, t in fields(j):
        if n.startswith('hreg'):
            m = re.fullmatch(r'ω\[(\d+)\] = UInt64\.ofNat (\w+)', t)
            if not m: raise Unencodable(t)
            regs.append(f'({m.group(1)}, {sval(m.group(2))})'); regn.append(n)
        elif n.startswith('hm_'):
            m = re.fullmatch(r'μ\.readN (\d+) (\d+) = \[(.*)\]', t); assert m, t
            cells.append(f'(⟨none, {m.group(1)}⟩, {m.group(2)}, .const (Num.decodeLE [{m.group(3)}]))'); celln.append((n, True))
        elif n.startswith('hbn_'):
            m = re.fullmatch(r'μ\.readN (\d+) (\d+) = Num\.encodeLE \d+ (\w+)', t)
            if not m: raise Unencodable(t)
            cells.append(f'(⟨none, {m.group(1)}⟩, {m.group(2)}, {sval(m.group(3))})'); celln.append((n, False))
        elif n.startswith('hrd_'):
            a, b = map(int, n[4:].split('_')); rd.append((a, b)); rdn.append(n)
        elif n.startswith('hw_'):
            a, b = map(int, n[3:].split('_')); wr.append((a, b)); wrn.append(n)
        elif n in ('fr', 'rdq', 'wrq'):
            pass
        else:
            raise Unencodable(f'St{j}: field {n}')
    return dict(regs=regs, cells=cells, rd=rd, wr=wr, regn=regn, celln=celln, rdn=rdn, wrn=wrn)

class Unencodable(Exception): pass

_enc = {}
def encodable(j):
    if j not in _enc:
        try: spec(j); _enc[j] = True
        except Unencodable: _enc[j] = False
    return _enc[j]

def lst(xs):
    return '[' + ', '.join(xs) + ']'

def rgn(rs):
    return lst([f'(⟨none, {a}⟩, {b - a})' for a, b in rs])

def tup(xs):
    return '⟨' + ', '.join(xs + ['trivial']) + '⟩' if xs else 'trivial'

def cut_def(j, b):
    sp = spec(j)
    fr = frame_between(b, j)
    return (f'def cut{j} : Cut :=\n  {{ regs := {lst(sp["regs"])}\n    cells := {lst(sp["cells"])}\n'
            f'    rd := {rgn(sp["rd"])}\n    wr := {rgn(sp["wr"])}\n    frame := {rgn(fr)} }}\n')

def containing(rngs, names, a, b):
    for (x, y), n in zip(rngs, names):
        if x <= a and b <= y: return n
    return None

# ---------------------------------------------------------------- one executor run
def cuts_for(b, e):
    cuts = [b]
    while cuts[-1] + every < e:
        j = cuts[-1] + every
        extra = [c for c in cutat if cuts[-1] < c < j]
        if extra: j = min(extra)
        while not encodable(j): j -= 1
        assert j > cuts[-1], f'no encodable state after St{cuts[-1]}'
        cuts.append(j)
    cuts.append(e)
    return cuts

def exec_file(b, e):
    cuts = cuts_for(b, e)
    first = segs[b]
    o = [f'''/-
  GENERATED by `scripts/gen_exec_chain.py {chain_dir}` from the chain `genwitnesssteps` wrote.
  Steps {sum(s["n"] for s in segs[:b])} … {sum(s["n"] for s in segs[:e]) - 1} of the chain. Do not edit by hand.
-/
{chr(10).join(first["imports"])}
import PVM.SymExec.Cut
import {prog_mod}
import {ns}.St

/-!
`St{b}` to `St{e}` of `{ns}` ({sum(s["n"] for s in segs[b:e])} steps, pc {segs[b]["start"]} to pc
{segs[e - 1]["end"]}) by the symbolic executor (`PVM/SymExec`): the states at cuts
{", ".join(map(str, cuts))} as `Cut` data, one kernel-evaluated check per piece (`seg_sound`).
-/

namespace {ns}.E{b}

open {first["opens"]} PVM.SymExec

set_option maxRecDepth 100000

/-- Bounds of the named naturals {", ".join(vars_)}. -/
def ub : List Nat := {ub}
def lb : List Nat := {lb}
''']
    for j in cuts:
        o.append(cut_def(j, b))
    X = '{X : Type} {R : HostRel X} {p : ByteArray} {P : Program} ' + inst
    for a, c in zip(cuts, cuts[1:]):
        st, en, n = segs[a]['start'], segs[c - 1]['end'], sum(s['n'] for s in segs[a:c])
        o.append(f'''/-- Segments `S{a}` … `S{c - 1}` ({n} steps, pc {st} to pc {en}), by one check. -/
theorem seg{a} {X} {vbind} (hB : BHold {vl} ub) (hLB : LBHold {vl} lb)
    (μ₀ : Memory) (ω : Regs) (μ : Memory) (h : cut{a}.Holds {vl} μ₀ ω μ) (x : X) :
    ∃ ω' μ', FreeStepsH p R {st} ω μ x {en} ω' μ' x {n} ∧ cut{c}.Holds {vl} μ₀ ω' μ' :=
  seg_sound (lb := lb) (sep := []) (by decide +kernel) ({prog_hyp} (p := p) (P := P)) hB hLB
    (fun _ _ => trivial) h x
''')
    A, B = spec(b), spec(e)
    total = sum(s['n'] for s in segs[b:e])
    hb = tup(bpf); hl = tup(lpf)
    c0 = (f'⟨{tup(["h." + n for n in A["regn"]])},\n      '
          f'{tup([("(cell_of_list h." + n + " rfl)") if conc else ("h." + n) for n, conc in A["celln"]])},\n      '
          f'{tup([f"rng_rd (lo := {x}) (hi := {y}) h.{n}" for (x, y), n in zip(A["rd"], A["rdn"])])},\n      '
          f'{tup([f"rng_wr (lo := {x}) (hi := {y}) h.{n}" for (x, y), n in zip(A["wr"], A["wrn"])])},\n      '
          f'fun _ _ _ => rfl, rfl⟩')
    body = [f'  have c{b} : cut{b}.Holds {vl} μ ω μ :=\n    {c0}']
    prev = ('ω', 'μ')
    runs = []
    for k, (a, c) in enumerate(zip(cuts, cuts[1:])):
        body.append(f'  obtain ⟨ω{c}, μ{c}, run{c}, c{c}⟩ := seg{a} (R := {contr}) (p := p) (P := P) {" ".join(vars_)} {hb} {hl} μ {prev[0]} {prev[1]} c{a} x')
        prev = (f'ω{c}', f'μ{c}'); runs.append(f'run{c}')
    rr = runs[-1]
    for r in reversed(runs[:-1]): rr = f'({r}.trans {rr})'
    regs_o = ', '.join(f'r{k}' for k in range(len(B['regn'])))
    cells_o = ', '.join(f'm{k}' for k in range(len(B['celln'])))
    pr = f'⟨{regs_o}, -⟩' if regs_o else '-'
    pc = f'⟨{cells_o}, -⟩' if cells_o else '-'
    body.append(f'  obtain ⟨{pr}, {pc}, -, -, hfr, hpg⟩ := c{e}')
    fl = []
    for k, n in enumerate(B['regn']): fl.append(f'{n} := r{k}')
    for k, (n, conc) in enumerate(B['celln']): fl.append(f'{n} := list_of_cell rfl m{k}' if conc else f'{n} := m{k}')
    for (x, y), n in zip(B['wr'], B['wrn']):
        w = containing(A['wr'], A['wrn'], x, y); assert w, f'St{e}.{n}: not within St{b}'
        fl.append(f'{n} := fun a h1 h2 => (writable_pages hpg a).trans (h.{w} a (by omega) (by omega))')
    for (x, y), n in zip(B['rd'], B['rdn']):
        r = containing(A['rd'], A['rdn'], x, y)
        if r: fl.append(f'{n} := fun a h1 h2 => (readable_pages hpg a).trans (h.{r} a (by omega) (by omega))')
        else:
            w = containing(A['wr'], A['wrn'], x, y); assert w, f'St{e}.{n}: not within St{b}'
            fl.append(f'{n} := fun a h1 h2 => (readable_pages hpg a).trans (Memory.readable_of_writable (h.{w} a (by omega) (by omega)))')
    cs = ', '.join(f'C{k}' for k in range(e, b, -1))
    fl.append(f'''fr := fun a ha => by
            simp only [{cs}, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt] at ha
            rw [hfr a (by show a < 4294967296; omega) (out_of_bool (by simp only [cut{e}, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]; omega))]
            exact h.fr a (by simp_all)''')
    fl.append('rdq := fun a => (readable_pages hpg a).trans (h.rdq a)')
    fl.append('wrq := fun a => (writable_pages hpg a).trans (h.wrq a)')
    body.append(f'  exact ⟨{prev[0]}, {prev[1]}, {rr},\n    {{ ' + '\n      '.join(fl) + ' }⟩')
    tnext = targs.rsplit(' ', 2)[0]
    o.append(f'''/-- **Cut {b} to cut {e}**: the statement of the composed `S{b}.run` … `S{e - 1}.run`. -/
theorem run {sig} (h : St{b} {targs}) :
    ∃ ω' μ', FreeStepsH p ({contr}) {segs[b]["start"]} ω μ x {segs[e - 1]["end"]} ω' μ' x {total} ∧ St{e} {tnext} ω' μ' := by
''' + '\n'.join(body) + '\n')
    o.append(f'end {ns}.E{b}\n')
    return '\n'.join(o)

# ---------------------------------------------------------------- the plan
plan = []   # ('E', b, e) or ('S', i)
ok = [not (s_['host'] or s_['i'] in keep) for s_ in segs]
k = 0
while k < N:
    if not ok[k] or not encodable(k):
        plan.append(('S', k)); k += 1
        continue
    e = k
    while e < N and ok[e]: e += 1
    while not encodable(e): e -= 1
    if e == k:
        plan.append(('S', k)); k += 1
    else:
        cs = cuts_for(k, e)
        for q in range(0, len(cs) - 1, maxchecks):
            plan.append(('E', cs[q], cs[min(q + maxchecks, len(cs) - 1)]))
        k = e
print(f'{chain_dir}: {N} segments ->', ' '.join(f'E{p[1]}-{p[2]}' if p[0] == 'E' else f'S{p[1]}' for p in plan))
if dry: sys.exit(0)

files = {}
for p in plan:
    if p[0] == 'E': files[f'{chain_dir}/E{p[1]}.lean'] = exec_file(p[1], p[2])

# ---------------------------------------------------------------- the composition
m = re.search(r'(theorem chain .*? := by\n)(.*?\n)(\n/--|\nend )', csrc, re.S)
head, oldbody = m.group(1), m.group(2)
call = re.search(r':= S0\.run (.*?) ω μ x (.*?) h\n', oldbody)
pre, post = call.group(1), call.group(2)
lines, runs = [], []
cur, curh, idx = ('ω', 'μ'), 'h', 0
for p in plan:
    idx += 1
    mod = f'E{p[1]}' if p[0] == 'E' else f'S{p[1]}'
    lines.append(f'  obtain ⟨ω{idx}, μ{idx}, run{idx}, h{idx}⟩ := {mod}.run {pre} {cur[0]} {cur[1]} x {post} {curh}')
    cur, curh = (f'ω{idx}', f'μ{idx}'), f'h{idx}'
    runs.append(f'run{idx}')
rr = runs[-1]
for r in reversed(runs[:-1]): rr = f'({r}.trans {rr})'
lines.append(f'  exact ⟨{cur[0]}, {cur[1]}, {rr}, {curh}⟩')
newc = csrc[:m.start(2)] + '\n'.join(lines) + '\n' + csrc[m.end(2):]
imps = [f'import {ns}.{("E" + str(p[1])) if p[0] == "E" else ("S" + str(p[1]))}' for p in plan]
newc = re.sub(r'(?:^import .*\n)+', '\n'.join(imps) + '\n', newc, count=1, flags=re.M)
newc = re.sub(r'(GENERATED by `lake exe genwitnesssteps [^`]*` from \S+?)\.?$', r'\1, then by `scripts/gen_exec_chain.py ' + chain_dir + '`.', newc, count=1, flags=re.M)
newc = newc.replace('The segments composed.', 'The executor runs (`E…`) and the remaining segments composed.')
files[chain_file] = newc

# ---------------------------------------------------------------- the states kept
need = {0, N}
for p in plan:
    if p[0] == 'E': need |= {p[1], p[2]}
    else: need |= {p[1], p[1] + 1}
# states named by the files that import the chain (they may `open` its namespace)
for root, _, fs in os.walk('.'):
    if '.lake' in root or root.startswith('./' + chain_dir): continue
    for fn in fs:
        if not fn.endswith('.lean'): continue
        path = os.path.join(root, fn)
        if os.path.normpath(path) == os.path.normpath(chain_file): continue
        t = open(path).read()
        if re.search(rf'^import {re.escape(ns)}(\.St)?$', t, re.M):
            need |= {int(x) for x in re.findall(r'\bSt(\d+)\b', t)}
def drop_st(src):
    def rep(mm):
        return mm.group(0) if int(mm.group(2)) in need else ''
    return re.sub(r'(\n(?:/--[^\n]*-/\n)?structure St(\d+) [^\n]* where\n(?:  [^\n]*\n)*)', rep, src)
files[f'{chain_dir}/St.lean'] = drop_st(stsrc)

for f, t in files.items():
    open(f, 'w').write(t)
for p in plan:
    if p[0] == 'E':
        for j in range(p[1], p[2]): os.remove(f'{chain_dir}/S{j}.lean')
print('wrote', ', '.join(sorted(files)), file=sys.stderr)
