#!/usr/bin/env python3
"""EXPERIMENTAL (symexec spike): emit a Lean file proving `St_k -> St_l` of a generated chain
(e.g. Services/Bootstrap/BTail1) with the reflective executor, from the existing St structures,
segment files and code facts.  Usage:
  gen_stretch.py <chain dir> <chain namespace> <k> <l> <out.lean> <ModName>
"""
import re, sys

chain_dir, chain_ns, k, l, out, mod = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
code = open('Services/Bootstrap/Code.lean').read()
stsrc = open(f'{chain_dir}/St.lean').read()

def fields(i):
    body = re.search(rf'^structure St{i} .*? where\n(.*?)(?:\n\n|\Z)', stsrc, re.S | re.M).group(1)
    fs = []
    for line in body.split('\n'):
        mm = re.match(r'  (\w+) : (.*)$', line)
        if mm: fs.append((mm.group(1), mm.group(2)))
    return fs

def frame_of(i):
    m = re.search(rf'^def C{i} \(a : Nat\) : Bool := (.*)$', stsrc, re.M).group(1)
    return [(int(a), int(b)) for a, b in re.findall(r'decide \((\d+) ≤ a ∧ a < (\d+)\)', m)]

# segment files k .. l-1: start/end pcs, counts, d_ pcs, run signature
pcs, total, start, end, sig = [], 0, None, None, None
for i in range(k, l):
    s = open(f'{chain_dir}/S{i}.lean').read()
    mm = re.search(r'FreeStepsH p \(refineContract env\) (\d+) ω μ x (\d+) ω\' μ\' x (\d+)', s)
    if start is None: start = int(mm.group(1))
    end = int(mm.group(2)); total += int(mm.group(3))
    pcs += [int(x) for x in re.findall(r'step_decode \(d_(\d+)', s)]
    if re.search(r'host_decode|hostCall|ecalli', s): raise SystemExit(f'S{i}: host call, unsupported')
    if sig is None:
        sig = re.search(r'theorem run (.*?) \(h : St\d+ ', s, re.S).group(1)
        targs = re.search(r'\(h : St\d+ ([^)]*)\)', s).group(1)
upcs = sorted(set(pcs))
entries, bsneed = [], set()
for pc in upcs:
    mm = re.search(rf'^theorem d_{pc} .*?P\.decode {pc} = some (.*?) ∧ P\.next {pc} = (\d+) ∧', code, re.M)
    ins, nx = mm.group(1), int(mm.group(2))
    entries.append((pc, ins, nx))
    nums = re.findall(r'-?\d+', ins)
    if re.search(r'regImmOffset|twoRegOffset|oneOffset', ins):
        bsneed.add(int(nums[-1])); bsneed.add(nx)
    if 'fallthrough' in ins: bsneed.add(nx)
jts = set()
for pc, ins, nx in entries:
    if 'jumpInd' in ins:
        jts = None
if jts is None:
    # every jump-table entry the code facts give (the executor looks the target up)
    jt = [(int(a), int(b)) for a, b in re.findall(r'^@\[pvm_code\] theorem jte_(\d+) .*?getD \d+ 0 = (\d+) :=', code, re.M)]
    jsize = int(re.search(r'theorem jts .*?P\.jumpTable\.size = (\d+)', code).group(1))
    # only entries whose targets are in this stretch
    jt = [(a, b) for a, b in jt if b in set(pcs) or b == end]
    for a, b in jt: bsneed.add(b)
else:
    jt = []
jsize = int(re.search(r'theorem jts .*?P\.jumpTable\.size = (\d+)', code).group(1))
bs = sorted(n for n in bsneed if re.search(rf'theorem bs_{n} .*= true', code))

# bounds of the named naturals from the run signature
vars_, bounds, bproofs = [], [], []
for name, h, ty in re.findall(r'\((\w+) : Nat\) \((h\w+) : ([^)]*)\)', sig):
    vars_.append(name)
    mm = re.search(rf'{name} < (\d+)', ty)
    bounds.append(int(mm.group(1)))
    bproofs.append(f'{h}.2' if '∧' in ty else h)
vidx = {v: i for i, v in enumerate(vars_)}

def sval(e):
    e = e.strip()
    return f'.const {e}' if re.fullmatch(r'\d+', e) else f'.var {vidx[e]}'

def decode_le(lst):
    return sum(b << (8 * i) for i, b in enumerate(lst))

def spec(fs):
    regs, cells, rds, wrs, rdn, wrn, regn, celln = [], [], [], [], [], [], [], []
    for n, t in fs:
        if n.startswith('hreg'):
            mm = re.match(r'ω\[(\d+)\] = UInt64\.ofNat (.*)$', t)
            regs.append(f'({mm.group(1)}, {sval(mm.group(2))})'); regn.append(n)
        elif n.startswith('hm_'):
            mm = re.match(r'μ\.readN (\d+) (\d+) = \[(.*)\]$', t)
            lst = [int(x) for x in mm.group(3).split(',')]
            cells.append(f'(⟨none, {mm.group(1)}⟩, {mm.group(2)}, .const (Num.decodeLE [{mm.group(3)}]))'); celln.append((n, True))
        elif n.startswith('hbn_'):
            mm = re.match(r'μ\.readN (\d+) (\d+) = Num\.encodeLE \d+ (\w+)$', t)
            cells.append(f'(⟨none, {mm.group(1)}⟩, {mm.group(2)}, {sval(mm.group(3))})'); celln.append((n, False))
        elif n.startswith('hrd_'):
            a, b = n[4:].split('_'); rds.append((int(a), int(b))); rdn.append(n)
        elif n.startswith('hw_'):
            a, b = n[3:].split('_'); wrs.append((int(a), int(b))); wrn.append(n)
    return regs, cells, rds, wrs, rdn, wrn, regn, celln

F0, F1 = fields(k), fields(l)
r0, c0, rd0, wr0, rdn0, wrn0, regn0, celln0 = spec(F0)
r1, c1, rd1, wr1, rdn1, wrn1, regn1, celln1 = spec(F1)
frame = []
for i in range(k + 1, l + 1): frame += frame_of(i)

def lst(xs, ind='    '):
    return '[' + (',\n' + ind).join(xs) + ']' if xs else '[]'

def tup(xs):
    return '⟨' + ', '.join(xs + ['trivial']) + '⟩' if xs else 'trivial'

def tree(es):
    if not es: return '.leaf'
    m = len(es) // 2
    pc, ins, nx = es[m]
    return f'(.node {tree(es[:m])}\n    ⟨{pc}, {ins}, {nx}⟩ {tree(es[m+1:])})'

def treeproof(es):
    if not es: return 'trivial'
    m = len(es) // 2
    return f'⟨d_{es[m][0]} (p := p) (P := P), {treeproof(es[:m])}, {treeproof(es[m+1:])}⟩'

def containing(rngs, names, a, b):
    for (x, y), n in zip(rngs, names):
        if x <= a and b <= y: return n
    raise SystemExit(f'no range for {a} {b}')

o = []
o.append(f'''import Services.Bootstrap.SymExec.Prog
import {chain_ns.replace('Services.Bootstrap.', 'Services.Bootstrap.')}.St

/-!
EXPERIMENTAL (symexec spike, `docs/symexec-spike.md`): `St{k}` to `St{l}` of
`{chain_ns}` ({total} steps, pc {start} to pc {end}) by the reflective executor, generated by
`PVM/SymExec/gen_stretch.py` from the same data as the per-step proofs.
-/

namespace Services.Bootstrap.SymExec.{mod}

open PVM PVM.SymExec JAM Services.Bootstrap.Code {chain_ns}

def st : Static :=
  {{ ub := {bounds}
    lb := {[0] * len(bounds)}
    rd := {lst([f"(⟨none, {a}⟩, {b - a})" for a, b in rd0])}
    wr := {lst([f"(⟨none, {a}⟩, {b - a})" for a, b in wr0])}
    sep := [] }}

def A : Spec :=
  {{ regs := {lst(r0)}
    cells := {lst(c0)} }}

def T : Spec :=
  {{ regs := {lst(r1)}
    cells := {lst(c1)} }}

def frame : List (Aff × Nat) := {lst([f"(⟨none, {a}⟩, {b - a})" for a, b in frame])}

set_option maxRecDepth 100000 in
theorem ok : check st Services.Bootstrap.SymExec.prog A T frame {start} {end} {total} = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **Cut {k} to cut {l}** by the executor: the statement of the composed `S{k}.run` … `S{l-1}.run`. -/
theorem run {sig} (h : St{k} {targs}) :
    ∃ ω' μ', FreeStepsH p (refineContract env) {start} ω μ x {end} ω' μ' x {total} ∧ St{l} {targs.replace('ω μ', "ω' μ'") if False else targs.rsplit(' ', 2)[0]} ω' μ' := by
  obtain ⟨ω', μ', hrun, hr, hc, hfr, hpg⟩ := check_sound (R := refineContract env) ok
    (Services.Bootstrap.SymExec.hyp (p := p) (P := P))
    {'[' + ', '.join(vars_) + ']'} {tup(bproofs)} {tup(['Nat.zero_le _' for _ in vars_])} ω μ
    {tup([f"rng_rd (lo := {n.split('_')[1]}) (hi := {n.split('_')[2]}) h.{n}" for n in rdn0])}
    {tup([f"rng_wr (lo := {n.split('_')[1]}) (hi := {n.split('_')[2]}) h.{n}" for n in wrn0])} trivial
    {tup(['h.' + n for n in regn0])}
    {tup([('h.' + n) if not conc else f"(cell_of_list h.{n} rfl)" for n, conc in celln0])} x
  obtain {tup([f"r{i}" for i in range(len(regn1))]).replace(', trivial⟩', ', -⟩') if regn1 else '-'} := hr
  obtain {tup([f"c{i}" for i in range(len(celln1))]).replace(', trivial⟩', ', -⟩') if celln1 else '-'} := hc
  refine ⟨ω', μ', hrun, ?_⟩
  exact {{ ''')
fl = []
for i, n in enumerate(regn1): fl.append(f'{n} := r{i}')
for i, (n, conc) in enumerate(celln1): fl.append(f'{n} := list_of_cell rfl c{i}' if conc else f'{n} := c{i}')
for n in wrn1:
    a, b = map(int, n[3:].split('_'))
    fl.append(f'{n} := fun a h1 h2 => (writable_pages hpg a).trans (h.{containing(wr0, wrn0, a, b)} a (by omega) (by omega))')
for n in rdn1:
    a, b = map(int, n[4:].split('_'))
    fl.append(f'{n} := fun a h1 h2 => (readable_pages hpg a).trans (h.{containing(rd0 + wr0, rdn0 + wrn0, a, b)} a (by omega) (by omega))' if containing(rd0 + wr0, rdn0 + wrn0, a, b) in rdn0 else
              f'{n} := fun a h1 h2 => (readable_pages hpg a).trans (Memory.readable_of_writable (h.{containing(wr0, wrn0, a, b)} a (by omega) (by omega)))')
fl.append(f'fr := fun a ha => by\n            simp only [{", ".join(f"C{i}" for i in range(k + 1, l + 1))}, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true\', decide_eq_false_iff_not, not_and, Nat.not_lt] at ha\n            rw [hfr a (by show a < 4294967296; omega) (out_of_bool (by simp only [frame, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_self_eq_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]; omega))]\n            exact h.fr a (by simp_all)')
fl.append('rdq := fun a => (readable_pages hpg a).trans (h.rdq a)')
fl.append('wrq := fun a => (writable_pages hpg a).trans (h.wrq a)')
o.append('\n          '.join(fl) + ' }\n')
o.append(f'\nend Services.Bootstrap.SymExec.{mod}\n')
open(out, 'w').write(''.join(o))
print(out, total, 'steps', len(entries), 'instrs')
