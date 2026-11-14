#!/usr/bin/env python3
"""Emit Dec32 range proofs: named naturals, bounds, rewrites, check, and check_sound applied."""
import sys, re
sys.path.insert(0, sys.argv[0].rsplit('/',1)[0])
from gen_d32 import Gen, T64
NAMES = ['y','sp','v','F','ret','v5','v6']

def op_proof(pat, k):
    """the proof of `pat.eval E = E.ρ k`, by the one-operation lemmas"""
    m = re.match(r'\.alu2i \.shloLImm64 \(\.const 0\) \(\.var (\d+)\) (\d+)$', pat)
    if m: return f'(op_shloLm (by decide) (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu2i \.shloLImm64 \(\.const 0\) \(\.sx 4 \(\.var (\d+)\)\) 32$', pat)
    if m: return f'(op_shloL_sx (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu2i \.shloRImm64 \(\.const 0\) \(\.var (\d+)\) (\d+)$', pat)
    if m: return f'(op_shloR (by decide) (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu3 \.mulUpperUU \(\.var (\d+)\) \(\.const (\d+)\) \(\.const 0\)$', pat)
    if m: return f'op_mulU.trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu3 \.mul64 \(\.var (\d+)\) \(\.const (\d+)\) \(\.const 0\)$', pat)
    if m: return f'(op_mul (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu2i \.mulImm64 \(\.const 0\) \(\.var (\d+)\) (\d+)$', pat)
    if m: return f'(op_mulI (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu3 \.sub64 \(\.var (\d+)\) \(\.var (\d+)\) \(\.const 0\)$', pat)
    if m: return f'(op_sub (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu3 \.sub64 \(\.sx 4 \(\.var (\d+)\)\) \(\.var (\d+)\) \(\.const 0\)$', pat)
    if m: return f'(op_sub_sx (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    m = re.match(r'\.alu2i \.andImm \(\.const 0\) \(\.var (\d+)\) 2046$', pat)
    if m: return f'op_and2046.trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide)))'
    m = re.match(r'\.alu2i \.shloLImm32 \(\.const 0\) \(\.var (\d+)\) 1$', pat)
    if m: return f'(op_shloL32 (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [VALS, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)'
    raise Exception('no lemma for ' + pat)

def emit_proofs(tag, g, steps):
    n = len(g.names)
    lets = '\n'.join(f'  let v{k} := {e}' for k, e in g.defs)
    vlist = ', '.join(NAMES + [f'v{k}' for k, _ in g.defs])
    args = ' '.join(NAMES)
    rw_items = ',\n    '.join(op_proof(p, k).replace('VALS', f'vals_{tag}') for p, k in g.rws)
    return f'''
/-- The named naturals of the range {g.lo} ≤ y < {g.hi}. -/
def vals_{tag} ({args} : Nat) : List Nat :=
  let v0 := y
{lets}
  [{vlist}]

theorem bh_{tag} {{{args} : Nat}} (hy : {g.lo} ≤ y ∧ y < {g.hi}) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_{tag} {args}) st_{tag}.ub ∧ LBHold (vals_{tag} {args}) st_{tag}.lb := by
  simp only [vals_{tag}, st_{tag}, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_{tag} {{{args} : Nat}} (ω : Regs) (μ : Memory) (hy : {g.lo} ≤ y ∧ y < {g.hi}) :
    RwHold ⟨fun k => (vals_{tag} {args}).getD k 0, ω, μ⟩ st_{tag}.rw := by
  exact ⟨{rw_items}, trivial⟩
'''

def main(out, ranges, ends_file):
    import re
    ends = open(ends_file).read().replace('\\n', ' ')
    recs = {int(t): (int(st), r11, r12, ' '.join(c.split())) for t, st, r11, r12, c in
            re.findall(r'"RANGE (\d+) STEPS (\d+) R11 (.*?) R12 (.*?) CELLS (\[.*?\])"', ends, re.S)}
    from gen_d32 import build, emit
    src = '''import Services.Bootstrap.SymExec.ProgF
import PVM.SymExec.Ops

namespace Services.Bootstrap.SymExec.Dec32

open PVM PVM.SymExec

def pairs : List Nat := (List.range 100).flatMap fun i => [48 + i / 10, 48 + i % 10]

def A : Spec :=
  { regs := [(0, .var 4), (1, .var 1), (5, .var 5), (6, .var 6), (7, .var 2), (8, .var 3)]
    cells := (⟨some 2, 0⟩, 4, .var 0) :: (List.range 200).map fun j => (⟨none, (70844 + j : Nat)⟩, 1, .const (pairs.getD j 0)) }
'''
    for lo, hi in ranges:
        g = build(lo, hi)
        tag = str(lo)
        steps, r11, r12, cells = recs[lo]
        st = emit(tag, g).split('#eval')[0]
        src += st
        src += f'''
def T_{tag} : Spec :=
  {{ regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, {' '.join(r11.split())}), (12, {' '.join(r12.split())})]
    cells := {cells} }}

set_option maxRecDepth 100000 in
theorem ok_{tag} : check st_{tag} Services.Bootstrap.SymExec.progF A T_{tag} [(⟨some 1, -72⟩, 72)] 68146 61857 {steps} = true := by
  decide +kernel
'''
        src += emit_proofs(tag, g, steps)
    src += '\nend Services.Bootstrap.SymExec.Dec32\n'
    open(out, 'w').write(src)

if __name__ == '__main__':
    import ast
    main(sys.argv[1], ast.literal_eval(sys.argv[2]), sys.argv[3])
