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

# the caller's ω₀, ω₅, ω₆ (ret, v5, v6), saved at sp − 8, sp − 16, sp − 24 (fmt's T + 64, T + 56, T + 48)
SAVED = ', (⟨some 1, -8⟩, 8, .var 4), (⟨some 1, -16⟩, 8, .var 5), (⟨some 1, -24⟩, 8, .var 6)]'

def main(out, ranges, ends_file):
    import re
    ends = open(ends_file).read().replace('\\n', ' ')
    recs = {int(t): (int(st), r11, r12, ' '.join(c.split())) for t, st, r11, r12, c in
            re.findall(r'"RANGE (\d+) STEPS (\d+) R11 (.*?) R12 (.*?) CELLS (\[.*?\])"', ends, re.S)}
    from gen_d32 import build, emit
    src = '''import Services.Bootstrap.SymExec.ProgF
import Services.Bootstrap.SymExec.DecB
import PVM.SymExec.Ops

namespace Services.Bootstrap.SymExec.Dec32

open PVM PVM.SymExec

def pairs : List Nat := (List.range 100).flatMap fun i => [48 + i / 10, 48 + i % 10]

def A : Spec :=
  { regs := [(0, .var 4), (1, .var 1), (5, .var 5), (6, .var 6), (7, .var 2), (8, .var 3)]
    cells := (⟨some 2, 0⟩, 4, .var 0) :: (List.range 200).map fun j => (⟨none, (70844 + j : Nat)⟩, 1, .const (pairs.getD j 0)) }
'''
    src += '\nopen Num\n\n' + open(sys.argv[0].rsplit('/',1)[0] + '/d32_helpers.lean.in').read()
    for n in range(1, 11): src += emit_decB(n)
    for lo, hi in ranges:
        g = build(lo, hi)
        tag = str(lo)
        steps, r11, r12, cells = recs[lo]
        st = emit(tag, g).split('#eval')[0]
        src += st
        src += f'''
def T_{tag} : Spec :=
  {{ regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, {' '.join(r11.split())}), (12, {' '.join(r12.split())})]
    cells := {cells[:cells.rindex(']')] + SAVED} }}

set_option maxRecDepth 100000 in
theorem ok_{tag} : check st_{tag} Services.Bootstrap.SymExec.progF A T_{tag} [(⟨some 1, -72⟩, 72)] 68146 61857 {steps} = true := by
  decide +kernel
'''
        src += emit_proofs(tag, g, steps)
        n = int(re.search(r'const (\d+)', r12).group(1))
        src += emit_run(tag, g, steps, cells, n)
    src += '\nend Services.Bootstrap.SymExec.Dec32\n'
    open(out, 'w').write(src)


def expand(g, k):
    """the Lean term of named natural k in terms of y"""
    if k < 7: return ['y','sp','v','F','ret','v5','v6'][k]
    e = dict(g.defs)[k]
    return '(' + re.sub(r'v(\d+)', lambda m: expand(g, int(m.group(1))), e) + ')'

def kexpr(g, j):
    """K with named natural j = 2 * K"""
    e = dict(g.defs)[j]
    m = re.match(r'2 \* \((.*)\)$', e) or re.match(r'2 \* (v\d+)$', e)
    return '(' + re.sub(r'v(\d+)', lambda mm: expand(g, int(mm.group(1))), m.group(1)) + ')'

def parse_cells(cells):
    out = []
    for m in re.finditer(r'\(\{ base := some 1, off := (-?\d+) \}, (\d+), (PVM\.SymExec\.SVal\.mem0 \{ base := some (\d+), off := (\d+) \} \d+|PVM\.SymExec\.SVal\.tbl \[([0-9, ]*)\] \(PVM\.SymExec\.SVal\.var (\d+)\))\)', cells):
        off, w = int(m.group(1)), int(m.group(2))
        if m.group(4): out.append(('mem', off, w, int(m.group(4)), int(m.group(5))))
        else: out.append(('tbl', off, w, int(m.group(7)), m.group(6)))
    return out

def emit_run(tag, g, steps, cells, n):
    lo, hi = g.lo, g.hi
    base = 24 + n
    vals = f'vals_{tag} y sp v F ret v5 v6'
    E = f'⟨fun k => ({vals}).getD k 0, ω, μ⟩'
    VS = f'vals_{tag}, List.getD_cons_succ, List.getD_cons_zero'
    src = f'''
open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_{tag} {{X : Type}} {{R : HostRel X}} {{p : ByteArray}} {{P : Program}} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : {lo} ≤ y ∧ y < {hi}) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x {steps} ∧
      RegsHold {E} ω' T_{tag}.regs ∧ CellsHold {E} μ' T_{tag}.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_{tag} hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_{tag} (hypF (p := p) (P := P))
    ({vals}) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, {VS}] at ht; omega)
        (by simp only [InReg, Aff.eval, {VS}] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, {VS}] at ht; omega)
        (by simp only [InReg, Aff.eval, {VS}] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, {VS}] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_{tag}] using hY, tableHold ht⟩ x trivial (rw_{tag} ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, {VS}] at hin
  omega
'''
    # the octets
    cs = parse_cells(cells)
    names = ', '.join(f'c{i}' for i in range(len(cs)))
    lines = []
    facts = []
    for i, c in enumerate(cs):
        kind, off, w = c[0], c[1], c[2]
        pos = off + base   # index within the n octets
        lines.append(f'  have a{i} : ((sp : Int) + {off}).toNat = sp - {base} + {pos} := by omega')
        if kind == 'mem':
            j, b = c[3], c[4]
            K = kexpr(g, j)
            if w == 1:
                if b == 70844:
                    lines.append(f'  have b{i} : (((2 * {K} : Nat) : Int) + 70844).toNat = 70844 + 2 * {K} := by omega')
                    lines.append(f'  rw [a{i}, b{i}, tab1 ht (by omega), pairs_hi _ (by omega)] at c{i}')
                else:
                    lines.append(f'  have b{i} : (((2 * {K} : Nat) : Int) + 70845).toNat = 70844 + (2 * {K} + 1) := by omega')
                    lines.append(f'  rw [a{i}, b{i}, tab1 ht (by omega), pairs_lo _ (by omega)] at c{i}')
                facts.append(f'rd1 c{i}')
            else:
                lines.append(f'  have b{i} : (((2 * {K} : Nat) : Int) + 70844).toNat = 70844 + 2 * {K} := by omega')
                lines.append(f'  rw [a{i}, b{i}, enc2] at c{i}')
                lines.append(f'  have d{i}a : μ\'.read (sp - {base} + {pos}) = UInt8.ofNat ((48 + {K} / 10) % 256) := by')
                lines.append(f'    have e := (rd2 c{i}).1; rw [Nat.add_zero (sp - {base} + {pos}), Nat.add_zero (70844 + 2 * {K})] at e')
                lines.append(f'    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]')
                lines.append(f'  have d{i}b : μ\'.read (sp - {base} + {pos + 1}) = UInt8.ofNat ((48 + {K} % 10) % 256) := by')
                lines.append(f'    have e := (rd2 c{i}).2; rw [show sp - {base} + {pos} + 1 = sp - {base} + {pos + 1} by omega,')
                lines.append(f'      show 70844 + 2 * {K} + 1 = 70844 + (2 * {K} + 1) by omega] at e')
                lines.append(f'    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]')
                facts += [f'd{i}a', f'd{i}b']
        else:
            j, lst = c[3], c[4]
            K = kexpr(g, j)
            lem = 'tbl0' if lst.strip() == '48' else 'tblL'
            lines.append(f'  rw [a{i}, {lem} _ (by omega)] at c{i}')
            facts.append(f'rd1 c{i}')
    body = '\n'.join(lines)
    fl = ', '.join(facts)
    src += f'''
theorem digits_{tag} {{μ μ' : Memory}} {{ω : Regs}} {{y sp v F ret v5 v6 : Nat}} (hy : {lo} ≤ y ∧ y < {hi})
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_{tag} y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_{tag}.cells) :
    μ'.readN (sp - {base}) {n} = decB y := by
  obtain ⟨{names}, -⟩ := hc
  simp only [T_{tag}, Aff.eval, SVal.eval, vals_{tag}, List.getD_cons_succ, List.getD_cons_zero] at {' '.join(f'c{i}' for i in range(len(cs)))}
{body}
  rw [decB_{n} (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, {fl}, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)
'''
    return src

def emit_decB(n):
    lo = 10 ** (n - 1) if n > 1 else 0
    hi = 10 ** n
    steps = ''.join(f'decB, if_neg (by omega), ' for _ in range(n - 1)) + 'decB, if_pos (by omega)'
    entries = ', '.join(f'UInt8.ofNat (48 + y / {10 ** (n - 1 - i)} % 10)' for i in range(n))
    return f'''
theorem decB_{n} {{y : Nat}} (h : {lo} ≤ y ∧ y < {hi}) : decB y = [{entries}] := by
  rw [{steps}]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)
'''

if __name__ == '__main__':
    import ast
    main(sys.argv[1], ast.literal_eval(sys.argv[2]), sys.argv[3])
