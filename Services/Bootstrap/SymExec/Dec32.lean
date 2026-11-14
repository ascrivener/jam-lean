import Services.Bootstrap.SymExec.ProgF
import Services.Bootstrap.SymExec.DecB
import PVM.SymExec.Ops

namespace Services.Bootstrap.SymExec.Dec32

open PVM PVM.SymExec

def pairs : List Nat := (List.range 100).flatMap fun i => [48 + i / 10, 48 + i % 10]

def A : Spec :=
  { regs := [(0, .var 4), (1, .var 1), (5, .var 5), (6, .var 6), (7, .var 2), (8, .var 3)]
    cells := (⟨some 2, 0⟩, 4, .var 0) :: (List.range 200).map fun j => (⟨none, (70844 + j : Nat)⟩, 1, .const (pairs.getD j 0)) }

open Num

theorem pairs_hi : ∀ k, k < 100 → pairs.getD (2 * k) 0 = 48 + k / 10 := by decide
theorem pairs_lo : ∀ k, k < 100 → pairs.getD (2 * k + 1) 0 = 48 + k % 10 := by decide

theorem cellsHold_map {E : Env} {μ : Memory} {f : Nat → Aff × Nat × SVal} :
    ∀ (l : List Nat), (∀ j ∈ l, μ.readN ((f j).1.eval E).toNat (f j).2.1 = encodeLE (f j).2.1 ((f j).2.2.eval E)) →
      CellsHold E μ (l.map f)
  | [], _ => trivial
  | j :: l, h => ⟨h j (List.mem_cons_self ..), cellsHold_map l fun i hi => h i (List.mem_cons_of_mem _ hi)⟩

/-- The digit-pair table at 70844, as the start memory holds it. -/
def Table (μ : Memory) : Prop := ∀ j, j < 200 → μ.readN (70844 + j) 1 = encodeLE 1 (pairs.getD j 0)

theorem tableHold {E : Env} {μ : Memory} (ht : Table μ) :
    CellsHold E μ ((List.range 200).map fun j => (⟨none, ((70844 + j : Nat) : Int)⟩, 1, .const (pairs.getD j 0))) :=
  cellsHold_map _ fun j hj => by
    simp only [Aff.eval, SVal.eval, Int.zero_add, Int.toNat_natCast]
    exact ht j (List.mem_range.1 hj)


theorem rd1 {μ : Memory} {a v : Nat} (h : μ.readN a 1 = encodeLE 1 v) : μ.read a = UInt8.ofNat (v % 256) := by
  simpa [Memory.readN, encodeLE] using h

set_option maxRecDepth 10000 in
theorem pairs_lt : ∀ j, j < 200 → pairs.getD j 0 < 256 := by decide

theorem tab1 {μ : Memory} (ht : Table μ) {j : Nat} (hj : j < 200) :
    decodeLE (μ.readN (70844 + j) 1) = pairs.getD j 0 := by
  rw [ht j hj, decodeLE_encodeLE]
  have : pairs.getD j 0 < 256 := pairs_lt j hj
  simpa [pow8] using Nat.mod_eq_of_lt this

theorem tabR {μ : Memory} (ht : Table μ) {j : Nat} (hj : j < 200) :
    μ.read (70844 + j) = UInt8.ofNat (pairs.getD j 0 % 256) := rd1 (ht j hj)

theorem rd2 {μ μ' : Memory} {a b : Nat} (h : μ'.readN a 2 = μ.readN b 2) :
    μ'.read (a + 0) = μ.read (b + 0) ∧ μ'.read (a + 1) = μ.read (b + 1) := by
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq] at h
  exact ⟨h.1, h.2.1⟩

theorem enc2 (μ : Memory) (a : Nat) : encodeLE 2 (decodeLE (μ.readN a 2)) = μ.readN a 2 := by
  have := encodeLE_decodeLE (μ.readN a 2); rwa [Memory.length_readN] at this

theorem tblL : ∀ k, k < 10 → [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57].getD (2 * k) 0 = 48 + k := by decide
theorem tbl0 : ∀ k, k < 1 → [48].getD (2 * k) 0 = 48 + k := by decide

theorem decB_1 {y : Nat} (h : 0 ≤ y ∧ y < 10) : decB y = [UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_2 {y : Nat} (h : 10 ≤ y ∧ y < 100) : decB y = [UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_3 {y : Nat} (h : 100 ≤ y ∧ y < 1000) : decB y = [UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_4 {y : Nat} (h : 1000 ≤ y ∧ y < 10000) : decB y = [UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_5 {y : Nat} (h : 10000 ≤ y ∧ y < 100000) : decB y = [UInt8.ofNat (48 + y / 10000 % 10), UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_6 {y : Nat} (h : 100000 ≤ y ∧ y < 1000000) : decB y = [UInt8.ofNat (48 + y / 100000 % 10), UInt8.ofNat (48 + y / 10000 % 10), UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_7 {y : Nat} (h : 1000000 ≤ y ∧ y < 10000000) : decB y = [UInt8.ofNat (48 + y / 1000000 % 10), UInt8.ofNat (48 + y / 100000 % 10), UInt8.ofNat (48 + y / 10000 % 10), UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_8 {y : Nat} (h : 10000000 ≤ y ∧ y < 100000000) : decB y = [UInt8.ofNat (48 + y / 10000000 % 10), UInt8.ofNat (48 + y / 1000000 % 10), UInt8.ofNat (48 + y / 100000 % 10), UInt8.ofNat (48 + y / 10000 % 10), UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_9 {y : Nat} (h : 100000000 ≤ y ∧ y < 1000000000) : decB y = [UInt8.ofNat (48 + y / 100000000 % 10), UInt8.ofNat (48 + y / 10000000 % 10), UInt8.ofNat (48 + y / 1000000 % 10), UInt8.ofNat (48 + y / 100000 % 10), UInt8.ofNat (48 + y / 10000 % 10), UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

theorem decB_10 {y : Nat} (h : 1000000000 ≤ y ∧ y < 10000000000) : decB y = [UInt8.ofNat (48 + y / 1000000000 % 10), UInt8.ofNat (48 + y / 100000000 % 10), UInt8.ofNat (48 + y / 10000000 % 10), UInt8.ofNat (48 + y / 1000000 % 10), UInt8.ofNat (48 + y / 100000 % 10), UInt8.ofNat (48 + y / 10000 % 10), UInt8.ofNat (48 + y / 1000 % 10), UInt8.ofNat (48 + y / 100 % 10), UInt8.ofNat (48 + y / 10 % 10), UInt8.ofNat (48 + y / 1 % 10)] := by
  rw [decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_neg (by omega), decB, if_pos (by omega)]
  simp only [List.cons_append, List.nil_append, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_0 : Static :=
  { ub := [1, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 1]
    lb := [0, 2147484248, 0, 0, 2, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm32 (.const 0) (.var 0) 1, .var 7)] }

def T_0 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -25 }), (12, PVM.SymExec.SVal.const 1)]
    cells := [({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.tbl [48] (PVM.SymExec.SVal.var 7))] }

set_option maxRecDepth 100000 in
theorem ok_0 : check st_0 Services.Bootstrap.SymExec.progF A T_0 [(⟨some 1, -72⟩, 72)] 68146 61857 28 = true := by
  decide +kernel

/-- The named naturals of the range 0 ≤ y < 1. -/
def vals_0 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := 2 * v0
  [y, sp, v, F, ret, v5, v6, v7]

theorem bh_0 {y sp v F ret v5 v6 : Nat} (hy : 0 ≤ y ∧ y < 1) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_0 y sp v F ret v5 v6) st_0.ub ∧ LBHold (vals_0 y sp v F ret v5 v6) st_0.lb := by
  simp only [vals_0, st_0, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_0 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 0 ≤ y ∧ y < 1) :
    RwHold ⟨fun k => (vals_0 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_0.rw := by
  exact ⟨(op_shloL32 (by simp only [vals_0, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_0, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_0 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 0 ≤ y ∧ y < 1) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 28 ∧
      RegsHold ⟨fun k => (vals_0 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_0.regs ∧ CellsHold ⟨fun k => (vals_0 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_0.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_0 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_0 (hypF (p := p) (P := P))
    (vals_0 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_0] using hY, tableHold ht⟩ x trivial (rw_0 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_0 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 0 ≤ y ∧ y < 1)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_0 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_0.cells) :
    μ'.readN (sp - 25) 1 = decB y := by
  obtain ⟨c0, -⟩ := hc
  simp only [T_0, Aff.eval, SVal.eval, vals_0, List.getD_cons_succ, List.getD_cons_zero] at c0
  have a0 : ((sp : Int) + -25).toNat = sp - 25 + 0 := by omega
  rw [a0, tbl0 _ (by omega)] at c0
  rw [decB_1 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_1 : Static :=
  { ub := [10, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 19]
    lb := [1, 2147484248, 0, 0, 2, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm32 (.const 0) (.var 0) 1, .var 7)] }

def T_1 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -25 }), (12, PVM.SymExec.SVal.const 1)]
    cells := [({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 7))] }

set_option maxRecDepth 100000 in
theorem ok_1 : check st_1 Services.Bootstrap.SymExec.progF A T_1 [(⟨some 1, -72⟩, 72)] 68146 61857 29 = true := by
  decide +kernel

/-- The named naturals of the range 1 ≤ y < 10. -/
def vals_1 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := 2 * v0
  [y, sp, v, F, ret, v5, v6, v7]

theorem bh_1 {y sp v F ret v5 v6 : Nat} (hy : 1 ≤ y ∧ y < 10) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1 y sp v F ret v5 v6) st_1.ub ∧ LBHold (vals_1 y sp v F ret v5 v6) st_1.lb := by
  simp only [vals_1, st_1, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1 ≤ y ∧ y < 10) :
    RwHold ⟨fun k => (vals_1 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1.rw := by
  exact ⟨(op_shloL32 (by simp only [vals_1, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_1 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 1 ≤ y ∧ y < 10) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 29 ∧
      RegsHold ⟨fun k => (vals_1 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_1.regs ∧ CellsHold ⟨fun k => (vals_1 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_1 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_1 (hypF (p := p) (P := P))
    (vals_1 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_1] using hY, tableHold ht⟩ x trivial (rw_1 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_1 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 1 ≤ y ∧ y < 10)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_1 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1.cells) :
    μ'.readN (sp - 25) 1 = decB y := by
  obtain ⟨c0, -⟩ := hc
  simp only [T_1, Aff.eval, SVal.eval, vals_1, List.getD_cons_succ, List.getD_cons_zero] at c0
  have a0 : ((sp : Int) + -25).toNat = sp - 25 + 0 := by omega
  rw [a0, tblL _ (by omega)] at c0
  rw [decB_1 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_10 : Static :=
  { ub := [100, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 27866022694354945, 25, 125833, 1, 1, 100, 56294995342131200, 199]
    lb := [10, 2147484248, 0, 0, 2, 0, 0, 2814749767106560, 2, 10486, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 48, .var 7),
    (.alu2i .shloRImm64 (.const 0) (.var 7) 50, .var 8),
    (.alu2i .mulImm64 (.const 0) (.var 8) 5243, .var 9),
    (.alu2i .shloRImm64 (.const 0) (.var 9) 17, .var 10),
    (.alu2i .mulImm64 (.const 0) (.var 10) 100, .var 11),
    (.alu3 .sub64 (.var 0) (.var 11) (.const 0), .var 12),
    (.alu2i .shloLImm64 (.const 0) (.var 12) 49, .var 13),
    (.alu2i .shloRImm64 (.const 0) (.var 13) 48, .var 14)] }

def T_10 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -26 }), (12, PVM.SymExec.SVal.const 2)]
    cells := [({ base := some 1, off := -26 }, 2, PVM.SymExec.SVal.mem0 { base := some 14, off := 70844 } 2)] }

set_option maxRecDepth 100000 in
theorem ok_10 : check st_10 Services.Bootstrap.SymExec.progF A T_10 [(⟨some 1, -72⟩, 72)] 68146 61857 37 = true := by
  decide +kernel

/-- The named naturals of the range 10 ≤ y < 100. -/
def vals_10 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 281474976710656
  let v8 := v0 / 4
  let v9 := v0 / 4 * 5243
  let v10 := v0 / 100
  let v11 := v0 / 100 * 100
  let v12 := v0 % 100
  let v13 := v0 % 100 * 562949953421312
  let v14 := 2 * (v0 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]

theorem bh_10 {y sp v F ret v5 v6 : Nat} (hy : 10 ≤ y ∧ y < 100) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_10 y sp v F ret v5 v6) st_10.ub ∧ LBHold (vals_10 y sp v F ret v5 v6) st_10.lb := by
  simp only [vals_10, st_10, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_10 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 10 ≤ y ∧ y < 100) :
    RwHold ⟨fun k => (vals_10 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_10.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_10 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 10 ≤ y ∧ y < 100) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 37 ∧
      RegsHold ⟨fun k => (vals_10 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_10.regs ∧ CellsHold ⟨fun k => (vals_10 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_10.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_10 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_10 (hypF (p := p) (P := P))
    (vals_10 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_10] using hY, tableHold ht⟩ x trivial (rw_10 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_10 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 10 ≤ y ∧ y < 100)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_10 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_10.cells) :
    μ'.readN (sp - 26) 2 = decB y := by
  obtain ⟨c0, -⟩ := hc
  simp only [T_10, Aff.eval, SVal.eval, vals_10, List.getD_cons_succ, List.getD_cons_zero] at c0
  have a0 : ((sp : Int) + -26).toNat = sp - 26 + 0 := by omega
  have b0 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a0, b0, enc2] at c0
  have d0a : μ'.read (sp - 26 + 0) = UInt8.ofNat ((48 + (y % 100) / 10) % 256) := by
    have e := (rd2 c0).1; rw [Nat.add_zero (sp - 26 + 0), Nat.add_zero (70844 + 2 * (y % 100))] at e
    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]
  have d0b : μ'.read (sp - 26 + 1) = UInt8.ofNat ((48 + (y % 100) % 10) % 256) := by
    have e := (rd2 c0).2; rw [show sp - 26 + 0 + 1 = sp - 26 + 1 by omega,
      show 70844 + 2 * (y % 100) + 1 = 70844 + (2 * (y % 100) + 1) by omega] at e
    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]
  rw [decB_2 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, d0a, d0b, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_100 : Static :=
  { ub := [1000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 281193501733945345, 250, 1305508, 10, 901, 100, 56294995342131200, 199, 19]
    lb := [100, 2147484248, 0, 0, 2, 0, 0, 28147497671065600, 25, 131075, 1, 100, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 48, .var 7),
    (.alu2i .shloRImm64 (.const 0) (.var 7) 50, .var 8),
    (.alu2i .mulImm64 (.const 0) (.var 8) 5243, .var 9),
    (.alu2i .shloRImm64 (.const 0) (.var 9) 17, .var 10),
    (.alu2i .mulImm64 (.const 0) (.var 10) 100, .var 11),
    (.alu3 .sub64 (.var 0) (.var 11) (.const 0), .var 12),
    (.alu2i .shloLImm64 (.const 0) (.var 12) 49, .var 13),
    (.alu2i .shloRImm64 (.const 0) (.var 13) 48, .var 14),
    (.alu2i .shloLImm32 (.const 0) (.var 10) 1, .var 15)] }

def T_100 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -27 }), (12, PVM.SymExec.SVal.const 3)]
    cells := [({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 15)), ({ base := some 1, off := -26 }, 2, PVM.SymExec.SVal.mem0 { base := some 14, off := 70844 } 2)] }

set_option maxRecDepth 100000 in
theorem ok_100 : check st_100 Services.Bootstrap.SymExec.progF A T_100 [(⟨some 1, -72⟩, 72)] 68146 61857 46 = true := by
  decide +kernel

/-- The named naturals of the range 100 ≤ y < 1000. -/
def vals_100 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 281474976710656
  let v8 := v0 / 4
  let v9 := v0 / 4 * 5243
  let v10 := v0 / 100
  let v11 := v0 / 100 * 100
  let v12 := v0 % 100
  let v13 := v0 % 100 * 562949953421312
  let v14 := 2 * (v0 % 100)
  let v15 := 2 * (v0 / 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]

theorem bh_100 {y sp v F ret v5 v6 : Nat} (hy : 100 ≤ y ∧ y < 1000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_100 y sp v F ret v5 v6) st_100.ub ∧ LBHold (vals_100 y sp v F ret v5 v6) st_100.lb := by
  simp only [vals_100, st_100, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_100 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 100 ≤ y ∧ y < 1000) :
    RwHold ⟨fun k => (vals_100 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_100.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_100 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 100 ≤ y ∧ y < 1000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 46 ∧
      RegsHold ⟨fun k => (vals_100 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_100.regs ∧ CellsHold ⟨fun k => (vals_100 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_100.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_100 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_100 (hypF (p := p) (P := P))
    (vals_100 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_100] using hY, tableHold ht⟩ x trivial (rw_100 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_100 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 100 ≤ y ∧ y < 1000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_100 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_100.cells) :
    μ'.readN (sp - 27) 3 = decB y := by
  obtain ⟨c0, c1, -⟩ := hc
  simp only [T_100, Aff.eval, SVal.eval, vals_100, List.getD_cons_succ, List.getD_cons_zero] at c0 c1
  have a0 : ((sp : Int) + -27).toNat = sp - 27 + 0 := by omega
  rw [a0, tblL _ (by omega)] at c0
  have a1 : ((sp : Int) + -26).toNat = sp - 27 + 1 := by omega
  have b1 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a1, b1, enc2] at c1
  have d1a : μ'.read (sp - 27 + 1) = UInt8.ofNat ((48 + (y % 100) / 10) % 256) := by
    have e := (rd2 c1).1; rw [Nat.add_zero (sp - 27 + 1), Nat.add_zero (70844 + 2 * (y % 100))] at e
    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]
  have d1b : μ'.read (sp - 27 + 2) = UInt8.ofNat ((48 + (y % 100) % 10) % 256) := by
    have e := (rd2 c1).2; rw [show sp - 27 + 1 + 1 = sp - 27 + 2 by omega,
      show 70844 + 2 * (y % 100) + 1 = 70844 + (2 * (y % 100) + 1) by omega] at e
    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]
  rw [decB_3 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, d1a, d1b, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_1000 : Static :=
  { ub := [10000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 42945377992705, 35180853652792, 1, 1, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199]
    lb := [1000, 2147484248, 0, 0, 2, 0, 0, 4294967296000, 3518437209000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21)] }

def T_1000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -28 }), (12, PVM.SymExec.SVal.const 4)]
    cells := [({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_1000 : check st_1000 Services.Bootstrap.SymExec.progF A T_1000 [(⟨some 1, -72⟩, 72)] 68146 61857 69 = true := by
  decide +kernel

/-- The named naturals of the range 1000 ≤ y < 10000. -/
def vals_1000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21]

theorem bh_1000 {y sp v F ret v5 v6 : Nat} (hy : 1000 ≤ y ∧ y < 10000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1000 y sp v F ret v5 v6) st_1000.ub ∧ LBHold (vals_1000 y sp v F ret v5 v6) st_1000.lb := by
  simp only [vals_1000, st_1000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1000 ≤ y ∧ y < 10000) :
    RwHold ⟨fun k => (vals_1000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_1000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 1000 ≤ y ∧ y < 10000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 69 ∧
      RegsHold ⟨fun k => (vals_1000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_1000.regs ∧ CellsHold ⟨fun k => (vals_1000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_1000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_1000 (hypF (p := p) (P := P))
    (vals_1000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_1000] using hY, tableHold ht⟩ x trivial (rw_1000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_1000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 1000 ≤ y ∧ y < 10000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_1000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1000.cells) :
    μ'.readN (sp - 28) 4 = decB y := by
  obtain ⟨c0, c1, c2, c3, -⟩ := hc
  simp only [T_1000, Aff.eval, SVal.eval, vals_1000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3
  have a0 : ((sp : Int) + -25).toNat = sp - 28 + 3 := by omega
  have b0 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a0, b0, tab1 ht (by omega), pairs_lo _ (by omega)] at c0
  have a1 : ((sp : Int) + -26).toNat = sp - 28 + 2 := by omega
  have b1 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_hi _ (by omega)] at c1
  have a2 : ((sp : Int) + -27).toNat = sp - 28 + 1 := by omega
  have b2 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_lo _ (by omega)] at c2
  have a3 : ((sp : Int) + -28).toNat = sp - 28 + 0 := by omega
  have b3 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_hi _ (by omega)] at c3
  rw [decB_4 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, rd1 c1, rd1 c2, rd1 c3, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_10000 : Static :=
  { ub := [100000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 429492434632705, 351840202462792, 10, 90001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 19]
    lb := [10000, 2147484248, 0, 0, 2, 0, 0, 42949672960000, 35184372090000, 1, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm32 (.const 0) (.var 9) 1, .var 22)] }

def T_10000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -29 }), (12, PVM.SymExec.SVal.const 5)]
    cells := [({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 22)), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_10000 : check st_10000 Services.Bootstrap.SymExec.progF A T_10000 [(⟨some 1, -72⟩, 72)] 68146 61857 78 = true := by
  decide +kernel

/-- The named naturals of the range 10000 ≤ y < 100000. -/
def vals_10000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := 2 * v9
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22]

theorem bh_10000 {y sp v F ret v5 v6 : Nat} (hy : 10000 ≤ y ∧ y < 100000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_10000 y sp v F ret v5 v6) st_10000.ub ∧ LBHold (vals_10000 y sp v F ret v5 v6) st_10000.lb := by
  simp only [vals_10000, st_10000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_10000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 10000 ≤ y ∧ y < 100000) :
    RwHold ⟨fun k => (vals_10000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_10000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_10000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 10000 ≤ y ∧ y < 100000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 78 ∧
      RegsHold ⟨fun k => (vals_10000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_10000.regs ∧ CellsHold ⟨fun k => (vals_10000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_10000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_10000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_10000 (hypF (p := p) (P := P))
    (vals_10000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_10000] using hY, tableHold ht⟩ x trivial (rw_10000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_10000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 10000 ≤ y ∧ y < 100000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_10000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_10000.cells) :
    μ'.readN (sp - 29) 5 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hc
  simp only [T_10000, Aff.eval, SVal.eval, vals_10000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4
  have a0 : ((sp : Int) + -29).toNat = sp - 29 + 0 := by omega
  rw [a0, tblL _ (by omega)] at c0
  have a1 : ((sp : Int) + -25).toNat = sp - 29 + 4 := by omega
  have b1 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_lo _ (by omega)] at c1
  have a2 : ((sp : Int) + -26).toNat = sp - 29 + 3 := by omega
  have b2 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_hi _ (by omega)] at c2
  have a3 : ((sp : Int) + -27).toNat = sp - 29 + 2 := by omega
  have b3 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_lo _ (by omega)] at c3
  have a4 : ((sp : Int) + -28).toNat = sp - 29 + 1 := by omega
  have b4 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_hi _ (by omega)] at c4
  rw [decB_5 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, rd1 c1, rd1 c2, rd1 c3, rd1 c4, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_100000 : Static :=
  { ub := [1000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 4294963001032705, 3518433690562792, 100, 990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 27866022694354945, 25, 125833, 1, 1, 100, 56294995342131200, 199]
    lb := [100000, 2147484248, 0, 0, 2, 0, 0, 429496729600000, 351843720900000, 10, 100000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2814749767106560, 2, 10486, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 48, .var 22),
    (.alu2i .shloRImm64 (.const 0) (.var 22) 50, .var 23),
    (.alu2i .mulImm64 (.const 0) (.var 23) 5243, .var 24),
    (.alu2i .shloRImm64 (.const 0) (.var 24) 17, .var 25),
    (.alu2i .mulImm64 (.const 0) (.var 25) 100, .var 26),
    (.alu3 .sub64 (.var 9) (.var 26) (.const 0), .var 27),
    (.alu2i .shloLImm64 (.const 0) (.var 27) 49, .var 28),
    (.alu2i .shloRImm64 (.const 0) (.var 28) 48, .var 29)] }

def T_100000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -30 }), (12, PVM.SymExec.SVal.const 6)]
    cells := [({ base := some 1, off := -30 }, 2, PVM.SymExec.SVal.mem0 { base := some 29, off := 70844 } 2), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_100000 : check st_100000 Services.Bootstrap.SymExec.progF A T_100000 [(⟨some 1, -72⟩, 72)] 68146 61857 85 = true := by
  decide +kernel

/-- The named naturals of the range 100000 ≤ y < 1000000. -/
def vals_100000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 281474976710656
  let v23 := v9 / 4
  let v24 := v9 / 4 * 5243
  let v25 := v9 / 100
  let v26 := v9 / 100 * 100
  let v27 := v9 % 100
  let v28 := v9 % 100 * 562949953421312
  let v29 := 2 * (v9 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29]

theorem bh_100000 {y sp v F ret v5 v6 : Nat} (hy : 100000 ≤ y ∧ y < 1000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_100000 y sp v F ret v5 v6) st_100000.ub ∧ LBHold (vals_100000 y sp v F ret v5 v6) st_100000.lb := by
  simp only [vals_100000, st_100000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_100000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 100000 ≤ y ∧ y < 1000000) :
    RwHold ⟨fun k => (vals_100000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_100000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_100000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 100000 ≤ y ∧ y < 1000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 85 ∧
      RegsHold ⟨fun k => (vals_100000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_100000.regs ∧ CellsHold ⟨fun k => (vals_100000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_100000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_100000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_100000 (hypF (p := p) (P := P))
    (vals_100000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_100000] using hY, tableHold ht⟩ x trivial (rw_100000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_100000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 100000 ≤ y ∧ y < 1000000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_100000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_100000.cells) :
    μ'.readN (sp - 30) 6 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, -⟩ := hc
  simp only [T_100000, Aff.eval, SVal.eval, vals_100000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4
  have a0 : ((sp : Int) + -30).toNat = sp - 30 + 0 := by omega
  have b0 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 100) := by omega
  rw [a0, b0, enc2] at c0
  have d0a : μ'.read (sp - 30 + 0) = UInt8.ofNat ((48 + ((y / 10000) % 100) / 10) % 256) := by
    have e := (rd2 c0).1; rw [Nat.add_zero (sp - 30 + 0), Nat.add_zero (70844 + 2 * ((y / 10000) % 100))] at e
    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]
  have d0b : μ'.read (sp - 30 + 1) = UInt8.ofNat ((48 + ((y / 10000) % 100) % 10) % 256) := by
    have e := (rd2 c0).2; rw [show sp - 30 + 0 + 1 = sp - 30 + 1 by omega,
      show 70844 + 2 * ((y / 10000) % 100) + 1 = 70844 + (2 * ((y / 10000) % 100) + 1) by omega] at e
    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]
  have a1 : ((sp : Int) + -25).toNat = sp - 30 + 5 := by omega
  have b1 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_lo _ (by omega)] at c1
  have a2 : ((sp : Int) + -26).toNat = sp - 30 + 4 := by omega
  have b2 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_hi _ (by omega)] at c2
  have a3 : ((sp : Int) + -27).toNat = sp - 30 + 3 := by omega
  have b3 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_lo _ (by omega)] at c3
  have a4 : ((sp : Int) + -28).toNat = sp - 30 + 2 := by omega
  have b4 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_hi _ (by omega)] at c4
  rw [decB_6 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, d0a, d0b, rd1 c1, rd1 c2, rd1 c3, rd1 c4, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_1000000 : Static :=
  { ub := [10000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 42949668665032705, 35184368571562792, 1000, 9990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 281193501733945345, 250, 1305508, 10, 901, 100, 56294995342131200, 199, 19]
    lb := [1000000, 2147484248, 0, 0, 2, 0, 0, 4294967296000000, 3518437209000000, 100, 1000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28147497671065600, 25, 131075, 1, 100, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 48, .var 22),
    (.alu2i .shloRImm64 (.const 0) (.var 22) 50, .var 23),
    (.alu2i .mulImm64 (.const 0) (.var 23) 5243, .var 24),
    (.alu2i .shloRImm64 (.const 0) (.var 24) 17, .var 25),
    (.alu2i .mulImm64 (.const 0) (.var 25) 100, .var 26),
    (.alu3 .sub64 (.var 9) (.var 26) (.const 0), .var 27),
    (.alu2i .shloLImm64 (.const 0) (.var 27) 49, .var 28),
    (.alu2i .shloRImm64 (.const 0) (.var 28) 48, .var 29),
    (.alu2i .shloLImm32 (.const 0) (.var 25) 1, .var 30)] }

def T_1000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -31 }), (12, PVM.SymExec.SVal.const 7)]
    cells := [({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 30)), ({ base := some 1, off := -30 }, 2, PVM.SymExec.SVal.mem0 { base := some 29, off := 70844 } 2), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_1000000 : check st_1000000 Services.Bootstrap.SymExec.progF A T_1000000 [(⟨some 1, -72⟩, 72)] 68146 61857 94 = true := by
  decide +kernel

/-- The named naturals of the range 1000000 ≤ y < 10000000. -/
def vals_1000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 281474976710656
  let v23 := v9 / 4
  let v24 := v9 / 4 * 5243
  let v25 := v9 / 100
  let v26 := v9 / 100 * 100
  let v27 := v9 % 100
  let v28 := v9 % 100 * 562949953421312
  let v29 := 2 * (v9 % 100)
  let v30 := 2 * (v9 / 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30]

theorem bh_1000000 {y sp v F ret v5 v6 : Nat} (hy : 1000000 ≤ y ∧ y < 10000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1000000 y sp v F ret v5 v6) st_1000000.ub ∧ LBHold (vals_1000000 y sp v F ret v5 v6) st_1000000.lb := by
  simp only [vals_1000000, st_1000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1000000 ≤ y ∧ y < 10000000) :
    RwHold ⟨fun k => (vals_1000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_1000000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 1000000 ≤ y ∧ y < 10000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 94 ∧
      RegsHold ⟨fun k => (vals_1000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_1000000.regs ∧ CellsHold ⟨fun k => (vals_1000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1000000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_1000000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_1000000 (hypF (p := p) (P := P))
    (vals_1000000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_1000000] using hY, tableHold ht⟩ x trivial (rw_1000000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_1000000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 1000000 ≤ y ∧ y < 10000000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_1000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1000000.cells) :
    μ'.readN (sp - 31) 7 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, c5, -⟩ := hc
  simp only [T_1000000, Aff.eval, SVal.eval, vals_1000000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4 c5
  have a0 : ((sp : Int) + -31).toNat = sp - 31 + 0 := by omega
  rw [a0, tblL _ (by omega)] at c0
  have a1 : ((sp : Int) + -30).toNat = sp - 31 + 1 := by omega
  have b1 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 100) := by omega
  rw [a1, b1, enc2] at c1
  have d1a : μ'.read (sp - 31 + 1) = UInt8.ofNat ((48 + ((y / 10000) % 100) / 10) % 256) := by
    have e := (rd2 c1).1; rw [Nat.add_zero (sp - 31 + 1), Nat.add_zero (70844 + 2 * ((y / 10000) % 100))] at e
    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]
  have d1b : μ'.read (sp - 31 + 2) = UInt8.ofNat ((48 + ((y / 10000) % 100) % 10) % 256) := by
    have e := (rd2 c1).2; rw [show sp - 31 + 1 + 1 = sp - 31 + 2 by omega,
      show 70844 + 2 * ((y / 10000) % 100) + 1 = 70844 + (2 * ((y / 10000) % 100) + 1) by omega] at e
    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]
  have a2 : ((sp : Int) + -25).toNat = sp - 31 + 6 := by omega
  have b2 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_lo _ (by omega)] at c2
  have a3 : ((sp : Int) + -26).toNat = sp - 31 + 5 := by omega
  have b3 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_hi _ (by omega)] at c3
  have a4 : ((sp : Int) + -27).toNat = sp - 31 + 4 := by omega
  have b4 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_lo _ (by omega)] at c4
  have a5 : ((sp : Int) + -28).toNat = sp - 31 + 3 := by omega
  have b5 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a5, b5, tab1 ht (by omega), pairs_hi _ (by omega)] at c5
  rw [decB_7 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, d1a, d1b, rd1 c2, rd1 c3, rd1 c4, rd1 c5, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_10000000 : Static :=
  { ub := [100000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 429496725305032705, 351843717381562792, 10000, 99990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 42945377992705, 35180853652792, 1, 1, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199]
    lb := [10000000, 2147484248, 0, 0, 2, 0, 0, 42949672960000000, 35184372090000000, 1000, 10000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4294967296000, 3518437209000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36)] }

def T_10000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -32 }), (12, PVM.SymExec.SVal.const 8)]
    cells := [({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_10000000 : check st_10000000 Services.Bootstrap.SymExec.progF A T_10000000 [(⟨some 1, -72⟩, 72)] 68146 61857 107 = true := by
  decide +kernel

/-- The named naturals of the range 10000000 ≤ y < 100000000. -/
def vals_10000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36]

theorem bh_10000000 {y sp v F ret v5 v6 : Nat} (hy : 10000000 ≤ y ∧ y < 100000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_10000000 y sp v F ret v5 v6) st_10000000.ub ∧ LBHold (vals_10000000 y sp v F ret v5 v6) st_10000000.lb := by
  simp only [vals_10000000, st_10000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_10000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 10000000 ≤ y ∧ y < 100000000) :
    RwHold ⟨fun k => (vals_10000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_10000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_10000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_10000000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 10000000 ≤ y ∧ y < 100000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 107 ∧
      RegsHold ⟨fun k => (vals_10000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_10000000.regs ∧ CellsHold ⟨fun k => (vals_10000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_10000000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_10000000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_10000000 (hypF (p := p) (P := P))
    (vals_10000000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_10000000] using hY, tableHold ht⟩ x trivial (rw_10000000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_10000000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 10000000 ≤ y ∧ y < 100000000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_10000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_10000000.cells) :
    μ'.readN (sp - 32) 8 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, -⟩ := hc
  simp only [T_10000000, Aff.eval, SVal.eval, vals_10000000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4 c5 c6 c7
  have a0 : ((sp : Int) + -29).toNat = sp - 32 + 3 := by omega
  have b0 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 100) + 1) := by omega
  rw [a0, b0, tab1 ht (by omega), pairs_lo _ (by omega)] at c0
  have a1 : ((sp : Int) + -30).toNat = sp - 32 + 2 := by omega
  have b1 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 100) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_hi _ (by omega)] at c1
  have a2 : ((sp : Int) + -31).toNat = sp - 32 + 1 := by omega
  have b2 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 10000 / 100) + 1) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_lo _ (by omega)] at c2
  have a3 : ((sp : Int) + -32).toNat = sp - 32 + 0 := by omega
  have b3 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 10000 / 100) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_hi _ (by omega)] at c3
  have a4 : ((sp : Int) + -25).toNat = sp - 32 + 7 := by omega
  have b4 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_lo _ (by omega)] at c4
  have a5 : ((sp : Int) + -26).toNat = sp - 32 + 6 := by omega
  have b5 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a5, b5, tab1 ht (by omega), pairs_hi _ (by omega)] at c5
  have a6 : ((sp : Int) + -27).toNat = sp - 32 + 5 := by omega
  have b6 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a6, b6, tab1 ht (by omega), pairs_lo _ (by omega)] at c6
  have a7 : ((sp : Int) + -28).toNat = sp - 32 + 4 := by omega
  have b7 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a7, b7, tab1 ht (by omega), pairs_hi _ (by omega)] at c7
  rw [decB_8 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, rd1 c1, rd1 c2, rd1 c3, rd1 c4, rd1 c5, rd1 c6, rd1 c7, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_100000000 : Static :=
  { ub := [1000000000, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 4294967291705032705, 3518437205481562792, 100000, 999990001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 429492434632705, 351840202462792, 10, 90001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 19]
    lb := [100000000, 2147484248, 0, 0, 2, 0, 0, 429496729600000000, 351843720900000000, 10000, 100000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42949672960000, 35184372090000, 1, 10000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36),
    (.alu2i .shloLImm32 (.const 0) (.var 24) 1, .var 37)] }

def T_100000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -33 }), (12, PVM.SymExec.SVal.const 9)]
    cells := [({ base := some 1, off := -33 }, 1, PVM.SymExec.SVal.tbl [48, 48, 49, 48, 50, 48, 51, 48, 52, 48, 53, 48, 54, 48, 55, 48, 56, 48, 57] (PVM.SymExec.SVal.var 37)), ({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_100000000 : check st_100000000 Services.Bootstrap.SymExec.progF A T_100000000 [(⟨some 1, -72⟩, 72)] 68146 61857 116 = true := by
  decide +kernel

/-- The named naturals of the range 100000000 ≤ y < 1000000000. -/
def vals_100000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  let v37 := 2 * v24
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37]

theorem bh_100000000 {y sp v F ret v5 v6 : Nat} (hy : 100000000 ≤ y ∧ y < 1000000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_100000000 y sp v F ret v5 v6) st_100000000.ub ∧ LBHold (vals_100000000 y sp v F ret v5 v6) st_100000000.lb := by
  simp only [vals_100000000, st_100000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_100000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 100000000 ≤ y ∧ y < 1000000000) :
    RwHold ⟨fun k => (vals_100000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_100000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloL32 (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_100000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_100000000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 100000000 ≤ y ∧ y < 1000000000) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 116 ∧
      RegsHold ⟨fun k => (vals_100000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_100000000.regs ∧ CellsHold ⟨fun k => (vals_100000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_100000000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_100000000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_100000000 (hypF (p := p) (P := P))
    (vals_100000000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_100000000] using hY, tableHold ht⟩ x trivial (rw_100000000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_100000000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 100000000 ≤ y ∧ y < 1000000000)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_100000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_100000000.cells) :
    μ'.readN (sp - 33) 9 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, -⟩ := hc
  simp only [T_100000000, Aff.eval, SVal.eval, vals_100000000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  have a0 : ((sp : Int) + -33).toNat = sp - 33 + 0 := by omega
  rw [a0, tblL _ (by omega)] at c0
  have a1 : ((sp : Int) + -29).toNat = sp - 33 + 4 := by omega
  have b1 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 100) + 1) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_lo _ (by omega)] at c1
  have a2 : ((sp : Int) + -30).toNat = sp - 33 + 3 := by omega
  have b2 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 100) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_hi _ (by omega)] at c2
  have a3 : ((sp : Int) + -31).toNat = sp - 33 + 2 := by omega
  have b3 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 10000 / 100) + 1) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_lo _ (by omega)] at c3
  have a4 : ((sp : Int) + -32).toNat = sp - 33 + 1 := by omega
  have b4 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 10000 / 100) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_hi _ (by omega)] at c4
  have a5 : ((sp : Int) + -25).toNat = sp - 33 + 8 := by omega
  have b5 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a5, b5, tab1 ht (by omega), pairs_lo _ (by omega)] at c5
  have a6 : ((sp : Int) + -26).toNat = sp - 33 + 7 := by omega
  have b6 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a6, b6, tab1 ht (by omega), pairs_hi _ (by omega)] at c6
  have a7 : ((sp : Int) + -27).toNat = sp - 33 + 6 := by omega
  have b7 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a7, b7, tab1 ht (by omega), pairs_lo _ (by omega)] at c7
  have a8 : ((sp : Int) + -28).toNat = sp - 33 + 5 := by omega
  have b8 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a8, b8, tab1 ht (by omega), pairs_hi _ (by omega)] at c8
  rw [decB_9 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, rd1 c0, rd1 c1, rd1 c2, rd1 c3, rd1 c4, rd1 c5, rd1 c6, rd1 c7, rd1 c8, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_1000000000 : Static :=
  { ub := [2147483648, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 9223372032559808513, 7555786369323821224, 214749, 2147480001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 922335636881409, 755577353758333, 22, 210001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 5910974510923777, 6, 26216, 1, 1, 100, 56294995342131200, 199]
    lb := [1000000000, 2147484248, 0, 0, 2, 0, 0, 4294967296000000000, 3518437209000000000, 100000, 1000000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 429496729600000, 351843720900000, 10, 100000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2814749767106560, 2, 10486, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.var 0) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.var 0) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36),
    (.alu2i .shloLImm64 (.const 0) (.var 24) 48, .var 37),
    (.alu2i .shloRImm64 (.const 0) (.var 37) 50, .var 38),
    (.alu2i .mulImm64 (.const 0) (.var 38) 5243, .var 39),
    (.alu2i .shloRImm64 (.const 0) (.var 39) 17, .var 40),
    (.alu2i .mulImm64 (.const 0) (.var 40) 100, .var 41),
    (.alu3 .sub64 (.var 24) (.var 41) (.const 0), .var 42),
    (.alu2i .shloLImm64 (.const 0) (.var 42) 49, .var 43),
    (.alu2i .shloRImm64 (.const 0) (.var 43) 48, .var 44)] }

def T_1000000000 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -34 }), (12, PVM.SymExec.SVal.const 10)]
    cells := [({ base := some 1, off := -34 }, 2, PVM.SymExec.SVal.mem0 { base := some 44, off := 70844 } 2), ({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_1000000000 : check st_1000000000 Services.Bootstrap.SymExec.progF A T_1000000000 [(⟨some 1, -72⟩, 72)] 68146 61857 123 = true := by
  decide +kernel

/-- The named naturals of the range 1000000000 ≤ y < 2147483648. -/
def vals_1000000000 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 % 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 % 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  let v37 := v24 * 281474976710656
  let v38 := v24 / 4
  let v39 := v24 / 4 * 5243
  let v40 := v24 / 100
  let v41 := v24 / 100 * 100
  let v42 := v24 % 100
  let v43 := v24 % 100 * 562949953421312
  let v44 := 2 * (v24 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44]

theorem bh_1000000000 {y sp v F ret v5 v6 : Nat} (hy : 1000000000 ≤ y ∧ y < 2147483648) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_1000000000 y sp v F ret v5 v6) st_1000000000.ub ∧ LBHold (vals_1000000000 y sp v F ret v5 v6) st_1000000000.lb := by
  simp only [vals_1000000000, st_1000000000, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_1000000000 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 1000000000 ≤ y ∧ y < 2147483648) :
    RwHold ⟨fun k => (vals_1000000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_1000000000.rw := by
  exact ⟨(op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_1000000000, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_1000000000 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 1000000000 ≤ y ∧ y < 2147483648) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 123 ∧
      RegsHold ⟨fun k => (vals_1000000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_1000000000.regs ∧ CellsHold ⟨fun k => (vals_1000000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1000000000.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_1000000000 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_1000000000 (hypF (p := p) (P := P))
    (vals_1000000000 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_1000000000] using hY, tableHold ht⟩ x trivial (rw_1000000000 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_1000000000 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 1000000000 ≤ y ∧ y < 2147483648)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_1000000000 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_1000000000.cells) :
    μ'.readN (sp - 34) 10 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, -⟩ := hc
  simp only [T_1000000000, Aff.eval, SVal.eval, vals_1000000000, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  have a0 : ((sp : Int) + -34).toNat = sp - 34 + 0 := by omega
  have b0 : (((2 * (((y / 10000) / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (((y / 10000) / 10000) % 100) := by omega
  rw [a0, b0, enc2] at c0
  have d0a : μ'.read (sp - 34 + 0) = UInt8.ofNat ((48 + (((y / 10000) / 10000) % 100) / 10) % 256) := by
    have e := (rd2 c0).1; rw [Nat.add_zero (sp - 34 + 0), Nat.add_zero (70844 + 2 * (((y / 10000) / 10000) % 100))] at e
    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]
  have d0b : μ'.read (sp - 34 + 1) = UInt8.ofNat ((48 + (((y / 10000) / 10000) % 100) % 10) % 256) := by
    have e := (rd2 c0).2; rw [show sp - 34 + 0 + 1 = sp - 34 + 1 by omega,
      show 70844 + 2 * (((y / 10000) / 10000) % 100) + 1 = 70844 + (2 * (((y / 10000) / 10000) % 100) + 1) by omega] at e
    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]
  have a1 : ((sp : Int) + -29).toNat = sp - 34 + 5 := by omega
  have b1 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 100) + 1) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_lo _ (by omega)] at c1
  have a2 : ((sp : Int) + -30).toNat = sp - 34 + 4 := by omega
  have b2 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 100) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_hi _ (by omega)] at c2
  have a3 : ((sp : Int) + -31).toNat = sp - 34 + 3 := by omega
  have b3 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 10000 / 100) + 1) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_lo _ (by omega)] at c3
  have a4 : ((sp : Int) + -32).toNat = sp - 34 + 2 := by omega
  have b4 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 10000 / 100) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_hi _ (by omega)] at c4
  have a5 : ((sp : Int) + -25).toNat = sp - 34 + 9 := by omega
  have b5 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a5, b5, tab1 ht (by omega), pairs_lo _ (by omega)] at c5
  have a6 : ((sp : Int) + -26).toNat = sp - 34 + 8 := by omega
  have b6 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a6, b6, tab1 ht (by omega), pairs_hi _ (by omega)] at c6
  have a7 : ((sp : Int) + -27).toNat = sp - 34 + 7 := by omega
  have b7 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a7, b7, tab1 ht (by omega), pairs_lo _ (by omega)] at c7
  have a8 : ((sp : Int) + -28).toNat = sp - 34 + 6 := by omega
  have b8 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a8, b8, tab1 ht (by omega), pairs_hi _ (by omega)] at c8
  rw [decB_10 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, d0a, d0b, rd1 c1, rd1 c2, rd1 c3, rd1 c4, rd1 c5, rd1 c6, rd1 c7, rd1 c8, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

def st_2147483648 : Static :=
  { ub := [4294967296, 4294967296, 4294967292, 4294967296, 2807, 18446744073709551616, 18446744073709551616, 18446744069414584321, 15111572742166079656, 429497, 4294960001, 18446744073709551616, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 18446744073709551616, 56294995342131200, 199, 1844671273762817, 1511154707516665, 43, 420001, 10000, 2814749767106560000, 2500, 13107500, 201, 199, 100, 9901, 100, 56294995342131200, 199, 11821949021847553, 11, 52431, 1, 1, 100, 56294995342131200, 199]
    lb := [2147483648, 2147484248, 0, 0, 2, 0, 0, 9223372036854775808, 7555786372842258432, 214748, 2147480000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 922335636881408, 755577353758332, 21, 210000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5910974510923776, 5, 26215, 0, 0, 0, 0, 0]
    rd := [(⟨some 2, 0⟩, 4), (⟨none, 70844⟩, 200)]
    wr := [(⟨some 1, -72⟩, 72)]
    sep := [((⟨some 2, 0⟩, 4), (⟨some 1, -72⟩, 72))]
    rw := [(.alu2i .shloLImm64 (.const 0) (.sx 4 (.var 0)) 32, .var 7),
    (.alu3 .mulUpperUU (.var 7) (.const 15111572745684516864) (.const 0), .var 8),
    (.alu2i .shloRImm64 (.const 0) (.var 8) 45, .var 9),
    (.alu3 .mul64 (.var 9) (.const 10000) (.const 0), .var 10),
    (.alu3 .sub64 (.sx 4 (.var 0)) (.var 10) (.const 0), .var 11),
    (.alu2i .shloLImm64 (.const 0) (.var 11) 48, .var 12),
    (.alu2i .shloRImm64 (.const 0) (.var 12) 50, .var 13),
    (.alu3 .mul64 (.var 13) (.const 5243) (.const 0), .var 14),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 16, .var 15),
    (.alu2i .andImm (.const 0) (.var 15) 2046, .var 16),
    (.alu2i .shloRImm64 (.const 0) (.var 14) 17, .var 17),
    (.alu2i .mulImm64 (.const 0) (.var 17) 100, .var 18),
    (.alu3 .sub64 (.var 11) (.var 18) (.const 0), .var 19),
    (.alu2i .shloLImm64 (.const 0) (.var 19) 49, .var 20),
    (.alu2i .shloRImm64 (.const 0) (.var 20) 48, .var 21),
    (.alu2i .shloLImm64 (.const 0) (.var 9) 32, .var 22),
    (.alu3 .mulUpperUU (.var 22) (.const 15111572745684516864) (.const 0), .var 23),
    (.alu2i .shloRImm64 (.const 0) (.var 23) 45, .var 24),
    (.alu3 .mul64 (.var 24) (.const 10000) (.const 0), .var 25),
    (.alu3 .sub64 (.var 9) (.var 25) (.const 0), .var 26),
    (.alu2i .shloLImm64 (.const 0) (.var 26) 48, .var 27),
    (.alu2i .shloRImm64 (.const 0) (.var 27) 50, .var 28),
    (.alu3 .mul64 (.var 28) (.const 5243) (.const 0), .var 29),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 16, .var 30),
    (.alu2i .andImm (.const 0) (.var 30) 2046, .var 31),
    (.alu2i .shloRImm64 (.const 0) (.var 29) 17, .var 32),
    (.alu2i .mulImm64 (.const 0) (.var 32) 100, .var 33),
    (.alu3 .sub64 (.var 26) (.var 33) (.const 0), .var 34),
    (.alu2i .shloLImm64 (.const 0) (.var 34) 49, .var 35),
    (.alu2i .shloRImm64 (.const 0) (.var 35) 48, .var 36),
    (.alu2i .shloLImm64 (.const 0) (.var 24) 48, .var 37),
    (.alu2i .shloRImm64 (.const 0) (.var 37) 50, .var 38),
    (.alu2i .mulImm64 (.const 0) (.var 38) 5243, .var 39),
    (.alu2i .shloRImm64 (.const 0) (.var 39) 17, .var 40),
    (.alu2i .mulImm64 (.const 0) (.var 40) 100, .var 41),
    (.alu3 .sub64 (.var 24) (.var 41) (.const 0), .var 42),
    (.alu2i .shloLImm64 (.const 0) (.var 42) 49, .var 43),
    (.alu2i .shloRImm64 (.const 0) (.var 43) 48, .var 44)] }

def T_2147483648 : Spec :=
  { regs := [(0, .const 2802), (1, .addr ⟨some 1, -72⟩), (7, .var 3), (11, PVM.SymExec.SVal.addr { base := some 1, off := -34 }), (12, PVM.SymExec.SVal.const 10)]
    cells := [({ base := some 1, off := -34 }, 2, PVM.SymExec.SVal.mem0 { base := some 44, off := 70844 } 2), ({ base := some 1, off := -29 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70845 } 1), ({ base := some 1, off := -30 }, 1, PVM.SymExec.SVal.mem0 { base := some 36, off := 70844 } 1), ({ base := some 1, off := -31 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70845 } 1), ({ base := some 1, off := -32 }, 1, PVM.SymExec.SVal.mem0 { base := some 31, off := 70844 } 1), ({ base := some 1, off := -25 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70845 } 1), ({ base := some 1, off := -26 }, 1, PVM.SymExec.SVal.mem0 { base := some 21, off := 70844 } 1), ({ base := some 1, off := -27 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70845 } 1), ({ base := some 1, off := -28 }, 1, PVM.SymExec.SVal.mem0 { base := some 16, off := 70844 } 1)] }

set_option maxRecDepth 100000 in
theorem ok_2147483648 : check st_2147483648 Services.Bootstrap.SymExec.progF A T_2147483648 [(⟨some 1, -72⟩, 72)] 68146 61857 123 = true := by
  decide +kernel

/-- The named naturals of the range 2147483648 ≤ y < 4294967296. -/
def vals_2147483648 (y sp v F ret v5 v6 : Nat) : List Nat :=
  let v0 := y
  let v7 := v0 * 4294967296
  let v8 := v7 * 15111572745684516864 / 18446744073709551616
  let v9 := v0 / 10000
  let v10 := v0 / 10000 * 10000
  let v11 := v0 + 18446744069414584320 - v0 / 10000 * 10000
  let v12 := v0 % 10000 * 281474976710656
  let v13 := v0 % 10000 / 4
  let v14 := v0 % 10000 / 4 * 5243
  let v15 := v0 % 10000 / 4 * 5243 / 65536
  let v16 := 2 * (v0 % 10000 / 100)
  let v17 := v0 % 10000 / 100
  let v18 := v0 % 10000 / 100 * 100
  let v19 := v0 + 18446744069414584320 - v0 / 10000 * 10000 - v0 % 10000 / 100 * 100
  let v20 := v0 % 100 * 562949953421312
  let v21 := 2 * (v0 % 100)
  let v22 := v9 * 4294967296
  let v23 := v22 * 15111572745684516864 / 18446744073709551616
  let v24 := v9 / 10000
  let v25 := v9 / 10000 * 10000
  let v26 := v9 % 10000
  let v27 := v9 % 10000 * 281474976710656
  let v28 := v9 % 10000 / 4
  let v29 := v9 % 10000 / 4 * 5243
  let v30 := v9 % 10000 / 4 * 5243 / 65536
  let v31 := 2 * (v9 % 10000 / 100)
  let v32 := v9 % 10000 / 100
  let v33 := v9 % 10000 / 100 * 100
  let v34 := v9 % 100
  let v35 := v9 % 100 * 562949953421312
  let v36 := 2 * (v9 % 100)
  let v37 := v24 * 281474976710656
  let v38 := v24 / 4
  let v39 := v24 / 4 * 5243
  let v40 := v24 / 100
  let v41 := v24 / 100 * 100
  let v42 := v24 % 100
  let v43 := v24 % 100 * 562949953421312
  let v44 := 2 * (v24 % 100)
  [y, sp, v, F, ret, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44]

theorem bh_2147483648 {y sp v F ret v5 v6 : Nat} (hy : 2147483648 ≤ y ∧ y < 4294967296) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616) :
    BHold (vals_2147483648 y sp v F ret v5 v6) st_2147483648.ub ∧ LBHold (vals_2147483648 y sp v F ret v5 v6) st_2147483648.lb := by
  simp only [vals_2147483648, st_2147483648, BHold, LBHold]
  and_intros
  all_goals first | omega | trivial

theorem rw_2147483648 {y sp v F ret v5 v6 : Nat} (ω : Regs) (μ : Memory) (hy : 2147483648 ≤ y ∧ y < 4294967296) :
    RwHold ⟨fun k => (vals_2147483648 y sp v F ret v5 v6).getD k 0, ω, μ⟩ st_2147483648.rw := by
  exact ⟨(op_shloL_sx (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub_sx (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_mulU.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mul (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    op_and2046.trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero]; exact idx_hi _ (Nat.mod_lt _ (by decide))),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_mulI (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_sub (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloLm (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega),
    (op_shloR (by decide) (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega)).trans (by simp only [vals_2147483648, SVal.eval, List.getD_cons_succ, List.getD_cons_zero] <;> omega), trivial⟩

open Services.Bootstrap.Code Services.Bootstrap.CodeF in
theorem run_2147483648 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P]
    (x : X) (ω : Regs) (μ : Memory) (y sp v F ret v5 v6 : Nat)
    (hy : 2147483648 ≤ y ∧ y < 4294967296) (hsp : 2147484248 ≤ sp ∧ sp < 4294967296)
    (hv : v < 4294967292) (hF : F < 4294967296) (hret : 2 ≤ ret ∧ ret < 2807) (h5 : v5 < 18446744073709551616)
    (h6 : v6 < 18446744073709551616)
    (r0 : ω[0] = UInt64.ofNat ret) (r1 : ω[1] = UInt64.ofNat sp) (r5 : ω[5] = UInt64.ofNat v5)
    (r6 : ω[6] = UInt64.ofNat v6) (r7 : ω[7] = UInt64.ofNat v) (r8 : ω[8] = UInt64.ofNat F)
    (hY : μ.readN v 4 = encodeLE 4 y) (ht : Table μ)
    (hrv : ∀ t, v ≤ t → t < v + 4 → μ.readable t = true)
    (hrt : ∀ t, 70844 ≤ t → t < 71044 → μ.readable t = true)
    (hw : ∀ t, sp - 72 ≤ t → t < sp → μ.writable t = true) (hs : v + 4 ≤ sp - 72 ∨ sp ≤ v) :
    ∃ ω' μ', FreeStepsH p R 68146 ω μ x 61857 ω' μ' x 123 ∧
      RegsHold ⟨fun k => (vals_2147483648 y sp v F ret v5 v6).getD k 0, ω, μ⟩ ω' T_2147483648.regs ∧ CellsHold ⟨fun k => (vals_2147483648 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_2147483648.cells ∧
      (∀ t, t < two32 → (t < sp - 72 ∨ sp ≤ t) → μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  obtain ⟨hB, hLB⟩ := bh_2147483648 hy hsp hv hF hret h5 h6
  obtain ⟨ω', μ', run, hr, hc, hfr, hpg⟩ := check_sound (R := R) ok_2147483648 (hypF (p := p) (P := P))
    (vals_2147483648 y sp v F ret v5 v6) hB hLB ω μ
    ⟨fun t ht => hrv t (by simp only [InReg, Aff.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at ht; omega),
      fun t ht => hrt t (by simp only [InReg, Aff.eval] at ht; omega) (by simp only [InReg, Aff.eval] at ht; omega),
      trivial⟩
    ⟨fun t ht => hw t (by simp only [InReg, Aff.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at ht; omega)
        (by simp only [InReg, Aff.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at ht; omega), trivial⟩
    ⟨fun t h1 h2 => by simp only [InReg, Aff.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at h1 h2; omega, trivial⟩
    ⟨r0, r1, r5, r6, r7, r8, trivial⟩
    ⟨by simpa [Aff.eval, SVal.eval, vals_2147483648] using hY, tableHold ht⟩ x trivial (rw_2147483648 ω μ hy)
  refine ⟨ω', μ', run, hr, hc, fun t ht hout => hfr t ht fun f hf hin => ?_, hpg⟩
  simp only [List.mem_singleton] at hf; subst hf
  simp only [InReg, Aff.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at hin
  omega

theorem digits_2147483648 {μ μ' : Memory} {ω : Regs} {y sp v F ret v5 v6 : Nat} (hy : 2147483648 ≤ y ∧ y < 4294967296)
    (hsp : 2147484248 ≤ sp ∧ sp < 4294967296) (ht : Table μ)
    (hc : CellsHold ⟨fun k => (vals_2147483648 y sp v F ret v5 v6).getD k 0, ω, μ⟩ μ' T_2147483648.cells) :
    μ'.readN (sp - 34) 10 = decB y := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, -⟩ := hc
  simp only [T_2147483648, Aff.eval, SVal.eval, vals_2147483648, List.getD_cons_succ, List.getD_cons_zero] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  have a0 : ((sp : Int) + -34).toNat = sp - 34 + 0 := by omega
  have b0 : (((2 * (((y / 10000) / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (((y / 10000) / 10000) % 100) := by omega
  rw [a0, b0, enc2] at c0
  have d0a : μ'.read (sp - 34 + 0) = UInt8.ofNat ((48 + (((y / 10000) / 10000) % 100) / 10) % 256) := by
    have e := (rd2 c0).1; rw [Nat.add_zero (sp - 34 + 0), Nat.add_zero (70844 + 2 * (((y / 10000) / 10000) % 100))] at e
    rw [e, tabR ht (by omega), pairs_hi _ (by omega)]
  have d0b : μ'.read (sp - 34 + 1) = UInt8.ofNat ((48 + (((y / 10000) / 10000) % 100) % 10) % 256) := by
    have e := (rd2 c0).2; rw [show sp - 34 + 0 + 1 = sp - 34 + 1 by omega,
      show 70844 + 2 * (((y / 10000) / 10000) % 100) + 1 = 70844 + (2 * (((y / 10000) / 10000) % 100) + 1) by omega] at e
    rw [e, tabR ht (by omega), pairs_lo _ (by omega)]
  have a1 : ((sp : Int) + -29).toNat = sp - 34 + 5 := by omega
  have b1 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 100) + 1) := by omega
  rw [a1, b1, tab1 ht (by omega), pairs_lo _ (by omega)] at c1
  have a2 : ((sp : Int) + -30).toNat = sp - 34 + 4 := by omega
  have b2 : (((2 * ((y / 10000) % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 100) := by omega
  rw [a2, b2, tab1 ht (by omega), pairs_hi _ (by omega)] at c2
  have a3 : ((sp : Int) + -31).toNat = sp - 34 + 3 := by omega
  have b3 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * ((y / 10000) % 10000 / 100) + 1) := by omega
  rw [a3, b3, tab1 ht (by omega), pairs_lo _ (by omega)] at c3
  have a4 : ((sp : Int) + -32).toNat = sp - 34 + 2 := by omega
  have b4 : (((2 * ((y / 10000) % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * ((y / 10000) % 10000 / 100) := by omega
  rw [a4, b4, tab1 ht (by omega), pairs_hi _ (by omega)] at c4
  have a5 : ((sp : Int) + -25).toNat = sp - 34 + 9 := by omega
  have b5 : (((2 * (y % 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 100) + 1) := by omega
  rw [a5, b5, tab1 ht (by omega), pairs_lo _ (by omega)] at c5
  have a6 : ((sp : Int) + -26).toNat = sp - 34 + 8 := by omega
  have b6 : (((2 * (y % 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 100) := by omega
  rw [a6, b6, tab1 ht (by omega), pairs_hi _ (by omega)] at c6
  have a7 : ((sp : Int) + -27).toNat = sp - 34 + 7 := by omega
  have b7 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70845).toNat = 70844 + (2 * (y % 10000 / 100) + 1) := by omega
  rw [a7, b7, tab1 ht (by omega), pairs_lo _ (by omega)] at c7
  have a8 : ((sp : Int) + -28).toNat = sp - 34 + 6 := by omega
  have b8 : (((2 * (y % 10000 / 100) : Nat) : Int) + 70844).toNat = 70844 + 2 * (y % 10000 / 100) := by omega
  rw [a8, b8, tab1 ht (by omega), pairs_hi _ (by omega)] at c8
  rw [decB_10 (y := y) (by omega)]
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, d0a, d0b, rd1 c1, rd1 c2, rd1 c3, rd1 c4, rd1 c5, rd1 c6, rd1 c7, rd1 c8, List.cons.injEq]
  and_intros <;> first | trivial | (congr 1; omega)

end Services.Bootstrap.SymExec.Dec32
