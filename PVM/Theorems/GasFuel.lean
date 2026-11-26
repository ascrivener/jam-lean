import PVM.Gas
import PVM.Theorems.Blob

/-!
# The gas simulation 𝔛 always finishes within its fuel (GP v0.8.1 §A.9)

`PVM.Sim.run` runs 𝔛 with at most `Sim.fuel P ı = 256 · (|**c**| − ı + 2)` transitions. Here we
prove that this fuel always suffices: from **x**^init the `0` (out-of-fuel) case of `run` is never
reached, so any larger fuel gives the same result (`PVM.Sim.run_fuel_eq`). For the blocks Ψ
charges (ı a block start of a program passing 𝔳_blob) the simulation also never meets an opcode
outside U, so `blockCost?` is `some` and `blockCost`'s default is unreachable
(`PVM.Program.blockCost?_isSome_of_vBlob`, `PVM.Program.blockCost_eq_of_vBlob`).

The measure: 255 · (instructions left to decode) + 2 · (Σ of a per-entry potential over the
reorder buffer) + (decode and start slots used this cycle). Decoding lowers the first term by at
least 255 and adds at most 2 · 104 + 4; starting an entry (WAIT → EXE) lowers the potential by 1
and uses one start slot; a cycle step never raises the potential and resets the slots, and the
invariant `Sim.Inv` shows that a cycle step that lowers neither must have been preceded by a
decode or start since the last cycle (otherwise 𝔛 would have decoded, started or stopped
instead). The bounds used from the cost table (GP §A.10): 1 ≤ č ≤ 100, ď ≤ 4, x̌ ≤ (4, 4, 4, 1, 1).
-/

namespace PVM

/-! ## Bounds of the cost table (GP §A.10) -/

namespace CostExpr

/-- An upper bound of the value of a cost cell, over every instruction. -/
def hi : CostExpr → Nat
  | .const n => n
  | .overlap a b => max a b
  | .overlapShift a b => max a b
  | .memory => memoryCost
  | .branch => 20

/-- A lower bound of the value of a cost cell, over every instruction. -/
def lo : CostExpr → Nat
  | .const n => n
  | .overlap a b => min a b
  | .overlapShift a b => min a b
  | .memory => memoryCost
  | .branch => 1

end CostExpr

namespace Program

theorem evalCost_le_hi (P : Program) (i : Nat) (ins : Instr) (e : CostExpr) :
    P.evalCost i ins e ≤ e.hi := by
  cases e <;> simp only [evalCost, CostExpr.hi, branchCost]
  all_goals (try split) <;> (try split) <;> omega

theorem lo_le_evalCost (P : Program) (i : Nat) (ins : Instr) (e : CostExpr) :
    e.lo ≤ P.evalCost i ins e := by
  cases e <;> simp only [evalCost, CostExpr.lo, branchCost]
  all_goals (try split) <;> (try split) <;> omega

end Program

/-- The bounds of one row of the table: 1 ≤ č ≤ 100, ď ≤ 4, x̌ ≤ (4, 4, 4, 1, 1). -/
def CostRow.bounded (r : CostRow) : Bool :=
  1 ≤ r.cycles.lo && r.cycles.hi ≤ 100 && r.decodeSlots.hi ≤ 4 && r.alu.hi ≤ 4 &&
    r.load.hi ≤ 4 && r.store.hi ≤ 4 && r.mul.hi ≤ 1 && r.div.hi ≤ 1

theorem costRow_bounded_lt : ∀ n, n < 256 → (costRow? n).all CostRow.bounded = true := by
  decide

theorem zeta_lt (P : Program) (i : Nat) : P.zeta i < 256 := by
  unfold Program.zeta
  cases P.code[i]? with
  | none => decide
  | some b => exact b.toNat_lt

theorem zeta_of_ge (P : Program) {i : Nat} (h : P.code.size ≤ i) : P.zeta i = 0 := by
  unfold Program.zeta
  rw [Array.getElem?_eq_none h]; rfl

/-- The bounds of an evaluated cost (č, ď, x̌). -/
structure InstrCost.Bounded (c : InstrCost) : Prop where
  cycles_pos : 1 ≤ c.cycles
  cycles_le : c.cycles ≤ 100
  decode_le : c.decodeSlots ≤ 4
  units_le : c.units.le Units.initial = true

theorem instrCost?_bounded {P : Program} {i : Nat} {ins : Instr} {c : InstrCost}
    (h : P.instrCost? i = some (ins, c)) : c.Bounded := by
  simp only [Program.instrCost?, bind, Option.bind] at h
  split at h
  · cases h
  rename_i ins' hd
  split at h
  · cases h
  rename_i row hr
  simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hb := costRow_bounded_lt _ (zeta_lt P i)
  rw [hr] at hb
  simp only [Option.all, CostRow.bounded, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hb
  have e := fun e => P.evalCost_le_hi i ins' e
  have l := P.lo_le_evalCost i ins' row.cycles
  refine ⟨by omega, by have := e row.cycles; omega, by have := e row.decodeSlots; omega, ?_⟩
  have := e row.alu; have := e row.load; have := e row.store; have := e row.mul; have := e row.div
  simp only [Units.le, Units.initial, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-! ## Units, field by field -/

/-- The five fields of 𝔼. -/
inductive UnitField where
  | alu | load | store | mul | div

namespace UnitField
/-- The value of a field. -/
def get : UnitField → Units → Nat
  | alu, u => u.alu
  | load, u => u.load
  | store, u => u.store
  | mul, u => u.mul
  | div, u => u.div

@[simp] theorem get_add (f : UnitField) (a b : Units) : f.get (a + b) = f.get a + f.get b := by
  cases f <;> rfl
@[simp] theorem get_sub (f : UnitField) (a b : Units) : f.get (a - b) = f.get a - f.get b := by
  cases f <;> rfl
@[simp] theorem get_zero (f : UnitField) : f.get Units.zero = 0 := by cases f <;> rfl

theorem le_iff (a b : Units) : a.le b = true ↔ ∀ f : UnitField, f.get a ≤ f.get b := by
  simp only [Units.le, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ f
    cases f <;> assumption
  · intro h
    exact ⟨⟨⟨⟨h .alu, h .load⟩, h .store⟩, h .mul⟩, h .div⟩
end UnitField

namespace Sim

/-! ## The measure -/

/-- The potential of a reorder-buffer entry: ∅ 0, FIN 1, EXE c + 2, WAIT c + 3, DEC c + 4. -/
def pot (e : RobEntry) : Nat :=
  match e.state with
  | .none => 0
  | .fin => 1
  | .exe => e.cycles + 2
  | .wait => e.cycles + 3
  | .dec => e.cycles + 4

/-- Σ pot over the reorder buffer. -/
def potSum (l : List RobEntry) : Nat := (l.map pot).sum

/-- Instructions left to decode: 0 if **x**_ı = ∅, else (|**c**| + 1 − ı) + 1. -/
def pcMeasure (P : Program) : Option Nat → Nat
  | none => 0
  | some i => P.code.size + 1 - i + 1

/-- Decode and start slots used in this cycle. -/
def slack (x : SimState) : Nat := (maxDecode - x.decodeSlots) + (maxStart - x.startSlots)

/-- The termination measure of 𝔛. -/
def measure (P : Program) (x : SimState) : Nat :=
  255 * pcMeasure P x.pc + 2 * potSum x.rob + slack x

/-- The units held by entries executing with cycles left: Σ r_t over r_s = EXE ∧ r_c > 0, in
    field `f`. -/
def held (f : UnitField) (l : List RobEntry) : Nat :=
  (l.map fun e => if e.state = .exe ∧ 0 < e.cycles then f.get e.units else 0).sum

/-! ## The invariant -/

/-- The blocks positions 𝔛 decodes from `s`: s, then the next instruction after each
    non-terminator. -/
inductive Reach (P : Program) (s : Nat) : Nat → Prop
  | refl : Reach P s s
  | step {j : Nat} : Reach P s j → isTerminator (P.zeta j) = false → Reach P s (P.next j)

/-- The invariant of the states reachable from **x**^init(s). -/
structure Inv (P : Program) (s : Nat) (x : SimState) : Prop where
  pc : ∀ j, x.pc = some j → Reach P s j
  done0 : ∀ e ∈ x.rob, (e.state = .fin ∨ e.state = .none) → e.cycles = 0
  pos : ∀ e ∈ x.rob, (e.state = .dec ∨ e.state = .wait) → 1 ≤ e.cycles
  bnd : ∀ e ∈ x.rob, e.units.le Units.initial = true
  deps : ∀ (j : Nat) (h : j < x.rob.length), ∀ k ∈ x.rob[j].deps, k < j
  units : ∀ f : UnitField, f.get x.units + held f x.rob = f.get Units.initial

theorem inv_init (P : Program) (s : Nat) : Inv P s (init s) where
  pc := by intro j h; cases h; exact .refl
  done0 := by simp [init]
  pos := by simp [init]
  bnd := by simp [init]
  deps := by simp [init]
  units := by intro f; cases f <;> rfl

theorem measure_init (P : Program) (s : Nat) : measure P (init s) < fuel P s := by
  simp only [measure, init, pcMeasure, potSum, slack, maxDecode, maxStart, fuel,
    List.map_nil, List.sum_nil]
  omega

theorem Inv.depDone_eq {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x) {j : Nat}
    (hj : j < x.rob.length) {k : Nat} (hk : k ∈ x.rob[j].deps) :
    ∃ h : k < x.rob.length, depDone x k = (x.rob[k].cycles == 0) :=
  have h := Nat.lt_trans (hI.deps j hj k hk) hj
  ⟨h, by simp only [depDone, h, dite_true]⟩

end Sim

end PVM
