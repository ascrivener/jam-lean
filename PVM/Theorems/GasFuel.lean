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

/-- The bounds of one row of the table: č ≤ 100, ď ≤ 4, x̌ ≤ (4, 4, 4, 1, 1), and 1 ≤ č unless
    x̌ = 0 (only `move_reg` has č = 0). -/
def CostRow.bounded (r : CostRow) : Bool :=
  (1 ≤ r.cycles.lo || (r.alu.hi == 0 && r.load.hi == 0 && r.store.hi == 0 && r.mul.hi == 0 &&
    r.div.hi == 0)) && r.cycles.hi ≤ 100 && r.decodeSlots.hi ≤ 4 && r.alu.hi ≤ 4 &&
    r.load.hi ≤ 4 && r.store.hi ≤ 4 && r.mul.hi ≤ 1 && r.div.hi ≤ 1

set_option maxRecDepth 100000 in
theorem costRow_bounded_lt : ∀ n, n < 256 → (costRow? n).all CostRow.bounded = true := by
  decide

theorem zeta_lt (P : Program) (i : Nat) : P.zeta i < 256 := by
  unfold Program.zeta
  cases P.code[i]? with
  | none => decide
  | some b => exact b.toNat_lt

theorem zeta_of_ge (P : Program) {i : Nat} (h : P.code.size ≤ i) : P.zeta i = 0 := by
  simp [Program.zeta, h]

/-- The bounds of an evaluated cost (č, ď, x̌). -/
structure InstrCost.Bounded (c : InstrCost) : Prop where
  cycles_pos : 1 ≤ c.cycles ∨ ∀ f : UnitField, f.get c.units = 0
  cycles_le : c.cycles ≤ 100
  decode_le : c.decodeSlots ≤ 4
  units_le : c.units.le Units.initial = true

theorem instrCost?_bounded {P : Program} {i : Nat} {ins : Instr} {c : InstrCost}
    (h : P.instrCost? i = some (ins, c)) : c.Bounded := by
  unfold Program.instrCost? at h
  cases hd : P.decode i with
  | none => simp [hd] at h
  | some ins' =>
  cases hr : costRow? (P.zeta i) with
  | none => simp [hd, hr] at h
  | some row =>
  simp only [hd, hr, bind, Option.bind, pure, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hb := costRow_bounded_lt _ (zeta_lt P i)
  rw [hr] at hb
  simp only [Option.all, CostRow.bounded, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hb
  have e := fun e => P.evalCost_le_hi i ins' e
  have l := P.lo_le_evalCost i ins' row.cycles
  have := e row.alu; have := e row.load; have := e row.store; have := e row.mul; have := e row.div
  have := e row.cycles; have := e row.decodeSlots
  refine ⟨?_, by dsimp only; omega, by dsimp only; omega, ?_⟩
  · rcases h1 with h1 | ⟨⟨⟨⟨ha, hl⟩, hs⟩, hm⟩, hv⟩
    · left; dsimp only; omega
    · right; intro f; cases f <;> simp only [UnitField.get] <;> omega
  · rw [UnitField.le_iff]; intro f
    cases f <;> simp only [UnitField.get, Units.initial] <;> omega

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
  pos : ∀ e ∈ x.rob, (e.state = .dec ∨ e.state = .wait) →
    1 ≤ e.cycles ∨ ∀ f : UnitField, f.get e.units = 0
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

/-! ## List lemmas -/

theorem sum_map_modify {α : Type} (h : α → Nat) (f : α → α) :
    ∀ (l : List α) (n : Nat) (hn : n < l.length),
      ((l.modify n f).map h).sum + h l[n] = (l.map h).sum + h (f l[n])
  | [], _, hn => absurd hn (Nat.not_lt_zero _)
  | a :: l, 0, _ => by
    simp only [List.modify_zero_cons, List.map_cons, List.sum_cons, List.getElem_cons_zero]; omega
  | a :: l, n + 1, hn => by
    have := sum_map_modify h f l n (by simp at hn; omega)
    simp only [List.modify_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ]; omega

theorem mem_modify {α : Type} {f : α → α} {l : List α} {n : Nat} {e : α} (h : e ∈ l.modify n f) :
    e ∈ l ∨ ∃ hn : n < l.length, e = f l[n] := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
  rw [List.getElem_modify]
  have hj' : j < l.length := by simpa using hj
  split
  · rename_i hnj; subst hnj; exact .inr ⟨hj', rfl⟩
  · exact .inl (List.getElem_mem _)

theorem foldl_live_none : ∀ (l : List RobEntry) (n : Nat), (∀ e ∈ l, e.state = .none) →
    l.foldl (fun n e => if e.state != .none then n + 1 else n) n = n
  | [], _, _ => rfl
  | e :: l, n, h => by
    rw [List.foldl_cons, if_neg (by simp [h e (by simp)])]
    exact foldl_live_none l n fun e he => h e (by simp [he])

/-! ## The cycle step 𝔛''' entry by entry -/

/-- 𝔛''' on one entry, given whether it is retired. -/
def cyc (e : RobEntry) (r : Bool) : RobEntry :=
  { e with
    state :=
      if r then .none
      else if e.state == .dec then .wait
      else if e.state == .exe && e.cycles == 0 then .fin
      else e.state
    cycles := if e.state == .exe && e.cycles > 0 then e.cycles - 1 else e.cycles }

theorem cycleStep_rob (x : SimState) :
    (cycleStep x).rob = x.rob.zipWith cyc (retiredPrefix x.rob true) :=
  rfl

/-- The units freed in field `f`: Σ r_t over r_s = EXE ∧ r_c = 1. -/
def freed (f : UnitField) (l : List RobEntry) : Nat :=
  (l.map fun e => if e.state = .exe ∧ e.cycles = 1 then f.get e.units else 0).sum

theorem freed_foldl (f : UnitField) : ∀ (l : List RobEntry) (z : Units),
    f.get (l.foldl (fun u e => if e.state == .exe && e.cycles == 1 then u + e.units else u) z) =
      f.get z + freed f l
  | [], z => by simp [freed]
  | e :: l, z => by
    rw [List.foldl_cons, freed_foldl f l]
    simp only [freed, List.map_cons, List.sum_cons]
    by_cases h : e.state = .exe ∧ e.cycles = 1
    · rw [if_pos (by simp [h.1, h.2]), if_pos h, UnitField.get_add]; omega
    · rw [if_neg (by simpa using h), if_neg h]; omega

/-- Facts about one entry under 𝔛''', when a retired entry is FIN or ∅. -/
theorem cyc_pot_le (e : RobEntry) (r : Bool) (hr : r = true → e.state = .fin ∨ e.state = .none) :
    pot (cyc e r) ≤ pot e ∧
      ((e.state = .dec ∨ e.state = .exe ∨ (r = true ∧ e.state = .fin)) →
        pot (cyc e r) < pot e) := by
  rcases e with ⟨st, c, d, rg, u⟩
  cases st <;> cases r <;> by_cases hc : c = 0 <;> simp_all [cyc, pot, Nat.pos_iff_ne_zero] <;> omega

theorem cyc_held (f : UnitField) (e : RobEntry) (r : Bool)
    (hr : r = true → e.state = .fin ∨ e.state = .none) :
    (if (cyc e r).state = .exe ∧ 0 < (cyc e r).cycles then f.get (cyc e r).units else 0) +
      (if e.state = .exe ∧ e.cycles = 1 then f.get e.units else 0) =
    (if e.state = .exe ∧ 0 < e.cycles then f.get e.units else 0) := by
  rcases e with ⟨st, c, d, rg, u⟩
  cases st <;> cases r <;> by_cases hc : c = 0 <;> by_cases hc1 : c = 1 <;>
    simp_all [cyc, Nat.pos_iff_ne_zero] <;> (repeat' split) <;> omega

theorem cyc_inv (e : RobEntry) (r : Bool) (hr : r = true → e.state = .fin ∨ e.state = .none)
    (h0 : (e.state = .fin ∨ e.state = .none) → e.cycles = 0)
    (hp : (e.state = .dec ∨ e.state = .wait) → 1 ≤ e.cycles ∨ ∀ f : UnitField, f.get e.units = 0) :
    ((cyc e r).state = .fin ∨ (cyc e r).state = .none → (cyc e r).cycles = 0) ∧
    ((cyc e r).state = .dec ∨ (cyc e r).state = .wait →
      1 ≤ (cyc e r).cycles ∨ ∀ f : UnitField, f.get (cyc e r).units = 0) := by
  rcases e with ⟨st, c, d, rg, u⟩
  cases st <;> cases r <;> by_cases hc : c = 0 <;> simp_all [cyc] <;> omega

theorem retiredPrefix_length :
    ∀ (l : List RobEntry) (ok : Bool), (retiredPrefix l ok).length = l.length
  | [], _ => rfl
  | _ :: l, _ => by simp [retiredPrefix, retiredPrefix_length l]

theorem retired_cons (e : RobEntry) (ok : Bool) :
    (ok && (e.state == .fin || e.state == .none)) = true → e.state = .fin ∨ e.state = .none := by
  intro h; simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h; exact h.2

theorem potSum_cyc : ∀ (l : List RobEntry) (ok : Bool),
    potSum (l.zipWith cyc (retiredPrefix l ok)) ≤ potSum l ∧
    ((∃ e ∈ l, e.state = .dec ∨ e.state = .exe) →
      potSum (l.zipWith cyc (retiredPrefix l ok)) < potSum l)
  | [], _ => by simp [potSum, retiredPrefix]
  | e :: l, ok => by
    have ih := potSum_cyc l (ok && (e.state == .fin || e.state == .none))
    have he := cyc_pot_le e _ (retired_cons e ok)
    simp only [retiredPrefix, List.zipWith_cons_cons, potSum, List.map_cons, List.sum_cons] at ih ⊢
    refine ⟨by omega, ?_⟩
    rintro ⟨e', he', hs⟩
    rcases List.mem_cons.1 he' with rfl | hl
    · have := he.2 (by rcases hs with h | h <;> simp [h]); omega
    · have := ih.2 ⟨e', hl, hs⟩; omega

theorem potSum_cyc_fin : ∀ (l : List RobEntry), (∀ e ∈ l, e.state = .fin ∨ e.state = .none) →
    (∃ e ∈ l, e.state = .fin) → potSum (l.zipWith cyc (retiredPrefix l true)) < potSum l
  | [], _, ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | e :: l, hall, ⟨e', he', hf⟩ => by
    have hok : (true && (e.state == .fin || e.state == .none)) = true := by
      rcases hall e (by simp) with h | h <;> simp [h]
    have hle := (potSum_cyc l true).1
    simp only [retiredPrefix, hok, List.zipWith_cons_cons, potSum, List.map_cons,
      List.sum_cons] at hle ⊢
    rcases hall e (by simp) with h | h
    · have := (cyc_pot_le e true (fun _ => .inl h)).2 (.inr (.inr ⟨rfl, h⟩)); omega
    · rcases List.mem_cons.1 he' with rfl | hl
      · rw [h] at hf; cases hf
      · have := potSum_cyc_fin l (fun e he => hall e (by simp [he])) ⟨e', hl, hf⟩
        have h1 : pot (cyc e true) = 0 := by simp [cyc, pot]
        have h2 : pot e = 0 := by simp [pot, h]
        simp only [potSum] at this; omega

theorem held_cyc (f : UnitField) : ∀ (l : List RobEntry) (ok : Bool),
    held f (l.zipWith cyc (retiredPrefix l ok)) + freed f l = held f l
  | [], _ => by simp [held, freed, retiredPrefix]
  | e :: l, ok => by
    have ih := held_cyc f l (ok && (e.state == .fin || e.state == .none))
    have he := cyc_held f e _ (retired_cons e ok)
    simp only [retiredPrefix, List.zipWith_cons_cons, held, freed, List.map_cons,
      List.sum_cons] at ih he ⊢
    omega

theorem mem_cyc : ∀ (l : List RobEntry) (ok : Bool) (e' : RobEntry),
    e' ∈ l.zipWith cyc (retiredPrefix l ok) →
      ∃ e ∈ l, ∃ r : Bool, (r = true → e.state = .fin ∨ e.state = .none) ∧ e' = cyc e r
  | [], _, _, h => by simp [retiredPrefix] at h
  | e :: l, ok, e', h => by
    simp only [retiredPrefix, List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨e, by simp, _, retired_cons e ok, rfl⟩
    · obtain ⟨e₁, h₁, r, hr, rfl⟩ := mem_cyc l _ e' h
      exact ⟨e₁, by simp [h₁], r, hr, rfl⟩

/-! ## Decoding keeps the invariant and lowers the measure -/

theorem held_map_regs (f : UnitField) (l : List RobEntry) (g : RobEntry → RegSet) :
    held f (l.map fun e => { e with regs := g e }) = held f l := by
  simp [held, Function.comp_def]

theorem potSum_map_regs (l : List RobEntry) (g : RobEntry → RegSet) :
    potSum (l.map fun e => { e with regs := g e }) = potSum l := by
  simp only [potSum, List.map_map, Function.comp_def]
  rfl

theorem Inv.map_regs {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x)
    (g : RobEntry → RegSet) (pc : Option Nat) (hpc : ∀ j, pc = some j → Reach P s j) (d : Nat) :
    Inv P s { x with pc := pc, decodeSlots := d, rob := x.rob.map fun e => { e with regs := g e } } where
  pc := hpc
  done0 := by
    intro e he; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he; exact hI.done0 a ha
  pos := by
    intro e he; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he; exact hI.pos a ha
  bnd := by
    intro e he; obtain ⟨a, ha, rfl⟩ := List.mem_map.1 he; exact hI.bnd a ha
  deps := by
    intro j hj k hk
    simp only [List.getElem_map] at hk
    exact hI.deps j (by simpa using hj) k hk
  units := by intro f; rw [held_map_regs]; exact hI.units f

theorem decodeMove_spec {P : Program} {s : Nat} {x : SimState} {i : Nat} {ins : Instr}
    (hI : Inv P s x) (hpc : x.pc = some i) (hi : i < P.code.size) (hz : P.zeta i = moveRegOpcode) :
    Inv P s (decodeMove P x i ins) ∧ measure P (decodeMove P x i ins) < measure P x := by
  refine ⟨hI.map_regs _ _ ?_ _, ?_⟩
  · intro j hj; cases hj
    exact .step (hI.pc i hpc) (by rw [hz]; decide)
  · have hn : i < P.next i := by unfold Program.next; omega
    simp only [measure, decodeMove, pcMeasure, hpc, slack, potSum_map_regs]
    omega

theorem mem_zipIdx_filter_lt {l : List RobEntry} {p : RobEntry × Nat → Bool} {k : Nat}
    (hk : k ∈ (l.zipIdx.filter p).map (·.2)) : k < l.length := by
  obtain ⟨⟨e, k'⟩, hm, rfl⟩ := List.mem_map.1 hk
  obtain ⟨_, h2, _⟩ := List.mem_zipIdx (List.mem_filter.1 hm).1
  simpa using h2

theorem decodeInstr_spec {P : Program} {s : Nat} {x : SimState} {i : Nat} {ins : Instr}
    {c : InstrCost} (hI : Inv P s x) (hpc : x.pc = some i) (hc : P.instrCost? i = some (ins, c)) :
    Inv P s (decodeInstr P x i ins c) ∧ measure P (decodeInstr P x i ins c) < measure P x := by
  have hb := instrCost?_bounded hc
  have hb1 := hb.cycles_le; have hb2 := hb.decode_le
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j hj
    simp only [decodeInstr] at hj
    split at hj
    · cases hj
    · rename_i ht
      cases hj; exact .step (hI.pc i hpc) (by simpa using ht)
  · intro e he
    simp only [decodeInstr, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨e, he, rfl⟩ | rfl
    · exact hI.done0 e he
    · simp
  · intro e he
    simp only [decodeInstr, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨e, he, rfl⟩ | rfl
    · exact hI.pos e he
    · intro _; exact hb.cycles_pos
  · intro e he
    simp only [decodeInstr, List.mem_append, List.mem_map, List.mem_singleton] at he
    rcases he with ⟨e, he, rfl⟩ | rfl
    · exact hI.bnd e he
    · exact hb.units_le
  · intro j hj k hk
    simp only [decodeInstr, List.length_append, List.length_map, List.length_singleton] at hj hk
    by_cases hlt : j < x.rob.length
    · rw [List.getElem_append_left (by simpa using hlt), List.getElem_map] at hk
      exact hI.deps j hlt k hk
    · have hj' : j = x.rob.length := by omega
      subst hj'
      rw [List.getElem_append_right (by simp)] at hk
      simp only [List.length_map, Nat.sub_self, List.getElem_singleton] at hk
      exact mem_zipIdx_filter_lt hk
  · intro f
    have := hI.units f
    simp only [decodeInstr, held, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.map_map, Function.comp_def] at this ⊢
    simp at this ⊢; omega
  · have hn : i < P.next i := by unfold Program.next; omega
    have hpot : potSum (decodeInstr P x i ins c).rob = potSum x.rob + (c.cycles + 4) := by
      simp only [decodeInstr, potSum, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.map_map, Function.comp_def]
      simp [pot]; rfl
    have hpcm : pcMeasure P (decodeInstr P x i ins c).pc + 1 ≤ pcMeasure P x.pc := by
      by_cases ht : isTerminator (P.zeta i) = true
      · simp [decodeInstr, ht, pcMeasure, hpc]
      · have : i < P.code.size := Nat.lt_of_not_le fun hge => by
          rw [zeta_of_ge P hge] at ht; exact ht rfl
        simp only [decodeInstr, ht, hpc, pcMeasure]; simp only [if_false, Bool.false_eq_true]
        omega
    have hsl : slack (decodeInstr P x i ins c) ≤ slack x + 4 := by
      simp only [slack, decodeInstr]; omega
    simp only [measure]
    omega

end Sim

end PVM
