import PVM.Gas
import PVM.Theorems.Blob

/-!
# The gas simulation $\mathfrak{X}$ always finishes within its fuel (GP v0.8.1 §A.9)

`PVM.Sim.run` runs $\mathfrak{X}$ with at most `Sim.fuel P ı` $= 256 \cdot (|\mathbf{c}| - \imath + 2)$ transitions. Here we
prove that this fuel always suffices: from $\mathbf{x}^{\text{init}}$ the `0` (out-of-fuel) case of `run` is never
reached, so any larger fuel gives the same result (`PVM.Sim.run_fuel_eq`). For the blocks $\Psi$
charges ($\imath$ a block start of a program passing $\mathfrak{v}_{\text{blob}}$) the simulation also never meets an opcode
outside U, so `blockCost?` is `some` and `blockCost`'s default is unreachable
(`PVM.Program.blockCost?_isSome_of_vBlob`; for a decoded blob, `PVM.Program.blockCost_eq_of_deblob`).

The measure: 255 · (instructions left to decode) + 2 · ($\Sigma$ of a per-entry potential over the
reorder buffer) + (decode and start slots used this cycle). Decoding lowers the first term by at
least 255 and adds at most $2 \cdot 104 + 4$; starting an entry (WAIT → EXE) lowers the potential by 1
and uses one start slot; a cycle step never raises the potential and resets the slots, and the
invariant `Sim.Inv` shows that a cycle step that lowers neither must have been preceded by a
decode or start since the last cycle (otherwise $\mathfrak{X}$ would have decoded, started or stopped
instead). The bounds used from the cost table (GP §A.10), checked by `decide` over all 256
octets: $\check{c} \le 100$, $\check{d} \le 4$, $\check{x} \le (4, 4, 4, 1, 1)$, and $\check{c} \ge 1$ unless $\check{x} = 0$ (only `move_reg` has $\check{c} = 0$).
-/

namespace PVM

/-! ## Units, field by field -/

/-- The five fields of $\mathbb{E}$. -/
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

/-- The bounds of one row of the table: $\check{c} \le 100$, $\check{d} \le 4$, $\check{x} \le (4, 4, 4, 1, 1)$, and $1 \le \check{c}$ unless
    $\check{x} = 0$ (only `move_reg` has $\check{c} = 0$). -/
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

/-- The bounds of an evaluated cost $(\check{c}, \check{d}, \check{x})$. -/
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

/-- The potential of a reorder-buffer entry: $\emptyset$ 0, FIN 1, EXE c + 2, WAIT c + 3, DEC c + 4. -/
def pot (e : RobEntry) : Nat :=
  match e.state with
  | .none => 0
  | .fin => 1
  | .exe => e.cycles + 2
  | .wait => e.cycles + 3
  | .dec => e.cycles + 4

/-- $\Sigma$ pot over the reorder buffer. -/
def potSum (l : List RobEntry) : Nat := (l.map pot).sum

/-- Instructions left to decode: 0 if $\mathbf{x}_{\imath} = \emptyset$, else $(|\mathbf{c}| + 1 - \imath) + 1$. -/
def pcMeasure (P : Program) : Option Nat → Nat
  | none => 0
  | some i => P.code.size + 1 - i + 1

/-- Decode and start slots used in this cycle. -/
def slack (x : SimState) : Nat := (maxDecode - x.decodeSlots) + (maxStart - x.startSlots)

/-- The termination measure of $\mathfrak{X}$. -/
def measure (P : Program) (x : SimState) : Nat :=
  255 * pcMeasure P x.pc + 2 * potSum x.rob + slack x

/-- The units held by entries executing with cycles left: $\Sigma\, r_t$ over $r_s = \text{EXE} \wedge r_c > 0$, in
    field `f`. -/
def held (f : UnitField) (l : List RobEntry) : Nat :=
  (l.map fun e => if e.state = .exe ∧ 0 < e.cycles then f.get e.units else 0).sum

/-! ## The invariant -/

/-- The blocks positions $\mathfrak{X}$ decodes from `s`: s, then the next instruction after each
    non-terminator. -/
inductive Reach (P : Program) (s : Nat) : Nat → Prop
  | refl : Reach P s s
  | step {j : Nat} : Reach P s j → isTerminator (P.zeta j) = false → Reach P s (P.next j)

/-- The invariant of the states reachable from $\mathbf{x}^{\text{init}}(s)$. -/
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

/-! ## The cycle step $\mathfrak{X}'''$ entry by entry -/

/-- $\mathfrak{X}'''$ on one entry, given whether it is retired. -/
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

/-- The units freed in field `f`: $\Sigma\, r_t$ over $r_s = \text{EXE} \wedge r_c = 1$. -/
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

/-- Facts about one entry under $\mathfrak{X}'''$, when a retired entry is FIN or $\emptyset$. -/
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

/-! ## Starting an entry keeps the invariant and lowers the measure -/

theorem readyToStart_spec {x : SimState} {n : Fin x.rob.length} (h : readyToStart x = some n) :
    x.rob[n].state = .wait ∧ x.rob[n].units.le x.units = true ∧
      x.rob[n].deps.all (depDone x) = true := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem startStep_spec {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x)
    {n : Fin x.rob.length} (h : readyToStart x = some n) :
    Inv P s (startStep x n) ∧ measure P (startStep x n) < measure P x := by
  obtain ⟨hw, hle, -⟩ := readyToStart_spec h
  have hmem : x.rob[n] ∈ x.rob := List.getElem_mem _
  have hpos := hI.pos _ hmem (.inr hw)
  refine ⟨⟨hI.pc, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he hs
    rcases mem_modify he with he | ⟨_, rfl⟩
    · exact hI.done0 e he hs
    · simp at hs
  · intro e he hs
    rcases mem_modify he with he | ⟨_, rfl⟩
    · exact hI.pos e he hs
    · simp at hs
  · intro e he
    rcases mem_modify he with he | ⟨_, rfl⟩
    · exact hI.bnd e he
    · exact hI.bnd x.rob[n] hmem
  · intro j hj k hk
    simp only [startStep, List.getElem_modify] at hk
    have hj' : j < x.rob.length := by simpa [startStep] using hj
    split at hk
    · exact hI.deps j hj' k hk
    · exact hI.deps j hj' k hk
  · intro f
    have hu := hI.units f
    have hs := sum_map_modify (fun e => if e.state = .exe ∧ 0 < e.cycles then f.get e.units else 0)
      (fun e => { e with state := .exe }) x.rob n n.isLt
    have hl := (UnitField.le_iff _ _).1 hle f
    simp only [Fin.getElem_fin] at hw hs hl hpos
    simp only [startStep, held, UnitField.get_sub, Fin.getElem_fin] at hu hs ⊢
    simp only [hw, reduceCtorEq, false_and, if_false, Nat.add_zero] at hs
    rcases hpos with hc | hz
    · rw [if_pos ⟨trivial, hc⟩] at hs; omega
    · rw [hz f] at hs hl ⊢; split at hs <;> omega
  · have hs := sum_map_modify pot (fun e => { e with state := .exe }) x.rob n n.isLt
    simp only [Fin.getElem_fin] at hw hs
    simp only [pot, hw] at hs
    simp only [measure, startStep, slack, potSum, Fin.getElem_fin]
    omega

/-! ## The cycle step keeps the invariant, and lowers the measure when $\mathfrak{X}$ takes it -/

theorem cycleStep_spec {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x)
    (hprog : potSum (cycleStep x).rob < potSum x.rob ∨ 0 < slack x) :
    Inv P s (cycleStep x) ∧ measure P (cycleStep x) < measure P x := by
  refine ⟨⟨hI.pc, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rw [cycleStep_rob] at he
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_cyc _ _ _ he
    exact (cyc_inv a r hr (hI.done0 a ha) (hI.pos a ha)).1
  · intro e he
    rw [cycleStep_rob] at he
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_cyc _ _ _ he
    exact (cyc_inv a r hr (hI.done0 a ha) (hI.pos a ha)).2
  · intro e he
    rw [cycleStep_rob] at he
    obtain ⟨a, ha, r, hr, rfl⟩ := mem_cyc _ _ _ he
    exact hI.bnd a ha
  · intro j hj k hk
    have hj' : j < x.rob.length := by
      simp only [cycleStep_rob, List.length_zipWith, retiredPrefix_length] at hj; omega
    simp only [cycleStep_rob, List.getElem_zipWith] at hk
    exact hI.deps j hj' k hk
  · intro f
    have hu := hI.units f
    have hc := held_cyc f x.rob true
    have hf := freed_foldl f x.rob Units.zero
    rw [← cycleStep_rob] at hc
    simp only [UnitField.get_zero, Nat.zero_add] at hf
    simp only [cycleStep, UnitField.get_add] at hf hc ⊢
    omega
  · have hle := (potSum_cyc x.rob true).1
    rw [← cycleStep_rob] at hle
    simp only [measure, slack, cycleStep, maxDecode, maxStart] at hprog hle ⊢
    omega

theorem held_zero (f : UnitField) : ∀ (l : List RobEntry), (∀ e ∈ l, e.state ≠ .exe) → held f l = 0
  | [], _ => rfl
  | e :: l, h => by
    have := held_zero f l fun e he => h e (by simp [he])
    simp only [held, List.map_cons, List.sum_cons] at this ⊢
    rw [if_neg (fun hc => h e (by simp) hc.1)]; omega

theorem exists_first_wait (x : SimState) :
    ∀ j (hj : j < x.rob.length), x.rob[j].state = .wait →
      ∃ m, ∃ hm : m < x.rob.length, x.rob[m].state = .wait ∧
        ∀ k (hk : k < m), x.rob[k].state ≠ .wait := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj hw
    by_cases h : ∃ k, ∃ hk : k < j, x.rob[k].state = .wait
    · obtain ⟨k, hk, hkw⟩ := h
      exact ih k hk (by omega) hkw
    · refine ⟨j, hj, hw, fun k hk hkw => h ⟨k, hk, hkw⟩⟩

theorem readyToStart_ne_none {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x)
    (hnde : ∀ e ∈ x.rob, e.state ≠ .dec ∧ e.state ≠ .exe)
    {j : Nat} (hj : j < x.rob.length) (hw : x.rob[j].state = .wait) : readyToStart x ≠ none := by
  obtain ⟨m, hm, hmw, hmin⟩ := exists_first_wait x j hj hw
  intro hnone
  rw [readyToStart, List.find?_eq_none] at hnone
  apply hnone ⟨m, hm⟩ (List.mem_finRange _)
  simp only [Fin.getElem_fin, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨hmw, ?_⟩, ?_⟩
  · rw [UnitField.le_iff]; intro f
    have hu := hI.units f
    rw [held_zero f x.rob fun e he => (hnde e he).2, Nat.add_zero] at hu
    rw [hu]
    exact (UnitField.le_iff _ _).1 (hI.bnd _ (List.getElem_mem _)) f
  · intro k hk
    obtain ⟨hk', hd⟩ := hI.depDone_eq hm hk
    rw [hd]
    have hkm := hI.deps m hm k hk
    have hne := hmin k hkm
    have hmem : x.rob[k] ∈ x.rob := List.getElem_mem _
    have h0 : x.rob[k].state = .fin ∨ x.rob[k].state = .none := by
      have := hnde _ hmem
      cases h : x.rob[k].state <;> simp_all
    simp [hI.done0 _ hmem h0]

theorem cycle_progress {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x)
    (hdec : ∀ i, x.pc = some i → ∃ ins c, P.instrCost? i = some (ins, c) ∧
      ¬(c.decodeSlots ≤ x.decodeSlots ∧ live x < 32))
    (hstart : ∀ n, readyToStart x = some n → x.startSlots = 0)
    (hstop : ¬(x.pc = none ∧ live x = 0)) :
    potSum (cycleStep x).rob < potSum x.rob ∨ 0 < slack x := by
  by_cases hs : 0 < slack x
  · exact .inr hs
  left
  have hs' : maxDecode ≤ x.decodeSlots ∧ maxStart ≤ x.startSlots := by
    simp only [slack] at hs; omega
  simp only [maxDecode, maxStart] at hs'
  rw [cycleStep_rob]
  by_cases ha : ∃ e ∈ x.rob, e.state = .dec ∨ e.state = .exe
  · exact (potSum_cyc x.rob true).2 ha
  have hnde : ∀ e ∈ x.rob, e.state ≠ .dec ∧ e.state ≠ .exe :=
    fun e he => ⟨fun h => ha ⟨e, he, .inl h⟩, fun h => ha ⟨e, he, .inr h⟩⟩
  by_cases hw : ∃ e ∈ x.rob, e.state = .wait
  · obtain ⟨e, he, hew⟩ := hw
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 he
    cases hr : readyToStart x with
    | none => exact absurd hr (readyToStart_ne_none hI hnde hj hew)
    | some n => have := hstart n hr; omega
  have hfn : ∀ e ∈ x.rob, e.state = .fin ∨ e.state = .none := by
    intro e he
    have := hnde e he
    cases h : e.state <;> simp_all
  by_cases hf : ∃ e ∈ x.rob, e.state = .fin
  · exact potSum_cyc_fin x.rob hfn hf
  have hnone : ∀ e ∈ x.rob, e.state = .none := fun e he =>
    (hfn e he).resolve_left fun h => hf ⟨e, he, h⟩
  have hl : live x = 0 := foldl_live_none x.rob 0 hnone
  cases hpc : x.pc with
  | none => exact absurd ⟨hpc, hl⟩ hstop
  | some i =>
    obtain ⟨ins, c, hc, hn⟩ := hdec i hpc
    have := (instrCost?_bounded hc).decode_le
    exact absurd ⟨by omega, by omega⟩ hn

/-! ## The transition -/

theorem transition_inl {P : Program} {x x' : SimState} (h : transition P x = some (.inl x')) :
    (∃ i ins c, x.pc = some i ∧ P.instrCost? i = some (ins, c) ∧ x' = decodeStep P x i ins c) ∨
    (∃ n, readyToStart x = some n ∧ x' = startStep x n) ∨
    (x' = cycleStep x ∧
      (∀ i, x.pc = some i → ∃ ins c, P.instrCost? i = some (ins, c) ∧
        ¬(c.decodeSlots ≤ x.decodeSlots ∧ live x < 32)) ∧
      (∀ n, readyToStart x = some n → x.startSlots = 0) ∧ ¬(x.pc = none ∧ live x = 0)) := by
  -- the stages after decoding, once decoding is ruled out
  have tail : (hdec : ∀ i, x.pc = some i → ∃ ins c, P.instrCost? i = some (ins, c) ∧
        ¬(c.decodeSlots ≤ x.decodeSlots ∧ live x < 32)) →
      (∀ n, readyToStart x = some n → 0 < x.startSlots → transition P x = some (.inl (startStep x n))) →
      ((∀ n, readyToStart x = some n → x.startSlots = 0) →
        transition P x = if x.pc.isNone && live x == 0 then some (.inr x) else some (.inl (cycleStep x))) →
      (∃ n, readyToStart x = some n ∧ x' = startStep x n) ∨
      (x' = cycleStep x ∧
        (∀ i, x.pc = some i → ∃ ins c, P.instrCost? i = some (ins, c) ∧
          ¬(c.decodeSlots ≤ x.decodeSlots ∧ live x < 32)) ∧
        (∀ n, readyToStart x = some n → x.startSlots = 0) ∧ ¬(x.pc = none ∧ live x = 0)) := by
    intro hdec hS hC
    by_cases hr : ∃ n, readyToStart x = some n ∧ 0 < x.startSlots
    · obtain ⟨n, hn, hs⟩ := hr
      rw [hS n hn hs] at h
      simp only [Option.some.injEq, Sum.inl.injEq] at h
      exact .inl ⟨n, hn, h.symm⟩
    · have hst : ∀ n, readyToStart x = some n → x.startSlots = 0 :=
        fun n hn => Nat.eq_zero_of_not_pos fun hs => hr ⟨n, hn, hs⟩
      rw [hC hst] at h
      split at h
      · simp at h
      · rename_i hc
        simp only [Option.some.injEq, Sum.inl.injEq] at h
        refine .inr ⟨h.symm, hdec, hst, fun ⟨h1, h2⟩ => hc ?_⟩
        simp [h1, h2]
  by_cases hn : x.pc = none
  · refine .inr (tail (fun i hi => by simp [hn] at hi) ?_ ?_)
    · intro n hr hs; simp [transition, hn, hr, hs, pure]
    · intro hst
      cases hr : readyToStart x with
      | none => simp [transition, hn, hr, pure]
      | some n => simp [transition, hn, hr, hst n hr, pure]
  · obtain ⟨i, hpc⟩ := Option.ne_none_iff_exists'.1 hn
    cases hc : P.instrCost? i with
    | none => simp [transition, hpc, hc, bind, Option.bind] at h
    | some ic =>
      obtain ⟨ins, c⟩ := ic
      by_cases hd : c.decodeSlots ≤ x.decodeSlots ∧ live x < 32
      · simp [transition, hpc, hc, hd, bind, Option.bind, pure] at h
        exact .inl ⟨i, ins, c, hpc, hc, h.symm⟩
      · have hd' : ¬(c.decodeSlots ≤ x.decodeSlots ∧ live x < 32) := hd
        refine .inr (tail ?_ ?_ ?_)
        · intro j hj; rw [hpc] at hj; cases hj; exact ⟨ins, c, hc, hd'⟩
        · intro n hr hs
          simp only [Classical.not_and_iff_not_or_not, Nat.not_le, Nat.not_lt] at hd
          rcases hd with hd | hd <;>
            simp [transition, hpc, hc, bind, Option.bind, pure, hr, hs, Nat.not_le.2 hd,
              Nat.not_lt.2 hd]
        · intro hst
          simp only [Classical.not_and_iff_not_or_not, Nat.not_le, Nat.not_lt] at hd
          cases hr : readyToStart x <;>
            rcases hd with hd | hd <;>
            simp [transition, hpc, hc, bind, Option.bind, pure, hr, Nat.not_le.2 hd,
              Nat.not_lt.2 hd, hst]

theorem transition_spec {P : Program} {s : Nat} {x x' : SimState} (hI : Inv P s x)
    (h : transition P x = some (.inl x')) : Inv P s x' ∧ measure P x' < measure P x := by
  rcases transition_inl h with ⟨i, ins, c, hpc, hc, rfl⟩ | ⟨n, hn, rfl⟩ | ⟨rfl, hdec, hst, hstop⟩
  · unfold decodeStep
    split
    · rename_i hm
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
      exact decodeMove_spec hI hpc hm.1 hm.2
    · exact decodeInstr_spec hI hpc hc
  · exact startStep_spec hI hn
  · exact cycleStep_spec hI (cycle_progress hI hdec hst hstop)

/-- The transitions reachable from an invariant state are all defined when every instruction $\mathfrak{X}$
    may decode is in U. -/
theorem transition_isSome {P : Program} {s : Nat} {x : SimState} (hI : Inv P s x)
    (hU : ∀ j, Reach P s j → (P.instrCost? j).isSome) : (transition P x).isSome := by
  unfold transition
  cases hpc : x.pc with
  | none =>
    simp only
    split
    · split <;> (try split) <;> simp [pure]
    · split <;> simp [pure]
  | some i =>
    obtain ⟨⟨ins, c⟩, hc⟩ := Option.isSome_iff_exists.1 (hU i (hI.pc i hpc))
    simp only [hc, bind, Option.bind]
    split
    · simp [pure]
    · split
      · split <;> (try split) <;> simp [pure]
      · split <;> simp [pure]

/-! ## The fuel suffices -/

/-- Beyond the measure, the fuel does not change the result of `run`. -/
theorem run_stable (P : Program) (s : Nat) :
    ∀ (f : Nat) (x : SimState), Inv P s x → measure P x < f →
      ∀ f', f ≤ f' → run P f' x = run P f x
  | 0, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, x, hI, hm, f', hf => by
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := ⟨f' - 1, by omega⟩
    simp only [run]
    cases ht : transition P x with
    | none => rfl
    | some r =>
      cases r with
      | inr y => rfl
      | inl y =>
        have ⟨hI', hm'⟩ := transition_spec hI ht
        exact run_stable P s f y hI' (by omega) f'' (by omega)

/-- `run` with more fuel than the measure is never out of fuel: it is `some` whenever every
    transition is defined. -/
theorem run_isSome (P : Program) (s : Nat) (hU : ∀ j, Reach P s j → (P.instrCost? j).isSome) :
    ∀ (f : Nat) (x : SimState), Inv P s x → measure P x < f → (run P f x).isSome
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | f + 1, x, hI, hm => by
    simp only [run]
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (transition_isSome hI hU)
    rw [hr]
    cases r with
    | inr y => rfl
    | inl y =>
      have ⟨hI', hm'⟩ := transition_spec hI hr
      exact run_isSome P s hU f y hI' (by omega)

/-- **The fuel of $\mathfrak{X}$ suffices**: from $\mathbf{x}^{\text{init}}$, any fuel at least `fuel P s` gives the same
    result, so the out-of-fuel case of `run` is never what `blockCost?` returns. -/
theorem run_fuel_eq (P : Program) (s f : Nat) (hf : fuel P s ≤ f) :
    run P f (init s) = run P (fuel P s) (init s) :=
  run_stable P s (fuel P s) (init s) (inv_init P s) (measure_init P s) f hf

/-- With every instruction $\mathfrak{X}$ may decode from `s` in U, the simulation finishes within its fuel. -/
theorem run_fuel_isSome (P : Program) (s : Nat) (hU : ∀ j, Reach P s j → (P.instrCost? j).isSome) :
    (run P (fuel P s) (init s)).isSome :=
  run_isSome P s hU _ _ (inv_init P s) (measure_init P s)

end Sim

/-! ## Every block $\Psi$ charges decodes only opcodes in U -/

/-- Every opcode in U decodes, and has a row in the cost table (GP §A.5, §A.10). -/
def opcodeTotal (n : Nat) : Bool :=
  (match formatOf? n with
    | none => true
    | some .noArgs => (NoArgsOp.ofOpcode? n).isSome
    | some .oneImm => (OneImmOp.ofOpcode? n).isSome
    | some .regExtImm => (RegExtImmOp.ofOpcode? n).isSome
    | some .twoImm => (TwoImmOp.ofOpcode? n).isSome
    | some .oneOffset => (OneOffsetOp.ofOpcode? n).isSome
    | some .regImm => (RegImmOp.ofOpcode? n).isSome
    | some .regTwoImm => (RegTwoImmOp.ofOpcode? n).isSome
    | some .regImmOffset => (RegImmOffsetOp.ofOpcode? n).isSome
    | some .twoReg => (TwoRegOp.ofOpcode? n).isSome
    | some .twoRegImm => (TwoRegImmOp.ofOpcode? n).isSome
    | some .twoRegOffset => (TwoRegOffsetOp.ofOpcode? n).isSome
    | some .twoRegTwoImm => (TwoRegTwoImmOp.ofOpcode? n).isSome
    | some .threeReg => (ThreeRegOp.ofOpcode? n).isSome) &&
  (!isValidOpcode n || (costRow? n).isSome)

set_option maxRecDepth 100000 in
theorem opcodeTotal_lt : ∀ n, n < 256 → opcodeTotal n = true := by
  decide

namespace Program

/-- $\mathfrak{v}_{\text{inst}}$'s opcode condition $\mathbf{c}_{\imath} \in U$ makes the instruction at $\imath$ decode (so $\Psi_1$'s fallback
    `trap` for an undecodable octet is unreachable). -/
theorem decode_isSome {P : Program} {i : Nat} (h : isValidOpcode (P.zeta i) = true) :
    (P.decode i).isSome := by
  have ht := opcodeTotal_lt _ (zeta_lt P i)
  unfold isValidOpcode at h
  unfold opcodeTotal at ht
  unfold decode
  generalize P.zeta i = op at h ht ⊢
  cases hf : formatOf? op with
  | none => rw [hf] at h; cases h
  | some fmt => cases fmt <;> simp_all

theorem costRow_isSome {P : Program} {i : Nat} (h : isValidOpcode (P.zeta i) = true) :
    (costRow? (P.zeta i)).isSome := by
  have ht := opcodeTotal_lt _ (zeta_lt P i)
  simp only [opcodeTotal, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at ht
  rcases ht.2 with h' | h'
  · rw [h] at h'; cases h'
  · exact h'

theorem instrCost?_isSome {P : Program} {i : Nat} (h : isValidOpcode (P.zeta i) = true) :
    (P.instrCost? i).isSome := by
  obtain ⟨ins, hd⟩ := Option.isSome_iff_exists.1 (decode_isSome h)
  obtain ⟨row, hr⟩ := Option.isSome_iff_exists.1 (costRow_isSome h)
  simp [instrCost?, hd, hr, bind, Option.bind, pure]

theorem maskAt_eq_maskExt (P : Program) {i : Nat} (h : i < P.mask.size) : P.maskAt i = P.maskExt i := by
  simp [maskAt, maskExt, Array.getD, h]

/-- $\text{skip}(c)$ is the least $j$ with $(\mathbf{k} \frown [1, 1, \dots])_{c+1+j} = 1$, capped at 24 (GP eq. `skip`). -/
theorem maskExt_of_lt_skip (P : Program) (c : Nat) {k : Nat} (hk : k < P.skip c) :
    P.maskExt (c + 1 + k) = false := by
  unfold skip at hk
  cases hf : (List.range 24).find? (fun j => P.maskExt (c + 1 + j)) with
  | none =>
    rw [hf] at hk
    have := List.find?_eq_none.1 hf k (List.mem_range.2 (by simpa using hk))
    simpa using this
  | some m =>
    rw [hf] at hk
    obtain ⟨-, i, hi, him, hmin⟩ := List.find?_eq_some_iff_getElem.1 hf
    rw [List.getElem_range] at him
    subst him
    have := hmin k (by simpa using hk)
    simpa [List.getElem_range] using this

theorem vBlobAux_cases (P : Program) :
    ∀ (f c : Nat), P.vBlobAux f c = true → (0 < c ∧ c = P.mask.size) ∨ P.vInst c = true
  | 0, _, h => by simp [vBlobAux] at h
  | f + 1, c, h => by
    simp only [vBlobAux] at h
    split at h
    · rename_i h1; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1; exact .inl h1
    · split at h
      · cases h
      · split at h
        · exact .inr ‹_›
        · cases h

/-- Along a program passing $\mathfrak{v}_{\text{blob}}$, every opcode index $\ge c$ of the chain is $\mathfrak{v}_{\text{inst}}$, and so is the
    one after a non-terminator. -/
theorem vBlobAux_chain (P : Program) (hsz : P.mask.size = P.code.size) :
    ∀ (f c : Nat), P.vBlobAux f c = true → ∀ j, c ≤ j → j < P.code.size → P.maskAt j = true →
      P.vInst j = true ∧ (isTerminator (P.zeta j) = false → P.vInst (P.next j) = true)
  | 0, _, h => by simp [vBlobAux] at h
  | f + 1, c, h => by
    intro j hcj hj hm
    simp only [vBlobAux] at h
    split at h
    · rename_i h1; simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1; omega
    · rename_i h1
      split at h
      · cases h
      · rename_i h2
        split at h
        · rename_i hvc
          by_cases hjc : j = c
          · subst hjc
            refine ⟨hvc, fun ht => ?_⟩
            rcases vBlobAux_cases P f _ h with ⟨-, hn⟩ | hn
            · exact absurd (by simp [hn, ht]) h2
            · exact hn
          · have hlt : P.next c ≤ j := by
              refine Nat.le_of_not_lt fun hlt => ?_
              have hk : j - (c + 1) < P.skip c := by unfold next at hlt; omega
              have := P.maskExt_of_lt_skip c hk
              rw [show c + 1 + (j - (c + 1)) = j by omega, ← P.maskAt_eq_maskExt (by omega),
                hm] at this
              cases this
            exact vBlobAux_chain P hsz f _ h j hlt hj hm
        · cases h

theorem vBlob_vInst_zero {P : Program} (hv : P.vBlob = true) : P.vInst 0 = true := by
  rcases vBlobAux_cases P _ 0 hv with ⟨h, -⟩ | h
  · cases h
  · exact h

theorem vBlob_size {P : Program} (hv : P.vBlob = true) : P.mask.size = P.code.size := by
  have := vBlob_vInst_zero hv
  simp only [vInst, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.1.1

/-- In a program passing $\mathfrak{v}_{\text{blob}}$, every instruction $\mathfrak{X}$ decodes from a valid opcode index is valid. -/
theorem vBlob_reach {P : Program} (hv : P.vBlob = true) {s : Nat} (hs : P.vInst s = true) :
    ∀ j, Sim.Reach P s j → P.vInst j = true := by
  intro j hr
  induction hr with
  | refl => exact hs
  | step _ ht ih =>
    have hj := ih
    simp only [vInst, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hj
    exact (vBlobAux_chain P (vBlob_size hv) _ 0 hv _ (Nat.zero_le _) (by omega) hj.1.2 |>.2) ht

theorem vInst_isValidOpcode {P : Program} {i : Nat} (h : P.vInst i = true) :
    isValidOpcode (P.zeta i) = true := by
  simp only [vInst, Bool.and_eq_true] at h; exact h.2

/-- $\varrho^\Delta(\mathbf{c}, \mathbf{k}, s)$ is defined (the simulation finishes within its fuel and meets no opcode
    outside U) for every valid opcode index s of a program passing $\mathfrak{v}_{\text{blob}}$. -/
theorem blockCost?_isSome_of_vBlob {P : Program} (hv : P.vBlob = true) {s : Nat}
    (hs : P.vInst s = true) : (P.blockCost? s).isSome := by
  unfold blockCost?
  rw [Option.isSome_map]
  exact Sim.run_fuel_isSome P s fun j hj =>
    instrCost?_isSome (vInst_isValidOpcode (vBlob_reach hv hs j hj))

theorem blockStartFrom_spec (P : Program) :
    ∀ n, P.isBlockStart (P.blockStartFrom n) = true ∨ P.blockStartFrom n = 0
  | 0 => .inr rfl
  | n + 1 => by
    simp only [blockStartFrom]
    split
    · exact .inl ‹_›
    · exact blockStartFrom_spec P n

/-- $\mathfrak{L}(\imath)$, for a program passing $\mathfrak{v}_{\text{blob}}$, is a valid opcode index. -/
theorem vInst_blockStartOf {P : Program} (hv : P.vBlob = true) (i : Nat) :
    P.vInst (P.blockStartOf i) = true := by
  rcases blockStartFrom_spec P i with h | h
  · simp only [isBlockStart, isInstrStart, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨-, ⟨hlt, hm⟩, hu⟩ := h
    simp only [blockStartOf, vInst, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨⟨⟨vBlob_size hv, by rw [vBlob_size hv]; exact decide_eq_true hlt⟩, hm⟩, hu⟩
  · rw [blockStartOf, h]; exact vBlob_vInst_zero hv

/-- **The default of `blockCost` is unreachable in $\Psi$**: at every step $\Psi$ takes (deblob succeeds),
    the block it charges has a simulated cost. -/
theorem blockCost?_isSome_of_deblob {p : ByteArray} {i : Nat} {P : Program}
    (h : deblob p i = some P) : (P.blockCost? (P.blockStartOf i)).isSome := by
  unfold deblob at h
  cases hp : Blob.parse? p with
  | none => simp [hp] at h
  | some Q =>
    simp only [hp, bind, Option.bind] at h
    split at h
    · rename_i hv
      cases h
      simp only [Bool.and_eq_true] at hv
      exact blockCost?_isSome_of_vBlob hv.1 (vInst_blockStartOf hv.1 i)
    · cases h

/-- `blockCost` is the simulated cost $\max(\mathbf{x}^{\text{final}}_c - 3, 1)$ for every block $\Psi$ charges. -/
theorem blockCost_eq_of_deblob {p : ByteArray} {i : Nat} {P : Program}
    (h : deblob p i = some P) :
    ∃ z, Sim.run P (Sim.fuel P (P.blockStartOf i)) (Sim.init (P.blockStartOf i)) = some z ∧
      P.blockCost (P.blockStartOf i) = max (z.cycle - 3) 1 := by
  have hs := blockCost?_isSome_of_deblob h
  unfold blockCost? at hs
  rw [Option.isSome_map] at hs
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hs
  exact ⟨z, hz, by simp [blockCost, blockCost?, hz]⟩

end Program

end PVM
