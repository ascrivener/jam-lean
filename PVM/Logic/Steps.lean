import PVM.Logic.Code
import PVM.Logic.Attr

/-!
# Chains of gas-free steps

`FreeSteps p i ω μ i' ω' μ'`: from (ı, ω, μ) the gas-free machine continues, step by step, to
(ı', ω', μ'). Chains compose (`FreeSteps.trans`) and end in a `FreeRun` (`FreeSteps.run`), so a
proof can cover a long path piece by piece: a basic block, a function, a loop.

`FreeSteps.step_decode` takes one step at an index whose instruction is known (from code facts),
leaving the instruction's effect as an equation for `simp` to compute.
-/

namespace PVM

/-- Zero or more continuing gas-free steps. -/
inductive FreeSteps (p : ByteArray) : Nat → Regs → Memory → Nat → Regs → Memory → Prop where
  | refl {i ω μ} : FreeSteps p i ω μ i ω μ
  | next {i ω μ i' ω' μ' i'' ω'' μ''} : FreeNext p i ω μ i' ω' μ' →
      FreeSteps p i' ω' μ' i'' ω'' μ'' → FreeSteps p i ω μ i'' ω'' μ''

namespace FreeSteps

variable {p : ByteArray}

theorem trans {i ω μ i' ω' μ' i'' ω'' μ''} (h₁ : FreeSteps p i ω μ i' ω' μ')
    (h₂ : FreeSteps p i' ω' μ' i'' ω'' μ'') : FreeSteps p i ω μ i'' ω'' μ'' := by
  induction h₁ with
  | refl => exact h₂
  | next hn _ ih => exact .next hn (ih h₂)

/-- A chain followed by a run is a run. -/
theorem run {i ω μ i' ω' μ' ε e ω'' μ''} (h : FreeSteps p i ω μ i' ω' μ')
    (hr : FreeRun p i' ω' μ' ε e ω'' μ'') : FreeRun p i ω μ ε e ω'' μ'' := by
  induction h with
  | refl => exact hr
  | next hn _ ih => exact .next hn (ih hr)

/-- One step at an index where the code facts give the instruction `ins` and ı + 1 + skip(ı) = n.
    The second hypothesis is the step's effect, for `simp` to compute. -/
theorem step_decode {P : Program} {i : Nat} {ins : Instr} {n : Nat} {ω : Regs} {μ : Memory}
    {i' : Nat} {ω' : Regs} {μ' : Memory} {i'' : Nat} {ω'' : Regs} {μ'' : Memory}
    (hd : deblob p i = some P ∧ P.decode i = some ins ∧ P.next i = n)
    (hs : (let m := P.exec i ins ω μ
           Program.finalState .cont i ω μ m (memoryException μ m.reads m.writes)) = (.cont, i', ω', μ'))
    (rest : FreeSteps p i' ω' μ' i'' ω'' μ'') : FreeSteps p i ω μ i'' ω'' μ'' :=
  .next ⟨P, hd.1, by rw [Program.freeStep_of_decode ω μ hd.2.1]; exact hs⟩ rest

end FreeSteps


/-! ## Memory lemmas for stepping -/

@[simp] theorem Memory.writable_writeN (μ : Memory) (a : Nat) (bs : List UInt8) (i : Nat) :
    (μ.writeN a bs).writable i = μ.writable i := by
  simp [Memory.writable, Memory.writeN_pages]

@[simp] theorem Memory.readable_writeN (μ : Memory) (a : Nat) (bs : List UInt8) (i : Nat) :
    (μ.writeN a bs).readable i = μ.readable i := by
  simp [Memory.readable, Memory.writeN_pages]

theorem Memory.readable_of_writable {μ : Memory} {a : Nat} (h : μ.writable a = true) :
    μ.readable a = true := by
  unfold Memory.writable at h; unfold Memory.readable
  cases hp : μ.pages.get? (a / pageSize) <;> simp_all

/-- Reading back exactly what was written. -/
theorem Memory.readN_writeN_same (μ : Memory) (a n : Nat) (bs : List UInt8) (hn : bs.length = n)
    (hlen : n ≤ two32) : (μ.writeN a bs).readN a n = bs := by
  subst hn; exact Memory.readN_writeN μ a bs hlen

/-- Reading a range disjoint from a write (neither wrapping past 2^32). -/
theorem Memory.readN_writeN_disjoint (μ : Memory) (a : Nat) (bs : List UInt8) (b n : Nat)
    (h : a + bs.length ≤ b ∨ b + n ≤ a) (ha : a + bs.length ≤ two32) (hb : b + n ≤ two32) :
    (μ.writeN a bs).readN b n = μ.readN b n := by
  unfold Memory.readN
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  apply Memory.read_writeN_of_not_mem
  intro k' hk'
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

@[simp] theorem Num.length_encodeLE (n v : Nat) : (Num.encodeLE n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [Num.encodeLE, ih]

@[simp] theorem Num.decodeLE_encodeLE (n v : Nat) : Num.decodeLE (Num.encodeLE n v) = v % 2 ^ (8 * n) := by
  induction n generalizing v with
  | zero => simp [Num.encodeLE, Num.decodeLE, Nat.mod_one]
  | succ n ih =>
    simp only [Num.encodeLE, Num.decodeLE, ih, UInt8.toNat_ofNat']
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add, Nat.mod_mul]
    simp

/-! Register indices are `Fin 13` literals; `simp` reads their values with these. -/

@[simp] theorem regIdx_val_0 : (((0 : Fin 13) : Nat)) = 0 := rfl
@[simp] theorem regIdx_val_1 : (((1 : Fin 13) : Nat)) = 1 := rfl
@[simp] theorem regIdx_val_2 : (((2 : Fin 13) : Nat)) = 2 := rfl
@[simp] theorem regIdx_val_3 : (((3 : Fin 13) : Nat)) = 3 := rfl
@[simp] theorem regIdx_val_4 : (((4 : Fin 13) : Nat)) = 4 := rfl
@[simp] theorem regIdx_val_5 : (((5 : Fin 13) : Nat)) = 5 := rfl
@[simp] theorem regIdx_val_6 : (((6 : Fin 13) : Nat)) = 6 := rfl
@[simp] theorem regIdx_val_7 : (((7 : Fin 13) : Nat)) = 7 := rfl
@[simp] theorem regIdx_val_8 : (((8 : Fin 13) : Nat)) = 8 := rfl
@[simp] theorem regIdx_val_9 : (((9 : Fin 13) : Nat)) = 9 := rfl
@[simp] theorem regIdx_val_10 : (((10 : Fin 13) : Nat)) = 10 := rfl
@[simp] theorem regIdx_val_11 : (((11 : Fin 13) : Nat)) = 11 := rfl
@[simp] theorem regIdx_val_12 : (((12 : Fin 13) : Nat)) = 12 := rfl


/-! ## The step tactic -/

/-- Compute one gas-free step's effect: unfold Ψ₁'s mutation for the (known) instruction, reduce
    the register file and concrete arithmetic, decide ε^μ from the given access hypotheses, and
    close `(ε, ı', ω', μ') = (▸, ?, ?, ?)` by `rfl`, which fixes the next state. Fails if the
    step does not provably continue. The extra terms are memory-access facts for `simp`. -/
syntax "pvm_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pvm_simp [$hs,*]) => `(tactic| (
    simp only [PVM.Program.exec, PVM.Program.sjump, PVM.Program.branch, PVM.Program.isBlockStartInt,
      PVM.Program.finalState, PVM.memoryException, pvm_code, PVM.Exec.twoRegImmAlu,
      PVM.Exec.twoRegAlu, PVM.Exec.indices, PVM.Regs.get, Fin.getElem_fin, PVM.regIdx_val_0,
      PVM.regIdx_val_1, PVM.regIdx_val_2, PVM.regIdx_val_3, PVM.regIdx_val_4, PVM.regIdx_val_5,
      PVM.regIdx_val_6, PVM.regIdx_val_7, PVM.regIdx_val_8, PVM.regIdx_val_9, PVM.regIdx_val_10,
      PVM.regIdx_val_11, PVM.regIdx_val_12, Option.getD_some, Vector.getElem_ofFn,
      Vector.getElem_set, PVM.two32, PVM.two64, PVM.pageSize, UInt64.toNat_ofNat',
      UInt64.toNat_ofNat, UInt64.reduceToNat, ne_eq, not_true_eq_false, ↓reduceIte,
      List.append_nil, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, Fin.isValue,
      Fin.val_ofNat, decide_false, decide_true, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ite_true, ite_false, List.filter_nil, List.filter_cons, List.min?_nil, List.map_cons,
      List.map_nil, List.range_succ, List.range_zero, List.map_append, List.filter_append,
      Int.reduceLT, Int.reduceToNat, Int.reduceNeg, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMul, Nat.reducePow, Nat.reduceDiv, Nat.reduceEqDiff, Nat.reduceLeDiff,
      Nat.reduceLT, Nat.lt_irrefl, PVM.Memory.writable_writeN, PVM.Memory.readable_writeN,
      PVM.RegTwoImmOp.width, PVM.TwoImmOp.width, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Num.length_encodeLE, PVM.Num.decodeLE_encodeLE,
      or_true, true_or, or_false, false_or, $hs,*]
    rfl))

end PVM
