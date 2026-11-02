import PVM.Logic.Code
import PVM.Logic.Attr
import PVM.Theorems.InitMem

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


/-! ## Keeping the register file small

Every instruction that writes a register adds a `Vector.set` to the register file's term, so a
long path builds a long chain. The stepper keeps the file as `regsNF base L` instead: the
starting file `base` with the overrides `L`, at most one per register, sorted by index. A write
inserts into `L` (`set_regsNF`, computed by `insertReg` on literal indices) and a read looks it
up (`getElem_regsNF`). -/

/-- `base` with the overrides `L` (the first entry for an index wins). -/
def regsNF (base : Regs) (L : List (Nat × UInt64)) : Regs :=
  L.foldr (fun q ω => ω.setIfInBounds q.1 q.2) base

/-- Insert the override (k, v), keeping `L` sorted with one entry per index. -/
def insertReg (k : Nat) (v : UInt64) : List (Nat × UInt64) → List (Nat × UInt64)
  | [] => [(k, v)]
  | (i, x) :: rest =>
    if k < i then (k, v) :: (i, x) :: rest
    else if k = i then (k, v) :: rest
    else (i, x) :: insertReg k v rest

theorem lookup_cons_nat {β : Type} (k a : Nat) (v : β) (l : List (Nat × β)) :
    ((k, v) :: l).lookup a = if a = k then some v else l.lookup a := by
  simp only [List.lookup_cons]
  cases hb : a == k
  · have : a ≠ k := by simpa using hb
    simp [this]
  · have : a = k := by simpa using hb
    simp [this]

theorem lookup_insertReg (k j : Nat) (v : UInt64) (L : List (Nat × UInt64)) :
    (insertReg k v L).lookup j = if j = k then some v else L.lookup j := by
  induction L with
  | nil => simp only [insertReg, lookup_cons_nat, List.lookup_nil]
  | cons q rest ih =>
    obtain ⟨i, x⟩ := q
    simp only [insertReg]
    by_cases hki : k < i
    · simp only [hki, ↓reduceIte, lookup_cons_nat]
    · by_cases hke : k = i
      · subst hke; simp only [hki, ↓reduceIte, lookup_cons_nat]
        by_cases hjk : j = k <;> simp [hjk]
      · simp only [hki, hke, ↓reduceIte, lookup_cons_nat, ih]
        by_cases hji : j = i
        · subst hji; simp [Ne.symm hke]
        · simp [hji]

theorem getElem_regsNF (base : Regs) (L : List (Nat × UInt64)) (j : Nat) (hj : j < 13) :
    (regsNF base L)[j] = (L.lookup j).getD base[j] := by
  induction L with
  | nil => rfl
  | cons q rest ih =>
    obtain ⟨i, x⟩ := q
    simp only [regsNF, List.foldr_cons] at ih ⊢
    rw [Vector.getElem_setIfInBounds]
    simp only [lookup_cons_nat]
    by_cases hij : i = j
    · subst hij; simp
    · rw [ite_eq_right hij, ih]; simp [Ne.symm hij]

theorem set_regsNF (base : Regs) (L : List (Nat × UInt64)) (k : Nat) (v : UInt64) (h : k < 13) :
    (regsNF base L).set k v h = regsNF base (insertReg k v L) := by
  apply Vector.ext; intro j hj
  rw [Vector.getElem_set, getElem_regsNF _ _ _ hj, getElem_regsNF _ _ _ hj, lookup_insertReg]
  by_cases hjk : k = j
  · subst hjk; simp
  · simp [hjk, Ne.symm hjk]


/-! ## Evaluating closed terms the stepper meets -/

@[simp] theorem natCast_lt_zero (n : Nat) : ((n : Int) < 0) = False := by
  simp only [eq_iff_iff, iff_false, Int.not_lt]; exact Int.natCast_nonneg n

open Lean Meta Simp in
/-- `Exec.bitwise f a b` for literals `a`, `b` and a closed `f`: evaluated bit by bit, as its
    definition does. The result is a literal; the kernel checks it by evaluating the definition. -/
dsimproc reduceBitwise (PVM.Exec.bitwise _ _ _) := fun e => do
  let_expr PVM.Exec.bitwise f a b ← e | return .continue
  let some a ← Nat.fromExpr? a | return .continue
  let some b ← Nat.fromExpr? b | return .continue
  let evalF (x y : Bool) : MetaM (Option Bool) := do
    let r ← whnfD (mkApp2 f (toExpr x) (toExpr y))
    if r.isConstOf ``Bool.true then return some true
    else if r.isConstOf ``Bool.false then return some false
    else return none
  let some ff ← evalF false false | return .continue
  let some ft ← evalF false true | return .continue
  let some tf ← evalF true false | return .continue
  let some tt ← evalF true true | return .continue
  let tbl (x y : Bool) : Bool := match x, y with
    | false, false => ff | false, true => ft | true, false => tf | true, true => tt
  let bitOf (x i : Nat) : Bool := x / 2 ^ i % 2 = 1
  let r := (List.range 64).foldr (fun i acc => acc + (if tbl (bitOf a i) (bitOf b i) then 2 ^ i else 0)) 0
  return .done (toExpr r)


open Lean Meta Simp in
/-- Evaluate a PVM bit helper on literal arguments by calling the model's own definition; the
    kernel re-checks the literal by evaluating the definition. -/
def evalNatFn2 (f : Nat → Nat → Nat) (e : Expr) : SimpM DStep := do
  let args := e.getAppArgs
  if args.size != 2 then return .continue
  let some a ← Nat.fromExpr? args[0]! | return .continue
  let some b ← Nat.fromExpr? args[1]! | return .continue
  return .done (toExpr (f a b))

open Lean Meta Simp in
def evalNatFn3 (f : Nat → Nat → Nat → Nat) (e : Expr) : SimpM DStep := do
  let args := e.getAppArgs
  if args.size != 3 then return .continue
  let some a ← Nat.fromExpr? args[0]! | return .continue
  let some b ← Nat.fromExpr? args[1]! | return .continue
  let some c ← Nat.fromExpr? args[2]! | return .continue
  return .done (toExpr (f a b c))

dsimproc reduceTrailingZeros (PVM.Num.trailingZeros _ _) := evalNatFn2 PVM.Num.trailingZeros
dsimproc reduceLeadingZeros (PVM.Num.leadingZeros _ _) := evalNatFn2 PVM.Num.leadingZeros
dsimproc reducePopcount (PVM.Num.popcount _ _) := evalNatFn2 PVM.Num.popcount
dsimproc reduceRotl (PVM.Num.rotl _ _ _) := evalNatFn3 PVM.Num.rotl
dsimproc reduceRotr (PVM.Num.rotr _ _ _) := evalNatFn3 PVM.Num.rotr


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
      Vector.getElem_set, PVM.set_regsNF, PVM.getElem_regsNF, PVM.insertReg, PVM.lookup_cons_nat,
      PVM.Num.decodeLE, UInt8.toNat_ofNat',
      List.lookup_nil, Option.getD_none, PVM.two32, PVM.two64, PVM.pageSize, UInt64.toNat_ofNat',
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
      or_true, true_or, or_false, false_or, id_eq, Int.toNat_natCast, PVM.natCast_lt_zero,
      PVM.reduceBitwise, List.length_cons, List.length_nil, PVM.Memory.read_setPages,
      PVM.Memory.readN_setPages, PVM.Memory.writable_setPages, PVM.Memory.readable_setPages,
      Option.isSome_some, PVM.Exec.threeRegAlu, PVM.Exec.regImmBranchCond,
      PVM.Exec.twoRegBranchCond, PVM.Exec.u64, PVM.Exec.s64, PVM.Num.sext, PVM.Num.signed,
      PVM.Num.unsigned, PVM.Num.floorShift, PVM.Program.djump, UInt8.reduceToNat, Int.reduceAdd,
      Int.reduceSub, Int.reduceMul, Int.reduceMod, Int.reduceFDiv, Int.reducePow,
      Int.reduceToNat, Int.reduceNeg, Int.reduceLE, Int.reduceOfNat, Int.cast_ofNat_Int,
      Int.add_emod_left, Nat.min_def, Nat.max_def, PVM.Exec.ofBool,
      PVM.reduceTrailingZeros, PVM.reduceLeadingZeros, PVM.reducePopcount, PVM.reduceRotl,
      PVM.reduceRotr, $hs,*]
    try simp only [PVM.Memory.readN, List.range_succ, List.range_zero, List.map_cons,
          List.map_nil, List.map_append, List.nil_append, List.cons_append,
          PVM.Memory.read_writeN, PVM.Num.length_encodeLE, PVM.Num.encodeLE,
          List.getElem!_cons_zero, List.getElem!_cons_succ, PVM.Num.decodeLE, UInt8.toNat_ofNat',
          Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
          Nat.reduceDiv, Nat.reduceLT, Nat.reduceLeDiff, Nat.lt_irrefl, PVM.two32, and_true,
          true_and, and_false, false_and, ↓reduceIte, ite_true, ite_false, id_eq, PVM.Program.exec, PVM.Program.sjump, PVM.Program.branch, PVM.Program.isBlockStartInt,
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
      or_true, true_or, or_false, false_or, id_eq, Int.toNat_natCast, PVM.natCast_lt_zero,
      PVM.reduceBitwise, List.length_cons, List.length_nil, PVM.Memory.read_setPages,
      PVM.Memory.readN_setPages, PVM.Memory.writable_setPages, PVM.Memory.readable_setPages,
      Option.isSome_some, PVM.Exec.threeRegAlu, PVM.Exec.regImmBranchCond,
      PVM.Exec.twoRegBranchCond, PVM.Exec.u64, PVM.Exec.s64, PVM.Num.sext, PVM.Num.signed,
      PVM.Num.unsigned, PVM.Num.floorShift, PVM.Program.djump, UInt8.reduceToNat, Int.reduceAdd,
      Int.reduceSub, Int.reduceMul, Int.reduceMod, Int.reduceFDiv, Int.reducePow,
      Int.reduceToNat, Int.reduceNeg, Int.reduceLE, Int.reduceOfNat, Int.cast_ofNat_Int,
      Int.add_emod_left, Nat.min_def, Nat.max_def, PVM.Exec.ofBool,
      PVM.reduceTrailingZeros, PVM.reduceLeadingZeros, PVM.reducePopcount, PVM.reduceRotl,
      PVM.reduceRotr, $hs,*]
    rfl))

end PVM
