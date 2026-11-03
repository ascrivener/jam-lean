import PVM.Logic.Code
import PVM.Logic.Attr
import PVM.Theorems.InitMem
import PVM.Logic.Bits

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

open Lean Meta Simp in
/-- `sx8` of a literal, evaluated. -/
dsimproc reduceSx8 (PVM.sx8 _) := fun e => do
  let some b ← Nat.fromExpr? e.appArg! | return .continue
  return .done (toExpr (PVM.sx8 b))


open Lean Meta Simp in
/-- `Num.encodeLE l x` for literal `l` and `x`, as the octet list `[UInt8.ofNat b₀, …]` it unfolds
    to. A symbolic `x` is left folded, so a stored register reads back by `readN_writeN_same` and
    `decodeLE_encodeLE`. -/
dsimproc reduceEncodeLE (PVM.Num.encodeLE _ _) := fun e => do
  let args := e.getAppArgs
  if args.size != 2 then return .continue
  let some l ← Nat.fromExpr? args[0]! | return .continue
  let some x ← Nat.fromExpr? args[1]! | return .continue
  let bytes := (PVM.Num.encodeLE l x).map fun b => mkApp (mkConst ``UInt8.ofNat) (mkNatLit b.toNat)
  return .done (← mkListLit (mkConst ``UInt8) bytes)

theorem Num.getElem_encodeLE (l v k : Nat) (hk : k < (Num.encodeLE l v).length) :
    (Num.encodeLE l v)[k] = UInt8.ofNat (v / 256 ^ k % 256) := by
  induction l generalizing v k with
  | zero => simp [Num.encodeLE] at hk
  | succ l ih =>
    cases k with
    | zero => simp [Num.encodeLE]
    | succ k =>
      simp only [Num.encodeLE, List.getElem_cons_succ]
      rw [ih]
      congr 2
      rw [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]

@[simp] theorem Memory.length_readN (μ : Memory) (a n : Nat) : (μ.readN a n).length = n := by
  simp [Memory.readN]

/-- A one-octet read outside a write (neither wrapping past 2^32). -/
theorem Memory.read_writeN_disjoint (μ : Memory) (a : Nat) (bs : List UInt8) (b : Nat)
    (h : a + bs.length ≤ b ∨ b + 1 ≤ a) (ha : a + bs.length ≤ two32) (hb : b + 1 ≤ two32) :
    (μ.writeN a bs).read b = μ.read b := by
  have := Memory.readN_writeN_disjoint μ a bs b 1 h ha hb
  simpa [Memory.readN] using this

/-- A one-octet `ℰ₁(v)` is the octet `v`. -/
theorem Num.encodeLE_one (v : Nat) : Num.encodeLE 1 v = [UInt8.ofNat v] := by
  simp only [Num.encodeLE, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_ofNat, Nat.mod_mod]

/-- Reading the low `m ≤ l` octets of a stored `ℰ_l(v)` gives `ℰ_m(v)`. -/
theorem Memory.readN_writeN_encodeLE_low (μ : Memory) (a l m v : Nat) (hm : m ≤ l)
    (ha : l ≤ two32) : (μ.writeN a (Num.encodeLE l v)).readN a m = Num.encodeLE m v := by
  apply List.ext_getElem
  · simp [Memory.readN, Num.length_encodeLE]
  · intro k h1 h2
    simp only [Memory.readN, List.getElem_map, List.getElem_range]
    rw [Memory.read_writeN_at _ _ _ (by simpa using ha) k (by simp at h2 ⊢; omega),
      Num.getElem_encodeLE, Num.getElem_encodeLE]

/-! ## Symbolic arithmetic

When a value depends on an unknown (the argument length `L`), the concrete simprocs stop. These
lemmas, used with `omega` as discharger, finish such terms from linear facts in context. -/

/-- One octet of a little-endian read folds into the rest: read back octet by octet, from the
    innermost, `Num.decodeLE` of `Num.encodeLE` gives `x mod 2^(8n)` (cf. `Nat.mod_mul`). -/
theorem le_byte (x k : Nat) : x % 256 + 256 * (x / 256 % k) = x % (256 * k) :=
  Nat.mod_mul.symm

/-- `Option.getD_some` with a propositional proof. As an `rfl` lemma `simp` uses it by `dsimp`,
    leaving the kernel to check `(some a).getD b ≡ a` by reduction; when `a` is arithmetic over an
    unknown, the kernel may unfold `a` instead (e.g. `x * 2^32` by `Nat.rec`, 2^32 times). -/
theorem getD_some' {α : Type _} (a b : α) : (some a).getD b = a := by
  simp only [Option.getD]

/-! Propositional copies of `rfl` lemmas for the symbolic stages: `simp` applies an `rfl` lemma
by `dsimp`, and the kernel's check of that step may evaluate a product of the unknown with a
large literal by `Nat.rec`. -/

theorem add_zero' (n : Nat) : n + 0 = n := by omega
theorem zero_add' (n : Nat) : 0 + n = n := by omega
theorem mul_zero' (n : Nat) : n * 0 = 0 := by omega
theorem zero_mul' (n : Nat) : 0 * n = 0 := by omega
theorem zero_div' (n : Nat) : 0 / n = 0 := by rw [Nat.zero_div]
theorem div_zero' (n : Nat) : n / 0 = 0 := by rw [Nat.div_zero]
theorem mod_zero' (n : Nat) : n % 0 = n := by rw [Nat.mod_zero]
theorem mul_one' (n : Nat) : n * 1 = n := by omega
theorem sub_zero' (n : Nat) : n - 0 = n := by omega
theorem one_mul' (n : Nat) : 1 * n = n := by omega

/-- Adding a multiple of the modulus (a literal `c`) leaves the remainder. -/
theorem add_mod_of_dvd (a c m : Nat) (h : c % m = 0) : (a + c) % m = a % m := by
  rw [Nat.add_mod, h, Nat.add_zero, Nat.mod_mod]

/-- Adding a "negative" 64-bit immediate `m = 2^64 − c` subtracts `c` when no borrow occurs:
    the wrapped form of `addImm64` with a negative immediate (cf. `Nat.mod_eq_of_lt` when the sum
    does not wrap). -/
theorem add_wrap64 (a m : Nat) (hm : m < 18446744073709551616) (h : 18446744073709551616 - m ≤ a)
    (ha : a < 18446744073709551616) :
    (a + m) % 18446744073709551616 = a - (18446744073709551616 - m) := by
  omega

/-- A register's value is below any modulus of at least 2^64. -/
theorem u64_toNat_mod (x : UInt64) (m : Nat) (h : 18446744073709551616 ≤ m) : x.toNat % m = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt h)

/-- An octet's value is below any modulus of at least 256. -/
theorem u8_toNat_mod (x : UInt8) (m : Nat) (h : 256 ≤ m) : x.toNat % m = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt h)

/-- `sub64` without borrow: (a + 2^64 − b) mod 2^64 = a − b for b ≤ a < 2^64. -/
theorem sub_wrap64 (a b : Nat) (h : b ≤ a) (ha : a < 18446744073709551616) :
    (a + 18446744073709551616 - b) % 18446744073709551616 = a - b := by
  omega

/-- A small natural through `Int` and back (the non-negative case of `signed`/`u64`). -/
theorem toNat_natCast_emod (n : Nat) (m : Int) (h : (n : Int) < m) : ((n : Int) % m).toNat = n := by
  rw [Int.emod_eq_of_lt (by omega) h]; rfl

/-- A negative value through `Int` and back modulo `m` (the negative case of `signed`/`u64`):
    ((b − c) mod m).toNat = b + m − c for b < c ≤ b + m. -/
theorem toNat_natCast_sub_emod (b : Nat) (c m : Int) (h1 : (b : Int) < c) (h2 : c ≤ b + m) (h3 : c ≤ m) :
    (((b : Int) - c) % m).toNat = b + (m - c).toNat := by
  have h : ((b : Int) - c) % m = ((b : Int) - c + m) % m := by
    rw [show (b : Int) - c + m = (b : Int) - c + 1 * m by omega, Int.add_mul_emod_self_right]
  rw [h, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- `add_mod_of_dvd` with the literal on the left. -/
theorem add_mod_of_dvd' (a c m : Nat) (h : c % m = 0) : (c + a) % m = a % m := by
  rw [Nat.add_comm]; exact add_mod_of_dvd a c m h

/-- The first octet of a write. -/
theorem Memory.read_writeN_head (μ : Memory) (a : Nat) (b : UInt8) (bs : List UInt8)
    (h : bs.length + 1 ≤ two32) : (μ.writeN a (b :: bs)).read a = b := by
  have := Memory.read_writeN_at μ a (b :: bs) (by simpa using h) 0 (by simp)
  simpa using this

theorem ite_of_pos {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : ite c a b = a :=
  ite_eq_left h

theorem ite_of_neg {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) (a b : α) : ite c a b = b :=
  ite_eq_right h

/-! ## The step tactic -/

open Lean Meta Elab Tactic in
/-- Succeeds when the step goal `lhs = rhs` is fully reduced: its left side mentions no `if`,
    `match`, `decide`, memory access check, multi-octet read, `decodeLE`, read through a write, or
    `mod` of a non-literal (left for the symbolic stages).
    Then `rfl` fixes the next state without absorbing an unreduced term. -/
elab "pvm_finished" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, lhs, _) := t.eq? | throwError "pvm_finished: not an equation"
  let stuck := lhs.find? fun e =>
    match e.getAppFn with
    | .const n _ =>
      n == ``ite || n == ``dite || n == ``Decidable.decide || n == ``PVM.Memory.readN ||
      n == ``PVM.Num.decodeLE || n == ``PVM.Memory.readable || n == ``PVM.Memory.writable ||
      n == ``List.min? || (n.toString.splitOn "match_").length > 1 ||
      (n == ``HMod.hMod && e.getAppNumArgs == 6 && (e.getArg! 4).nat?.isNone) ||
      (n == ``PVM.Memory.read && (e.getArg! 0).getAppFn.constName?.any
        (· ∈ [``PVM.Memory.writeN, ``PVM.Memory.write, ``PVM.Memory.setPages]))
    | _ => false
  if let some e := stuck then throwError "pvm_finished: unreduced {e}"

/-- The discharger of `pvm_simp`'s symbolic stages: `omega`, after normalizing list lengths and
    `two32`. The final `fail` matters: the last alternative of `first` runs with error recovery,
    so a failing `omega` there would be logged and its goal admitted instead of the rewrite being
    rejected. -/
macro "pvm_arith" : tactic => `(tactic| first
  | omega
  | (simp only [PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32,
      List.length_append, List.length_map, List.length_range, PVM.Memory.length_readN] <;> omega)
  | fail "pvm_arith")

/-- The main pass of `pvm_simp`: unfold the instruction's mutation and reduce concrete
    arithmetic, register lookups and memory accesses. -/
syntax "pvm_core" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pvm_core [$hs,*]) => `(tactic| (
    simp only [PVM.Program.exec, PVM.Program.sjump, PVM.Program.branch, PVM.Program.isBlockStartInt,
      PVM.Program.finalState, PVM.memoryException, pvm_code, PVM.Exec.twoRegImmAlu,
      ↓PVM.twoRegAlu_signExtend8, PVM.reduceSx8, PVM.Exec.twoRegAlu, PVM.Exec.indices, PVM.Regs.get, Fin.getElem_fin, PVM.regIdx_val_0,
      PVM.regIdx_val_1, PVM.regIdx_val_2, PVM.regIdx_val_3, PVM.regIdx_val_4, PVM.regIdx_val_5,
      PVM.regIdx_val_6, PVM.regIdx_val_7, PVM.regIdx_val_8, PVM.regIdx_val_9, PVM.regIdx_val_10,
      PVM.regIdx_val_11, PVM.regIdx_val_12, PVM.getD_some', Vector.getElem_ofFn,
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
      PVM.Memory.readN_writeN_encodeLE_low, PVM.Num.encodeLE_one,
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
      PVM.reduceRotr, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reduceGT, Nat.reduceBEq,
      Nat.reduceBNe, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true, Bool.false_and,
      Bool.and_false, Bool.true_and, Bool.and_true, $hs,*]))

/-- Compute one gas-free step's effect: unfold Ψ₁'s mutation for the (known) instruction, reduce
    the register file and concrete arithmetic, decide ε^μ from the given access hypotheses, and
    close `(ε, ı', ω', μ') = (▸, ?, ?, ?)` by `rfl`, which fixes the next state. Fails if the
    step does not provably continue. The extra terms are memory-access facts for `simp`. -/
syntax "pvm_simp" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| pvm_simp [$hs,*]) => `(tactic| (
    pvm_core [$hs,*]
    first
      | (pvm_finished; rfl)
      | (
        try simp (disch := pvm_arith) only [Nat.mod_mod, Nat.mod_eq_of_lt, PVM.add_wrap64, PVM.sub_wrap64, PVM.toNat_natCast_emod, PVM.add_zero',
          Nat.sub_add_cancel, Nat.add_sub_cancel, PVM.Memory.readN_writeN_same,
          PVM.Memory.readN_writeN_encodeLE_low, PVM.Memory.readN_writeN_disjoint,
          PVM.Memory.read_writeN_disjoint, PVM.Memory.writable_writeN, PVM.Memory.readable_writeN, PVM.Num.decodeLE_encodeLE,
          PVM.Num.length_encodeLE, PVM.u64_toNat_mod, UInt64.ofNat_toNat, PVM.two32]
        try pvm_core [$hs,*]
        try simp only [PVM.Memory.readN, List.range_succ, List.range_zero, List.map_cons,
              List.map_nil, List.map_append, List.nil_append, List.cons_append,
              PVM.Memory.read_writeN, PVM.Num.length_encodeLE, PVM.reduceEncodeLE,
              List.getElem!_cons_zero, List.getElem!_cons_succ, PVM.Num.decodeLE, UInt8.toNat_ofNat',
              Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
              Nat.reduceDiv, Nat.reduceLT, Nat.reduceLeDiff, Nat.lt_irrefl, PVM.two32, and_true,
              true_and, and_false, false_and, ↓reduceIte, ite_true, ite_false, id_eq, PVM.Program.exec, PVM.Program.sjump, PVM.Program.branch, PVM.Program.isBlockStartInt,
          PVM.Program.finalState, PVM.memoryException, pvm_code, PVM.Exec.twoRegImmAlu,
          ↓PVM.twoRegAlu_signExtend8, PVM.reduceSx8, PVM.Exec.twoRegAlu, PVM.Exec.indices, PVM.Regs.get, Fin.getElem_fin, PVM.regIdx_val_0,
          PVM.regIdx_val_1, PVM.regIdx_val_2, PVM.regIdx_val_3, PVM.regIdx_val_4, PVM.regIdx_val_5,
          PVM.regIdx_val_6, PVM.regIdx_val_7, PVM.regIdx_val_8, PVM.regIdx_val_9, PVM.regIdx_val_10,
          PVM.regIdx_val_11, PVM.regIdx_val_12, PVM.getD_some', Vector.getElem_ofFn,
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
          PVM.Memory.readN_writeN_encodeLE_low, PVM.Num.encodeLE_one,
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
          PVM.reduceRotr, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reduceGT, Nat.reduceBEq,
          Nat.reduceBNe, Bool.false_or, Bool.or_false, Bool.true_or, Bool.or_true, Bool.false_and,
          Bool.and_false, Bool.true_and, Bool.and_true, $hs,*]
        try simp only [Nat.mod_mod, PVM.add_zero', PVM.zero_add', PVM.mul_zero', PVM.zero_mul',
          PVM.zero_div', PVM.div_zero', PVM.mod_zero', PVM.le_byte, Nat.reduceMul]
        try simp (disch := pvm_arith) only [Nat.mod_mod, PVM.add_zero', PVM.zero_add', PVM.mul_zero',
          PVM.zero_mul', PVM.zero_div', PVM.div_zero', PVM.mod_zero', PVM.mul_one', PVM.one_mul', PVM.sub_zero',
      Nat.mod_eq_of_lt, PVM.add_mod_of_dvd, PVM.add_mod_of_dvd', Nat.div_eq_of_lt, Nat.mod_add_div',
      Nat.div_add_mod', Nat.mod_add_div, Nat.sub_sub, Nat.reduceAdd,
      PVM.toNat_natCast_sub_emod, Int.reduceToNat, PVM.Memory.read_writeN_head, PVM.sx8_mod_two64,
      PVM.sx8_lt_two63, PVM.sx8_cast_sub_lt, PVM.sx8_of_lt, PVM.sx8_div64_mod2, PVM.sx8_div32_mod2,
      PVM.sx8_div16_mod2, PVM.sx8_div8_mod2, PVM.sx8_div4_mod2, PVM.sx8_div2_mod2, PVM.sx8_div1_mod2,
      PVM.sx8_div128_mod2, PVM.sx8_mod128, PVM.sx8_mod64, PVM.sx8_mod32, PVM.sx8_mod16, PVM.sx8_mod8,
      PVM.sx8_mod4, PVM.sx8_mod2,
      PVM.Memory.read_writeN_at, List.getElem_cons_zero, List.getElem_cons_succ, PVM.add_wrap64, PVM.sub_wrap64, PVM.toNat_natCast_emod,
          PVM.u8_toNat_mod, UInt8.ofNat_toNat, Nat.add_sub_cancel, Nat.sub_add_cancel, Nat.reduceSub,
          PVM.Memory.writable_writeN, PVM.Memory.readable_writeN, PVM.Memory.readN_writeN_same,
          PVM.Memory.readN_writeN_encodeLE_low, PVM.Num.encodeLE_one, PVM.Memory.readN_writeN_disjoint,
      PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
          PVM.Num.decodeLE_encodeLE, List.length_cons, List.length_nil, PVM.two32, PVM.u64_toNat_mod,
          UInt64.ofNat_toNat, Nat.mul_div_cancel, PVM.ite_of_pos, PVM.ite_of_neg,
          Bool.not_eq_true', Bool.not_eq_false', beq_eq_false_iff_ne, beq_iff_eq, bne_eq_false_iff_eq,
          bne_iff_ne, ne_eq, decide_eq_true_eq,
          decide_eq_false_iff_not, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, $hs,*]
        try pvm_core [$hs,*]
        try simp (disch := pvm_arith) only [Nat.mod_mod, PVM.add_zero', PVM.zero_add', PVM.mul_zero',
          PVM.zero_mul', PVM.zero_div', PVM.div_zero', PVM.mod_zero', PVM.mul_one', PVM.one_mul', PVM.sub_zero',
      Nat.mod_eq_of_lt, PVM.add_mod_of_dvd, PVM.add_mod_of_dvd', Nat.div_eq_of_lt, Nat.mod_add_div',
      Nat.div_add_mod', Nat.mod_add_div, Nat.sub_sub, Nat.reduceAdd,
      PVM.toNat_natCast_sub_emod, Int.reduceToNat, PVM.Memory.read_writeN_head, PVM.sx8_mod_two64,
      PVM.sx8_lt_two63, PVM.sx8_cast_sub_lt, PVM.sx8_of_lt, PVM.sx8_div64_mod2, PVM.sx8_div32_mod2,
      PVM.sx8_div16_mod2, PVM.sx8_div8_mod2, PVM.sx8_div4_mod2, PVM.sx8_div2_mod2, PVM.sx8_div1_mod2,
      PVM.sx8_div128_mod2, PVM.sx8_mod128, PVM.sx8_mod64, PVM.sx8_mod32, PVM.sx8_mod16, PVM.sx8_mod8,
      PVM.sx8_mod4, PVM.sx8_mod2,
      PVM.Memory.read_writeN_at, List.getElem_cons_zero, List.getElem_cons_succ, PVM.add_wrap64, PVM.sub_wrap64, PVM.toNat_natCast_emod,
          PVM.u8_toNat_mod, UInt8.ofNat_toNat, Nat.add_sub_cancel, Nat.sub_add_cancel, Nat.reduceSub,
          PVM.Memory.writable_writeN, PVM.Memory.readable_writeN, PVM.Memory.readN_writeN_same,
          PVM.Memory.readN_writeN_encodeLE_low, PVM.Num.encodeLE_one, PVM.Memory.readN_writeN_disjoint,
      PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,
          PVM.Num.decodeLE_encodeLE, List.length_cons, List.length_nil, PVM.two32, PVM.u64_toNat_mod,
          UInt64.ofNat_toNat, Nat.mul_div_cancel, PVM.ite_of_pos, PVM.ite_of_neg,
          Bool.not_eq_true', Bool.not_eq_false', beq_eq_false_iff_ne, beq_iff_eq, bne_eq_false_iff_eq,
          bne_iff_ne, ne_eq, decide_eq_true_eq,
          decide_eq_false_iff_not, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, $hs,*]
        try pvm_core [$hs,*]
        try rfl)))

end PVM
