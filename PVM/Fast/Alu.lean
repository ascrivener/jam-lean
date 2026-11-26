import PVM.Exec
import PVM.Logic.Bits

/-!
# Fast bitwise register operations, proved equal to the paper's

`Exec.bitwise f a b` follows GP §A.5 literally: ∀ i ∈ ℕ_64 : ℬ_8(r)_i = f(ℬ_8(a)_i, ℬ_8(b)_i), computed
bit by bit (`Num.ofBits` over `Num.bit`, each bit a big-number power and division). `bitwiseFast`
computes the same 64 bits with machine-word operations, from the truth table of `f`:
r = ⋁ over the rows (p, q) with f(p, q) = 1 of (a or ¬a) ∧ (b or ¬b).

`bitwise_eq_bitwiseFast` is registered with `@[csimp]`. Since `Exec.twoRegImmAlu` and
`Exec.threeRegAlu` were compiled before it, `twoRegImmAluFast` and `threeRegAluFast` restate them
word for word here, so that their compiled code uses `bitwiseFast`; the equalities
`twoRegImmAlu_eq_twoRegImmAluFast` and `threeRegAlu_eq_threeRegAluFast` (both `rfl` case by case)
are registered with `@[csimp]` too.
-/

namespace PVM


namespace Exec

open Num

/-- `bitwise` on machine words: the disjunction of the rows of the truth table of `f`. -/
def bitwiseFast (f : Bool → Bool → Bool) (a b : Nat) : Nat :=
  let x := UInt64.ofNat a
  let y := UInt64.ofNat b
  ((if f true true then x &&& y else 0) ||| (if f true false then x &&& ~~~y else 0) |||
    (if f false true then ~~~x &&& y else 0) ||| (if f false false then ~~~x &&& ~~~y else 0)).toNat

/-- **The word-level bitwise operation is the paper's bit-by-bit one.** -/
@[csimp] theorem bitwise_eq_bitwiseFast : @bitwise = @bitwiseFast := by
  funext f a b
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bitwise, bitwiseFast, Num.testBit_ofBits, Num.bit_eq_testBit]
  rw [← UInt64.toNat_toBitVec, BitVec.testBit_toNat]
  by_cases hi : i < 64
  · have ha : a.testBit i = (UInt64.ofNat a).toBitVec.getLsbD i := by
      rw [UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat]; simp [hi]
    have hb : b.testBit i = (UInt64.ofNat b).toBitVec.getLsbD i := by
      rw [UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat]; simp [hi]
    have h0 : (0 : UInt64).toBitVec.getLsbD i = false := BitVec.getLsbD_zero
    rw [ha, hb]
    generalize UInt64.ofNat a = x
    generalize UInt64.ofNat b = y
    cases h1 : f true true <;> cases h2 : f true false <;> cases h3 : f false true <;>
      cases h4 : f false false <;>
      simp only [↓reduceIte, Bool.false_eq_true, UInt64.toBitVec_or, UInt64.toBitVec_and,
        UInt64.toBitVec_not, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, h0, hi,
        decide_true, Bool.true_and, decide_false] <;>
      cases x.toBitVec.getLsbD i <;> cases y.toBitVec.getLsbD i <;> simp_all
  · simp only [hi, decide_false, Bool.false_and]
    rw [BitVec.getLsbD_of_ge _ _ (by omega)]

/-- `twoRegImmAlu`, restated so that its compiled code uses `bitwiseFast`. -/
def twoRegImmAluFast : TwoRegImmOp → Nat → Nat → Nat → Option Nat
  | .addImm32, _, b, x => some <| sext 4 ((b + x) % two32)
  | .andImm, _, b, x => some <| bitwise (· && ·) b x
  | .xorImm, _, b, x => some <| bitwise (· ^^ ·) b x
  | .orImm, _, b, x => some <| bitwise (· || ·) b x
  | .mulImm32, _, b, x => some <| sext 4 ((b * x) % two32)
  | .setLtUImm, _, b, x => some <| ofBool (b < x)
  | .setLtSImm, _, b, x => some <| ofBool (s64 b < s64 x)
  | .shloLImm32, _, b, x => some <| sext 4 ((b * 2 ^ (x % 32)) % two32)
  | .shloRImm32, _, b, x => some <| sext 4 (b % two32 / 2 ^ (x % 32))
  | .sharRImm32, _, b, x => some <| u64 (Num.floorShift (Num.signed 4 (b % two32)) (x % 32))
  | .negAddImm32, _, b, x => some <| sext 4 (((x : Int) + two32 - b) % (two32 : Int)).toNat
  | .setGtUImm, _, b, x => some <| ofBool (b > x)
  | .setGtSImm, _, b, x => some <| ofBool (s64 b > s64 x)
  | .shloLImmAlt32, _, b, x => some <| sext 4 ((x * 2 ^ (b % 32)) % two32)
  | .shloRImmAlt32, _, b, x => some <| sext 4 (x % two32 / 2 ^ (b % 32))
  | .sharRImmAlt32, _, b, x => some <| u64 (Num.floorShift (Num.signed 4 (x % two32)) (b % 32))
  | .cmovIzImm, a, b, x => some <| if b = 0 then x else a
  | .cmovNzImm, a, b, x => some <| if b ≠ 0 then x else a
  | .addImm64, _, b, x => some <| (b + x) % two64
  | .mulImm64, _, b, x => some <| (b * x) % two64
  | .shloLImm64, _, b, x => some <| sext 8 ((b * 2 ^ (x % 64)) % two64)
  | .shloRImm64, _, b, x => some <| sext 8 (b / 2 ^ (x % 64))
  | .sharRImm64, _, b, x => some <| u64 (Num.floorShift (s64 b) (x % 64))
  | .negAddImm64, _, b, x => some <| (x + two64 - b) % two64
  | .shloLImmAlt64, _, b, x => some <| (x * 2 ^ (b % 64)) % two64
  | .shloRImmAlt64, _, b, x => some <| x / 2 ^ (b % 64)
  | .sharRImmAlt64, _, b, x => some <| u64 (Num.floorShift (s64 x) (b % 64))
  | .rotR64Imm, _, b, x => some <| Num.rotr 64 b x
  | .rotR64ImmAlt, _, b, x => some <| Num.rotr 64 x b
  | .rotR32Imm, _, b, x => some <| sext 4 (Num.rotr 32 b x)
  | .rotR32ImmAlt, _, b, x => some <| sext 4 (Num.rotr 32 x b)
  | .storeIndU8, _, _, _ | .storeIndU16, _, _, _ | .storeIndU32, _, _, _
  | .storeIndU64, _, _, _ | .loadIndU8, _, _, _ | .loadIndI8, _, _, _ | .loadIndU16, _, _, _
  | .loadIndI16, _, _, _ | .loadIndU32, _, _, _ | .loadIndI32, _, _, _
  | .loadIndU64, _, _, _ => none

@[csimp] theorem twoRegImmAlu_eq_twoRegImmAluFast : @twoRegImmAlu = @twoRegImmAluFast := by
  funext op a b x
  cases op <;> rfl

/-- `threeRegAlu`, restated so that its compiled code uses `bitwiseFast`. -/
def threeRegAluFast : ThreeRegOp → Nat → Nat → Nat → Nat
  | .add32, a, b, _ => sext 4 ((a + b) % two32)
  | .sub32, a, b, _ => sext 4 ((a + two32 - b % two32) % two32)
  | .mul32, a, b, _ => sext 4 ((a * b) % two32)
  | .divU32, a, b, _ => if b % two32 = 0 then two64 - 1 else sext 4 (a % two32 / (b % two32))
  | .divS32, a, b, _ =>
    let a' := Num.signed 4 (a % two32)
    let b' := Num.signed 4 (b % two32)
    if b' = 0 then two64 - 1
    else if a' = -2 ^ 31 ∧ b' = -1 then u64 a'
    else u64 (Num.divRtz a' b')
  | .remU32, a, b, _ =>
    if b % two32 = 0 then sext 4 (a % two32) else sext 4 (a % two32 % (b % two32))
  | .remS32, a, b, _ =>
    let a' := Num.signed 4 (a % two32)
    let b' := Num.signed 4 (b % two32)
    if a' = -2 ^ 31 ∧ b' = -1 then 0 else u64 (Num.smod a' b')
  | .shloL32, a, b, _ => sext 4 ((a * 2 ^ (b % 32)) % two32)
  | .shloR32, a, b, _ => sext 4 (a % two32 / 2 ^ (b % 32))
  | .sharR32, a, b, _ => u64 (Num.floorShift (Num.signed 4 (a % two32)) (b % 32))
  | .add64, a, b, _ => (a + b) % two64
  | .sub64, a, b, _ => (a + two64 - b) % two64
  | .mul64, a, b, _ => (a * b) % two64
  | .divU64, a, b, _ => if b = 0 then two64 - 1 else a / b
  | .divS64, a, b, _ =>
    if b = 0 then two64 - 1
    else if s64 a = -2 ^ 63 ∧ s64 b = -1 then a
    else u64 (Num.divRtz (s64 a) (s64 b))
  | .remU64, a, b, _ => if b = 0 then a else a % b
  | .remS64, a, b, _ =>
    if s64 a = -2 ^ 63 ∧ s64 b = -1 then 0 else u64 (Num.smod (s64 a) (s64 b))
  | .shloL64, a, b, _ => (a * 2 ^ (b % 64)) % two64
  | .shloR64, a, b, _ => a / 2 ^ (b % 64)
  | .sharR64, a, b, _ => u64 (Num.floorShift (s64 a) (b % 64))
  | .and, a, b, _ => bitwise (· && ·) a b
  | .xor, a, b, _ => bitwise (· ^^ ·) a b
  | .or, a, b, _ => bitwise (· || ·) a b
  | .mulUpperSS, a, b, _ => u64 ((s64 a * s64 b).fdiv (2 ^ 64))
  | .mulUpperUU, a, b, _ => a * b / two64
  | .mulUpperSU, a, b, _ => u64 ((s64 a * (b : Int)).fdiv (2 ^ 64))
  | .setLtU, a, b, _ => ofBool (a < b)
  | .setLtS, a, b, _ => ofBool (s64 a < s64 b)
  | .cmovIz, a, b, d => if b = 0 then a else d
  | .cmovNz, a, b, d => if b ≠ 0 then a else d
  | .rotL64, a, b, _ => Num.rotl 64 a b
  | .rotL32, a, b, _ => sext 4 (Num.rotl 32 a b)
  | .rotR64, a, b, _ => Num.rotr 64 a b
  | .rotR32, a, b, _ => sext 4 (Num.rotr 32 a b)
  | .andInv, a, b, _ => bitwise (fun x y => x && !y) a b
  | .orInv, a, b, _ => bitwise (fun x y => x || !y) a b
  | .xnor, a, b, _ => bitwise (fun x y => !(x ^^ y)) a b
  | .max, a, b, _ => u64 (max (s64 a) (s64 b))
  | .maxU, a, b, _ => max a b
  | .min, a, b, _ => u64 (min (s64 a) (s64 b))
  | .minU, a, b, _ => min a b

@[csimp] theorem threeRegAlu_eq_threeRegAluFast : @threeRegAlu = @threeRegAluFast := by
  funext op a b d
  cases op <;> rfl

end Exec

end PVM
