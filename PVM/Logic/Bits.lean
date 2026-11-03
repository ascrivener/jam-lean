import PVM.Exec

/-!
# Bitwise operations on symbolic values

`bitwise f a b` is `ofBits 64` of the bitwise `f`. For a symbolic `a` and a literal `b` of a
simple shape (one bit, a low mask, or the complement of a high mask), these lemmas turn it into
arithmetic that `omega` can decide.
-/

namespace PVM

open Num Exec

theorem Num.bit_eq_testBit (x i : Nat) : Num.bit x i = x.testBit i := by
  simp only [Num.bit, Nat.testBit_eq_decide_div_mod_eq]

private theorem foldr_add (h : Nat → Nat) (a : Nat) (l : List Nat) :
    l.foldr (fun i acc => acc + h i) a = a + l.foldr (fun i acc => acc + h i) 0 := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons, ih]; omega

theorem Num.ofBits_succ (w : Nat) (f : Nat → Bool) :
    Num.ofBits (w + 1) f = 2 ^ w * (if f w then 1 else 0) + Num.ofBits w f := by
  simp only [Num.ofBits, List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil]
  rw [foldr_add]
  split <;> simp <;> omega

theorem Num.ofBits_lt (w : Nat) (f : Nat → Bool) : Num.ofBits w f < 2 ^ w := by
  induction w with
  | zero => simp [Num.ofBits]
  | succ w ih =>
    rw [Num.ofBits_succ, Nat.pow_succ]
    split <;> omega

theorem Num.testBit_ofBits (w : Nat) (f : Nat → Bool) (i : Nat) :
    (Num.ofBits w f).testBit i = (decide (i < w) && f i) := by
  induction w with
  | zero => simp [Num.ofBits]
  | succ w ih =>
    rw [Num.ofBits_succ, Nat.testBit_two_pow_mul_add _ (Num.ofBits_lt w f)]
    by_cases h : i < w
    · simp [h, ih, show i < w + 1 by omega]
    · by_cases hw : i = w
      · subst hw; cases f i <;> simp
      · have : w < i := by omega
        simp only [h, ite_false, show ¬ i < w + 1 by omega, decide_false, Bool.false_and]
        split
        · exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
        · simp

/-- `a &&& 2^k`: one bit of `a` (the `and_imm` tests of a leading-ones count). The literal `m` is
    the pattern, so `k` is given at the use site. -/
theorem bitwise_and_pow2 (a m k : Nat) (hm : m = 2 ^ k) (hk : k < 64) :
    bitwise (· && ·) a m = if a / m % 2 = 1 then m else 0 := by
  subst hm
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_two_pow]
  by_cases hik : k = i
  · subst hik
    have : a.testBit k = decide (a / 2 ^ k % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
    split <;> simp_all [Nat.testBit_two_pow]
  · split <;> simp [hik, Nat.testBit_two_pow]

/-- `a & ~m` for `m = 2^64 − 2^s`, the high-bits mask: the low `s` bits of `a` (an `and_inv`
    that strips a length prefix). -/
theorem bitwise_andInv_high (a m s : Nat) (hm : m + 2 ^ s = 2 ^ 64) (hs : s ≤ 64) :
    bitwise (fun x y => x && !y) a m = a % 2 ^ s := by
  have hm' : m = 2 ^ 64 - ((2 ^ s - 1) + 1) := by
    have := Nat.two_pow_pos s; omega
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_mod_two_pow, hm']
  rw [Nat.testBit_two_pow_sub_succ (by have := Nat.pow_le_pow_right (by decide : 0 < 2) hs; omega)]
  simp only [Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < s <;> by_cases h2 : i < 64 <;> simp [h1, h2] <;> omega

/-- `a &&& (2^j − 1)`, the low mask: `a mod 2^j`. -/
theorem bitwise_and_low (a m j : Nat) (hm : m + 1 = 2 ^ j) (hj : j ≤ 64) :
    bitwise (· && ·) a m = a % 2 ^ j := by
  have hm' : m = 2 ^ j - 1 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_mod_two_pow, hm',
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : i < j <;> by_cases h2 : i < 64 <;> simp [h1, h2] <;> omega


/-! ## Sign-extended octets

`sign_extend_8` of an octet `b ≥ 128` is `b + (2^64 − 256)`. Kept folded as `sx8 b`, it never puts
a 2^64-size constant next to a symbolic value, which the kernel would otherwise have to reduce in
unary when checking a step. The lemmas give the facts the code uses. -/

/-- 𝒳₁ of an octet (GP eq. `signedextension`), folded. -/
def sx8 (b : Nat) : Nat := if b < 128 then b else b + 18446744073709551360

theorem twoRegAlu_signExtend8 (a : Nat) : Exec.twoRegAlu .signExtend8 a = sx8 (a % 256) := by
  simp only [Exec.twoRegAlu, Exec.u64, Num.unsigned, Num.signed, sx8, Nat.reducePow, Nat.reduceMul,
    Nat.reduceSub]
  split <;> (try split) <;> omega

theorem sx8_of_lt (b : Nat) (h : b < 128) : sx8 b = b := by simp [sx8, h]

theorem sx8_mod_two64 (b : Nat) (h : b < 256) : sx8 b % 18446744073709551616 = sx8 b := by
  unfold sx8; split <;> omega

theorem signed8_sx8 (b : Nat) (h1 : 128 ≤ b) (h2 : b < 256) :
    Num.signed 8 (sx8 b) = (b : Int) - 256 := by
  simp only [Num.signed, sx8, Nat.reducePow, Nat.reduceMul, Nat.reduceSub]
  split <;> (try split) <;> omega

theorem sx8_div1_mod2 (b : Nat) (h : b < 256) : sx8 b / 1 % 2 = b / 1 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div2_mod2 (b : Nat) (h : b < 256) : sx8 b / 2 % 2 = b / 2 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div4_mod2 (b : Nat) (h : b < 256) : sx8 b / 4 % 2 = b / 4 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div8_mod2 (b : Nat) (h : b < 256) : sx8 b / 8 % 2 = b / 8 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div16_mod2 (b : Nat) (h : b < 256) : sx8 b / 16 % 2 = b / 16 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div32_mod2 (b : Nat) (h : b < 256) : sx8 b / 32 % 2 = b / 32 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div64_mod2 (b : Nat) (h : b < 256) : sx8 b / 64 % 2 = b / 64 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_div128_mod2 (b : Nat) (h : b < 256) : sx8 b / 128 % 2 = b / 128 % 2 := by
  unfold sx8; split <;> omega

theorem sx8_mod1 (b : Nat) (h : b < 256) : sx8 b % 1 = b % 1 := by
  unfold sx8; split <;> omega

theorem sx8_mod2 (b : Nat) (h : b < 256) : sx8 b % 2 = b % 2 := by
  unfold sx8; split <;> omega

theorem sx8_mod4 (b : Nat) (h : b < 256) : sx8 b % 4 = b % 4 := by
  unfold sx8; split <;> omega

theorem sx8_mod8 (b : Nat) (h : b < 256) : sx8 b % 8 = b % 8 := by
  unfold sx8; split <;> omega

theorem sx8_mod16 (b : Nat) (h : b < 256) : sx8 b % 16 = b % 16 := by
  unfold sx8; split <;> omega

theorem sx8_mod32 (b : Nat) (h : b < 256) : sx8 b % 32 = b % 32 := by
  unfold sx8; split <;> omega

theorem sx8_mod64 (b : Nat) (h : b < 256) : sx8 b % 64 = b % 64 := by
  unfold sx8; split <;> omega

theorem sx8_mod128 (b : Nat) (h : b < 256) : sx8 b % 128 = b % 128 := by
  unfold sx8; split <;> omega

theorem sx8_mod256 (b : Nat) (h : b < 256) : sx8 b % 256 = b % 256 := by
  unfold sx8; split <;> omega

theorem sx8_lt_two63 (b : Nat) (h : b < 256) : (sx8 b < 9223372036854775808) = (b < 128) := by
  unfold sx8; split <;> simp <;> omega

theorem sx8_cast_sub_lt (b : Nat) (h : b < 256) :
    (((sx8 b : Nat) : Int) - 18446744073709551616 < 0) = True := by
  unfold sx8; split <;> simp <;> omega

end PVM
