import Services.Bootstrap.Alloc.Rep
import PVM.Logic.Bits

/-!
# The allocator's arithmetic in the binary

The compiled code finds a size's bin with `leading_zero_bits_32`: for 0 < x < 2³², the count is
31 − ⌊log₂ x⌋ (`clz32`). `binDown_big` is `toBin` for sizes of 128 units or more in the form the
code computes it.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc

theorem bit_log2 {x : Nat} (hx : x ≠ 0) : Num.bit x (Nat.log2 x) = true := by
  have h1 := Nat.log2_self_le hx
  have h2 := Nat.lt_log2_self (n := x)
  have : x / 2 ^ Nat.log2 x = 1 := by
    have hp : 0 < 2 ^ Nat.log2 x := Nat.two_pow_pos _
    have hlt : x / 2 ^ Nat.log2 x < 2 := by
      rw [Nat.div_lt_iff_lt_mul hp]; rw [Nat.pow_succ] at h2; omega
    have hge : 1 ≤ x / 2 ^ Nat.log2 x := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    omega
  simp [Num.bit, this]

theorem bit_above {x j : Nat} (hj : Nat.log2 x < j) : Num.bit x j = false := by
  have h2 := Nat.lt_log2_self (n := x)
  have : x < 2 ^ j := Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hj)
  simp [Num.bit, Nat.div_eq_of_lt this]

/-- **`leading_zero_bits_32`** of a nonzero 32-bit value: 31 − ⌊log₂ x⌋. -/
theorem clz32 {x : Nat} (h0 : x ≠ 0) (h : x < 2 ^ 32) : Num.leadingZeros 32 x = 31 - Nat.log2 x := by
  have hl : Nat.log2 x < 32 := (Nat.log2_lt h0).mpr h
  unfold Num.leadingZeros
  have : (List.range 32).find? (fun i => Num.bit x (32 - 1 - i)) = some (31 - Nat.log2 x) := by
    rw [List.find?_range_eq_some]
    refine ⟨?_, by simp; omega, fun j hj => ?_⟩
    · rw [show 32 - 1 - (31 - Nat.log2 x) = Nat.log2 x by omega]; exact bit_log2 h0
    · rw [bit_above (by omega)]; rfl
  rw [this]; rfl

theorem or_mul128 (a m : Nat) (hm : m < 128) : a * 128 ||| m = a * 128 + m := by
  have := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := m) hm a
  rw [show (2 : Nat) ^ 7 = 128 by rfl, Nat.mul_comm 128 a] at this
  exact this.symm

/-- **`binDown`** of 128 units or more, as the code computes it from y = min(x, 2²⁵): the top
    seven bits after the leading one, plus 128 per bit position, less one. -/
theorem binDown_big {x : Nat} (h1 : 128 ≤ x) :
    binDown x = (min x 33554432) / 2 ^ (Nat.log2 (min x 33554432) - 7) % 128 +
      128 * (Nat.log2 (min x 33554432) - 6) - 1 := by
  unfold binDown toBin
  rw [maxSize_val]
  generalize hy : min x 33554432 = y
  have hy1 : 128 ≤ y := by omega
  have hy0 : y ≠ 0 := by omega
  have hl : 7 ≤ Nat.log2 y := (Nat.le_log2 hy0).mpr (by simpa using hy1)
  simp only [hy0, ↓reduceIte, mantissaBits, show ¬ y < 2 ^ 7 by simp; omega, log2, Bool.false_and]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show (2 : Nat) ^ 7 = 128 by rfl, or_mul128 _ _ (Nat.mod_lt _ (by decide))]
  rw [show Nat.log2 y - 6 = Nat.log2 y - 7 + 1 by omega]
  omega


/-- `or` of two 64-bit words is `|||`. -/
theorem bitwise_or_lor (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Exec.bitwise (· || ·) a b = a ||| b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_or]
  by_cases hi : i < 64
  · simp [hi]
  · have h1 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, h1, h2]

theorem bitwise_and_m127 (a : Nat) : Exec.bitwise (· && ·) a 127 = a % 128 := by
  rw [PVM.bitwise_and_low _ 127 7 (by decide) (by decide)]


/-- A 32-bit load of a value below 2³¹ sign-extends to itself. -/
theorem sxw4_small {v : Nat} (hv : v < 2147483648) : sxw 4 v = v := by
  simp only [sxw, Exec.u64, Num.unsigned, Num.signed, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]
  split <;> omega


/-- `and` of two 64-bit words is `&&&`. -/
theorem bitwise_and_land (a b : Nat) (hb : b < 2 ^ 64) : Exec.bitwise (· && ·) a b = a &&& b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_and]
  by_cases hi : i < 64
  · simp [hi]
  · have h2 : b.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hi, h2]

/-- **The code's bit-clearing mask**: −2 rotated left by k is every bit but bit k. -/
theorem rotl_clear (k : Nat) (hk : k < 64) :
    Num.rotl 64 18446744073709551614 k = (2 ^ 64 - 1) ^^^ 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Num.rotl, Num.testBit_ofBits, Num.bit_eq_testBit, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow, Nat.mod_eq_of_lt hk]
  by_cases hj : j < 64
  · have : (18446744073709551614 : Nat).testBit ((j + 64 - k) % 64) = decide ((j + 64 - k) % 64 ≠ 0) := by
      have hlt : (j + 64 - k) % 64 < 64 := Nat.mod_lt _ (by decide)
      generalize (j + 64 - k) % 64 = i at hlt ⊢
      rw [show (18446744073709551614 : Nat) = 2 ^ 64 - 1 - 1 by rfl]
      rw [show 2 ^ 64 - 1 - 1 = (2 ^ 64 - 1) ^^^ 1 by decide, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
        show (1 : Nat) = 2 ^ 0 by rfl, Nat.testBit_two_pow]
      by_cases hi : i = 0 <;> simp [hi, hlt] <;> omega
    rw [this]
    by_cases hjk : j = k
    · subst hjk; simp [hj]
    · have : (j + 64 - k) % 64 ≠ 0 := by omega
      simp [hj, this, hjk, Ne.symm hjk]
  · simp [hj]; omega

end Services.Bootstrap.Alloc
