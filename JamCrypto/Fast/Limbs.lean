/-!
# Generic lemmas for the fixed-limb field arithmetic of `JamCrypto.Fast`

The generated field modules (`Fast/gen/field.py`) prove their operations from these: the `Nat`
value of the `UInt64` masks and shifts they use, and the bound on a product of two limbs.
-/

namespace JamCrypto.Fast

theorem land_mask (x : UInt64) : (x &&& 536870911).toNat = x.toNat % 2 ^ 29 := by
  rw [UInt64.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 29

theorem shr29 (x : UInt64) : (x >>> 29).toNat = x.toNat / 2 ^ 29 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem shr63 (x : UInt64) : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow]

theorem mul_lt29 {x y : Nat} (hx : x < 2 ^ 29) (hy : y < 2 ^ 29) : x * y < 2 ^ 58 := by
  have := Nat.mul_lt_mul_of_lt_of_le hx (Nat.le_of_lt hy) (by omega)
  omega

end JamCrypto.Fast
