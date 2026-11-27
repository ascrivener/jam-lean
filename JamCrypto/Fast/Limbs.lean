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

/-- A fact kept out of sight of `omega` (which uses every hypothesis it can read) until it is
    needed: the carry chains of the generated proofs. -/
def Hide (p : Prop) : Prop := p

/-- One step of a carry chain: if the inputs so far equal the outputs so far plus the carry c at
    weight B, and the next digit satisfies u + c = t + K·c', then the inputs including u equal the
    outputs including t plus the new carry c' at weight B·K. -/
theorem chain {I O c u t c' B K B' : Nat} (h1 : Hide (I = O + B * c)) (h2 : u + c = t + K * c')
    (hB : B * K = B') : Hide (I + B * u = (O + B * t) + B' * c') := by
  unfold Hide at *
  subst h1 hB
  have := congrArg (B * ·) h2
  simp only [Nat.mul_add] at this
  rw [Nat.mul_assoc]
  omega

/-- The first limb of a limb sum is below 2^29. -/
theorem bfirst {x : Nat} (hx : x < 2 ^ 29) : x * 2 ^ 0 < 2 ^ 29 := by simpa using hx

/-- A limb sum below B, extended by a limb below 2^29 at weight B, is below B·2^29. -/
theorem bstep {S x B C : Nat} (hS : S < B) (hx : x < 2 ^ 29) (hC : B * 2 ^ 29 = C) :
    S + x * B < C := by
  subst hC
  have : x * B ≤ (2 ^ 29 - 1) * B := Nat.mul_le_mul_right B (by omega)
  have h2 : (2 ^ 29 - 1) * B + B = B * 2 ^ 29 := by
    rw [Nat.sub_one_mul, Nat.mul_comm B]; have : B ≤ 2 ^ 29 * B := Nat.le_mul_of_pos_left B (by decide); omega
  omega

/-- The last carry of a Montgomery product is a limb: if V0·R = V1 + V2·p with V1 < p², V2 < R and
    p ≤ R, then V0 < 2p, so a carry c with c·K ≤ V0 is below 2^29 when 2p ≤ K·2^29. -/
theorem carry_lt {V0 V1 V2 c K R p : Nat} (e1 : V0 * R = V1 + V2 * p) (e3 : c * K ≤ V0)
    (h : V1 < p * p) (b : V2 < R) (hK : 2 * p ≤ K * 2 ^ 29) (hp : p ≤ R) : c < 2 ^ 29 := by
  have h1 : V2 * p ≤ R * p := Nat.mul_le_mul_right p (Nat.le_of_lt b)
  have h2 : p * p ≤ R * p := Nat.mul_le_mul_right p hp
  have h3 : V0 * R < (2 * p) * R := by
    rw [e1, Nat.mul_comm (2 * p) R, Nat.mul_comm 2 p, ← Nat.mul_assoc, Nat.mul_two, Nat.mul_comm R p]
    rw [Nat.mul_comm R p] at h1 h2
    omega
  have h4 : V0 < 2 * p := Nat.lt_of_mul_lt_mul_right h3
  have h5 : c * K < 2 ^ 29 * K := by rw [Nat.mul_comm (2 ^ 29) K]; omega
  exact Nat.lt_of_mul_lt_mul_right h5

/-- A limb subtraction with borrow out: the low 29 bits d and the borrow w of t − P satisfy
    d + P = t + 2^29·w (t, P limbs). -/
theorem sub_limb (t P : UInt64) (ht : t.toNat < 2 ^ 29) (hP : P.toNat < 2 ^ 29) :
    ((t - P) &&& 536870911).toNat + P.toNat + 0 = t.toNat + 2 ^ 29 * ((t - P) >>> 63).toNat ∧
      ((t - P) &&& 536870911).toNat < 2 ^ 29 ∧ ((t - P) >>> 63).toNat ≤ 1 := by
  rw [land_mask, shr63, UInt64.toNat_sub]
  have : t.toNat < P.toNat ∨ P.toNat ≤ t.toNat := Nat.lt_or_ge _ _
  rcases this with h | h
  · have e : (2 ^ 64 - P.toNat + t.toNat) % 2 ^ 64 = 2 ^ 64 - P.toNat + t.toNat := Nat.mod_eq_of_lt (by omega)
    rw [e]; omega
  · have e : (2 ^ 64 - P.toNat + t.toNat) % 2 ^ 64 = t.toNat - P.toNat := by omega
    rw [e]; omega

/-- A limb subtraction with borrow in and out: d + P + bw = t + 2^29·w for t − P − bw. -/
theorem sub_limb_b (t P bw : UInt64) (ht : t.toNat < 2 ^ 29) (hP : P.toNat < 2 ^ 29) (hb : bw.toNat ≤ 1) :
    ((t - P - bw) &&& 536870911).toNat + P.toNat + bw.toNat = t.toNat + 2 ^ 29 * ((t - P - bw) >>> 63).toNat ∧
      ((t - P - bw) &&& 536870911).toNat < 2 ^ 29 ∧ ((t - P - bw) >>> 63).toNat ≤ 1 := by
  rw [land_mask, shr63, UInt64.toNat_sub, UInt64.toNat_sub]
  have e1 : (2 ^ 64 - P.toNat + t.toNat) % 2 ^ 64 + 2 ^ 64 * (if t.toNat < P.toNat then 0 else 1)
      = 2 ^ 64 - P.toNat + t.toNat := by split <;> omega
  split at e1 <;> omega

/-- The conclusion of a Montgomery product: X·R + k·p = E + M·p gives X·R ≡ E (mod p). -/
theorem mod_of_eq {X R k p E M : Nat} (h : X * R + k * p = E + M * p) : X * R % p = E % p := by
  have := congrArg (· % p) h
  simpa [Nat.add_mul_mod_self_right] using this

end JamCrypto.Fast
