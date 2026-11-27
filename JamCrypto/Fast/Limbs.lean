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

/-! ## Montgomery values

An element with limb value x stands for x·R⁻¹ mod p. With R·R⁻¹ ≡ 1 (mod p), the operations on
limb values give the field operations on these. -/

section Mont
variable {p R rInv : Nat}

theorem mod_mul_one (hR : R * rInv % p = 1) (y : Nat) : y * (R * rInv) % p = y % p := by
  rw [Nat.mul_mod, hR, Nat.mul_one, Nat.mod_mod]

theorem mont_mul_value (hR : R * rInv % p = 1) {x a b : Nat} (h : x * R % p = a * b % p) :
    x * rInv % p = (a * rInv % p) * (b * rInv % p) % p := by
  rw [← Nat.mul_mod, ← mod_mul_one hR (x * rInv)]
  have e1 : x * rInv * (R * rInv) = (x * R) * (rInv * rInv) := by grind
  have e2 : a * rInv * (b * rInv) = (a * b) * (rInv * rInv) := by grind
  rw [e1, e2, ← Nat.mod_mul_mod, h, Nat.mod_mul_mod]

theorem mont_add_value {x a b : Nat} (h : x = (a + b) % p) :
    x * rInv % p = (a * rInv % p + b * rInv % p) % p := by
  rw [h, Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod]

/-- (y + c) mod p = a with y, c < p determines y = (a + p − c) mod p. -/
theorem sub_unique {y c a : Nat} (hy : y < p) (hc : c < p) (h : (y + c) % p = a) :
    y = (a + p - c) % p := by
  subst h
  by_cases hlt : y + c < p
  · rw [Nat.mod_eq_of_lt hlt]
    have : y + c + p - c = y + p := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  · have h2 : (y + c) % p = y + c - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have : y + c - p + p - c = y := by omega
    rw [this, Nat.mod_eq_of_lt hy]

theorem mont_sub_value (hp : 0 < p) {x a b : Nat} (h : x = (a + p - b) % p) (hb : b < p) :
    x * rInv % p = (a * rInv % p + p - b * rInv % p) % p := by
  apply sub_unique (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)
  rw [← Nat.add_mod, ← Nat.add_mul, h]
  have e : ((a + p - b) % p + b) * rInv % p = ((a + p - b) + b) * rInv % p := by
    rw [Nat.add_mul, Nat.add_mul, Nat.add_mod, Nat.mod_mul_mod, ← Nat.add_mod]
  have : a + p - b + b = a + p := by omega
  rw [e, this, Nat.add_mul, Nat.add_mod, Nat.mul_mod p, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_mod]

/-- The Montgomery value determines a reduced limb value. -/
theorem mont_inj (hR : R * rInv % p = 1) {a b : Nat} (ha : a < p) (hb : b < p)
    (h : a * rInv % p = b * rInv % p) : a = b := by
  have h2 : a * rInv % p * R % p = b * rInv % p * R % p := by rw [h]
  rw [Nat.mod_mul_mod, Nat.mod_mul_mod] at h2
  have e : ∀ y, y * rInv * R % p = y % p := fun y => by
    rw [Nat.mul_assoc, Nat.mul_comm rInv R, mod_mul_one hR]
  rw [e, e, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  exact h2

/-- A reduced x with x·R ≡ a (mod p) is a·R⁻¹ mod p. -/
theorem mont_of_mul (hR : R * rInv % p = 1) {x a : Nat} (hx : x < p) (h : x * R % p = a % p) :
    x = a * rInv % p := by
  have : x * R * rInv % p = a * rInv % p := by rw [← Nat.mod_mul_mod, h, Nat.mod_mul_mod]
  rw [Nat.mul_assoc, mod_mul_one hR, Nat.mod_eq_of_lt hx] at this
  exact this

end Mont

/-- The sum of the first n base-2^29 digits of y is y mod 2^(29n). -/
def digitSum (y : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => digitSum y n + (y / (2 ^ 29) ^ n % 2 ^ 29) * (2 ^ 29) ^ n

theorem digitSum_eq (y n : Nat) : digitSum y n = y % (2 ^ 29) ^ n := by
  induction n with
  | zero => simp [digitSum, Nat.mod_one]
  | succ n ih => rw [digitSum, ih, @Nat.mod_pow_succ y (2 ^ 29) n, Nat.mul_comm ((2 ^ 29) ^ n)]

/-- Equal limb sums with limbs below 2^29 have equal low limbs and equal rests. -/
theorem limb_inj {x y X Y : Nat} (hx : x < 2 ^ 29) (hy : y < 2 ^ 29)
    (h : x + 2 ^ 29 * X = y + 2 ^ 29 * Y) : x = y ∧ X = Y := by omega

theorem mod29_mod64 (n : Nat) : n % 2 ^ 29 % 2 ^ 64 = n % 2 ^ 29 :=
  Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

/-! ## The conclusions of the generated proofs

From the summed carry chains of an operation, the result (one of the two candidate limb vectors,
chosen by the final borrow) is reduced and has the right value. Stated for arbitrary p and R, so
that the generated proofs only instantiate them. -/

theorem add_fin {A B T D c w p R : Nat} (e1 : T + R * c = A + B) (e2 : D + p = T + R * w)
    (hA : A < p) (hB : B < p) (hD : D < R) (hc : c ≤ 1) (hw : w ≤ 1) (hpR : 2 * p ≤ R) :
    ((¬c = 0 ∨ w = 0) → D < p ∧ D = (A + B) % p) ∧ (¬(¬c = 0 ∨ w = 0) → T < p ∧ T = (A + B) % p) := by
  have hc' : c = 0 ∨ c = 1 := by omega
  have hw' : w = 0 ∨ w = 1 := by omega
  rcases hc' with rfl | rfl <;> rcases hw' with rfl | rfl <;> simp only [Nat.mul_zero, Nat.mul_one] at e1 e2
  · refine ⟨fun _ => ?_, fun h => absurd (Or.inr rfl) h⟩
    have : p ≤ A + B := by omega
    rw [Nat.mod_eq_sub_mod this, Nat.mod_eq_of_lt (by omega)]; omega
  · refine ⟨fun h => by omega, fun _ => ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · omega
  · omega

theorem sub_fin {A B D E w c p R : Nat} (e1 : D + B = A + R * w) (e2 : E + R * c = D + p)
    (hA : A < p) (hB : B < p) (hD : D < R) (hE : E < R) (hw : w ≤ 1) (hc : c ≤ 1) (hpR : 2 * p ≤ R) :
    (w = 0 → D < p ∧ D = (A + p - B) % p) ∧ (¬w = 0 → E < p ∧ E = (A + p - B) % p) := by
  have hc' : c = 0 ∨ c = 1 := by omega
  have hw' : w = 0 ∨ w = 1 := by omega
  rcases hc' with rfl | rfl <;> rcases hw' with rfl | rfl <;> simp only [Nat.mul_zero, Nat.mul_one] at e1 e2
  · refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have e : A + p - B = (A - B) + p := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · omega
  · refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
    have e : A + p - B = (A - B) + p := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem mul_fin {T D E M w p R : Nat} (e1 : T * R = E + M * p) (e2 : D + p = T + R * w)
    (hE : E < p * p) (hM : M < R) (hD : D < R) (hw : w ≤ 1) (hpR : p ≤ R) :
    (w = 0 → D < p ∧ D * R % p = E % p) ∧ (¬w = 0 → T < p ∧ T * R % p = E % p) := by
  have h1 : M * p ≤ R * p := Nat.mul_le_mul_right p (Nat.le_of_lt hM)
  have h2 : p * p ≤ R * p := Nat.mul_le_mul_right p hpR
  have h3 : T * R < (2 * p) * R := by
    rw [e1, Nat.mul_comm (2 * p) R, Nat.mul_comm 2 p, ← Nat.mul_assoc, Nat.mul_two, Nat.mul_comm R p]
    rw [Nat.mul_comm R p] at h1 h2
    omega
  have hT : T < 2 * p := Nat.lt_of_mul_lt_mul_right h3
  have hw' : w = 0 ∨ w = 1 := by omega
  rcases hw' with rfl | rfl <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at e2
  · refine ⟨fun _ => ⟨by omega, mod_of_eq (k := R) (M := M) ?_⟩, fun h => absurd rfl h⟩
    rw [← e1, ← e2, Nat.add_mul, Nat.mul_comm p R]
  · refine ⟨fun h => absurd h (by omega), fun _ => ⟨by omega, mod_of_eq (k := 0) (M := M) ?_⟩⟩
    rw [Nat.zero_mul, Nat.add_zero, e1]

end JamCrypto.Fast
