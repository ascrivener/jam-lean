import Mathlib
import JAM.Erasure
import JAM.Theorems.CheckedIndex.Erasure

/-!
# GF(2¹⁶) as a Mathlib field (GP v0.8.1 §H.2)

The model computes in GF(2¹⁶) on natural numbers below 2¹⁶: bit i of a number is the
coefficient of αⁱ in the polynomial basis of 𝔽₂[x]/(x¹⁶ + x⁵ + x³ + x² + 1) (`JAM.Erasure.GF`).
Here that ring is `K := AdjoinRoot f` over `ZMod 2`, and `φ a` is the element whose coordinates
are the bits of `a`. We show:

* `φ` is additive for `^^^` and injective on numbers below 2¹⁶, and every element of `K` is some
  `φ a` with `a < 2¹⁶` (`K` has 2¹⁶ elements);
* multiplying by α is `xt`, the model's "shift left, reduce by `GF.poly`" step;
* α has order 2¹⁶ − 1. The four checks α^((2¹⁶−1)/p) ≠ 1 for p ∈ {3, 5, 17, 257} and
  α^(2¹⁶−1) = 1 are small kernel computations on numbers (`gpow`, square-and-multiply over
  `gmul`), by `decide`;
* hence every nonzero element is a power of α, so `K` is a field (`instField`).
-/

open Polynomial

namespace JAM.Erasure.Proofs

/-- x¹⁶ + x⁵ + x³ + x² + 1 over 𝔽₂ (GP §H.2). -/
noncomputable def f : (ZMod 2)[X] := X ^ 16 + X ^ 5 + X ^ 3 + X ^ 2 + 1

theorem f_monic : f.Monic := by unfold f; monicity!

theorem f_natDegree : f.natDegree = 16 := by unfold f; compute_degree!

theorem f_degree : f.degree = 16 := by
  rw [degree_eq_natDegree f_monic.ne_zero, f_natDegree]; rfl

theorem f_ne_zero : f ≠ 0 := f_monic.ne_zero

/-- GF(2¹⁶): 𝔽₂[x]/(f). Shown to be a field below (`instField`). -/
abbrev K := AdjoinRoot f

/-- α, the class of x. -/
noncomputable abbrev α : K := AdjoinRoot.root f

/-! ## Numbers as polynomials -/

/-- The polynomial whose coefficient of xⁱ is bit i of `a`. -/
noncomputable def toPoly (a : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range a, if a.testBit i then X ^ i else 0

/-- `if b then 1 else 0` in 𝔽₂. -/
def bitZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitZ_xor (a b : Bool) : bitZ (a ^^ b) = bitZ a + bitZ b := by
  cases a <;> cases b <;> decide

theorem bitZ_inj {a b : Bool} (h : bitZ a = bitZ b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem coeff_toPoly (a i : ℕ) : (toPoly a).coeff i = bitZ (a.testBit i) := by
  unfold toPoly bitZ
  rw [finsetSum_coeff]
  by_cases hi : i < a
  · rw [Finset.sum_eq_single i]
    · split <;> simp [coeff_X_pow]
    · intro j _ hj
      split <;> simp [coeff_X_pow, Ne.symm hj]
    · intro h; exact absurd (Finset.mem_range.2 hi) h
  · have hb : a.testBit i = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    rw [hb, Finset.sum_eq_zero]
    · simp
    · intro j hj
      have : j ≠ i := by simp at hj; omega
      split <;> simp [coeff_X_pow, Ne.symm this]

theorem toPoly_xor (a b : ℕ) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext i; simp only [coeff_add, coeff_toPoly, Nat.testBit_xor, bitZ_xor]

theorem toPoly_shiftLeft (a : ℕ) : toPoly (a <<< 1) = X * toPoly a := by
  ext i
  cases i with
  | zero => simp [coeff_toPoly, bitZ]
  | succ i => simp [coeff_toPoly, Nat.testBit_shiftLeft, coeff_X_mul]

theorem toPoly_zero : toPoly 0 = 0 := by simp [toPoly]

theorem toPoly_one : toPoly 1 = 1 := by
  ext i; rw [coeff_toPoly, coeff_one]
  cases i with
  | zero => simp [bitZ]
  | succ n =>
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 1 < 2)
      (Nat.le_self_pow (by omega) 2))]
    simp [bitZ]

theorem toPoly_two : toPoly 2 = X := by
  have := toPoly_shiftLeft 1
  rwa [toPoly_one, mul_one] at this

theorem toPoly_poly : toPoly GF.poly = f := by
  ext i
  rw [coeff_toPoly]
  unfold f
  simp only [coeff_add, coeff_X_pow, coeff_one]
  by_cases hi : i < 17
  · interval_cases i <;> decide
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (show GF.poly < 2 ^ 17 by decide)
      (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [bitZ, show i ≠ 16 by omega, show i ≠ 5 by omega, show i ≠ 3 by omega,
      show i ≠ 2 by omega, show i ≠ 0 by omega]

theorem degree_toPoly_lt {a : ℕ} (ha : a < 65536) : (toPoly a).degree < 16 := by
  show (toPoly a).degree < ((16 : ℕ) : WithBot ℕ)
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_toPoly, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha
    (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hm))]
  rfl

theorem toPoly_injective : Function.Injective toPoly := by
  intro a b h
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (·.coeff i) h
  simp only [coeff_toPoly] at this
  exact bitZ_inj this

/-! ## The embedding φ -/

/-- The element of `K` whose coordinates in 1, α, …, α¹⁵ are the bits of `a`. -/
noncomputable def φ (a : ℕ) : K := AdjoinRoot.mk f (toPoly a)

@[simp] theorem φ_zero : φ 0 = 0 := by simp [φ, toPoly_zero]

@[simp] theorem φ_one : φ 1 = 1 := by simp [φ, toPoly_one]

theorem φ_two : φ 2 = α := by simp [φ, toPoly_two]

theorem φ_xor (a b : ℕ) : φ (a ^^^ b) = φ a + φ b := by simp [φ, toPoly_xor]

theorem φ_poly : φ GF.poly = 0 := by simp [φ, toPoly_poly]

theorem φ_shiftLeft (a : ℕ) : φ (a <<< 1) = α * φ a := by simp [φ, toPoly_shiftLeft]

theorem φ_injOn {a b : ℕ} (ha : a < 65536) (hb : b < 65536) (h : φ a = φ b) : a = b := by
  unfold φ at h
  rw [AdjoinRoot.mk_eq_mk] at h
  have hd : (toPoly a - toPoly b).degree < f.degree := by
    rw [f_degree]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_toPoly_lt ha) (degree_toPoly_lt hb))
  exact toPoly_injective (sub_eq_zero.1 (eq_zero_of_dvd_of_degree_lt h hd))

/-! ## Multiplication by α -/

/-- The model's step "x ← x·2, reduced by `GF.poly`" (the body of `GF.expTable`'s loop). -/
def xt (x : ℕ) : ℕ := if x <<< 1 &&& 0x10000 ≠ 0 then x <<< 1 ^^^ GF.poly else x <<< 1

theorem φ_xt (x : ℕ) : φ (xt x) = α * φ x := by
  unfold xt; split <;> simp [φ_xor, φ_poly, φ_shiftLeft]

theorem and_bit16 (y : ℕ) : (y &&& 0x10000 ≠ 0) ↔ y.testBit 16 = true := by
  rw [show (0x10000 : ℕ) = 2 ^ 16 from rfl, Nat.and_two_pow]
  cases y.testBit 16 <;> simp

theorem lt_of_testBit {x : ℕ} (h : ∀ i, 16 ≤ i → x.testBit i = false) : x < 65536 :=
  Nat.lt_pow_two_of_testBit x h

theorem testBit_of_lt {x : ℕ} (hx : x < 65536) {i : ℕ} (hi : 16 ≤ i) : x.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx
    (by simpa using Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi))

theorem xor_lt {a b : ℕ} (ha : a < 65536) (hb : b < 65536) : a ^^^ b < 65536 :=
  lt_of_testBit fun i hi => by rw [Nat.testBit_xor, testBit_of_lt ha hi, testBit_of_lt hb hi]; rfl

theorem xt_lt {x : ℕ} (hx : x < 65536) : xt x < 65536 := by
  apply lt_of_testBit
  intro i hi
  have hp : ∀ j, 17 ≤ j → GF.poly.testBit j = false := fun j hj =>
    Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (show GF.poly < 2 ^ 17 by decide)
      (Nat.pow_le_pow_right (by norm_num) hj))
  have hs : ∀ j, 17 ≤ j → (x <<< 1).testBit j = false := fun j hj => by
    rw [Nat.testBit_shiftLeft, testBit_of_lt hx (by omega : 16 ≤ j - 1)]; simp
  unfold xt
  split
  · rename_i h
    rw [and_bit16] at h
    rw [Nat.testBit_xor]
    rcases Nat.lt_or_ge i 17 with h17 | h17
    · obtain rfl : i = 16 := by omega
      rw [h]; decide
    · rw [hs i h17, hp i h17]; rfl
  · rename_i h
    rw [and_bit16] at h
    rcases Nat.lt_or_ge i 17 with h17 | h17
    · obtain rfl : i = 16 := by omega
      simpa using h
    · exact hs i h17

theorem φ_iterate_xt (n : ℕ) : φ (xt^[n] 1) = α ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', φ_xt, ih, pow_succ, mul_comm]

theorem iterate_xt_lt (n : ℕ) : xt^[n] 1 < 65536 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Function.iterate_succ_apply']; exact xt_lt ih

/-! ## Multiplication and powers on numbers, for kernel checks -/

/-- Shift-and-add multiplication of 16-bit numbers in GF(2¹⁶): after n steps, the first component
    is the product of `a` with the low n bits of `b`, the second is `a`·αⁿ. -/
def gmulAux (a b : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, a)
  | n + 1 =>
    let r := gmulAux a b n
    (if b.testBit n then r.1 ^^^ r.2 else r.1, xt r.2)

/-- The product of two 16-bit numbers in GF(2¹⁶). -/
def gmul (a b : ℕ) : ℕ := (gmulAux a b 16).1

/-- Square-and-multiply over the low n bits of the exponent. -/
def gpowAux (a e : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, a)
  | n + 1 =>
    let r := gpowAux a e n
    (if e.testBit n then gmul r.1 r.2 else r.1, gmul r.2 r.2)

/-- aᵉ in GF(2¹⁶), for e < 2¹⁶. -/
def gpow (a e : ℕ) : ℕ := (gpowAux a e 16).1

/-- φ b as a sum over its low n bits. -/
theorem φ_eq_sum (b n : ℕ) (hb : b < 2 ^ n) :
    φ b = ∑ i ∈ Finset.range n, if b.testBit i then α ^ i else 0 := by
  have : toPoly b = ∑ i ∈ Finset.range n, if b.testBit i then X ^ i else 0 := by
    ext j
    rw [coeff_toPoly, finsetSum_coeff]
    by_cases hj : j < n
    · rw [Finset.sum_eq_single j]
      · unfold bitZ; split <;> simp [coeff_X_pow]
      · intro i _ hij; split <;> simp [coeff_X_pow, Ne.symm hij]
      · intro h; exact absurd (Finset.mem_range.2 hj) h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num)
        (by omega))), Finset.sum_eq_zero]
      · rfl
      · intro i hi
        have : i ≠ j := by simp at hi; omega
        split <;> simp [coeff_X_pow, Ne.symm this]
  rw [φ, this, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp

theorem gmulAux_spec (a b : ℕ) (ha : a < 65536) (n : ℕ) :
    (gmulAux a b n).1 < 65536 ∧ (gmulAux a b n).2 < 65536 ∧
    φ (gmulAux a b n).2 = α ^ n * φ a ∧
    φ (gmulAux a b n).1 = (∑ i ∈ Finset.range n, if b.testBit i then α ^ i else 0) * φ a := by
  induction n with
  | zero => simp [gmulAux, ha]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [gmulAux]
    refine ⟨?_, xt_lt h2, ?_, ?_⟩
    · split
      · exact xor_lt h1 h2
      · exact h1
    · rw [φ_xt, h3, pow_succ]; ring
    · rw [Finset.sum_range_succ]
      split
      · rename_i hb
        rw [φ_xor, h4, h3]; ring
      · rename_i hb
        rw [h4]; simp

theorem gmul_lt {a b : ℕ} (ha : a < 65536) : gmul a b < 65536 :=
  (gmulAux_spec a b ha 16).1

theorem φ_gmul {a b : ℕ} (ha : a < 65536) (hb : b < 65536) : φ (gmul a b) = φ a * φ b := by
  rw [gmul, (gmulAux_spec a b ha 16).2.2.2, φ_eq_sum b 16 hb, mul_comm]

theorem gpowAux_spec (a e : ℕ) (ha : a < 65536) (n : ℕ) :
    (gpowAux a e n).1 < 65536 ∧ (gpowAux a e n).2 < 65536 ∧
    φ (gpowAux a e n).2 = φ a ^ (2 ^ n) ∧ φ (gpowAux a e n).1 = φ a ^ (e % 2 ^ n) := by
  induction n with
  | zero => simp [gpowAux, ha, Nat.mod_one]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [gpowAux]
    refine ⟨?_, gmul_lt h2, ?_, ?_⟩
    · split
      · exact gmul_lt h1
      · exact h1
    · rw [φ_gmul h2 h2, h3, ← pow_add, pow_succ 2 n]; ring_nf
    · rw [Nat.mod_pow_succ]
      have hbit : e / 2 ^ n % 2 = if e.testBit n then 1 else 0 := by
        rw [Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ n) with h | h <;> simp [h]
      rw [hbit]
      split
      · rw [φ_gmul h1 h2, h4, h3, ← pow_add]; ring_nf
      · rw [h4]; simp

theorem φ_gpow {a e : ℕ} (ha : a < 65536) (he : e < 65536) : φ (gpow a e) = φ a ^ e := by
  rw [gpow, (gpowAux_spec a e ha 16).2.2.2, Nat.mod_eq_of_lt (by simpa using he)]

theorem gpow_lt {a e : ℕ} (ha : a < 65536) : gpow a e < 65536 := (gpowAux_spec a e ha 16).1

/-! ## The order of α -/

theorem α_pow_65535 : α ^ 65535 = 1 := by
  rw [← φ_two, ← φ_gpow (by decide) (by decide), show gpow 2 65535 = 1 by decide +kernel, φ_one]

theorem α_pow_ne_one {e : ℕ} (he : e < 65536) (h : gpow 2 e ≠ 1) : α ^ e ≠ 1 := by
  rw [← φ_two, ← φ_gpow (by decide) he, ← φ_one]
  exact fun h' => h (φ_injOn (gpow_lt (by decide)) (by decide) h')

theorem prime_dvd_65535 {p : ℕ} (hp : p.Prime) (h : p ∣ 65535) :
    p = 3 ∨ p = 5 ∨ p = 17 ∨ p = 257 := by
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  have h257 : Nat.Prime 257 := by norm_num
  rw [show (65535 : ℕ) = 3 * (5 * (17 * 257)) by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp h3).1 h)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp h5).1 h))
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp h17).1 h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp h257).1 h)))

/-- α has order 2¹⁶ − 1: x¹⁶ + x⁵ + x³ + x² + 1 is primitive, as GP §H.2 and `GF.expTable`
    assume. -/
theorem orderOf_α : orderOf α = 65535 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) α_pow_65535
  intro p hp hd
  rcases prime_dvd_65535 hp hd with rfl | rfl | rfl | rfl
  · exact α_pow_ne_one (by decide) (by decide +kernel)
  · exact α_pow_ne_one (by decide) (by decide +kernel)
  · exact α_pow_ne_one (by decide) (by decide +kernel)
  · exact α_pow_ne_one (by decide) (by decide +kernel)

/-! ## Every element is some φ a; K is a field -/

noncomputable instance : Fintype K :=
  Module.fintypeOfFintype (AdjoinRoot.powerBasis f_ne_zero).basis

theorem card_K : Fintype.card K = 65536 := by
  rw [Module.card_fintype (AdjoinRoot.powerBasis f_ne_zero).basis, Fintype.card_fin,
    AdjoinRoot.powerBasis_dim, f_natDegree, ZMod.card]; rfl

theorem φ_surj (x : K) : ∃ a < 65536, φ a = x := by
  have hc : ((Finset.range 65536).image φ).card = Fintype.card K := by
    rw [card_K, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb h
    exact φ_injOn (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  have := Finset.eq_univ_of_card _ hc ▸ Finset.mem_univ x
  simp only [Finset.mem_image, Finset.mem_range] at this
  obtain ⟨a, ha, h⟩ := this
  exact ⟨a, ha, h⟩

theorem zero_ne_one_K : (0 : K) ≠ 1 := by
  rw [← φ_zero, ← φ_one]; intro h; exact absurd (φ_injOn (by decide) (by decide) h) (by decide)

theorem α_pow_injOn {i j : ℕ} (hi : i < 65535) (hj : j < 65535) (h : α ^ i = α ^ j) : i = j :=
  pow_injOn_Iio_orderOf (by simp [orderOf_α, hi]) (by simp [orderOf_α, hj]) h

theorem α_pow_ne_zero (i : ℕ) : α ^ i ≠ 0 := by
  intro h
  have : α ^ 65535 = α ^ (65535 * (i + 1) - i) * α ^ i := by
    rw [← pow_add, Nat.sub_add_cancel (by nlinarith), pow_mul, α_pow_65535, one_pow]
  rw [α_pow_65535, h, mul_zero] at this
  exact zero_ne_one_K this.symm

/-- Every nonzero element of `K` is a power α^i with i < 2¹⁶ − 1. -/
theorem eq_α_pow {x : K} (hx : x ≠ 0) : ∃ i < 65535, α ^ i = x := by
  classical
  have hsub : (Finset.range 65535).image (α ^ ·) ⊆ Finset.univ.erase 0 := by
    intro y hy
    simp only [Finset.mem_image] at hy
    obtain ⟨i, _, rfl⟩ := hy
    exact Finset.mem_erase.2 ⟨α_pow_ne_zero i, Finset.mem_univ _⟩
  have hc : ((Finset.range 65535).image (α ^ ·)).card = (Finset.univ.erase (0 : K)).card := by
    rw [Finset.card_image_of_injOn, Finset.card_range, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, card_K]
    intro i hi j hj h
    exact α_pow_injOn (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) h
  have := (Finset.eq_of_subset_of_card_le hsub hc.ge) ▸
    Finset.mem_erase.2 ⟨hx, Finset.mem_univ x⟩
  simp only [Finset.mem_image, Finset.mem_range] at this
  exact this

theorem isField_K : IsField K where
  exists_pair_ne := ⟨0, 1, zero_ne_one_K⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := eq_α_pow hx
    refine ⟨α ^ (65535 - i), ?_⟩
    rw [← pow_add, Nat.add_sub_cancel' hi.le, α_pow_65535]

/-- GF(2¹⁶) is a field. -/
noncomputable instance instField : Field K := isField_K.toField

end JAM.Erasure.Proofs
