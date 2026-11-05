import Services.Bootstrap.DecodeU16

/-!
# `memcpy` in bootstrap for any length (in progress)

The compiler's `memcpy` at 68729 for n ≥ 16: a head loop aligning the destination (68763), then an
aligned word loop (68804) or, when the source is misaligned by m, a loop splicing the high 8 − m
octets of one aligned source word with the low m of the next (68989), then the byte loop at 68840.
This file holds the arithmetic of the splice (`encodeLE_splice`) and the loops' summaries.
-/

namespace PVM

open Num Exec

/-- Or of a value below 2^k and a multiple of 2^k (below 2^64) is their sum. -/
theorem bitwise_or_add (x y k : Nat) (hk : k ≤ 64) (hx : x < 2 ^ k) (hy : y < 2 ^ (64 - k)) :
    bitwise (· || ·) x (y * 2 ^ k) = x + y * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 : x + y * 2 ^ k = 2 ^ k * y + x := by rw [Nat.mul_comm]; omega
  have e2 : y * 2 ^ k = 2 ^ k * y + 0 := by rw [Nat.mul_comm]; omega
  simp only [bitwise, Num.testBit_ofBits, Num.bit_eq_testBit]
  rw [e1, e2, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos k)]
  by_cases hi : i < k
  · simp only [hi, ite_true, Nat.zero_testBit, Bool.or_false]
    simp only [show i < 64 by omega, decide_true, Bool.true_and]
  · have hxi : x.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [hi, ite_false, hxi, Bool.false_or]
    by_cases h64 : i < 64
    · simp [h64]
    · have : y.testBit (i - k) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h64, this]

theorem decodeLE_append (l₁ l₂ : List UInt8) :
    Num.decodeLE (l₁ ++ l₂) = Num.decodeLE l₁ + 256 ^ l₁.length * Num.decodeLE l₂ := by
  induction l₁ with
  | nil => simp [Num.decodeLE]
  | cons b l ih =>
    simp only [List.cons_append, Num.decodeLE, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length)]
    omega

theorem decodeLE_lt (l : List UInt8) : Num.decodeLE l < 256 ^ l.length := by
  induction l with
  | nil => simp [Num.decodeLE]
  | cons b l ih =>
    simp only [Num.decodeLE, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt
    omega

theorem encodeLE_decodeLE (l : List UInt8) : Num.encodeLE l.length (Num.decodeLE l) = l := by
  induction l with
  | nil => simp [Num.encodeLE]
  | cons b l ih =>
    have hb := b.toNat_lt
    simp only [List.length_cons, Num.encodeLE, Num.decodeLE]
    rw [show (b.toNat + 256 * Num.decodeLE l) % 256 = b.toNat by omega,
      show (b.toNat + 256 * Num.decodeLE l) / 256 = Num.decodeLE l by omega, ih, UInt8.ofNat_toNat]

theorem encodeLE_mod (l v : Nat) : Num.encodeLE l (v % 256 ^ l) = Num.encodeLE l v := by
  induction l generalizing v with
  | zero => simp [Num.encodeLE]
  | succ l ih =>
    simp only [Num.encodeLE]
    rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, ih,
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _)]

/-- The misaligned word of `memcpy`: the high 8 − m octets of `a`, then the low m of `b`. -/
theorem encodeLE_splice (a b : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (m : Nat)
    (hm : 0 < m ∧ m < 8) :
    Num.encodeLE 8 (bitwise (· || ·) (Num.decodeLE a / 2 ^ (8 * m))
      (Num.decodeLE b * 2 ^ (64 - 8 * m) % 18446744073709551616)) = a.drop m ++ b.take m := by
  have hA : Num.decodeLE a = Num.decodeLE (a.take m) + 256 ^ m * Num.decodeLE (a.drop m) := by
    conv => lhs; rw [← List.take_append_drop m a]
    rw [decodeLE_append, List.length_take, ha, Nat.min_eq_left (by omega)]
  have hB : Num.decodeLE b = Num.decodeLE (b.take m) + 256 ^ m * Num.decodeLE (b.drop m) := by
    conv => lhs; rw [← List.take_append_drop m b]
    rw [decodeLE_append, List.length_take, hb, Nat.min_eq_left (by omega)]
  have p256 : ∀ j, (256 : Nat) ^ j = 2 ^ (8 * j) := fun j => by rw [Nat.pow_mul]
  have hat := decodeLE_lt (a.take m)
  have had := decodeLE_lt (a.drop m)
  have hbt := decodeLE_lt (b.take m)
  rw [List.length_take, ha, Nat.min_eq_left (by omega)] at hat
  rw [List.length_drop, ha] at had
  rw [List.length_take, hb, Nat.min_eq_left (by omega)] at hbt
  rw [p256] at hat had hbt
  rw [show 8 * (8 - m) = 64 - 8 * m by omega] at had
  have hH : Num.decodeLE a / 2 ^ (8 * m) = Num.decodeLE (a.drop m) := by
    rw [hA, p256, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hat, Nat.zero_add]
  have h64 : (2 : Nat) ^ 64 = 2 ^ (8 * m) * 2 ^ (64 - 8 * m) := by rw [← Nat.pow_add]; congr 1; omega
  have hL : Num.decodeLE b * 2 ^ (64 - 8 * m) % 18446744073709551616 =
      Num.decodeLE (b.take m) * 2 ^ (64 - 8 * m) := by
    rw [show (18446744073709551616 : Nat) = 2 ^ 64 by rfl, h64, Nat.mul_mod_mul_right, hB, p256,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbt]
  rw [hH, hL, bitwise_or_add _ _ _ (by omega) had
    (by rw [show 64 - (64 - 8 * m) = 8 * m by omega]; exact hbt)]
  have hs := Services.Bootstrap.Num.encodeLE_split (8 - m) m (Num.decodeLE (a.drop m) + Num.decodeLE (b.take m) * 2 ^ (64 - 8 * m))
  rw [show 8 - m + m = 8 by omega] at hs
  rw [hs, ← encodeLE_mod (8 - m), p256, show 8 * (8 - m) = 64 - 8 * m by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt had,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt had, Nat.zero_add]
  have e1 := encodeLE_decodeLE (a.drop m)
  have e2 := encodeLE_decodeLE (b.take m)
  rw [List.length_drop, ha] at e1
  rw [List.length_take, hb, Nat.min_eq_left (by omega)] at e2
  rw [e1, e2]

end PVM

namespace PVM

theorem bitwise_or_comm (a b : Nat) : Exec.bitwise (· || ·) a b = Exec.bitwise (· || ·) b a := by
  simp only [Exec.bitwise, Bool.or_comm]

theorem bitwise_lt (f : Bool → Bool → Bool) (a b : Nat) : Exec.bitwise f a b < 18446744073709551616 :=
  Num.ofBits_lt 64 _

theorem bitwise_mod64 (f : Bool → Bool → Bool) (a b : Nat) :
    Exec.bitwise f a b % 18446744073709551616 = Exec.bitwise f a b := Nat.mod_eq_of_lt (bitwise_lt f a b)

theorem readN_drop (μ : Memory) (a n m : Nat) : (μ.readN a n).drop m = μ.readN (a + m) (n - m) := by
  apply List.ext_getElem
  · simp [Memory.length_readN]
  · intro j h1 h2
    simp only [List.getElem_drop, Memory.readN, List.getElem_map, List.getElem_range, Nat.add_assoc]

theorem readN_take (μ : Memory) (a n m : Nat) (h : m ≤ n) : (μ.readN a n).take m = μ.readN a m := by
  apply List.ext_getElem
  · simp [Memory.length_readN]; omega
  · intro j h1 h2
    simp only [List.getElem_take, Memory.readN, List.getElem_map, List.getElem_range]

end PVM

namespace Services.Bootstrap

open PVM Services.Bootstrap.Code

set_option maxHeartbeats 8000000

variable {X : Type} {R : HostRel X}

/-- One iteration of the head loop at 68763: copy the octet at `s` to `d`, count down. -/
theorem memcpy_head_iter {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (k s d : Nat) (hC : ω[12] = UInt64.ofNat (k + 1)) (hS : ω[5] = UInt64.ofNat s)
    (hD : ω[6] = UInt64.ofNat d) (hk : k + 1 < 16) (hs : s + k + 1 < 4294967296)
    (hd : d + k + 1 < 4294967296) (hr : μ.readable s = true) (hw : μ.writable d = true) :
    ∃ ω', FreeStepsH p R 68763 ω μ x 68777 ω' (μ.writeN d [μ.read s]) x 6 ∧
      ω'[12] = UInt64.ofNat k ∧ ω'[5] = UInt64.ofNat (s + 1) ∧ ω'[6] = UInt64.ofNat (d + 1) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 10, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run =>
      apply FreeStepsH.step_decode (d_68763 (p := p) (P := P))
      · pvm_simp []
      apply FreeStepsH.step_decode (d_68764 (p := p) (P := P))
      · pvm_simp [hS, hr]
      apply FreeStepsH.step_decode (d_68766 (p := p) (P := P))
      · pvm_simp [hC]
      apply FreeStepsH.step_decode (d_68769 (p := p) (P := P))
      · pvm_simp [hD, hw]
      apply FreeStepsH.step_decode (d_68771 (p := p) (P := P))
      · pvm_simp [hD]
      apply FreeStepsH.step_decode (d_68774 (p := p) (P := P))
      · pvm_simp [hS]
      exact FreeStepsH.refl
  case post =>
    refine ⟨?r9, ?r8, ?r10, fun j hj => ?rest⟩
    case rest =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3, h4⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3, h4]
    all_goals simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some']

/-- **The head loop of `memcpy`** (68763 … 68777), aligning the destination: with ω₁₂ = k + 1,
    ω₅ = s and ω₆ = d, it copies the k + 1 octets at `s` to `d` (the ranges disjoint) and leaves
    for 68780, changing only ω₅, ω₆, ω₁₀, ω₁₂. -/
theorem memcpy_head_loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) : ∀ (k : Nat) (ω : Regs)
    (μ : Memory) (s d : Nat), ω[12] = UInt64.ofNat (k + 1) → ω[5] = UInt64.ofNat s →
    ω[6] = UInt64.ofNat d → k + 1 < 16 → s + k + 1 < 4294967296 → d + k + 1 < 4294967296 →
    (d + k + 1 ≤ s ∨ s + k + 1 ≤ d) → (∀ a, s ≤ a → a ≤ s + k → μ.readable a = true) →
    (∀ a, d ≤ a → a ≤ d + k → μ.writable a = true) →
    ∃ ω', FreeStepsH p R 68763 ω μ x 68780 ω' (μ.writeN d (μ.readN s (k + 1))) x (7 * (k + 1)) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 10, 12] → ω'[j] = ω[j] := by
  intro k
  induction k with
  | zero =>
    intro ω μ s d hC hS hD hk hs hd _ hr hw
    obtain ⟨ω₁, hrun, hC', _, _, hfr⟩ := memcpy_head_iter (p := p) (P := P) (R := R) ω μ x 0 s d hC hS hD hk hs hd
      (hr s (by omega) (by omega)) (hw d (by omega) (by omega))
    refine ⟨regsNF ω₁ [], ?_, hfr⟩
    rw [show μ.readN s (0 + 1) = [μ.read s] by simp [Memory.readN]]
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68777 (p := p) (P := P))
    · pvm_simp [hC']
    exact FreeStepsH.refl
  | succ k ih =>
    intro ω μ s d hC hS hD hk hs hd hdj hr hw
    obtain ⟨ω₁, hrun, hC', hS', hD', hfr⟩ := memcpy_head_iter (p := p) (P := P) (R := R) ω μ x (k + 1) s d hC hS hD hk
      hs hd (hr s (by omega) (by omega)) (hw d (by omega) (by omega))
    obtain ⟨ω₂, hrun₂, hfr₂⟩ := ih (regsNF ω₁ []) (μ.writeN d [μ.read s]) (s + 1) (d + 1) hC' hS'
      hD' (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [Memory.readable_writeN]; exact hr a (by omega) (by omega))
      (fun a h1 h2 => by rw [Memory.writable_writeN]; exact hw a (by omega) (by omega))
    refine ⟨ω₂, ?_, fun j hj => (hfr₂ j hj).trans (hfr j hj)⟩
    have hmem : μ.writeN d (μ.readN s (k + 1 + 1)) =
        (μ.writeN d [μ.read s]).writeN (d + 1) ((μ.writeN d [μ.read s]).readN (s + 1) (k + 1)) := by
      rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega)
        (by simp [two32]; omega), Services.Bootstrap.readN_succ]
      rfl
    rw [hmem]
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68777 (p := p) (P := P))
    · pvm_simp [hC']
    exact hrun₂

theorem writeN_append (μ : Memory) (d : Nat) (l₁ l₂ : List UInt8) :
    μ.writeN d (l₁ ++ l₂) = (μ.writeN d l₁).writeN (d + l₁.length) l₂ := by
  induction l₁ generalizing μ d with
  | nil => simp [Memory.writeN]
  | cons b l ih =>
    simp only [List.cons_append, Memory.writeN, ih, List.length_cons]
    congr 1; omega

/-- One iteration of the aligned word loop at 68804: copy the word at `s` to `d`. -/
theorem memcpy_word_iter {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (s d e : Nat) (h8 : ω[8] = UInt64.ofNat s) (h11 : ω[11] = UInt64.ofNat d) (h10 : ω[10] = UInt64.ofNat e)
    (hs : s + 8 < 4294967296) (hd : d + 8 < 4294967296) (he : e < 4294967296)
    (hr : ∀ a, s ≤ a → a < s + 8 → μ.readable a = true) (hw : ∀ a, d ≤ a → a < d + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 68804 ω μ x 68815 ω' (μ.writeN d (μ.readN s 8)) x 5 ∧
      ω'[8] = UInt64.ofNat (s + 8) ∧ ω'[11] = UInt64.ofNat (d + 8) ∧ ω'[10] = UInt64.ofNat e ∧
      ∀ j : Fin 13, j.val ∉ [6, 8, 11] → ω'[j] = ω[j] := by
  have hl := encodeLE_decodeLE (μ.readN s 8)
  have hlt := decodeLE_lt (μ.readN s 8)
  rw [Memory.length_readN] at hl hlt
  generalize Num.decodeLE (μ.readN s 8) = v at hl hlt
  rw [← hl]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run =>
      apply FreeStepsH.step_decode (d_68804 (p := p) (P := P))
      · pvm_simp []
      apply FreeStepsH.step_decode (d_68805 (p := p) (P := P))
      · pvm_simp [h8, hr, ← hl, hlt]
      apply FreeStepsH.step_decode (d_68807 (p := p) (P := P))
      · pvm_simp [h11, hw]
      apply FreeStepsH.step_decode (d_68809 (p := p) (P := P))
      · pvm_simp [h11]
      apply FreeStepsH.step_decode (d_68812 (p := p) (P := P))
      · pvm_simp [h8]
      exact FreeStepsH.refl
  case post =>
    refine ⟨?r8, ?r11, ?r10, fun j hj => ?rest⟩
    case rest =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3]
    all_goals simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none, h10]

/-- **The aligned word loop of `memcpy`** (68804 … 68815): with ω₈ = s, ω₁₁ = d and ω₁₀ = d + 8(k + 1),
    it copies the 8(k + 1) octets at `s` to `d` word by word and leaves for 68818, changing only
    ω₆, ω₈, ω₁₁. -/
theorem memcpy_word_loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) : ∀ (k : Nat) (ω : Regs)
    (μ : Memory) (s d : Nat), ω[8] = UInt64.ofNat s → ω[11] = UInt64.ofNat d →
    ω[10] = UInt64.ofNat (d + 8 * (k + 1)) → s + 8 * (k + 1) < 4294967296 → d + 8 * (k + 1) < 4294967296 →
    (d + 8 * (k + 1) ≤ s ∨ s + 8 * (k + 1) ≤ d) →
    (∀ a, s ≤ a → a < s + 8 * (k + 1) → μ.readable a = true) →
    (∀ a, d ≤ a → a < d + 8 * (k + 1) → μ.writable a = true) →
    ∃ ω', FreeStepsH p R 68804 ω μ x 68818 ω' (μ.writeN d (μ.readN s (8 * (k + 1)))) x (6 * (k + 1)) ∧
      ω'[8] = UInt64.ofNat (s + 8 * (k + 1)) ∧ ω'[11] = UInt64.ofNat (d + 8 * (k + 1)) ∧
      ∀ j : Fin 13, j.val ∉ [6, 8, 11] → ω'[j] = ω[j] := by
  intro k
  induction k with
  | zero =>
    intro ω μ s d h8 h11 h10 hs hd _ hr hw
    obtain ⟨ω₁, hrun, h8', h11', h10', hfr⟩ := memcpy_word_iter (p := p) (P := P) (R := R) ω μ x s d
      (d + 8 * (0 + 1)) h8 h11 h10 (by omega) (by omega) (by omega)
      (fun a h1 h2 => hr a h1 (by omega)) (fun a h1 h2 => hw a h1 (by omega))
    refine ⟨regsNF ω₁ [], ?_, h8', h11', hfr⟩
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68815 (p := p) (P := P))
    · pvm_simp [h11', h10']
    exact FreeStepsH.refl
  | succ k ih =>
    intro ω μ s d h8 h11 h10 hs hd hdj hr hw
    obtain ⟨ω₁, hrun, h8', h11', h10', hfr⟩ := memcpy_word_iter (p := p) (P := P) (R := R) ω μ x s d
      (d + 8 * (k + 1 + 1)) h8 h11 h10 (by omega) (by omega) (by omega)
      (fun a h1 h2 => hr a h1 (by omega)) (fun a h1 h2 => hw a h1 (by omega))
    obtain ⟨ω₂, hrun₂, h8₂, h11₂, hfr₂⟩ := ih (regsNF ω₁ []) (μ.writeN d (μ.readN s 8)) (s + 8) (d + 8) h8' h11'
      (h10'.trans (by congr 1; omega)) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [Memory.readable_writeN]; exact hr a (by omega) (by omega))
      (fun a h1 h2 => by rw [Memory.writable_writeN]; exact hw a (by omega) (by omega))
    refine ⟨ω₂, ?_, by rw [h8₂]; congr 1; omega, by rw [h11₂]; congr 1; omega,
      fun j hj => (hfr₂ j hj).trans (hfr j hj)⟩
    have hmem : μ.writeN d (μ.readN s (8 * (k + 1 + 1))) =
        (μ.writeN d (μ.readN s 8)).writeN (d + 8) ((μ.writeN d (μ.readN s 8)).readN (s + 8) (8 * (k + 1))) := by
      rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp [Memory.length_readN]; omega)
        (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega)]
      have := Memory.readN_split μ s 8 (8 * (k + 1))
      rw [show 8 + 8 * (k + 1) = 8 * (k + 1 + 1) by omega] at this
      rw [this, writeN_append, Memory.length_readN]
    rw [hmem]
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68815 (p := p) (P := P))
    · pvm_simp [h11', h10']
    exact hrun₂

/-- One iteration of the misaligned loop at 68989. -/
theorem memcpy_shift_iter {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A d e sp m : Nat) (hm : 0 < m ∧ m < 8) (hpw : pw < 18446744073709551616)
    (h4 : ω[4] = UInt64.ofNat pw) (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * m))
    (h11 : ω[11] = UInt64.ofNat d) (h10 : ω[10] = UInt64.ofNat e) (h1 : ω[1] = UInt64.ofNat sp)
    (hA : A + 16 < 4294967296) (hd : d + 16 < 4294967296) (he : e < 4294967296) (hsp : sp + 16 < 4294967296)
    (hsd : sp + 16 ≤ d ∨ d + 8 ≤ sp) (hsA : sp + 16 ≤ A + 8 ∨ A + 16 ≤ sp)
    (hT : μ.readN sp 8 = Num.encodeLE 8 (64 - 8 * m))
    (hr : ∀ a, A + 8 ≤ a → a < A + 16 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 16 → μ.writable a = true)
    (hw : ∀ a, d ≤ a → a < d + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 68989 ω μ x 69027 ω'
      ((μ.writeN (sp + 8) (Num.encodeLE 8 (pw / 2 ^ (8 * m)))).writeN d
        ((Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m)) x 15 ∧
      ω'[4] = UInt64.ofNat (Num.decodeLE (μ.readN (A + 8) 8)) ∧ ω'[6] = UInt64.ofNat (A + 8) ∧
      ω'[3] = UInt64.ofNat (8 * m) ∧ ω'[11] = UInt64.ofNat (d + 8) ∧ ω'[8] = UInt64.ofNat (d + 16) ∧
      ω'[10] = UInt64.ofNat e ∧ ω'[1] = UInt64.ofNat sp ∧
      ∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8, 11] → ω'[j] = ω[j] := by
  have hq : pw / 2 ^ (8 * m) < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hpw
  have hsplice : Num.encodeLE 8 (Exec.bitwise (fun x1 x2 => x1 || x2) (Num.decodeLE (μ.readN (A + 8) 8) * 2 ^ (64 - 8 * m) % 18446744073709551616)
      (pw / 2 ^ (8 * m))) = (Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m := by
    rw [bitwise_or_comm]
    have := encodeLE_splice (Num.encodeLE 8 pw) (μ.readN (A + 8) 8) (Num.length_encodeLE _ _)
      (Memory.length_readN _ _ _) m hm
    rwa [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hpw)] at this
  have hl := encodeLE_decodeLE (μ.readN (A + 8) 8)
  have hlt := decodeLE_lt (μ.readN (A + 8) 8)
  rw [Memory.length_readN] at hl hlt
  generalize Num.decodeLE (μ.readN (A + 8) 8) = v at hl hlt hsplice ⊢
  rw [← hl] at hsplice ⊢
  have hrs' : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run =>
    apply FreeStepsH.step_decode (d_68989 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_68990 (p := p) (P := P))
    · pvm_simp [h4]
    apply FreeStepsH.step_decode (d_68992 (p := p) (P := P))
    · pvm_simp [h6, hr, ← hl, hlt]
    apply FreeStepsH.step_decode (d_68995 (p := p) (P := P))
    · pvm_simp [h3]
    apply FreeStepsH.step_decode (d_68998 (p := p) (P := P))
    · pvm_simp [h1, hrs]
    apply FreeStepsH.step_decode (d_69001 (p := p) (P := P))
    · pvm_simp [h6]
    apply FreeStepsH.step_decode (d_69004 (p := p) (P := P))
    · pvm_simp [h3]
    apply FreeStepsH.step_decode (d_69006 (p := p) (P := P))
    · pvm_simp [h1, hrs', hT]
    apply FreeStepsH.step_decode (d_69008 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_69011 (p := p) (P := P))
    · pvm_simp [h1, hrs']
    apply FreeStepsH.step_decode (d_69014 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_69017 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_69019 (p := p) (P := P))
    · pvm_simp [h11]
    apply FreeStepsH.step_decode (d_69022 (p := p) (P := P))
    · pvm_simp [h11, hw, hq, bitwise_mod64, hsplice]
    apply FreeStepsH.step_decode (d_69024 (p := p) (P := P))
    · pvm_simp [h11]
    exact FreeStepsH.refl
  case post =>
    refine ⟨?r4, ?r6, ?r3, ?r11, ?r8, ?r10, ?r1, fun j hj => ?rest⟩
    case rest =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3, h4, h5, h6]
    all_goals simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none, h10, h1]

end Services.Bootstrap
