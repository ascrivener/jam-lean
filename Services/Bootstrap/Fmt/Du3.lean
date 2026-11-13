import Services.Bootstrap.Fmt.Du2

/-!
# `<u64 as fmt::Display>::fmt`: after the loop, the pair, the last digit, the call and the return
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 68598 … 68609: after the loop: the count ω₁₁ negated, the `Formatter` from T + 8 into ω₁₀, the
    value from T into ω₂; on to 68620 for q (ω₅) > 9, else 68665. -/
theorem du_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q a F y : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296) (hq : q < 1000) (ha : a < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat q) (h11 : ω[11] = UInt64.ofNat a)
    (rF : rdN μ (T + 8) 8 = F) (ry : rdN μ T 8 = y)
    (hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 68598 ω μ x (if 9 < q then 68620 else 68665) ω' μ x 6 ∧
      ω'[1] = ω[1] ∧ ω'[3] = ω[3] ∧ ω'[5] = UInt64.ofNat q ∧ ω'[2] = UInt64.ofNat y ∧
      ω'[10] = UInt64.ofNat F ∧ ω'[11] = UInt64.ofNat ((18446744073709551616 - a) % 18446744073709551616) := by
  rw [show ω = regsNF ω [] from rfl]
  have hF64 : F < 18446744073709551616 := by rw [← rF]; exact rdN_lt64 _ _
  have hy64 : y < 18446744073709551616 := by rw [← ry]; exact rdN_lt64 _ _
  by_cases hc : 9 < q
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h11, hT, hq, ha, rF, ry, hr, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hy64]
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h11, hT, hq, ha, rF, ry, hr, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hy64]

/-- 68611 … 68616: a value y (ω₂) below 1000: the count 20 in ω₁₁, y in ω₅; on to 68665 for y ≤ 9,
    else 68620. -/
theorem du_short {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (y : Nat) (hy : y < 1000) (h2 : ω[2] = UInt64.ofNat y) :
    ∃ ω', FreeStepsH p R 68611 ω μ x (if 9 < y then 68620 else 68665) ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[10] = ω[10] ∧ ω'[5] = UInt64.ofNat y ∧
      ω'[11] = UInt64.ofNat 20 := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : 9 < y
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h2, hy, hc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h2]
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h2, hy, hc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h2]

/-- 68620 … 68662: a digit pair. From q (ω₅) below 10000 and the count d (ω₁₁): the pair for
    q mod 100 at T + 34 + d; the count d − 2 and q / 100 in ω₅. -/
theorem du_two {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q d : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296) (hq : q < 10000) (hd : 2 ≤ d ∧ d ≤ 20)
    (h1 : ω[1] = UInt64.ofNat T) (h3 : ω[3] = UInt64.ofNat 70844) (h5 : ω[5] = UInt64.ofNat q)
    (h11 : ω[11] = UInt64.ofNat d)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : ∀ a, T + 34 + d ≤ a → a < T + 36 + d → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68620 ω μ x 68665 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[10] = ω[10] ∧ ω'[5] = UInt64.ofNat (q / 100) ∧
      ω'[11] = UInt64.ofNat (d - 2) ∧
      (∀ a, a < 4294967296 → (a < T + 34 + d ∨ T + 36 + d ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have e1 : q * 281474976710656 / 1125899906842624 * 5243 / 131072 = q / 100 := by omega
  have e2 : (q - q / 100 * 100) * 562949953421312 / 281474976710656 = 2 * (q % 100) := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h3, h5, h11, hT, hq, hd, e1, e2, hro, hw, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, h3]

/-- 68665 … 68692: the last digit. With the value y (ω₂), the quotient q (ω₅) below 10 and the count
    d (ω₁₁): if y = 0 or q ≠ 0, the digit for q goes to T + 35 + d and the count to d − 1; else nothing. -/
theorem du_one {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q d y : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296) (hq : q < 1000)
    (hd : d ≤ 20 ∧ (y = 0 ∨ q ≠ 0 → 1 ≤ d)) (hy : y < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h3 : ω[3] = UInt64.ofNat 70844) (h5 : ω[5] = UInt64.ofNat q)
    (h11 : ω[11] = UInt64.ofNat d) (h2 : ω[2] = UInt64.ofNat y)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : μ.writable (T + 35 + d) = true) :
    ∃ ω' μ', FreeStepsH p R 68665 ω μ x 68693 ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[10] = ω[10] ∧
      ω'[11] = UInt64.ofNat (if y = 0 ∨ q ≠ 0 then d - 1 else d) ∧
      (∀ a, a < 4294967296 → a ≠ T + 35 + d → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : y = 0 ∨ q ≠ 0
  · have hd1 := hd.2 hc
    have hw' : μ.writable (T + 36 + (d - 1)) = true := by rw [show T + 36 + (d - 1) = T + 35 + d by omega]; exact hw
    rw [if_pos hc]
    by_cases hy0 : y = 0
    · refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · pvm_go [h1, h3, h5, h11, h2, hT, hq, hd, hy, hy0, hro, hw', ↓rdN_fold]
      · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
        all_goals post_simp [h1, h3]
    · have hq0 : q ≠ 0 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · pvm_go [h1, h3, h5, h11, h2, hT, hq, hd, hy, hy0, hq0, hro, hw', ↓rdN_fold]
      · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
        all_goals post_simp [h1, h3]
  · rw [if_neg hc]
    have hy0 : y ≠ 0 := by omega
    have hq0 : q = 0 := by omega
    refine ⟨ω, μ, ?_, rfl, rfl, ?_, fun a _ _ => rfl, fun a => rfl, fun a => rfl⟩
    · pvm_go [h1, h3, h5, h11, h2, hT, hq, hd, hy, hy0, hq0]
    · simp [h11]

/-- 68693 … 68709: the digits at T + 36 + d, 20 − d of them; `pad_integral` (61857) called with the
    `Formatter` (ω₁₀), no prefix, returning to 68715 (2806). -/
theorem du_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T d F : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296) (hd : d ≤ 20) (hF : F < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h10 : ω[10] = UInt64.ofNat F) (h11 : ω[11] = UInt64.ofNat d) :
    ∃ ω', FreeStepsH p R 68693 ω μ x 61857 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 2806 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (T + 36 + d) ∧ ω'[12] = UInt64.ofNat (20 - d) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h10, h11, hT, hd, hF]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h10, Nat.mod_eq_of_lt hF]

/-- 68715 … 68727: ω₀, ω₅, ω₆ reloaded from T + 72, T + 64, T + 56, the frame closed, return. -/
theorem du_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 v5 v6 t : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (rr : rdN μ (T + 72) 8 = r0) (r5 : rdN μ (T + 64) 8 = v5)
    (r6 : rdN μ (T + 56) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T + 56 ≤ a → a < T + 80 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 68715 ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 80) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  have h5 : v5 < 18446744073709551616 := by rw [← r5]; exact rdN_lt64 _ _
  have h6 : v6 < 18446744073709551616 := by rw [← r6]; exact rdN_lt64 _ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, rr, r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h6]

end Services.Bootstrap.Fmt
