import Services.Bootstrap.Fmt.Dec

/-!
# `<u32 as fmt::Display>::fmt`: the steps around the four-digit loop

- `dl_setup`: 68173 … 68208, the loop's constants;
- `dl_short`: 68331, the value below 1000;
- `dl_post`: 68317, after the loop;
- `dl_two`: 68340, a digit pair;
- `dl_one`: 68385, the last digit;
- `dl_call`: 68413, `pad_integral`;
- `dl_ret`: 68435.

Digits go to T + 38 + d, where d (ω₉) counts down from 10.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 68173 … 68208: the `Formatter` (ω₆) saved at T + 8, the offset 0 in ω₉, the constants 10000 and
    5243 at T + 24 and T + 16, the multiplier in ω₂, 9999999 in ω₃, the value y (ω₁₂) saved at T and
    copied to ω₈. -/
theorem dl_setup {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F y : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat F) (h12 : ω[12] = UInt64.ofNat y)
    (hb : F < 18446744073709551616 ∧ y < 18446744073709551616)
    (hw : ∀ a, T ≤ a → a < T + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68173 ω μ x 68209 ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[2] = UInt64.ofNat 15111572745684516864 ∧ ω'[3] = UInt64.ofNat 9999999 ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat y ∧ ω'[9] = UInt64.ofNat 0 ∧
      rdN μ' (T + 24) 8 = 10000 ∧ rdN μ' (T + 16) 8 = 5243 ∧ rdN μ' (T + 8) 8 = F ∧ rdN μ' T 8 = y ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 32 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h12, hb, hT, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, h6, rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8]
    all_goals rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]

/-- 68331 … 68336: a value y below 1000: the offset 10 in ω₉, y in ω₈; on to 68385 for y ≤ 9, else
    68340. -/
theorem dl_short {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (y : Nat) (hy : y < 1000) (h12 : ω[12] = UInt64.ofNat y) :
    ∃ ω', FreeStepsH p R 68331 ω μ x (if y ≤ 9 then 68385 else 68340) ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat y ∧
      ω'[9] = UInt64.ofNat 10 ∧ ω'[12] = UInt64.ofNat y := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : y ≤ 9
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h12, hy, hc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h12]
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h12, hy, hc]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h12]

/-- 68317 … 68329: after the loop, with the offset o (ω₉) and the quotient q (ω₈): the offset
    o + 10, the `Formatter` reloaded from T + 8 into ω₆ and the value from T into ω₁₂; on to 68340 for
    q > 9, else 68385. -/
theorem dl_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q o F y : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296) (hq : q < 1000) (ho : o < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h8 : ω[8] = UInt64.ofNat q) (h9 : ω[9] = UInt64.ofNat o)
    (rF : rdN μ (T + 8) 8 = F) (ry : rdN μ T 8 = y)
    (hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 68317 ω μ x (if 9 < q then 68340 else 68385) ω' μ x 6 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat F ∧ ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat q ∧
      ω'[9] = UInt64.ofNat ((o + 10) % 18446744073709551616) ∧ ω'[12] = UInt64.ofNat y := by
  rw [show ω = regsNF ω [] from rfl]
  have hF64 : F < 18446744073709551616 := by rw [← rF]; exact rdN_lt64 _ _
  have hy64 : y < 18446744073709551616 := by rw [← ry]; exact rdN_lt64 _ _
  by_cases hc : 9 < q
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h8, h9, hT, hq, ho, rF, ry, hr, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, h8, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hy64]
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h8, h9, hT, hq, ho, rF, ry, hr, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, h8, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hy64]

/-- 68340 … 68382: a digit pair. From q (ω₈) below 10000 and the offset d (ω₉): the pair for q mod 100
    from the table, two octets at T + 36 + d; the offset d − 2 and q / 100 in ω₈. -/
theorem dl_two {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q d : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296) (hq : q < 10000) (hd : 2 ≤ d ∧ d ≤ 10)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat 70844) (h8 : ω[8] = UInt64.ofNat q)
    (h9 : ω[9] = UInt64.ofNat d)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : ∀ a, T + 36 + d ≤ a → a < T + 38 + d → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68340 ω μ x 68385 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[7] ∧ ω'[8] = UInt64.ofNat (q / 100) ∧
      ω'[9] = UInt64.ofNat (d - 2) ∧ ω'[12] = ω[12] ∧
      (∀ a, a < 4294967296 → (a < T + 36 + d ∨ T + 38 + d ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have e1 : q * 281474976710656 / 1125899906842624 * 5243 / 131072 = q / 100 := by omega
  have e2 : (q - q / 100 * 100) * 562949953421312 / 281474976710656 = 2 * (q % 100) := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, h8, h9, hT, hq, hd, e1, e2, hro, hw, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, h7]

/-- 68385 … 68412: the last digit. With the value y (ω₁₂), the quotient q (ω₈) below 10 and the offset
    d (ω₉): if y = 0 or q ≠ 0, the digit for q from the table goes to T + 37 + d and the offset to
    d − 1; else nothing is written. -/
theorem dl_one {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q d y : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296) (hq : q < 1000) (hd : 1 ≤ d ∧ d ≤ 10)
    (hy : y < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat 70844) (h8 : ω[8] = UInt64.ofNat q)
    (h9 : ω[9] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat y)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : μ.writable (T + 37 + d) = true) :
    ∃ ω' μ', FreeStepsH p R 68385 ω μ x 68413 ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[9] = UInt64.ofNat (if y = 0 ∨ q ≠ 0 then d - 1 else d) ∧
      (∀ a, a < 4294967296 → a ≠ T + 37 + d → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hw' : μ.writable (T + 38 + (d - 1)) = true := by rw [show T + 38 + (d - 1) = T + 37 + d by omega]; exact hw
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : y = 0 ∨ q ≠ 0
  · rw [if_pos hc]
    by_cases hy0 : y = 0
    · refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · pvm_go [h1, h7, h8, h9, h12, hT, hq, hd, hy, hy0, hro, hw', ↓rdN_fold]
      · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
        all_goals post_simp [h1, h7]
    · have hq0 : q ≠ 0 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · pvm_go [h1, h7, h8, h9, h12, hT, hq, hd, hy, hy0, hq0, hro, hw', ↓rdN_fold]
      · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
        all_goals post_simp [h1, h7]
  · rw [if_neg hc]
    have hy0 : y ≠ 0 := by omega
    have hq0 : q = 0 := by omega
    refine ⟨ω, μ, ?_, rfl, rfl, rfl, ?_, fun a _ _ => rfl, fun a => rfl, fun a => rfl⟩
    · pvm_go [h1, h7, h8, h9, h12, hT, hq, hd, hy, hy0, hq0]
    · simp [h9]

/-- 68413 … 68429: the digits at T + 38 + d, 10 − d of them; `pad_integral` (61857) called with the
    `Formatter` (ω₆), no prefix, returning to 68435 (2802). -/
theorem dl_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T d F : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296) (hd : d ≤ 10) (hF : F < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat F) (h9 : ω[9] = UInt64.ofNat d) :
    ∃ ω', FreeStepsH p R 68413 ω μ x 61857 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 2802 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (T + 38 + d) ∧ ω'[12] = UInt64.ofNat (10 - d) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, h9, hT, hd, hF]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h6, Nat.mod_eq_of_lt hF]

/-- 68435 … 68447: ω₀, ω₅, ω₆ reloaded from T + 64, T + 56, T + 48, the frame closed, return. -/
theorem dl_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 v5 v6 t : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (rr : rdN μ (T + 64) 8 = r0) (r5 : rdN μ (T + 56) 8 = v5)
    (r6 : rdN μ (T + 48) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T + 48 ≤ a → a < T + 72 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 68435 ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 72) ∧ ω'[5] = UInt64.ofNat v5 ∧
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
