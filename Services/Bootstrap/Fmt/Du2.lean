import Services.Bootstrap.Fmt.Du

/-!
# `<u64 as fmt::Display>::fmt`: the steps around the loop

They mirror the u32 ones (`Dec2.lean`), with a frame of 80 octets at T and digits at T + 36 + d,
where d (ω₁₁) counts down from 20.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 68449 … 68470: an 80-octet frame at T = sp − 80 (ω₀, ω₅, ω₆ at T + 72, T + 64, T + 56), the
    `Formatter` (ω₈) in ω₁₀, the value (u64 at ω₇) in ω₂, the table in ω₃; on to 68611 for a value
    below 1000, else 68476. -/
theorem du_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 v5 v6 : Nat) (hsp : 65536 + 80 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hb : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      F < 18446744073709551616)
    (hv : v + 8 < 4294967296) (hvf : v + 8 ≤ sp - 80 ∨ sp ≤ v)
    (hrv : ∀ a, v ≤ a → a < v + 8 → μ.readable a = true)
    (hw : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68449 ω μ x (if rdN μ v 8 < 1000 then 68611 else 68476) ω' μ' x 10 ∧
      ω'[1] = UInt64.ofNat (sp - 80) ∧ ω'[10] = UInt64.ofNat F ∧ ω'[3] = UInt64.ofNat 70844 ∧
      ω'[2] = UInt64.ofNat (rdN μ v 8) ∧
      rdN μ' (sp - 80 + 72) 8 = r0 ∧ rdN μ' (sp - 80 + 64) 8 = v5 ∧ rdN μ' (sp - 80 + 56) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 80 + 56 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 80 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hX := rdN_lt64 μ v
  generalize hXd : rdN μ v 8 = X at hX ⊢
  rw [show ω = regsNF ω [] from rfl]
  by_cases hc : X < 1000
  · rw [if_pos hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h5, h6, h7, h8, hb, hsp, hv, hvf, hrv, hw, hr, hXd, hX, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hX]
  · rw [if_neg hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h5, h6, h7, h8, hb, hsp, hv, hvf, hrv, hw, hr, hXd, hX, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hX]

/-- 68476 … 68520: the `Formatter` (ω₁₀) saved at T + 8, the count −20 in ω₁₁, the cursor T + 55 in
    ω₁₂, 10000 and the multiplier at T + 24 and T + 16, 5243 in ω₀, 9999999 in ω₄, the value y (ω₂)
    saved at T and copied to ω₅, 100 in ω₆. -/
theorem du_setup {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F y : Nat) (hT : 65536 ≤ T ∧ T + 80 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h2 : ω[2] = UInt64.ofNat y) (h10 : ω[10] = UInt64.ofNat F)
    (hb : F < 18446744073709551616 ∧ y < 18446744073709551616)
    (hw : ∀ a, T ≤ a → a < T + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68476 ω μ x 68521 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 5243 ∧ ω'[1] = ω[1] ∧ ω'[3] = ω[3] ∧ ω'[4] = UInt64.ofNat 9999999 ∧
      ω'[5] = UInt64.ofNat y ∧ ω'[6] = UInt64.ofNat 100 ∧ ω'[11] = UInt64.ofNat 18446744073709551596 ∧
      ω'[12] = UInt64.ofNat (T + 55) ∧
      rdN μ' (T + 24) 8 = 10000 ∧ rdN μ' (T + 16) 8 = 3777893186295716171 ∧ rdN μ' (T + 8) 8 = F ∧
      rdN μ' T 8 = y ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 32 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h2, h10, hb, hT, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8]
    all_goals try rw [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]

end Services.Bootstrap.Fmt
