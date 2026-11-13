import Services.Bootstrap.Fmt.Dec

/-!
# `<u8 as fmt::Display>::fmt` (67812): the steps

From the address v of an octet n (ω₇) and a `Formatter` F (ω₈): the frame T = sp − 16 holds ω₀ at
T + 8; n's k decimal digits (1 ≤ k ≤ 3, their values not stated) go to T + 8 − k … T + 8, and
`pad_integral` (61857) is called with F (ω₇), non-negative (ω₉ = 1), no prefix (ω₁₀ = 0), the
digits (ω₁₁) and k (ω₁₂), returning to 67924 (2796). `d8_b`: 67924 … 67930, the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem d8_lo {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 1 < 4294967296)
    (hdis : v + 1 ≤ sp - 16 ∨ sp ≤ v) (hn : rdN μ v 1 < 10)
    (hrv : ∀ a, v ≤ a → a < v + 1 → μ.readable a = true)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 67812 ω μ x 61857 ω' μ' x 27 ∧
      ω'[0] = UInt64.ofNat 2796 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (sp - 16 + 7) ∧
      ω'[12] = UInt64.ofNat 1 ∧ rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : rdN μ v 1 = 0
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.pad
      pvm_go [h0, h1, h7, h8, hsp, hv, hdis, hn, hz, hrv, hro, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
        Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1]
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, hn, hz, hrv, hro, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
        Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1]

theorem d8_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 1 < 4294967296)
    (hdis : v + 1 ≤ sp - 16 ∨ sp ≤ v) (hn : 10 ≤ rdN μ v 1 ∧ rdN μ v 1 < 100)
    (hrv : ∀ a, v ≤ a → a < v + 1 → μ.readable a = true)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 67812 ω μ x 61857 ω' μ' x 27 ∧
      ω'[0] = UInt64.ofNat 2796 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (sp - 16 + 6) ∧
      ω'[12] = UInt64.ofNat 2 ∧ rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  have q8 : rdN μ v 1 * 41 / 4096 = rdN μ v 1 / 100 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, hn, q8, hrv, hro, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1]

theorem d8_hi {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 1 < 4294967296)
    (hdis : v + 1 ≤ sp - 16 ∨ sp ≤ v) (hn : 100 ≤ rdN μ v 1 ∧ rdN μ v 1 < 256)
    (hrv : ∀ a, v ≤ a → a < v + 1 → μ.readable a = true)
    (hro : ∀ a, 65536 ≤ a → a < 77144 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 67812 ω μ x 61857 ω' μ' x 36 ∧
      ω'[0] = UInt64.ofNat 2796 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat (sp - 16 + 5) ∧
      ω'[12] = UInt64.ofNat 3 ∧ rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  have q8 : rdN μ v 1 * 41 / 4096 = rdN μ v 1 / 100 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, hn, q8, hrv, hro, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1]

/-- 67924 … 67930: ω₀ from T + 8, sp := T + 16, return. -/
theorem d8_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t : Nat) (hT : 65536 ≤ T ∧ T + 16 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 8) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 67924 ω μ x t ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega)]

end Services.Bootstrap.Fmt
