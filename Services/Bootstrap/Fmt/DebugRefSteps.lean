import Services.Bootstrap.Fmt.Tac

/-!
# `<&T as fmt::Debug>::fmt` for the integers: the steps

`<&u8 as Debug>::fmt` (37527): with plain options (the word 0x60000020 at F + 16: neither `{:x?}`
nor `{:X?}`), the reference at v is followed and the value's `Display` (67812) is jumped to, with
the value's address a (ω₇) and F (ω₈); ω₀, ω₁, ω₅, ω₆ are kept.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem rf_u8 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F a : Nat) (hv : v + 8 < 4294967296 ∧ F + 24 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (ra : rdN μ v 8 = a)
    (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 37527 ω μ x 67812 ω' μ x 7 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat a ∧
      ω'[8] = UInt64.ofNat F := by
  have ha : a < 18446744073709551616 := ra ▸ rdN_lt64 μ v
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, ro, ra, hrF, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

/-- `<&u64 as Debug>::fmt` (37589), plain options: on to `<u64 as Display>::fmt` (68449) with the
    value's address a. -/
theorem rf_u64 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F a : Nat) (hv : v + 8 < 4294967296 ∧ F + 24 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ro : rdN μ (F + 16) 4 = 1610612768) (ra : rdN μ v 8 = a)
    (hrF : ∀ b, F + 16 ≤ b → b < F + 20 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 37589 ω μ x 68449 ω' μ x 7 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat a ∧
      ω'[8] = UInt64.ofNat F := by
  have ha : a < 18446744073709551616 := ra ▸ rdN_lt64 μ v
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, ro, ra, hrF, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

end Services.Bootstrap.Fmt
