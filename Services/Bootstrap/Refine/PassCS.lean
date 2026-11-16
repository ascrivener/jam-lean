import Services.Bootstrap.Refine.Pass

/-!
# The pass-through of `CreateService` at the loop's dispatch

`CreateService`'s slot has no discriminant word: its word 0 is the `Option<Vec<u8>>` niche, the code's length
(< 2^63) or 2^64 − 1 for `None`. The loop's dispatch (5095 …) maps every word outside [2^63, 2^63 + 24] to index 0,
which it passes through to 5561 (5115 ≠ 8, 5120 ≠ 9). `pdCS` is `Pass.pd` for those words. GP v0.8.0 Appendix B.4.
-/

namespace Services.Bootstrap.Refine.Pass

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR

variable {X : Type} {R : HostRel X}

set_option maxHeartbeats 8000000 in
/-- 5095 … 5561 for a word D < 2^63 or D = 2^64 − 1 (`CreateService`'s niche): index 0, passed through. -/
theorem pdCS {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (x : X) (ω : Regs)
    (μ : Memory) (M D : Nat) (hD : D < 9223372036854775808 ∨ D = 18446744073709551615) (hM : M + 632 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h6 : ω[6] = UInt64.ofNat D)
    (s128 : μ.readN (M + 128) 8 = Num.encodeLE 8 9223372036854775832)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809)
    (hr : ∀ a, M + 128 ≤ a → a < M + 144 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 5095 ω μ x 5561 ω' μ x 10 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] := by
  have r128 := Services.Bootstrap.Encode.Writer.rd8 (by decide) s128
  have r136 := Services.Bootstrap.Encode.Writer.rd8 (by decide) s136
  rw [show ω = regsNF ω [] from rfl]
  rcases hD with hD | rfl
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h6, hM, hr, r128, r136, hD, ↓rdN_fold]
    · refine ⟨?_, ?_⟩ <;> simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        List.lookup_nil, Option.getD_none]
  · refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h6, hM, hr, r128, r136, ↓rdN_fold]
    · refine ⟨?_, ?_⟩ <;> simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        List.lookup_nil, Option.getD_none]

end Services.Bootstrap.Refine.Pass
