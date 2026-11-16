import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The items loop's work-error skip (7009 … 15191 …)

After the item's log line (at 7009), an operand whose work result is an error (the word at sp + 288,
copied from the slot's + 24, is −1) skips to the drop at 15191: the trace's buffer is freed
(`dealloc` 40613 on the pointer at sp + 272, size the capacity at sp + 264, align 1, return address
228 → 6766) unless its capacity is 0, and the loop goes round at 6766.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **7009 … 15198 → 6766**, a work error with trace capacity 0. -/
theorem err_skip_nofree {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m288 : rdN μ (sp + 288) 8 = 18446744073709551615) (m264 : rdN μ (sp + 264) 8 = 0)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 7009 ω μ x 6766 ω' μ x 7 ∧ ω'[1] = UInt64.ofNat sp := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, m288, m264, hrf, ↓rdN_fold, ↓loadI_fold]
  case post => reg_val; simp [h1]

/-- **7009 … 15212 → 40613**, a work error with trace capacity c ≠ 0: the call of `dealloc` on the
    pointer at sp + 272, size c, align 1, return address 228. -/
theorem err_skip_free {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp c t : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m288 : rdN μ (sp + 288) 8 = 18446744073709551615) (m264 : rdN μ (sp + 264) 8 = c) (hc : c ≠ 0)
    (m272 : rdN μ (sp + 272) 8 = t)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 7009 ω μ x 40613 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 228 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat t := by
  have hc' : c % 18446744073709551616 ≠ 0 := by
    rw [Nat.mod_eq_of_lt (by rw [← m264]; exact rdN_lt64 _ _)]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, m288, m264, hc', m272, hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val; simp [h1], ?_⟩
    reg_val

end Services.Bootstrap.Acc
