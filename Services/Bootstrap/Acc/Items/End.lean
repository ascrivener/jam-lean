import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# Accumulate's items loop: its end (15316 … 15359)

Every item handled: the items buffer freed (`dealloc` 40613, return address 574 → 15339) unless its
capacity is 0, then (ω₇, ω₈) = (0, 0), ω₀, ω₅, ω₆ restored from the entry frame (sp + 1848, + 1840,
+ 1832), the frame of 1856 octets popped, and the return `jumpInd` at 15359 (the halt: Ψ_A takes no
yield from the output, GP v0.8.0 eq. `accinvocation`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **15316 … 40613**, the items buffer's capacity c ≠ 0 (at sp + 32): the call of `dealloc` on q (at
    sp + 16), return address 574. -/
theorem il_end_free {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m32 : rdN μ (sp + 32) 8 = c) (m16 : rdN μ (sp + 16) 8 = q) (hc : c ≠ 0)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15316 ω μ x 40613 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 574 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat q ∧
      ∀ j : Fin 13, j.val ∉ [0, 7, 8, 9] → ω'[j] = ω[j] := by
  have hc' : c % 18446744073709551616 ≠ 0 := by
    rw [Nat.mod_eq_of_lt (by rw [← m32]; exact rdN_lt64 _ _)]; exact hc
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, m32, m16, hc', hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val; simp [h1], ?_, by reg_frame⟩
    reg_val

/-- **15316 … 15339**, the capacity 0: no `dealloc`. -/
theorem il_end_nofree {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m32 : rdN μ (sp + 32) 8 = 0) (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15316 ω μ x 15339 ω' μ x 5 ∧ ∀ j : Fin 13, j.val ∉ [8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, m32, hrf, ↓rdN_fold, ↓loadI_fold]
  case post => reg_frame

/-- **15339 … 15359**: (ω₇, ω₈) = (0, 0), ω₀, ω₅, ω₆ restored from sp + 1848, + 1840, + 1832, the
    frame popped, at the return's `jumpInd`. -/
theorem il_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 15339 ω μ x 15359 ω' μ x 10 ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[1] = UInt64.ofNat (sp + 1856) ∧
      ω'[0] = UInt64.ofNat (rdN μ (sp + 1848) 8) ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 1840) 8) ∧
      ω'[6] = UInt64.ofNat (rdN μ (sp + 1832) 8) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, ?_⟩ <;> (reg_val; try rfl)

end Services.Bootstrap.Acc
