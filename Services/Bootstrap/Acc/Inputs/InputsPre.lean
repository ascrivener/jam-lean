import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The inputs function's prologue (6630 … 6670) and `fetch_vec`'s return to 44495

6630 opens the inputs function's 144-octet frame (return address 226 → 6674, ω₅, ω₆ saved, the
output pointer sp + 1568 of the caller at s + 8), stores the kind 14 (GP v0.8.0 Appendix B, `fetch`:
the accumulation inputs ℰ(↕**i**)) at s + 32 and tail-calls `fetch_vec` (47417) with out = s + 56 and its
arguments at s + 32, returning through entry 2022 to 44495. See the Acc README.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **6630 … 47417**: the frame s = sp − 144 opened (the return address 226 at s + 136, ω₅ at + 128,
    ω₆ at + 120, the output sp + 1568 at s + 8), the kind 14 at s + 32, and the call of `fetch_vec`:
    ω₇ = s + 56 (out), ω₈ = s + 32 (the arguments), return address 2022. -/
theorem in_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 144 ≤ sp ∧ sp + 1568 + 24 < 4294967296)
    (hwf : ∀ a, sp - 144 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6630 ω μ x 47417 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 2022 ∧ ω'[1] = UInt64.ofNat (sp - 144) ∧
      ω'[7] = UInt64.ofNat (sp - 144 + 56) ∧ ω'[8] = UInt64.ofNat (sp - 144 + 32) ∧
      rdN μ' (sp - 144 + 136) 8 = 226 ∧ rdN μ' (sp - 144 + 128) 8 = ω[5].toNat ∧
      rdN μ' (sp - 144 + 120) 8 = ω[6].toNat ∧ rdN μ' (sp - 144 + 8) 8 = sp + 1568 ∧
      μ'.readN (sp - 144 + 32) 8 = Num.encodeLE 8 14 ∧
      (∀ a, a < 4294967296 → (a < sp - 144 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 7, 8] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp - 144 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_,
      fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    all_goals try exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals decide

/-- **47722**, `fetch_vec`'s return (ω₀ = 2022) to 44495. -/
theorem fv_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2022) : FreeStepsH p R 47722 ω μ x 44495 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **47631 … 47554**, `alloc_impl` returned no block (ω₇ = 0): the lock byte cleared and the branch to
    `handle_alloc_error` (47554), the trap: allocation failure while fetching is an exhaustion. -/
theorem fv_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat 196792)
    (h7 : ω[7] = UInt64.ofNat 0) (hwf : ∀ a, sp ≤ a → a < sp + 64 → μ.writable a = true)
    (hwl : μ.writable 206848 = true) :
    ∃ ω' μ', FreeStepsH p R 47631 ω μ x 47554 ω' μ' x 10 := by
  have hr : ∀ a, sp ≤ a → a < sp + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run⟩
  case run => pvm_go [h1, h6, h7, hwf, hr, hwl, hrl]

/-- **44674**, the inputs function's return (ω₀ = 226) to 6674. -/
theorem in_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 226) : FreeStepsH p R 44674 ω μ x 6674 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

end Services.Bootstrap.Acc
