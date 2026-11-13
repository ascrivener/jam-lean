import Services.Bootstrap.Acc.Wrappers.ReadHost
import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The SDK's `get` (47857): a value of this service's storage

`get(key)` (the SDK's storage read) reads in two phases, as `fetch_vec` does (GP v0.8.0 Appendix B,
Ω_R):
- `read` (4) with an empty buffer gives the value's length L, or NONE;
- NONE stores `None` (−1) at out; L = 0 stores the empty `Vec { 0, 1, 0 }`;
- otherwise a zeroed block of ⌈L/32⌉ units is allocated under the allocator's lock (41177, return
  2132 → 48047), a second `read` writes the value into it, and `Some(Vec { L, ptr, L })` is stored
  at out.
The frame is 48 octets (s = sp − 48): ω₀, ω₅, ω₆ at s + 40, + 32, + 24, out at s + 16, the key's
length at s + 8. The key's address stays in ω₅.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **47857 … 47886**: the frame s = sp − 48 (ω₀, ω₅, ω₆, out = ω₇ and the key's length ω₉ saved),
    ω₅ = the key's address ω₈, and the first `read`'s registers: ω₇ = NONE, ω₁₀ = ω₁₁ = ω₁₂ = 0. -/
theorem gr_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47857 ω μ x 47886 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat (sp - 48) ∧ ω'[5] = ω[8] ∧ ω'[7] = UInt64.ofNat 18446744073709551615 ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[11] = UInt64.ofNat 0 ∧ ω'[12] = UInt64.ofNat 0 ∧
      rdN μ' (sp - 48 + 40) 8 = ω[0].toNat ∧ rdN μ' (sp - 48 + 32) 8 = ω[5].toNat ∧
      rdN μ' (sp - 48 + 24) 8 = ω[6].toNat ∧ rdN μ' (sp - 48 + 16) 8 = ω[7].toNat ∧
      rdN μ' (sp - 48 + 8) 8 = ω[9].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 48 + 8 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [1, 5, 7, 10, 11, 12] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp - 48 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> rfl), by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

end Services.Bootstrap.Acc
