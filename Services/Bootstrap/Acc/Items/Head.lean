import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# Accumulate's items loop: its head (6674 … 6782)

After the inputs are decoded (`inputs_decode`, `Vec { n, q, n }` at sp + 1568), 6674 sets the loop up
(GP v0.8.0 §12: each accumulation input handled in order, `Spec.accumulate`'s `for it in items`):
- the end q + 184·n at sp + 144, q at sp + 16 and the capacity at sp + 32;
- constant words at sp + 24, + 40, + 112, + 120, + 184 and + 216;
- the cursor in ω₅ = ω₁₁ = q.
With no items it jumps to 15215. See the Acc README.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **6674 … 6782**, n > 0 items at q (the `Vec` at sp + 1568): the end q + 184·n at sp + 144, q at
    sp + 16, the capacity c at sp + 32, the constant words, and the cursor ω₅ = ω₁₁ = q. -/
theorem il_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp n q c : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1600 < 4294967296)
    (m0 : rdN μ (sp + 1568) 8 = c) (m8 : rdN μ (sp + 1576) 8 = q) (m16 : rdN μ (sp + 1584) 8 = n)
    (hn : 0 < n ∧ n ≤ 89) (hq : q + 184 * n < 2147483648)
    (hwf : ∀ a, sp ≤ a → a < sp + 1600 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 6674 ω μ x 6782 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧ ω'[11] = UInt64.ofNat q ∧
      ω'[7] = UInt64.ofNat n ∧
      rdN μ' (sp + 144) 8 = q + 184 * n ∧ rdN μ' (sp + 16) 8 = q ∧ rdN μ' (sp + 32) 8 = c ∧
      rdN μ' (sp + 24) 8 = 1702125934 ∧ rdN μ' (sp + 40) 8 = 3071 ∧ rdN μ' (sp + 112) 8 = 21903393 ∧
      rdN μ' (sp + 120) 8 = 16191 ∧ rdN μ' (sp + 184) 8 = 9223372036854775808 ∧
      rdN μ' (sp + 216) 8 = 9223372036854775809 ∧
      (∀ a, a < 4294967296 → (a < sp + 16 ∨ sp + 48 ≤ a) → (a < sp + 112 ∨ sp + 152 ≤ a) →
        (a < sp + 184 ∨ sp + 192 ≤ a) → (a < sp + 216 ∨ sp + 224 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [5, 7, 8, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp ≤ a → a < sp + 1600 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hn' : n % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hc : c < 18446744073709551616 := by rw [← m0]; exact rdN_lt64 _ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, m0, m8, m16, hn', hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 h4 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try with_reducible rfl
    all_goals try decide
    all_goals try (simp only [Nat.reduceMul, Nat.reducePow]; exact Nat.mod_eq_of_lt (by omega))
    all_goals try exact Nat.mod_eq_of_lt (by omega)
    all_goals try omega

end Services.Bootstrap.Acc
