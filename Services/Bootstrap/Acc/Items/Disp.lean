import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# Accumulate's items loop: the step and the dispatch (6766 … 6827)

At 6782, with the cursor ω₅ at the current item's 184-octet slot (`inputs_decode`'s layout):
- the next cursor ω₅ + 184 is saved at sp + 168;
- the slot's first word w selects the arm: −1 is a transfer (7159, `on_transfer`), −2 the end of the
  items (15215), and anything else an operand (6827).
At 6766 the loop steps: the saved cursor becomes ω₅, and it either reaches the end (sp + 144, then
15316) or goes round again (6782).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **6766 … 6782**: the next cursor `nx` (sp + 168) becomes ω₅; it is not the end e (sp + 144), so
    the loop goes round. -/
theorem il_step {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp nx e : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m168 : rdN μ (sp + 168) 8 = nx) (m144 : rdN μ (sp + 144) 8 = e) (hne : nx ≠ e)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6766 ω μ x 6782 ω' μ x 10 ∧
      ω'[5] = UInt64.ofNat nx ∧ ∀ j : Fin 13, j.val ∉ [5, 7, 8] → ω'[j] = ω[j] := by
  have hq' : rdN μ (sp + 168) 8 % 18446744073709551616 ≠ rdN μ (sp + 144) 8 % 18446744073709551616 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 _ _), Nat.mod_eq_of_lt (rdN_lt64 _ _), m168, m144]; exact hne
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hq', hrf, ↓rdN_fold, ↓loadI_fold]
  case post => exact ⟨by reg_val; rw [m168, Nat.mod_eq_of_lt (by rw [← m168]; exact rdN_lt64 _ _)], by reg_frame⟩

/-- **6766 … 15316**: the next cursor is the end e (sp + 144); the loop exits. -/
theorem il_step_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp e : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (m168 : rdN μ (sp + 168) 8 = e) (m144 : rdN μ (sp + 144) 8 = e)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6766 ω μ x 15316 ω' μ x 10 ∧ ∀ j : Fin 13, j.val ∉ [5, 7, 8] → ω'[j] = ω[j] := by
  have hq' : rdN μ (sp + 168) 8 % 18446744073709551616 = rdN μ (sp + 144) 8 % 18446744073709551616 := by
    rw [m168, m144]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hq', hrf, ↓rdN_fold, ↓loadI_fold]
  case post => reg_frame

/-- **6782 … 7159**, a transfer (the slot's first word −1): the next cursor q + 184 saved at sp + 168,
    678 at sp + 200; ω₆ the slot's word at + 136, ω₁₀ its 32-bit word at + 152 sign-extended, ω₈ = q + 8. -/
theorem il_disp_tr {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat q)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hq : 65536 ≤ q ∧ q + 184 < 4294967296)
    (w0 : rdN μ q 8 = 18446744073709551615)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (hrq : ∀ a, q ≤ a → a < q + 184 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 6782 ω μ x 7159 ω' μ' x 12 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧ ω'[11] = UInt64.ofNat (q + 184) ∧
      ω'[8] = UInt64.ofNat (q + 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (q + 136) 8) ∧
      rdN μ' (sp + 168) 8 = q + 184 ∧ rdN μ' (sp + 200) 8 = 678 ∧
      (∀ a, a < 4294967296 → (a < sp + 168 ∨ sp + 176 ≤ a) → (a < sp + 200 ∨ sp + 208 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [6, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, w0, hwf, hr, hrq, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val; simp [h5], by reg_val, by reg_val, ?_, ?_, ?_,
      fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try (reg_val; done)
    all_goals try (reg_val; rw [Nat.mod_eq_of_lt (rdN_lt64 _ _)])
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (by omega)
    all_goals decide

/-- **6782 … 6827**, an operand (the slot's first word w ∉ {−1, −2}): as `il_disp_tr`, on to the
    operand arm. -/
theorem il_disp_op {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat q)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hq : 65536 ≤ q ∧ q + 184 < 4294967296)
    (w0 : rdN μ q 8 ≠ 18446744073709551615) (w0' : rdN μ q 8 ≠ 18446744073709551614)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (hrq : ∀ a, q ≤ a → a < q + 184 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 6782 ω μ x 6827 ω' μ' x 14 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧ ω'[11] = UInt64.ofNat (q + 184) ∧
      ω'[8] = UInt64.ofNat (q + 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (q + 136) 8) ∧
      ω'[7] = UInt64.ofNat (rdN μ q 8) ∧
      rdN μ' (sp + 168) 8 = q + 184 ∧ rdN μ' (sp + 200) 8 = 678 ∧
      (∀ a, a < 4294967296 → (a < sp + 168 ∨ sp + 176 ≤ a) → (a < sp + 200 ∨ sp + 208 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [6, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have e1 : rdN μ q 8 % 18446744073709551616 ≠ 18446744073709551615 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 _ _)]; exact w0
  have e2 : rdN μ q 8 % 18446744073709551616 ≠ 18446744073709551614 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 _ _)]; exact w0'
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, e1, e2, hwf, hr, hrq, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val; simp [h1], by reg_val; simp [h5], by reg_val, by reg_val, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals try rd_simp []
    all_goals try (reg_val; done)
    all_goals try (reg_val; rw [Nat.mod_eq_of_lt (rdN_lt64 _ _)])
    all_goals try with_reducible rfl
    all_goals try exact Nat.mod_eq_of_lt (by omega)
    all_goals decide

end Services.Bootstrap.Acc
