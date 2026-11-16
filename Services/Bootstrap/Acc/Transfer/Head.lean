import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `on_transfer`'s head (7159 → 40494)

A transfer slot: `tr_head` copies the slot's 128 octets to sp + 1144 (`memcpy`, return 242 → 7176);
`tr_gk_pre` saves ω₅ / ω₆, puts the key "transfer-count" (read-only data at 65956, 14 octets) at
sp + 512, opens the helper's frame at sp − 56 with out = sp + 1568, and calls `alloc(14, 1)` (40494,
return 102 → 3820, `GetKey.lean`). Spec: `onTransfer`'s first `read` of "transfer-count".
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **7159 … 68729**, a transfer: the call of `memcpy` of 128 octets from ω₈ to sp + 1144, ω₁₀ moved
    to ω₅, return address 242. -/
theorem tr_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) :
    ∃ ω', FreeStepsH p R 7159 ω μ x 68729 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 242 ∧ ω'[7] = UInt64.ofNat (sp + 1144) ∧ ω'[9] = UInt64.ofNat 128 ∧
      ω'[5] = ω[10] ∧ ∀ j : Fin 13, j.val ∉ [0, 5, 7, 9] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1]
  case post => exact ⟨by reg_val, by reg_val, by reg_val, (by reg_val <;> simp [UInt64.ofNat_toNat]), by reg_frame⟩

/-- **7176 … 40494**: the u32 ω₅ at sp + 472, ω₆ at sp + 1000, the key "transfer-count" (65956) at
    sp + 512; then the helper's frame s = sp − 56 (ω₀ = 244, ω₅, ω₆ saved at s + 48, + 40, + 32, out
    = sp + 1568 at s) and `alloc(14, 1)` with return address 102 (to 3820); ω₆ = 65956. -/
theorem tr_gk_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 + 56 ≤ sp ∧ sp + 1856 < 4294967296)
    (hwf : ∀ a, sp - 56 ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7176 ω μ x 40494 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 102 ∧ ω'[1] = UInt64.ofNat (sp - 56) ∧ ω'[7] = UInt64.ofNat 14 ∧
      ω'[8] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat 14 ∧ ω'[6] = UInt64.ofNat 65956 ∧
      rdN μ' (sp - 56) 8 = sp + 1568 ∧ rdN μ' (sp - 56 + 48) 8 = 244 ∧
      rdN μ' (sp - 56 + 40) 8 = ω[5].toNat ∧ rdN μ' (sp - 56 + 32) 8 = ω[6].toNat ∧
      rdN μ' (sp + 472) 4 = ω[5].toNat % 4294967296 ∧ rdN μ' (sp + 1000) 8 = ω[6].toNat ∧
      rdN μ' (sp + 512) 8 = 65956 ∧
      (∀ a, a < 4294967296 → (a < sp - 56 ∨ sp ≤ a) → (a < sp + 472 ∨ sp + 476 ≤ a) →
        (a < sp + 512 ∨ sp + 520 ≤ a) → (a < sp + 1000 ∨ sp + 1008 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 5, 6, 7, 8] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp - 56 ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 h4 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) | exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)) | exact Nat.mod_eq_of_lt (by omega) | skip

end Services.Bootstrap.Acc
