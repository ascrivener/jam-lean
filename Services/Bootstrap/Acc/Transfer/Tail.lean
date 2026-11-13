import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `on_transfer` after the counter is read (7326 … 7437)

- 7326 … 40494 (`tr_sk_pre`): n stored at sp + 1496 (u32) and n + 1 at sp + 1568 (u32, the value
  written under "transfer-count"), then the copied-key `set` helper's frame s = sp − 64 (ω₀ = 250, ω₅,
  ω₆ = n + 1 at s + 56, + 48, + 40; the value's address sp + 1568 and length 4 at s, s + 8) and
  `alloc(14, 1)` returning to 3896 (`sk_call`).
- 7386 (`tr_chk`): the helper's result; anything but the octet 255 (`Ok`) goes to the trap at 15361
  (`orPanic`).
- 7399 … 40494 (`tr_a128`): `alloc(128, 1)` for the memo's copy, returning to 7413; 7413: null traps
  at 15363 (`tr_a128_null`), else `memcpy` of the memo (sp + 1144) to the block (`tr_a128_cpy`).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **7326 … 40494**: n at sp + 1496, n + 1 at sp + 1568, the helper's frame at s = sp − 64 and the
    call of `alloc(14, 1)` (return address 110, to 3896); ω₅ = 65956 (the key), ω₆ = 14. -/
theorem tr_sk_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp n : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat n)
    (hn : n < 4294967296) (hsp : 65536 + 64 ≤ sp ∧ sp + 1856 < 4294967296)
    (hwf : ∀ a, sp - 64 ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7326 ω μ x 40494 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 110 ∧ ω'[1] = UInt64.ofNat (sp - 64) ∧ ω'[7] = UInt64.ofNat 14 ∧
      ω'[8] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat 65956 ∧ ω'[6] = UInt64.ofNat 14 ∧
      rdN μ' (sp + 1496) 4 = n ∧ rdN μ' (sp + 1568) 4 = (n + 1) % 4294967296 ∧
      rdN μ' (sp - 64) 8 = sp + 1568 ∧ rdN μ' (sp - 64 + 8) 8 = 4 ∧ rdN μ' (sp - 64 + 56) 8 = 250 ∧
      rdN μ' (sp - 64 + 48) 8 = ω[5].toNat ∧ rdN μ' (sp - 64 + 40) 8 = n + 1 ∧
      (∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → (a < sp + 1496 ∨ sp + 1500 ≤ a) →
        (a < sp + 1568 ∨ sp + 1572 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 64 ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h6, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) | exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)) | exact Nat.mod_eq_of_lt (by omega) | skip

/-- **7386 … 7399**, the helper returned `Ok` (2⁶⁴ − 1): on to the memo's copy. -/
theorem tr_chk_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 18446744073709551615) :
    ∃ ω', FreeStepsH p R 7386 ω μ x 7399 ω' μ x 2 ∧ ∀ j : Fin 13, j.val ∉ [7] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h7]
  case post => exact by reg_frame

/-- **7386 … 15361**, the helper returned `Err` (3, FULL): the trap (`orPanic`). -/
theorem tr_chk_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 3) :
    ∃ ω', FreeStepsH p R 7386 ω μ x 15361 ω' μ x 4 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

/-- **7399 … 40494**: `alloc(128, 1)` with return address 252 (to 7413). -/
theorem tr_a128 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) :
    ∃ ω', FreeStepsH p R 7399 ω μ x 40494 ω' μ x 3 ∧ ω'[0] = UInt64.ofNat 252 ∧
      ω'[7] = UInt64.ofNat 128 ∧ ω'[8] = UInt64.ofNat 1 ∧ ∀ j : Fin 13, j.val ∉ [0, 7, 8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go []
  case post => exact ⟨by reg_val, by reg_val, by reg_val, by reg_frame⟩

/-- `alloc`'s return (40611) to 7413 (ω₀ = 252). -/
theorem tr_j252 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 252) : FreeStepsH p R 40611 ω μ x 7413 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- **7413 … 15363**, `alloc(128)` returned null: the allocation-failure trap. -/
theorem tr_a128_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (h7 : ω[7] = UInt64.ofNat 0) : ∃ ω', FreeStepsH p R 7413 ω μ x 15363 ω' μ x 3 := by
  rw [show ω = regsNF ω [] from rfl]
  exact ⟨_, by pvm_go [h7]⟩

/-- **7413 … 68729**, a block ptr ≠ 0: `memcpy(ptr, sp + 1144, 128)` (the memo), return address 254
    (to 7437); ω₆ = ptr. -/
theorem tr_a128_cpy {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0)
    (hp : ptr < 18446744073709551616) (hsp : sp + 1856 < 4294967296) :
    ∃ ω', FreeStepsH p R 7413 ω μ x 68729 ω' μ x 5 ∧ ω'[0] = UInt64.ofNat 254 ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[6] = UInt64.ofNat ptr ∧ ω'[8] = UInt64.ofNat (sp + 1144) ∧
      ω'[9] = UInt64.ofNat 128 ∧ ω'[1] = UInt64.ofNat sp ∧
      ∀ j : Fin 13, j.val ∉ [0, 6, 7, 8, 9] → ω'[j] = ω[j] := by
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hp]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, h7, hp0']
  case post =>
    exact ⟨by reg_val, (by reg_val <;> exact h7), (by reg_val <;> exact h7), by reg_val, by reg_val,
      (by reg_val <;> exact h1), by reg_frame⟩

end Services.Bootstrap.Acc
