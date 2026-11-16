import Services.Bootstrap.Acc.Transfer.Tail3

/-!
# `on_transfer`'s remaining straight-line segments (7437, 7743, 7763)

- 7437 … 60681 (`tr_u8_pre`): `from_utf8(out = sp + 744, ptr = ω₆, 128)` (return 256, to 7454), the
  memo's copy checked for the log line (`Utf8Call`).
- 7743 … 7763 (`lg_log_b0`): the log message's capacity is 0 (at sp + 744): nothing to free.
- 7763 … 59375 (`t2_kfmt_pre`): `format!("transfer{}", n)`'s argument pair (sp + 1496, the formatter
  word spilled at sp + 208) at sp + 1568, and `format_inner` of the template 66607 into sp + 512
  (return 268, to 7799; `KeyFmt`).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **7437 … 60681**: `from_utf8` of the 128 octets at ω₆ into sp + 744 (return address 256). -/
theorem tr_u8_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : sp + 1856 < 4294967296) :
    ∃ ω', FreeStepsH p R 7437 ω μ x 60681 ω' μ x 4 ∧ ω'[0] = UInt64.ofNat 256 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 744) ∧ ω'[8] = ω[6] ∧
      ω'[9] = UInt64.ofNat 128 ∧ ∀ j : Fin 13, j.val ∉ [0, 7, 8, 9] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1]
  case post =>
    exact ⟨by reg_val, (by reg_val <;> exact h1), (by reg_val <;> (rw [h1]; simp; omega)),
      (by reg_val <;> simp [List.lookup]), by reg_val, by reg_frame⟩

/-- **7743 … 7763**, the message's capacity 0 (at sp + 744): no free. -/
theorem lg_log_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp) (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296)
    (hrf : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true) (mc : rdN μ (sp + 744) 8 = 0) :
    ∃ ω', FreeStepsH p R 7743 ω μ x 7763 ω' μ x 3 ∧ ∀ j : Fin 13, j.val ∉ [8] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hrf, mc, ↓rdN_fold]
  case post => exact by reg_frame

/-- **7763 … 59375**: the argument pair (sp + 1496, the word at sp + 208) at sp + 1568 and
    `format_inner(out = sp + 512, template 66607, args = sp + 1568)` (return address 268). -/
theorem t2_kfmt_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 7763 ω μ x 59375 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 268 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat (sp + 512) ∧
      ω'[8] = UInt64.ofNat 66607 ∧ ω'[9] = UInt64.ofNat (sp + 1568) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' (sp + 1568) 8 = sp + 1496 ∧ rdN μ' (sp + 1576) 8 = rdN μ (sp + 208) 8 ∧
      (∀ a, a < 4294967296 → (a < sp + 1568 ∨ sp + 1584 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨by reg_val, (by reg_val <;> exact h1), by reg_val, by reg_val, by reg_val, (by reg_val <;> rfl),
      (by reg_val <;> rfl), ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
    all_goals try (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint]; done)
    all_goals try (simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals first | rfl | decide | exact Nat.mod_eq_of_lt (by omega) | skip
    all_goals exact lg_rmod64 μ _

end Services.Bootstrap.Acc
