import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# The items loop's operand arm, to the item's log line (6827 → 6955)

An operand at slot q (`RepOpBase`: the trace at + 0 … + 24, the result at + 24 … + 48, the four hashes
h at + 48 … + 176, the gas at + 176): `op_pre` saves some of its words and calls `memcpy` of the slot's
octets 8 … 136 to sp + 272 (so sp + 312 is h[0..32)); `op_mid` builds the operand's words at sp + 400
… + 448 and the arguments of the log line "Accumulating work item from {}": the pair
(sp + 312, 2502) at sp + 1144 (2502 is jump-table entry 1250, the formatter 56340), the template 66266
in ω₈ and the String's slot sp + 1568 in ω₇ (`item_fmt_site` starts at 6955, #162).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
variable {X : Type} {R : HostRel X}

/-- **6827 … 68729**, an operand at slot q: the slot's words at q + 144 and the i32 at q + 156 saved at
    sp + 240 / + 248, ω₇ (the slot's first word) at sp + 264, ω₁₀ at sp + 232, and the call of
    `memcpy` of 128 octets from ω₈ to sp + 272 (return address 230). -/
theorem op_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat q)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hq : 65536 ≤ q ∧ q + 184 ≤ sp)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (hrq : ∀ a, q ≤ a → a < q + 184 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 6827 ω μ x 68729 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 230 ∧ ω'[7] = UInt64.ofNat (sp + 272) ∧ ω'[9] = UInt64.ofNat 128 ∧
      rdN μ' (sp + 232) 8 = ω[10].toNat ∧ rdN μ' (sp + 240) 8 = rdN μ (q + 144) 8 ∧
      rdN μ' (sp + 248) 8 = sxw 4 (rdN μ (q + 156) 4) % 18446744073709551616 ∧
      rdN μ' (sp + 264) 8 = ω[7].toNat ∧
      (∀ a, a < 4294967296 → (a < sp + 232 ∨ sp + 256 ≤ a) → (a < sp + 264 ∨ sp + 272 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 7, 9] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hwf, hr, hrq, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_,
      by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE]; try simp)
    all_goals first | exact Nat.mod_eq_of_lt (rdN_lt64 _ _) | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) |
      (exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))) | skip
    all_goals first | rfl | exact rdN_lt64 _ _

/-- **6866 … 6955**, after the memcpy: the operand's words at q + 160, + 168, + 176 copied to
    sp + 424, + 432, + 440, ω₆ to sp + 400, the saved words at sp + 240 / + 232 / + 248 to sp + 408
    (u64) / + 416 (u32) / + 420 (u32), the i32 at sp + 256 to sp + 192, and the arguments of the item's
    log line: the pair (sp + 312, 2502) at sp + 1144 (the operand's first hash and its formatter),
    ω₇ = sp + 1568, ω₈ = 66266 (the template), ω₉ = sp + 1144. -/
theorem op_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp q : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat q)
    (hsp : 65536 ≤ sp ∧ sp + 1856 < 4294967296) (hq : 65536 ≤ q ∧ q + 184 ≤ sp)
    (hwf : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true)
    (hrq : ∀ a, q ≤ a → a < q + 184 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 6866 ω μ x 6955 ω' μ' x 30 ∧
      ω'[7] = UInt64.ofNat (sp + 1568) ∧ ω'[8] = UInt64.ofNat 66266 ∧ ω'[9] = UInt64.ofNat (sp + 1144) ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat q ∧
      rdN μ' (sp + 1144) 8 = sp + 312 ∧ rdN μ' (sp + 1152) 8 = 2502 ∧
      rdN μ' (sp + 424) 8 = rdN μ (q + 160) 8 ∧ rdN μ' (sp + 432) 8 = rdN μ (q + 168) 8 ∧
      rdN μ' (sp + 440) 8 = rdN μ (q + 176) 8 ∧ rdN μ' (sp + 400) 8 = ω[6].toNat ∧
      rdN μ' (sp + 408) 8 = rdN μ (sp + 240) 8 ∧ rdN μ' (sp + 416) 4 = rdN μ (sp + 232) 8 % 4294967296 ∧
      rdN μ' (sp + 420) 4 = rdN μ (sp + 248) 8 % 4294967296 ∧
      rdN μ' (sp + 192) 8 = sxw 4 (rdN μ (sp + 256) 4) % 18446744073709551616 ∧
      (∀ a, a < 4294967296 → (a < sp + 192 ∨ sp + 200 ≤ a) → (a < sp + 400 ∨ sp + 448 ≤ a) →
        (a < sp + 1144 ∨ sp + 1160 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [7, 8, 9, 10] → ω'[j] = ω[j] := by
  have hr : ∀ a, sp ≤ a → a < sp + 1856 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hwf, hr, hrq, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, (by reg_val <;> exact h1), (by reg_val <;> exact h5), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_, fun a => ?_, by reg_frame⟩
    all_goals try (rd_simp []; done)
    all_goals (simp (disch := pvm_arith) only [rdN, PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same,
      Num.decodeLE_encodeLE]; try simp)
    all_goals first | exact Nat.mod_eq_of_lt (rdN_lt64 _ _) | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _) |
      (exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))) | skip
    all_goals first | rfl | decide | omega | exact rdN_lt64 _ _ | skip

end Services.Bootstrap.Acc
