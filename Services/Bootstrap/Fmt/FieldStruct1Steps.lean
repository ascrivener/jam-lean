import Services.Bootstrap.Fmt.Tac

/-!
# One-field structs of refine's Debug line: the steps (step 8)

`s1_36917` (`<&Item as Debug>`, 36917 … 36958) and `s1_37067` (`<&Output as Debug>`, 37067 … 37108):
with the slot v (ω₇) holding the struct's address a and the `Formatter` F (ω₈), a 24-octet frame
T = sp − 24 holds ω₀ at T + 16, a at T + 8 (the field's slot) and the field's vtable at T;
`debug_struct_field1_finish` (62816) is called with the struct's and the field's names, returning
to 36964 (1748) / 37114 (1756). `s1_r`: those returns.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem s1_36917 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 24 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296)
    (hdv : sp ≤ v) (ra : rdN μ v 8 = a) (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 24 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 36917 ω μ x 62816 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 1748 ∧ ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68737 ∧ ω'[9] = UInt64.ofNat 4 ∧
      ω'[10] = UInt64.ofNat 68757 ∧ ω'[11] = UInt64.ofNat 3 ∧ ω'[12] = UInt64.ofNat (sp - 24 + 8) ∧
      rdN μ' (sp - 24 + 16) 8 = r0 ∧ rdN μ' (sp - 24 + 8) 8 = a ∧ rdN μ' (sp - 24) 8 = 76040 ∧
      (∀ b, b < 4294967296 → (b < sp - 24 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 24 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have ha : a < 18446744073709551616 := ra ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdv, ra, hrv, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, Nat.reduceMul,
      Nat.reducePow, h0, h1, h7, h8, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra,
      Nat.mod_eq_of_lt (show sp - 24 + 8 < 18446744073709551616 by omega)]

theorem s1_37067 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 24 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296)
    (hdv : sp ≤ v) (ra : rdN μ v 8 = a) (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 24 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 37067 ω μ x 62816 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 1756 ∧ ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68760 ∧ ω'[9] = UInt64.ofNat 6 ∧
      ω'[10] = UInt64.ofNat 68766 ∧ ω'[11] = UInt64.ofNat 5 ∧ ω'[12] = UInt64.ofNat (sp - 24 + 8) ∧
      rdN μ' (sp - 24 + 16) 8 = r0 ∧ rdN μ' (sp - 24 + 8) 8 = a ∧ rdN μ' (sp - 24) 8 = 76168 ∧
      (∀ b, b < 4294967296 → (b < sp - 24 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 24 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have ha : a < 18446744073709551616 := ra ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdv, ra, hrv, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, Nat.reduceMul,
      Nat.reducePow, h0, h1, h7, h8, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra,
      Nat.mod_eq_of_lt (show sp - 24 + 8 < 18446744073709551616 by omega)]

theorem s1_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t i : Nat) (hi : i = 36964 ∨ i = 37114) (hT : 65536 ≤ T ∧ T + 24 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (r0' : rdN μ (T + 16) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x t ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 24) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hT, r0', hret, hjt, hbt, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega)]

end Services.Bootstrap.Fmt
