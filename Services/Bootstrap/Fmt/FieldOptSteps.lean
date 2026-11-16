import Services.Bootstrap.Fmt.Tac

/-!
# Option-like field formatters of refine's Debug line: the steps

`o28_some` / `o28_none`: `<Option<Vec<u8>> as fmt::Debug>::fmt` (28739), the same code as 17465
(`os_some` / `os_none`) with other constants: `"Some"` at 67918, the field's vtable 75720
(`&Vec<u8>`), the return 28781 (1342); `"None"` at 67922. `fo_r`: the 3-instruction returns
(reload ω₀, pop 16 octets, jump) at 28781, 36575, 36635 and 26947.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem o28_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 16 < 4294967296)
    (hdis : v + 8 ≤ sp - 16 ∨ sp ≤ v) (rt : rdN μ v 8 ≠ 18446744073709551615)
    (hrv : ∀ a, v ≤ a → a < v + 8 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 28739 ω μ x 62471 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1342 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 67918 ∧ ω'[9] = UInt64.ofNat 4 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 75720 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = v ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rt' : rdN μ v 8 % 18446744073709551616 ≠ 18446744073709551615 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 μ v)]; exact rt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdis, rt, rt', hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega)]

theorem o28_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v F W : Nat) (hv : v + 8 < 4294967296 ∧ F + 16 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (rt : rdN μ v 8 = 18446744073709551615)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 28739 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat 67922 ∧ ω'[9] = UInt64.ofNat 4 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, rt, rW, rvt, rws, hro, hrv, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hW, rW]

theorem o36_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 16 < 4294967296)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 8 ≠ 18446744073709551615)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36534 ω μ x 62471 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1716 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68725 ∧ ω'[9] = UInt64.ofNat 4 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 75752 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = a ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rt' : rdN μ a 8 % 18446744073709551616 ≠ 18446744073709551615 := by
    rw [Nat.mod_eq_of_lt (rdN_lt64 μ a)]; exact rt
  have ha : a < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, ra, rt, rt', hrv, hra, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra]

theorem o36_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v a F W : Nat) (hv : v + 8 < 4294967296 ∧ a + 8 < 4294967296 ∧ F + 16 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 8 = 18446744073709551615)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 36534 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat 68733 ∧ ω'[9] = UInt64.ofNat 4 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, ra, rt, rW, hra, (show a < 18446744073709551616 by omega), rvt, rws, hro, hrv, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hW, rW]

/-- A 4-octet value, sign-extended to 64 bits, is 0 exactly when the value is. -/
theorem rdN_lt4 (μ : Memory) (a : Nat) : rdN μ a 4 < 4294967296 := by simpa using rdN_lt μ a 4

theorem sx4_zero {r : Nat} (hr : r < 4294967296) :
    (((if r < 2147483648 then (r : Int) else (r : Int) - 4294967296) % 18446744073709551616).toNat = 0) ↔ r = 0 := by
  by_cases h : r < 2147483648
  · simp only [h, if_true]; omega
  · simp only [h, if_false]; omega

theorem o365_some {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 8 < 4294967296)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 4 ≠ 0)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 4 → μ.readable b = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36594 ω μ x 62471 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1720 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68725 ∧ ω'[9] = UInt64.ofNat 4 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 76072 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = a + 4 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha : a < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, ra, rt, sx4_zero (rdN_lt4 μ a), hrv, hra, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra,
      Nat.mod_eq_of_lt (show a + 4 < 18446744073709551616 by omega)]

theorem o365_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (v a F W : Nat) (hv : v + 8 < 4294967296 ∧ a + 8 < 4294967296 ∧ F + 16 < 4294967296)
    (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 4 = 0)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true)
    (hra : ∀ b, a ≤ b → b < a + 4 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true) :
    ∃ ω', FreeStepsH p R 36594 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat 68733 ∧ ω'[9] = UInt64.ofNat 4 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hv, ra, rt, sx4_zero (rdN_lt4 μ a), rW, hra, (show a < 18446744073709551616 by omega), rvt, rws, hro, hrv, hrF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h7, h8, Nat.mod_eq_of_lt hW, rW]

/-- 26905 … 26940 (`Inline`, tag ≠ 0) or 26905 … 26975 (`Hash`, tag 0): `<&Code as Debug>::fmt`
    (the enum with an octet tag at a: 0 → `Hash` with the 32 octets at a + 1, field vtable 75528,
    `&[u8; 32]`; otherwise `Inline` with the `Vec<u8>` at a + 8, vtable 75720) calls
    `debug_tuple_field1_finish` (62471) with F, the name, T = sp − 16 and the vtable, returning to
    26947 (1260) or 26982 (1262). -/
theorem e26_inline {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 16 < 4294967296)
    (hdv : sp ≤ v) (hda : sp ≤ a ∨ a + 1 ≤ sp - 16)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 1 ≠ 0)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 1 → μ.readable b = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 26905 ω μ x 62471 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 1260 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68258 ∧ ω'[9] = UInt64.ofNat 6 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 75720 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = a + 8 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha : a < 18446744073709551616 := by omega
  have hb : rdN μ a 1 < 256 := by simpa using rdN_lt μ a 1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdv, hda, ra, rt, hrv, hra, hw, hr, ha, hb, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra,
      Nat.mod_eq_of_lt (show a + 8 < 18446744073709551616 by omega)]

theorem e26_hash {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 16 < 4294967296)
    (hdv : sp ≤ v) (hda : sp ≤ a ∨ a + 1 ≤ sp - 16)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 1 = 0)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 1 → μ.readable b = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 26905 ω μ x 62471 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 1262 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 67902 ∧ ω'[9] = UInt64.ofNat 4 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 75528 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = a + 1 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha : a < 18446744073709551616 := by omega
  have hb : rdN μ a 1 < 256 := by simpa using rdN_lt μ a 1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdv, hda, ra, rt, hrv, hra, hw, hr, ha, hb, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra,
      Nat.mod_eq_of_lt (show a + 1 < 18446744073709551616 by omega)]

theorem fo_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t i : Nat) (hi : i = 28781 ∨ i = 36575 ∨ i = 36635 ∨ i = 26947 ∨ i = 26982 ∨ i = 36693 ∨ i = 36724) (hT : 65536 ≤ T ∧ T + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (r0' : rdN μ (T + 8) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x t ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hT, r0', hret, hjt, hbt, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega)]

end Services.Bootstrap.Fmt
