import Services.Bootstrap.Fmt.Tac

/-!
# `<&Result<Output, ()> as Debug>::fmt` (36654) and `<() as Debug>` (37571): the steps

`r36_ok` / `r36_err` (36654 … 36687 / 36654 … 36718): with the slot v (ω₇) holding the `Result`'s
address a (its first word 2⁶⁴ − 1 for `Err`, a niche) and the `Formatter` F (ω₈), the frame
T = sp − 16 holds ω₀ at T + 8 and a at T; `debug_tuple_field1_finish` (62471) is called with `"Ok"`
(68932, 2) and the vtable 76456 (`&Output`, 37067), or `"Err"` (68934, 3) and 76488 (`()`, 37571),
returning to 36693 (1724) / 36724 (1726). `u37571`: `<() as Debug>`, `"()"` through `Formatter::pad`.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem r36_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 8 < 4294967296)
    (hdv : sp ≤ v) (hda : sp ≤ a ∨ a + 8 ≤ sp - 16)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 8 ≠ 18446744073709551615)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36654 ω μ x 62471 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1724 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68932 ∧ ω'[9] = UInt64.ofNat 2 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 76456 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = a ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha : a < 18446744073709551616 := by omega
  have rt' : rdN μ a 8 % 18446744073709551616 ≠ 18446744073709551615 := by rw [Nat.mod_eq_of_lt (rdN_lt64 μ a)]; exact rt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdv, hda, ra, rt, rt', hrv, hra, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra]

theorem r36_err {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ F < 18446744073709551616 ∧ v + 8 < 4294967296 ∧ a + 8 < 4294967296)
    (hdv : sp ≤ v) (hda : sp ≤ a ∨ a + 8 ≤ sp - 16)
    (ra : rdN μ v 8 = a) (rt : rdN μ a 8 = 18446744073709551615)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36654 ω μ x 62471 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1726 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = UInt64.ofNat 68934 ∧ ω'[9] = UInt64.ofNat 3 ∧
      ω'[10] = UInt64.ofNat (sp - 16) ∧ ω'[11] = UInt64.ofNat 76488 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = a ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have ha : a < 18446744073709551616 := by omega
  have rt' : rdN μ a 8 % 18446744073709551616 = 18446744073709551615 := by rw [Nat.mod_eq_of_lt (rdN_lt64 μ a)]; exact rt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hv, hdv, hda, ra, rt, rt', hrv, hra, hw, hr, ha, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt ha, ra]

/-- 37571 … 37586: `<() as Debug>::fmt`: `Formatter::pad` (64029) with `"()"` (68930, 2). -/
theorem u37571 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : F < 18446744073709551616) (h8 : ω[8] = UInt64.ofNat F) :
    ∃ ω', FreeStepsH p R 37571 ω μ x 64029 ω' μ x 5 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68930 ∧ ω'[9] = UInt64.ofNat 2 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h8, hF]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h8, Nat.mod_eq_of_lt hF]

end Services.Bootstrap.Fmt
