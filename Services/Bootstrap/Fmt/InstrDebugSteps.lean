import Services.Bootstrap.Fmt.DebugListSteps

/-!
# `<&Instruction as Debug>::fmt` (26990): steps for the milestone's arms

`id_t`: from the slot v (ω₇) holding the element's address a and the `Formatter` F (ω₈), with the
element's discriminant word 2⁶³ − 1 + t at a: the 320-octet frame at T = sp − 320 (ω₀, ω₅, ω₆ at
T + 312, + 304, + 296), the dispatch through the jump table at 67576, and the arm for tag t, to its
`debug_struct_field*_finish` with the struct's and the fields' names, the fields (each the field's
address, or for the last one the slot T + 152 holding it) and their vtables (the first on the stack at
T, the others at T + 8 + 32 (i − 2) …). `ir_ret`: the common return (restoring ω₀, ω₅, ω₆).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 26990 … 63149: `<&Instruction as Debug>` with tag 1 (the word at a = 2⁶³ − 1 + 1): the dispatch
    (the jump table at 67576) and the arm, to its builder (63149) returning through 1298. -/
theorem id_1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775808) (rj : rdN μ 67580 4 = 4294901016)
    (hro : ∀ b, 67580 ≤ b → b < 67584 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 63149 ω' μ' x 43 ∧
      ω'[0] = UInt64.ofNat 1298 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 67969 ∧
      ω'[9] = UInt64.ofNat 7 ∧
      ω'[10] = UInt64.ofNat 67856 ∧
      ω'[11] = UInt64.ofNat 9 ∧
      ω'[12] = UInt64.ofNat (a + 8) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 74808 ∧
      rdN μ' (sp - 320 + 8) 8 = 67865 ∧
      rdN μ' (sp - 320 + 16) 8 = 12 ∧
      rdN μ' (sp - 320 + 24) 8 = (a + 40) ∧
      rdN μ' (sp - 320 + 32) 8 = 74840 ∧
      rdN μ' (sp - 320 + 40) 8 = 67877 ∧
      rdN μ' (sp - 320 + 48) 8 = 12 ∧
      rdN μ' (sp - 320 + 56) 8 = (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 64) 8 = 75112 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 48) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 40) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 48) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 63347: `<&Instruction as Debug>` with tag 2 (the word at a = 2⁶³ − 1 + 2): the dispatch
    (the jump table at 67576) and the arm, to its builder (63347) returning through 1288. -/
theorem id_2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775809) (rj : rdN μ 67584 4 = 4294901006)
    (hro : ∀ b, 67584 ≤ b → b < 67588 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 63347 ω' μ' x 50 ∧
      ω'[0] = UInt64.ofNat 1288 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 67720 ∧
      ω'[9] = UInt64.ofNat 8 ∧
      ω'[10] = UInt64.ofNat 67976 ∧
      ω'[11] = UInt64.ofNat 11 ∧
      ω'[12] = UInt64.ofNat (a + 152) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75144 ∧
      rdN μ' (sp - 320 + 8) 8 = 67987 ∧
      rdN μ' (sp - 320 + 16) 8 = 6 ∧
      rdN μ' (sp - 320 + 24) 8 = (a + 136) ∧
      rdN μ' (sp - 320 + 32) 8 = 74840 ∧
      rdN μ' (sp - 320 + 40) 8 = 67993 ∧
      rdN μ' (sp - 320 + 48) 8 = 9 ∧
      rdN μ' (sp - 320 + 56) 8 = (a + 144) ∧
      rdN μ' (sp - 320 + 64) 8 = 74840 ∧
      rdN μ' (sp - 320 + 72) 8 = 67898 ∧
      rdN μ' (sp - 320 + 80) 8 = 4 ∧
      rdN μ' (sp - 320 + 88) 8 = (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 96) 8 = 75176 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 8) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 136) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 144) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 152) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 62816: `<&Instruction as Debug>` with tag 3 (the word at a = 2⁶³ − 1 + 3): the dispatch
    (the jump table at 67576) and the arm, to its builder (62816) returning through 1328. -/
theorem id_3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775810) (rj : rdN μ 67588 4 = 4294901012)
    (hro : ∀ b, 67588 ≤ b → b < 67592 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 62816 ω' μ' x 29 ∧
      ω'[0] = UInt64.ofNat 1328 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68002 ∧
      ω'[9] = UInt64.ofNat 7 ∧
      ω'[10] = UInt64.ofNat 68009 ∧
      ω'[11] = UInt64.ofNat 7 ∧
      ω'[12] = UInt64.ofNat (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75208 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 8) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 62972: `<&Instruction as Debug>` with tag 4 (the word at a = 2⁶³ − 1 + 4): the dispatch
    (the jump table at 67576) and the arm, to its builder (62972) returning through 1312. -/
theorem id_4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775811) (rj : rdN μ 67592 4 = 4294900998)
    (hro : ∀ b, 67592 ≤ b → b < 67596 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 62972 ω' μ' x 37 ∧
      ω'[0] = UInt64.ofNat 1312 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68016 ∧
      ω'[9] = UInt64.ofNat 5 ∧
      ω'[10] = UInt64.ofNat 68021 ∧
      ω'[11] = UInt64.ofNat 6 ∧
      ω'[12] = UInt64.ofNat (a + 40) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75144 ∧
      rdN μ' (sp - 320 + 8) 8 = 67856 ∧
      rdN μ' (sp - 320 + 16) 8 = 9 ∧
      rdN μ' (sp - 320 + 24) 8 = (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 32) 8 = 75240 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 8) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 40) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 62972: `<&Instruction as Debug>` with tag 6 (the word at a = 2⁶³ − 1 + 6): the dispatch
    (the jump table at 67576) and the arm, to its builder (62972) returning through 1312. -/
theorem id_6 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775813) (rj : rdN μ 67600 4 = 4294901030)
    (hro : ∀ b, 67600 ≤ b → b < 67604 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 62972 ω' μ' x 37 ∧
      ω'[0] = UInt64.ofNat 1312 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68051 ∧
      ω'[9] = UInt64.ofNat 7 ∧
      ω'[10] = UInt64.ofNat 67906 ∧
      ω'[11] = UInt64.ofNat 4 ∧
      ω'[12] = UInt64.ofNat (a + 8) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75304 ∧
      rdN μ' (sp - 320 + 8) 8 = 68058 ∧
      rdN μ' (sp - 320 + 16) 8 = 3 ∧
      rdN μ' (sp - 320 + 24) 8 = (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 32) 8 = 75112 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 40) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 40) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 62972: `<&Instruction as Debug>` with tag 7 (the word at a = 2⁶³ − 1 + 7): the dispatch
    (the jump table at 67576) and the arm, to its builder (62972) returning through 1312. -/
theorem id_7 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775814) (rj : rdN μ 67604 4 = 4294901014)
    (hro : ∀ b, 67604 ≤ b → b < 67608 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 62972 ω' μ' x 37 ∧
      ω'[0] = UInt64.ofNat 1312 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68061 ∧
      ω'[9] = UInt64.ofNat 6 ∧
      ω'[10] = UInt64.ofNat 67906 ∧
      ω'[11] = UInt64.ofNat 4 ∧
      ω'[12] = UInt64.ofNat (a + 8) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75304 ∧
      rdN μ' (sp - 320 + 8) 8 = 68058 ∧
      rdN μ' (sp - 320 + 16) 8 = 3 ∧
      rdN μ' (sp - 320 + 24) 8 = (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 32) 8 = 75112 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 40) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 40) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 63149: `<&Instruction as Debug>` with tag 8 (the word at a = 2⁶³ − 1 + 8): the dispatch
    (the jump table at 67576) and the arm, to its builder (63149) returning through 1320. -/
theorem id_8 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775815) (rj : rdN μ 67608 4 = 4294901038)
    (hro : ∀ b, 67608 ≤ b → b < 67612 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 63149 ω' μ' x 47 ∧
      ω'[0] = UInt64.ofNat 1320 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68067 ∧
      ω'[9] = UInt64.ofNat 6 ∧
      ω'[10] = UInt64.ofNat 68073 ∧
      ω'[11] = UInt64.ofNat 7 ∧
      ω'[12] = UInt64.ofNat (a + 8) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75144 ∧
      rdN μ' (sp - 320 + 8) 8 = 67906 ∧
      rdN μ' (sp - 320 + 16) 8 = 4 ∧
      rdN μ' (sp - 320 + 24) 8 = (a + 12) ∧
      rdN μ' (sp - 320 + 32) 8 = 75304 ∧
      rdN μ' (sp - 320 + 40) 8 = 68080 ∧
      rdN μ' (sp - 320 + 48) 8 = 5 ∧
      rdN μ' (sp - 320 + 56) 8 = (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 64) 8 = 75336 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 44) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 12) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 44) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 62816: `<&Instruction as Debug>` with tag 14 (the word at a = 2⁶³ − 1 + 14): the dispatch
    (the jump table at 67576) and the arm, to its builder (62816) returning through 1328. -/
theorem id_14 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775821) (rj : rdN μ 67632 4 = 4294900992)
    (hro : ∀ b, 67632 ≤ b → b < 67636 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 62816 ω' μ' x 29 ∧
      ω'[0] = UInt64.ofNat 1328 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 68149 ∧
      ω'[9] = UInt64.ofNat 5 ∧
      ω'[10] = UInt64.ofNat 67906 ∧
      ω'[11] = UInt64.ofNat 4 ∧
      ω'[12] = UInt64.ofNat (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75528 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 8) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega),
      rv]

/-- 26990 … 62816: `<&Instruction as Debug>` with tag 20 (the word at a = 2⁶³ − 1 + 20): the dispatch
    (the jump table at 67576) and the arm, to its builder (62816) returning through 1328. -/
theorem id_20 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F < 18446744073709551616)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775827) (rj : rdN μ 67656 4 = 4294901022)
    (hro : ∀ b, 67656 ≤ b → b < 67660 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 62816 ω' μ' x 29 ∧
      ω'[0] = UInt64.ofNat 1328 ∧
      ω'[1] = UInt64.ofNat (sp - 320) ∧
      ω'[7] = UInt64.ofNat F ∧
      ω'[8] = UInt64.ofNat 67712 ∧
      ω'[9] = UInt64.ofNat 8 ∧
      ω'[10] = UInt64.ofNat 68186 ∧
      ω'[11] = UInt64.ofNat 5 ∧
      ω'[12] = UInt64.ofNat (sp - 320 + 152) ∧
      rdN μ' (sp - 320 + 312) 8 = r0 ∧
      rdN μ' (sp - 320 + 304) 8 = v5 ∧
      rdN μ' (sp - 320 + 296) 8 = v6 ∧
      rdN μ' (sp - 320) 8 = 75112 ∧
      rdN μ' (sp - 320 + 152) 8 = (a + 8) ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, hro, hrv, hra, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2,
      Nat.mod_eq_of_lt (show v < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show a + 232 < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (sp - 320 + 152) < 18446744073709551616 by omega), Nat.mod_eq_of_lt (show (a + 8) < 18446744073709551616 by omega),
      rv]


/-- The arms' common return (28031, 27806, 28298, 28480, 28589): ω₀, ω₅, ω₆ restored from T + 312,
    + 304, + 296 and the frame popped; ω₇ (the builder's result) kept. -/
theorem ir_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 i : Nat) (hi : i = 28031 ∨ i = 27806 ∨ i = 28298 ∨ i = 28480 ∨ i = 28589)
    (hT : 65536 ≤ T ∧ T + 320 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 312) 8 = r0) (r5 : rdN μ (T + 304) 8 = v5) (r6 : rdN μ (T + 296) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 320 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R i ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 320) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
        Nat.mod_eq_of_lt (rdN_lt64 μ (T + 304)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 296)), r5, r6]

/-- 26990 … 59959: `<&Instruction as Debug>` with tag 15 (a unit variant): the dispatch, the frame
    popped again, and its name (10 octets at 68154) to the sink's `write_str` (`Formatter::write_str`,
    64485) with the `String` W; ω₀, ω₁, ω₅, ω₆ as on entry. -/
theorem id_15 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F W r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F + 16 < 4294967296)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a) ∧ (F + 16 ≤ sp - 320 ∨ sp ≤ F))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775822) (rj : rdN μ 67636 4 = 4294901010)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 59959 ω' μ' x 29 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 68154 ∧ ω'[9] = UInt64.ofNat 10 ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, rW, rvt, rws, hro, hrv, hra, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hW,
      Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega), rv, rW]

/-- 26990 … 59959: `<&Instruction as Debug>` with tag 16 (a unit variant): the dispatch, the frame
    popped again, and its name (5 octets at 68164) to the sink's `write_str` (`Formatter::write_str`,
    64485) with the `String` W; ω₀, ω₁, ω₅, ω₆ as on entry. -/
theorem id_16 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F W r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F + 16 < 4294967296)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a) ∧ (F + 16 ≤ sp - 320 ∨ sp ≤ F))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775823) (rj : rdN μ 67640 4 = 4294900990)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 59959 ω' μ' x 29 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 68164 ∧ ω'[9] = UInt64.ofNat 5 ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, rW, rvt, rws, hro, hrv, hra, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hW,
      Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega), rv, rW]

/-- 26990 … 59959: `<&Instruction as Debug>` with tag 23 (a unit variant): the dispatch, the frame
    popped again, and its name (9 octets at 68233) to the sink's `write_str` (`Formatter::write_str`,
    64485) with the `String` W; ω₀, ω₁, ω₅, ω₆ as on entry. -/
theorem id_23 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v a F W r0 v5 v6 : Nat) (hsp : 196608 + 320 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ a + 232 < 4294967296 ∧ F + 16 < 4294967296)
    (hdis : (v + 8 ≤ sp - 320 ∨ sp ≤ v) ∧ (a + 8 ≤ sp - 320 ∨ sp ≤ a) ∧ (F + 16 ≤ sp - 320 ∨ sp ≤ F))
    (rv : rdN μ v 8 = a) (rt : rdN μ a 8 = 9223372036854775830) (rj : rdN μ 67668 4 = 4294901050)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hro : ∀ b, 65536 ≤ b → b < 77144 → μ.readable b = true)
    (hrv : ∀ b, v ≤ b → b < v + 8 → μ.readable b = true) (hra : ∀ b, a ≤ b → b < a + 8 → μ.readable b = true)
    (hrF : ∀ b, F ≤ b → b < F + 16 → μ.readable b = true)
    (hw : ∀ b, sp - 320 ≤ b → b < sp → μ.writable b = true) :
    ∃ ω' μ', FreeStepsH p R 26990 ω μ x 59959 ω' μ' x 29 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 68233 ∧ ω'[9] = UInt64.ofNat 9 ∧
      (∀ b, b < 4294967296 → (b < sp - 320 ∨ sp ≤ b) → μ'.read b = μ.read b) ∧
      (∀ b, μ'.readable b = μ.readable b) ∧ (∀ b, μ'.writable b = μ.writable b) := by
  have hr : ∀ b, sp - 320 ≤ b → b < sp → μ.readable b = true := fun b h1 h2 => Memory.readable_of_writable (hw b h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hdis, rv, rt, rj, rW, rvt, rws, hro, hrv, hra, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun b hb0 hb1 => ?_, fun b => ?_, fun b => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hW,
      Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega), rv, rW]

end Services.Bootstrap.Fmt
