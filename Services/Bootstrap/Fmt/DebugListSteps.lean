import Services.Bootstrap.Fmt.Tac

/-!
# `Formatter::debug_list` (61708), `DebugList::entry` (66019) and `DebugList::finish` (66310): steps

A `DebugList` at D is the `Formatter` pointer F (D + 0), the result so far (an octet at D + 8, 0 for
`Ok`) and whether an entry was written (an octet at D + 9).

- `dl_a`: 61708 … the sink's `write_str` (59959 for the `String`), writing `[` (72829, 1 octet),
  returning to 61746 (2622);
- `dl_b`: 61746 … the return: the `DebugList` {F, result, 0} stored at D.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 61708 … 61741: `debug_list`'s 24-octet frame at sp − 24 (ω₀, ω₅, ω₆ at +16, +8, +0) and the
    sink's `write_str` (the word at the vtable + 24, 2596 for the `String`) called with the sink W,
    `[` (72829) and 1, returning to 61746 (2622); F in ω₅ and D in ω₆. -/
theorem dl_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D F W r0 v5 v6 : Nat) (hsp : 196608 + 24 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      D < 18446744073709551616 ∧ F + 16 < 4294967296)
    (hF : F + 16 ≤ sp - 24 ∨ sp ≤ F)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrF : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true)
    (hrv : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 61708 ω μ x 59959 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 2622 ∧ ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = UInt64.ofNat F ∧
      ω'[6] = UInt64.ofNat D ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 72829 ∧
      ω'[9] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 24 + 16) 8 = r0 ∧ rdN μ' (sp - 24 + 8) 8 = v5 ∧ rdN μ' (sp - 24) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 24 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hF, rW, rvt, rws, hrF, hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1,
      Nat.mod_eq_of_lt hW, rW]

/-- One octet, just written at a, read back. -/
theorem rdN_lit1 (μ : Memory) (a : Nat) (b : UInt8) (ha : a + 1 ≤ 4294967296) :
    rdN (μ.writeN a [b]) a 1 = Num.decodeLE [b] := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp only [two32]; omega)]

/-- 61746 … the return: the `DebugList` at D: F (D + 0), the result 0 (D + 8), no entry yet (D + 9);
    ω₀, ω₅, ω₆ restored from the frame at T = sp − 24. -/
theorem dl_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T D F r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 24 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat D)
    (h7 : ω[7] = UInt64.ofNat 0) (hF : F < 18446744073709551616)
    (hD : D + 16 < 4294967296 ∧ (D + 16 ≤ T ∨ T + 24 ≤ D))
    (r0' : rdN μ (T + 16) 8 = r0) (r5 : rdN μ (T + 8) 8 = v5) (r6 : rdN μ T 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, T ≤ a → a < T + 24 → μ.readable a = true)
    (hw : ∀ a, D ≤ a → a < D + 10 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 61746 ω μ x t ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 24) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      rdN μ' D 8 = F ∧ rdN μ' (D + 8) 1 = 0 ∧ rdN μ' (D + 9) 1 = 0 ∧
      (∀ a, a < 4294967296 → (a < D ∨ D + 10 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrD : ∀ a, D ≤ a → a < D + 10 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hT, hF, hD, r0', r5, r6, hret, hjt, hbt, hr, hw, hrD, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, rdN_lit1, Num.decodeLE_encodeLE, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hF, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 8)), Nat.mod_eq_of_lt (rdN_lt64 μ T)]

end Services.Bootstrap.Fmt
