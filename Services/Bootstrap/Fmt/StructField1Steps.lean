import Services.Bootstrap.Fmt.DebugListSteps

/-!
# `Formatter::debug_struct_field1_finish` (62816): steps

Called with the `Formatter` F (ω₇), the struct's name (ω₈, ω₉), the field's name (ω₁₀, ω₁₁), the
value's slot v (ω₁₂) and, on the caller's stack at sp + 0, the value's vtable. The frame is
T = sp − 56: ω₀, ω₅, ω₆ at T + 48, + 40, + 32; v at T + 8; the field name's length at T + 0; the
`DebugStruct` at T + 16 (F, the result at T + 24, "has fields" at T + 25).

- `sf1_a`: 62816 … 62845, the struct's name to the sink's `write_str`, returning to 62850 (2662);
- `sf1_b`: 62850 … 62872, the `DebugStruct` {F, `Ok`, 0} at T + 16, then `DebugStruct::field`
  (65057), returning to 62878 (2664);
- `sf1_c`: 62878 … 62931, `DebugStruct::finish` with a field written and result `Ok`, plain
  options: `" }"` (72827, 2 octets) to the sink's `write_str`, returning to 62955 (2666);
- `sf1_d`: 62955 … 62970, the return (ω₇ = the result's low bit).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem sf1_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp F W fnm fnl v r0 v5 v6 : Nat) (hsp : 196608 + 56 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h10 : ω[10] = UInt64.ofNat fnm)
    (h11 : ω[11] = UInt64.ofNat fnl) (h12 : ω[12] = UInt64.ofNat v)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      fnm < 18446744073709551616 ∧ fnl < 18446744073709551616 ∧ v < 18446744073709551616 ∧ F + 24 < 4294967296)
    (hdis : F + 24 ≤ sp - 56 ∨ sp ≤ F)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hro : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, sp - 56 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 62816 ω μ x 59959 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 2662 ∧ ω'[1] = UInt64.ofNat (sp - 56) ∧ ω'[5] = UInt64.ofNat fnm ∧
      ω'[6] = UInt64.ofNat F ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = ω[8] ∧ ω'[9] = ω[9] ∧
      rdN μ' (sp - 56 + 48) 8 = r0 ∧ rdN μ' (sp - 56 + 40) 8 = v5 ∧ rdN μ' (sp - 56 + 32) 8 = v6 ∧
      rdN μ' (sp - 56 + 8) 8 = v ∧ rdN μ' (sp - 56) 8 = fnl ∧
      (∀ a, a < 4294967296 → (a < sp - 56 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 56 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h10, h11, h12, hsp, hv, hdis, rW, rvt, rws, hrF, hro, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h10,
      h11, h12, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2.1,
      Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega), rW]

theorem sf1_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F fnm fnl v vt : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat fnm) (h6 : ω[6] = UInt64.ofNat F)
    (h7 : ω[7] = UInt64.ofNat 0) (hv : fnm < 18446744073709551616 ∧ F < 18446744073709551616)
    (rn : rdN μ T 8 = fnl) (rv : rdN μ (T + 8) 8 = v) (rvt : rdN μ (T + 56) 8 = vt)
    (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true)
    (hw : ∀ a, T + 16 ≤ a → a < T + 26 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 62850 ω μ x 65057 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 2664 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat fnm ∧
      ω'[6] = UInt64.ofNat F ∧ ω'[7] = UInt64.ofNat (T + 16) ∧ ω'[8] = UInt64.ofNat fnm ∧
      ω'[9] = UInt64.ofNat fnl ∧ ω'[10] = UInt64.ofNat v ∧ ω'[11] = UInt64.ofNat vt ∧
      rdN μ' (T + 16) 8 = F ∧ rdN μ' (T + 24) 1 = 0 ∧ rdN μ' (T + 25) 1 = 0 ∧
      (∀ a, a < 4294967296 → (a < T + 16 ∨ T + 26 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrw : ∀ a, T + 16 ≤ a → a < T + 26 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hn : fnl < 18446744073709551616 := rn ▸ rdN_lt64 μ T
  have hvv : v < 18446744073709551616 := rv ▸ rdN_lt64 μ _
  have hvt : vt < 18446744073709551616 := rvt ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hT, hv, rn, rv, rvt, hr, hw, hrw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit1, Num.decodeLE_encodeLE, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hvv,
      Nat.mod_eq_of_lt hvt, rn, rv, rvt]

theorem sf1_c {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F W : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (hF : F + 24 < 4294967296)
    (rF : rdN μ (T + 16) 8 = F) (rr : rdN μ (T + 24) 1 = 0) (rh : rdN μ (T + 25) 1 = 1)
    (rfl8 : rdN μ (F + 18) 1 = 0)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hro : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62878 ω μ x 59959 ω' μ x 19 ∧
      ω'[0] = UInt64.ofNat 2666 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 72827 ∧ ω'[9] = UInt64.ofNat 2 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, hF, rF, rr, rh, rfl8, rW, rvt, rws, hr, hrF, hro, rdN_lit1, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt hW, rW]

theorem sf1_d {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat 0)
    (r0' : rdN μ (T + 48) 8 = r0) (r5 : rdN μ (T + 40) 8 = v5) (r6 : rdN μ (T + 32) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62955 ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h7, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 40)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 32)), r5, r6]

end Services.Bootstrap.Fmt
