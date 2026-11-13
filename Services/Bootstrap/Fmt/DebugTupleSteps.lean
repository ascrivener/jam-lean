import Services.Bootstrap.Fmt.Tac

/-!
# `Formatter::debug_tuple_field1_finish` (62471): the steps, plain options

`f.debug_tuple_field1_finish(name, value)` with the `Formatter` F (ω₇), the name at nm (ω₈, nl > 0
octets, ω₉), the field's address v (ω₁₀) and `Debug` vtable vt (ω₁₁). The frame T = sp − 128 holds
ω₀, ω₅, ω₆ at T + 120, T + 112, T + 104, F at T + 0, nl at T + 8, the sink's vtable (77016) at
T + 16, vt at T + 24, v at T + 32 and the `String` W at T + 40.

- `dt_a` (62471 … 62508): the name to the sink's `write_str` (2596 → 59959), returning to 62513;
- `dt_b` (62513 … 62561), the name written: `"("` (72815), returning to 62566;
- `dt_c` (62566 … 62583): the field's `fmt` (the word at vt + 24) with v and F, returning to 62588;
- `dt_d` (62588 … 62796): `")"` (72824), returning to 62801;
- `dt_e` (62801 … 62814): ω₀, ω₅, ω₆ restored, sp := T + 128, return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem dt_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp F W nm nl v vt r0 v5 v6 : Nat) (hsp : 196608 + 128 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h8 : ω[8] = UInt64.ofNat nm)
    (h9 : ω[9] = UInt64.ofNat nl) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat vt)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      nm < 18446744073709551616 ∧ nl < 18446744073709551616 ∧ v < 18446744073709551616 ∧
      vt < 18446744073709551616 ∧ F + 16 < 4294967296)
    (hF : F + 16 ≤ sp - 128 ∨ sp ≤ F)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrF : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true)
    (hrv : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 62471 ω μ x 59959 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 2646 ∧ ω'[1] = UInt64.ofNat (sp - 128) ∧ ω'[5] = UInt64.ofNat 2596 ∧
      ω'[6] = UInt64.ofNat F ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat nm ∧ ω'[9] = UInt64.ofNat nl ∧
      rdN μ' (sp - 128 + 120) 8 = r0 ∧ rdN μ' (sp - 128 + 112) 8 = v5 ∧ rdN μ' (sp - 128 + 104) 8 = v6 ∧
      rdN μ' (sp - 128 + 8) 8 = nl ∧ rdN μ' (sp - 128 + 24) 8 = vt ∧ rdN μ' (sp - 128 + 32) 8 = v ∧
      rdN μ' (sp - 128 + 40) 8 = W ∧
      (∀ a, a < 4294967296 → (a < sp - 128 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, hsp, hv, hF, rW, rvt, rws, hrF, hrv, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8, h9,
      h10, h11, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.2.2.2.1, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega), rW]

theorem dt_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F W : Nat) (hT : 65536 ≤ T ∧ T + 128 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 2596) (h6 : ω[6] = UInt64.ofNat F)
    (h7 : ω[7] = UInt64.ofNat 0) (hF : F + 24 < 4294967296 ∧ (F + 24 ≤ T ∨ T + 128 ≤ F))
    (rfl8 : rdN μ (F + 18) 1 = 0) (rW : rdN μ (T + 40) 8 = W)
    (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hw : ∀ a, T ≤ a → a < T + 128 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 62513 ω μ x 59959 ω' μ' x 11 ∧
      ω'[0] = UInt64.ofNat 2648 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat 72815 ∧ ω'[9] = UInt64.ofNat 1 ∧ rdN μ' T 8 = F ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 128 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hT, hF, rfl8, rW, hrF, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt (show F < 18446744073709551616 by omega)]

theorem dt_c {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F v vt fn e : Nat) (hT : 65536 ≤ T ∧ T + 128 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat 0)
    (rF : rdN μ T 8 = F) (rvt : rdN μ (T + 24) 8 = vt) (rv : rdN μ (T + 32) 8 = v)
    (rfn : rdN μ (vt + 24) 8 = fn) (hvt : vt + 32 < 4294967296)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hr : ∀ a, T ≤ a → a < T + 128 → μ.readable a = true)
    (hrv : ∀ a, vt + 24 ≤ a → a < vt + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62566 ω μ x e ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 2650 ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat F ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat F := by
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  have hF : F < 18446744073709551616 := rF ▸ rdN_lt64 μ _
  have hv : v < 18446744073709551616 := rv ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hT, rF, rvt, rv, rfn, hvt, hfn, hfn', hjt, hbt, hr, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt hF, Nat.mod_eq_of_lt hv, rF, rv]

theorem dt_d {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F W nl : Nat) (hT : 65536 ≤ T ∧ T + 128 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0)
    (hF : F + 16 < 4294967296) (rnl : rdN μ (T + 8) 8 = nl) (hnl : nl ≠ 0)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hr : ∀ a, T ≤ a → a < T + 128 → μ.readable a = true)
    (hrF : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true)
    (hrv : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62588 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat 2660 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat 72824 ∧ ω'[9] = UInt64.ofNat 1 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  have hnl' : nl % 18446744073709551616 ≠ 0 := by
    have := rnl ▸ rdN_lt64 μ (T + 8); rw [Nat.mod_eq_of_lt this]; exact hnl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h7, hT, hF, rnl, hnl, hnl', rW, rvt, rws, hr, hrF, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hW, rW]

theorem dt_e {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 128 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 120) 8 = r0) (r5 : rdN μ (T + 112) 8 = v5) (r6 : rdN μ (T + 104) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 128 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62801 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 128) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 112)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 104)), r5, r6]

end Services.Bootstrap.Fmt
