import Services.Bootstrap.Fmt.DebugListSteps

/-!
# `DebugStruct::field` (65057): steps

A `DebugStruct` at D has the layout of a `DebugList` (`DL`): the `Formatter` pointer F (D + 0), the
result so far (an octet at D + 8, 0 for `Ok`) and whether a field was written (an octet at D + 9).
`DebugStruct::field` (plain options, result `Ok`) writes `" { "` before the first field and `", "`
before each later one, then the field's name, `": "`, and the value through its `Debug` vtable;
then the result and "has fields" are stored at D. Its frame is T = sp − 112.

- `ds_a`: 65057 … 65143, to the sink's `write_str` (the word at 77040, 2596 → 59959) with the
  prefix (72803 + 3h, 3 − h octets), returning to 65148 (2738);
- `ds_b`: 65148 … 65174, the name, returning to 65179 (2740);
- `ds_c`: 65179 … 65209, `": "` (72808, 2 octets), returning to 65214 (2742);
- `ds_d`: 65214 … 65237, the value's `fmt` (the word at vt + 24) with the value v and F, returning
  to 65242 (2744);
- `ds_e`: 65242 … 65464, the result and "has fields" stored at D, and the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 65057 … 65143: the frame T = sp − 112 (ω₀, ω₅, ω₆ at + 104, + 96, + 88; the value's vtable vt
    at + 16, the value v at + 24, F at + 8, the name's length nl at + 0); the prefix (`" { "` if no
    field was written, h = 0, else `", "`) goes to the sink's `write_str` with the `String` W;
    D stays in ω₅ and the name nm in ω₆. -/
theorem ds_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D F W nm nl v vt h r0 v5 v6 : Nat) (hsp : 196608 + 112 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat nm)
    (h9 : ω[9] = UInt64.ofNat nl) (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat vt)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      nm < 18446744073709551616 ∧ nl < 18446744073709551616 ∧ v < 18446744073709551616 ∧
      vt < 18446744073709551616 ∧ D + 16 < 4294967296 ∧ F + 24 < 4294967296)
    (hdis : (D + 16 ≤ sp - 112 ∨ sp ≤ D) ∧ (F + 24 ≤ sp - 112 ∨ sp ≤ F))
    (hh : h = 0 ∨ h = 1)
    (rD : rdN μ D 8 = F) (rr : rdN μ (D + 8) 1 = 0) (rh : rdN μ (D + 9) 1 = h) (rfl8 : rdN μ (F + 18) 1 = 0)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrD : ∀ a, D ≤ a → a < D + 16 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hro : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, sp - 112 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 65057 ω μ x 59959 ω' μ' x 31 ∧
      ω'[0] = UInt64.ofNat 2738 ∧ ω'[1] = UInt64.ofNat (sp - 112) ∧ ω'[5] = UInt64.ofNat D ∧
      ω'[6] = UInt64.ofNat nm ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat (72803 + 3 * h) ∧
      ω'[9] = UInt64.ofNat (3 - h) ∧
      rdN μ' (sp - 112 + 104) 8 = r0 ∧ rdN μ' (sp - 112 + 96) 8 = v5 ∧ rdN μ' (sp - 112 + 88) 8 = v6 ∧
      rdN μ' (sp - 112 + 16) 8 = vt ∧ rdN μ' (sp - 112 + 24) 8 = v ∧ rdN μ' (sp - 112 + 8) 8 = F ∧
      rdN μ' (sp - 112) 8 = nl ∧
      (∀ a, a < 4294967296 → (a < sp - 112 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 112 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  have hF64 : F < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  rcases hh with rfl | rfl
  all_goals
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, hsp, hv, hdis, rD, rr, rh, rfl8, rW, rvt, rws, hrD, hrF, hro, hw,
        hr, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8, h9,
        h10, h11, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
        Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.1,
        Nat.mod_eq_of_lt hv.2.2.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2.2.1,
        Nat.mod_eq_of_lt (show D < 18446744073709551616 by omega), rD, rW]

/-- 65148 … 65174: after the prefix (`write_str` returned `Ok`, ω₇ = 0), the name nm (ω₆) of nl
    octets (the word at T) to the sink's `write_str`, returning to 65179 (2740). -/
theorem ds_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T D F W nm nl : Nat) (hT : 65536 ≤ T ∧ T + 112 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat D) (h6 : ω[6] = UInt64.ofNat nm)
    (h7 : ω[7] = UInt64.ofNat 0) (hv : nm < 18446744073709551616 ∧ F + 24 < 4294967296)
    (rn : rdN μ T 8 = nl) (rF : rdN μ (T + 8) 8 = F)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrT : ∀ a, T ≤ a → a < T + 112 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hro : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 65148 ω μ x 59959 ω' μ x 11 ∧
      ω'[0] = UInt64.ofNat 2740 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat D ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat nm ∧ ω'[9] = UInt64.ofNat nl := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  have hn : nl < 18446744073709551616 := rn ▸ rdN_lt64 μ T
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hT, hv, rn, rF, rW, rvt, rws, hrT, hrF, hro, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h6, h7, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hv.1, rW, rn]

/-- 65179 … 65209: after the name, `": "` (72808, 2 octets) to the sink's `write_str`, returning to
    65214 (2742). -/
theorem ds_c {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T D F W : Nat) (hT : 65536 ≤ T ∧ T + 112 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat D) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : F + 24 < 4294967296) (rF : rdN μ (T + 8) 8 = F)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrT : ∀ a, T ≤ a → a < T + 112 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hro : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 65179 ω μ x 59959 ω' μ x 11 ∧
      ω'[0] = UInt64.ofNat 2742 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat D ∧
      ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 72808 ∧ ω'[9] = UInt64.ofNat 2 := by
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h7, hT, hv, rF, rW, rvt, rws, hrT, hrF, hro, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h7, Nat.mod_eq_of_lt hW, rW]

/-- 65214 … 65237: after `": "`, the value's `fmt` (the word fn at vt + 24, vt the word at T + 16,
    resolving to e) with the value v (the word at T + 24) and F, returning to 65242 (2744). -/
theorem ds_d {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T D F v vt fn e : Nat) (hT : 65536 ≤ T ∧ T + 112 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat D) (h7 : ω[7] = UInt64.ofNat 0)
    (hvt : vt + 32 < 4294967296) (rF : rdN μ (T + 8) 8 = F) (rvt : rdN μ (T + 16) 8 = vt)
    (rv : rdN μ (T + 24) 8 = v) (rfn : rdN μ (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hrT : ∀ a, T ≤ a → a < T + 112 → μ.readable a = true)
    (hrv : ∀ a, vt + 24 ≤ a → a < vt + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 65214 ω μ x e ω' μ x 9 ∧
      ω'[0] = UInt64.ofNat 2744 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat D ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat F := by
  have hF : F < 18446744073709551616 := rF ▸ rdN_lt64 μ _
  have hv : v < 18446744073709551616 := rv ▸ rdN_lt64 μ _
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h7, hT, hvt, rF, rvt, rv, rfn, hfn, hfn', hjt, hbt, hrT, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h7, Nat.mod_eq_of_lt hF, Nat.mod_eq_of_lt hv, rF, rv]

/-- 65242 … 65464: after the value (its result res in ω₇), the result and "has fields" (1) stored at
    D (ω₅), ω₇ = D, and the return: ω₀, ω₅, ω₆ restored from T + 104, + 96, + 88. -/
theorem ds_e {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T D r0 t v5 v6 res : Nat) (hT : 65536 ≤ T ∧ T + 112 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat D) (h7 : ω[7] = UInt64.ofNat res)
    (hres : res < 256) (hD : D + 16 < 4294967296 ∧ (D + 16 ≤ T ∨ T + 112 ≤ D))
    (r0' : rdN μ (T + 104) 8 = r0) (r5 : rdN μ (T + 96) 8 = v5) (r6 : rdN μ (T + 88) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, T ≤ a → a < T + 112 → μ.readable a = true)
    (hw : ∀ a, D + 8 ≤ a → a < D + 10 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 65242 ω μ x t ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat D ∧ rdN μ' (D + 8) 1 = res ∧ rdN μ' (D + 9) 1 = 1 ∧
      (∀ a, a < 4294967296 → (a < D + 8 ∨ D + 10 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrD : ∀ a, D + 8 ≤ a → a < D + 10 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hT, hres, hD, r0', r5, r6, hret, hjt, hbt, hr, hw, hrD, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_lit1, dec1 res hres, Num.decodeLE_encodeLE, h1, h5, h7,
      Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show D < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 96)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 88))]

end Services.Bootstrap.Fmt
