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

/-- One octet below 256 decodes to itself. -/
theorem dec1 (r : Nat) (h : r < 256) : Num.decodeLE [UInt8.ofNat r] = r := by
  simp [Num.decodeLE, UInt8.toNat_ofNat]; omega

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

/-- 66019 … 66123, `DebugList::entry` (D = ω₇, the value v = ω₈, its `Debug` vtable vt = ω₉) when the
    list has no entry yet (D + 9 = 0) and its result is `Ok` (D + 8 = 0), with plain options (the
    flags octet F + 18 is 0, so no `{:#?}`): the frame at T = sp − 104 holds ω₀, ω₅, ω₆ and D; the
    value's `fmt` (the word at vt + 24) is called with v and F, returning to 66128 (2774). -/
theorem de_a0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D F v vt fn e r0 v5 v6 : Nat) (hsp : 196608 + 104 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat v)
    (h9 : ω[9] = UInt64.ofNat vt)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v < 18446744073709551616 ∧ D + 16 < 4294967296 ∧ F + 24 < 4294967296 ∧ vt + 32 < 4294967296)
    (hdis : (D + 16 ≤ sp - 104 ∨ sp ≤ D) ∧ (F + 24 ≤ sp - 104 ∨ sp ≤ F) ∧ (vt + 32 ≤ sp - 104 ∨ sp ≤ vt))
    (rD : rdN μ D 8 = F) (rr : rdN μ (D + 8) 1 = 0) (rh : rdN μ (D + 9) 1 = 0) (rfl8 : rdN μ (F + 18) 1 = 0)
    (rfn : rdN μ (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hrD : ∀ a, D ≤ a → a < D + 16 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hrv : ∀ a, vt + 24 ≤ a → a < vt + 32 → μ.readable a = true)
    (hw : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 66019 ω μ x e ω' μ' x 22 ∧
      ω'[0] = UInt64.ofNat 2774 ∧ ω'[1] = UInt64.ofNat (sp - 104) ∧ ω'[7] = UInt64.ofNat v ∧
      ω'[8] = UInt64.ofNat F ∧
      rdN μ' (sp - 104 + 96) 8 = r0 ∧ rdN μ' (sp - 104 + 88) 8 = v5 ∧ rdN μ' (sp - 104 + 80) 8 = v6 ∧
      rdN μ' (sp - 104 + 16) 8 = D ∧
      (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hF64 : F < 18446744073709551616 := by omega
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hv, hdis, rD, rr, rh, rfl8, rfn, hfn, hfn', hjt, hbt, hrD, hrF, hrv, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8, h9,
      Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt (show D < 18446744073709551616 by omega), rD]

/-- 66019 … 66090, `DebugList::entry` after an entry (D + 9 = 1), result `Ok`, plain options: the
    frame as in `de_a0`, vt at T + 8; the separator `", "` (72806, 2 octets) goes to the sink's
    `write_str` (the word at 77040, 2596 → 59959) with the `String` W = the word at F, returning to
    66095 (2772); v stays in ω₅ and F in ω₆. -/
theorem de_a1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D F W v vt r0 v5 v6 : Nat) (hsp : 196608 + 104 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat v)
    (h9 : ω[9] = UInt64.ofNat vt)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v < 18446744073709551616 ∧ D + 16 < 4294967296 ∧ F + 24 < 4294967296 ∧ vt < 18446744073709551616)
    (hdis : (D + 16 ≤ sp - 104 ∨ sp ≤ D) ∧ (F + 24 ≤ sp - 104 ∨ sp ≤ F))
    (rD : rdN μ D 8 = F) (rr : rdN μ (D + 8) 1 = 0) (rh : rdN μ (D + 9) 1 = 1) (rfl8 : rdN μ (F + 18) 1 = 0)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrD : ∀ a, D ≤ a → a < D + 16 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hrv : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 66019 ω μ x 59959 ω' μ' x 26 ∧
      ω'[0] = UInt64.ofNat 2772 ∧ ω'[1] = UInt64.ofNat (sp - 104) ∧ ω'[5] = UInt64.ofNat v ∧
      ω'[6] = UInt64.ofNat F ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 72806 ∧ ω'[9] = UInt64.ofNat 2 ∧
      rdN μ' (sp - 104 + 96) 8 = r0 ∧ rdN μ' (sp - 104 + 88) 8 = v5 ∧ rdN μ' (sp - 104 + 80) 8 = v6 ∧
      rdN μ' (sp - 104 + 16) 8 = D ∧ rdN μ' (sp - 104 + 8) 8 = vt ∧
      (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hF64 : F < 18446744073709551616 := by omega
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hv, hdis, rD, rr, rh, rfl8, rW, rvt, rws, hrD, hrF, hrv, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7, h8, h9,
      Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2.2.2,
      Nat.mod_eq_of_lt (show D < 18446744073709551616 by omega), rD, rW]

/-- 66095 … 66123, after the separator's `Ok` (ω₇ = 0): v (ω₅) and F (ω₆) as `de_a1` left them, vt
    and D in the frame; the value's `fmt` (the word at vt + 24) is called with v and F, returning to
    66128 (2774). -/
theorem de_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T D F v vt fn e : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat F)
    (h7 : ω[7] = UInt64.ofNat 0) (hv : v < 18446744073709551616 ∧ F < 18446744073709551616 ∧ vt + 32 < 4294967296)
    (rvt : rdN μ (T + 8) 8 = vt) (rD : rdN μ (T + 16) 8 = D) (rfn : rdN μ (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hjt : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbt : P.isBlockStart e = true)
    (hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true)
    (hrv : ∀ a, vt + 24 ≤ a → a < vt + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 66095 ω μ x e ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat 2774 ∧ ω'[1] = ω[1] ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat F := by
  have hfn' : fn % 18446744073709551616 % 4294967296 = fn := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hT, hv, rvt, rD, rfn, hfn, hfn', hjt, hbt, hr, hrv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h6, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1]

/-- 66128 … 66308, the value's `fmt` returned res (ω₇): the result octet D + 8 := res, D + 9 := 1
    (an entry), ω₀, ω₅, ω₆ restored from the frame at T, sp := T + 104, and return. -/
theorem de_c {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T D r0 t v5 v6 res : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat res) (hres : res < 256)
    (hD : D + 16 < 4294967296 ∧ (D + 16 ≤ T ∨ T + 104 ≤ D))
    (rD : rdN μ (T + 16) 8 = D) (r0' : rdN μ (T + 96) 8 = r0) (r5 : rdN μ (T + 88) 8 = v5)
    (r6 : rdN μ (T + 80) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true)
    (hw : ∀ a, D + 8 ≤ a → a < D + 10 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 66128 ω μ x t ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 104) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ rdN μ' (D + 8) 1 = res ∧ rdN μ' (D + 9) 1 = 1 ∧
      (∀ a, a < 4294967296 → (a < D + 8 ∨ D + 10 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrD : ∀ a, D + 8 ≤ a → a < D + 10 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hres, hD, rD, r0', r5, r6, hret, hjt, hbt, hr, hw, hrD, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_lit1, dec1 res hres, Num.decodeLE_encodeLE, h1, h7,
      Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 88)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 80))]

/-- 66310 … 66362, `DebugList::finish` (D = ω₇) with result `Ok` (D + 8 = 0): the frame at
    T = sp − 16 holds ω₀ and ω₅; `"]"` (72826, 1 octet) goes to the sink's `write_str` (2596 →
    59959) with the `String` W = the word at F = the word at D, returning to 66367 (2782); D stays
    in ω₅. -/
theorem df_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp D F W r0 v5 : Nat) (hsp : 196608 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h7 : ω[7] = UInt64.ofNat D)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ D + 16 < 4294967296 ∧ F + 16 < 4294967296)
    (hdis : (D + 16 ≤ sp - 16 ∨ sp ≤ D) ∧ (F + 16 ≤ sp - 16 ∨ sp ≤ F))
    (rD : rdN μ D 8 = F) (rr : rdN μ (D + 8) 1 = 0)
    (rW : rdN μ F 8 = W) (rvt : rdN μ (F + 8) 8 = 77016) (rws : rdN μ 77040 8 = 2596)
    (hrD : ∀ a, D ≤ a → a < D + 16 → μ.readable a = true) (hrF : ∀ a, F ≤ a → a < F + 16 → μ.readable a = true)
    (hrv : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 66310 ω μ x 59959 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 2782 ∧ ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[5] = UInt64.ofNat D ∧
      ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat 72826 ∧ ω'[9] = UInt64.ofNat 1 ∧
      rdN μ' (sp - 16 + 8) 8 = r0 ∧ rdN μ' (sp - 16) 8 = v5 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hW : W < 18446744073709551616 := rW ▸ rdN_lt64 μ F
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h7, hsp, hv, hdis, rD, rr, rW, rvt, rws, hrD, hrF, hrv, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h7,
      Nat.mod_eq_of_lt hW, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt (show D < 18446744073709551616 by omega), rD, rW]

/-- 66367 … 66378, after the sink's `write_str` returned res (ω₇): D + 8 := res, ω₀ and ω₅ restored
    from the frame at T, sp := T + 16, and return with res in ω₇. -/
theorem df_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T D r0 t v5 res : Nat) (hT : 65536 ≤ T ∧ T + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat D) (h7 : ω[7] = UInt64.ofNat res) (hres : res < 256)
    (hD : D + 16 < 4294967296 ∧ (D + 16 ≤ T ∨ T + 16 ≤ D))
    (r0' : rdN μ (T + 8) 8 = r0) (r5 : rdN μ T 8 = v5)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, T ≤ a → a < T + 16 → μ.readable a = true)
    (hw : ∀ a, D + 8 ≤ a → a < D + 9 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 66367 ω μ x t ω' μ' x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 16) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat res ∧ rdN μ' (D + 8) 1 = res ∧
      (∀ a, a < 4294967296 → (a < D + 8 ∨ D + 9 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrD : ∀ a, D + 8 ≤ a → a < D + 9 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hT, hres, hD, r0', r5, hret, hjt, hbt, hr, hw, hrD, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_lit1, dec1 res hres, Num.decodeLE_encodeLE, h1, h5, h7,
      Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show res < 18446744073709551616 by omega), Nat.mod_eq_of_lt (rdN_lt64 μ T)]

end Services.Bootstrap.Fmt
