import Services.Bootstrap.Fmt.FieldWriteChar
import Services.Bootstrap.Fmt.FieldWriteSpec

/-!
# `Formatter::pad_integral` with the options of `{:02x}`: the steps

`pad_integral` (61857) through a `Formatter` F whose options word is o = 0x69000020 (fill ' ',
alignment unknown, the width flag and the zero-pad flag set; no `+`, no `#`) and whose width is w.
Bit 21 (`+`) and bit 23 (`#`) are clear, so no sign and no prefix are written.

- With len ≥ w digits, the plain path: `pw_a` (61857 … 64897), then `pi_b` and `pi_c` as with plain
  options.
- With len = 1 and w = 2, the zero-pad path (bit 24):
  - `pz_a`: 61857 … 64897, the options word at F + 16 saved at T + 0 and replaced by 0x29000030
    (fill '0', alignment right);
  - `pz_b`: `write_prefix` (no sign, no prefix) … 62129;
  - `pz_c`: 62129 … `write_char` (59743) of '0';
  - `pz_d`: 62173 … `write_str` (59959) of the digits;
  - `pz_e`: 62240 … the return, the options word restored.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- Two runs of n octets that read the same number read the same octets. -/
theorem read_of_rdN {μ μ' : Memory} {a n : Nat} (h : rdN μ' a n = rdN μ a n) (j : Nat) (hj : j < n) :
    μ'.read (a + j) = μ.read (a + j) := by
  have e : μ'.readN a n = μ.readN a n := by
    have h1 := encodeLE_decodeLE (μ'.readN a n)
    have h2 := encodeLE_decodeLE (μ.readN a n)
    simp only [Memory.length_readN] at h1 h2
    unfold rdN at h
    rw [← h1, ← h2, h]
  have := congrArg (fun l => l[j]?) e
  simpa [Memory.readN, hj] using this

/-- Four octets, just written at a, read back as a number. -/
theorem rdN_lit4 (μ : Memory) (a : Nat) (bs : List UInt8) (hb : bs.length = 4) (ha : a + 4 ≤ 4294967296) :
    rdN (μ.writeN a bs) a 4 = Num.decodeLE bs := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ hb (by simp only [two32]; omega)]

/-- 61857 … 62013, options 0x69000020 and width w ≤ len: as `pi_a`. -/
theorem pw_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp F dig len r0 v5 v6 buf vt pl w : Nat) (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h10 : ω[10] = UInt64.ofNat pl)
    (h11 : ω[11] = UInt64.ofNat dig) (h12 : ω[12] = UInt64.ofNat len)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      dig < 18446744073709551616 ∧ len < 4294967296 ∧ pl < 18446744073709551616)
    (hF : F + 24 ≤ sp - 104 ∨ sp ≤ F) (hF1 : F + 24 < 4294967296)
    (ro : rdN μ (F + 16) 4 = 1761607712) (rw0 : rdN μ (F + 20) 2 = w) (hwl : w ≤ len)
    (rb : rdN μ F 8 = buf) (rv : rdN μ (F + 8) 8 = vt)
    (hbv : buf < 18446744073709551616 ∧ vt < 18446744073709551616)
    (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 61857 ω μ x 64897 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2628 ∧ ω'[1] = UInt64.ofNat (sp - 104) ∧ ω'[5] = UInt64.ofNat buf ∧
      ω'[6] = UInt64.ofNat vt ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat vt ∧
      ω'[9] = UInt64.ofNat 18446744073709551615 ∧ ω'[10] = UInt64.ofNat 0 ∧
      rdN μ' (sp - 104 + 96) 8 = r0 ∧ rdN μ' (sp - 104 + 88) 8 = v5 ∧ rdN μ' (sp - 104 + 80) 8 = v6 ∧
      rdN μ' (sp - 104 + 16) 8 = dig ∧ rdN μ' (sp - 104 + 24) 8 = len ∧
      (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hw2 : w < 65536 := by rw [← rw0]; exact rdN_lt μ _ 2
  have hwl' : ¬ len < w := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h10, h11, h12, hv, hbv, hsp, hF, hF1, ro, rw0, hwl, hwl', hw2, rb, rv, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rw [rdN_ones _ (sp - 104 + 32) (by omega)]
    all_goals try rw [rdN_zero _ (sp - 104 + 40) (by omega)]
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8]

/-- 61857 … 61955, options 0x69000020, width 2 and one digit (len = 1): the frame at T = sp − 104
    as in `pi_a` (ω₀, ω₅, ω₆ at T + 96, T + 88, T + 80; the digits at T + 16, the length 1 at T + 24;
    no sign at T + 32, no prefix at T + 40, T + 48), then the branch to the zero-pad path (62076). -/
theorem pz_a1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp F dig r0 v5 v6 pl : Nat) (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h10 : ω[10] = UInt64.ofNat pl)
    (h11 : ω[11] = UInt64.ofNat dig) (h12 : ω[12] = UInt64.ofNat 1)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      dig < 18446744073709551616 ∧ pl < 18446744073709551616)
    (hF : F + 24 ≤ sp - 104 ∨ sp ≤ F) (hF1 : F + 24 < 4294967296)
    (ro : rdN μ (F + 16) 4 = 1761607712) (rw0 : rdN μ (F + 20) 2 = 2)
    (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 104 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 61857 ω μ x 62076 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat (sp - 104) ∧ ω'[5] = UInt64.ofNat 2 ∧ ω'[6] = UInt64.ofNat 1 ∧
      ω'[11] = UInt64.ofNat F ∧
      rdN μ' (sp - 104 + 96) 8 = r0 ∧ rdN μ' (sp - 104 + 88) 8 = v5 ∧ rdN μ' (sp - 104 + 80) 8 = v6 ∧
      rdN μ' (sp - 104 + 16) 8 = dig ∧ rdN μ' (sp - 104 + 24) 8 = 1 ∧
      rdN μ' (sp - 104 + 32) 8 = 18446744073709551615 ∧ rdN μ' (sp - 104 + 40) 8 = 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 104 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 104 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hF64 : F < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h10, h11, h12, hv, hsp, hF, hF1, ro, rw0, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rw [rdN_ones _ (sp - 104 + 32) (by omega)]
    all_goals try rw [rdN_zero _ (sp - 104 + 40) (by omega)]
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, rdN_lit8, Num.decodeLE_encodeLE, Nat.reduceMul, Nat.reducePow,
      Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2.1,
      Nat.mod_eq_of_lt hv.2.2.2.1]

/-- 62076 … 62123, the zero-pad path: the length 1 (ω₆) at T + 56, the options word F + 16 … F + 24
    saved at T + 0, F at T + 8, the sink (buf, vt) at T + 72, T + 64, the options at F + 16 set to
    0x29000030 (fill '0'), and the call of `write_prefix` (64897) with no sign and no prefix,
    returning to 62129 (2632). -/
theorem pz_a2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F buf vt : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h6 : ω[6] = UInt64.ofNat 1) (h11 : ω[11] = UInt64.ofNat F)
    (hFT : F + 24 ≤ T ∨ T + 104 ≤ F) (hF1 : F + 24 < 4294967296)
    (ro8 : rdN μ (F + 16) 8 = 10351542304) (rb : rdN μ F 8 = buf) (rv : rdN μ (F + 8) 8 = vt)
    (r32 : rdN μ (T + 32) 8 = 18446744073709551615) (r40 : rdN μ (T + 40) 8 = 0)
    (hrF : ∀ a, F ≤ a → a < F + 24 → μ.readable a = true)
    (hwF : ∀ a, F + 16 ≤ a → a < F + 20 → μ.writable a = true)
    (hw : ∀ a, T ≤ a → a < T + 104 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 62076 ω μ x 64897 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2632 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat 18446744073709551615 ∧ ω'[10] = UInt64.ofNat 0 ∧
      rdN μ' (T + 56) 8 = 1 ∧ rdN μ' T 8 = 10351542304 ∧ rdN μ' (T + 8) 8 = F ∧
      rdN μ' (T + 72) 8 = buf ∧ rdN μ' (T + 64) 8 = vt ∧ rdN μ' (F + 16) 4 = 687865904 ∧
      (∀ a, a < 4294967296 → (a < T ∨ (T + 16 ≤ a ∧ a < T + 56) ∨ T + 80 ≤ a) → (a < F + 16 ∨ F + 20 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hF64 : F < 18446744073709551616 := by omega
  have hbuf : buf < 18446744073709551616 := by rw [← rb]; exact rdN_lt64 μ _
  have hvt : vt < 18446744073709551616 := by rw [← rv]; exact rdN_lt64 μ _
  have hb5 := (ω[5]).toNat_lt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h11, hT, hFT, hF1, ro8, rb, rv, r32, r40, hrF, hwF, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, h6, rdN_writeN_disjoint, rdN_writeN_same8, rdN_writeN_enc, rdN_lit8, rdN_lit4,
      Num.decodeLE_encodeLE, Nat.reduceMul, Nat.reducePow, Nat.mod_eq_of_lt hF64, Nat.mod_eq_of_lt hbuf, Nat.mod_eq_of_lt hvt]
    all_goals try decide

/-- 64897 … 64990 and the return to 62129: `write_prefix` as in `pi_b`, called from the zero-pad
    path (return address 2632). -/
theorem pz_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 + 40 ≤ T ∧ T < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 2632) (h1 : ω[1] = UInt64.ofNat T)
    (h9 : ω[9] = UInt64.ofNat 18446744073709551615) (h10 : ω[10] = UInt64.ofNat 0)
    (hw : ∀ a, T - 40 ≤ a → a < T → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64897 ω μ x 62129 ω' μ' x 20 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat 0 ∧
      (∀ a, a < 4294967296 → (a < T - 40 ∨ T ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T - 40 ≤ a → a < T → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hb0 := (ω[0]).toNat_lt
  have hb5 := (ω[5]).toNat_lt
  have hb6 := (ω[6]).toNat_lt
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h9, h10, hT, hw, hr, rdN_writeN_disjoint, rdN_lit8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8]

/-- 62129 … 62168, `write_prefix` returned `Ok`: the fill count w − len = 1 (ω₅), the counter 1
    (ω₆, after the increment), and the call of the sink's `write_char` (the word at vt + 32, 2592 for
    the `String`, so 59743) with buf (ω₇) and '0' (ω₈), returning to 62173 (2634). -/
theorem pz_c {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T buf vt : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 2) (h6 : ω[6] = UInt64.ofNat 1)
    (h7 : ω[7] = UInt64.ofNat 0) (hvt : vt + 40 < 4294967296)
    (rwc : rdN μ (vt + 32) 8 = 2592) (r56 : rdN μ (T + 56) 8 = 1) (r64 : rdN μ (T + 64) 8 = vt)
    (r72 : rdN μ (T + 72) 8 = buf)
    (hrv : ∀ a, vt + 32 ≤ a → a < vt + 40 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62129 ω μ x 59743 ω' μ x 16 ∧
      ω'[0] = UInt64.ofNat 2634 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat 1 ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat 48 := by
  have hbuf : buf < 18446744073709551616 := by rw [← r72]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hT, hvt, rwc, r56, r64, r72, hrv, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h6, Nat.mod_eq_of_lt hbuf]

/-- 62173 … 62235, `write_char` returned `Ok`: the counter reached the fill count, and the call of
    the sink's `write_str` (the word at vt + 24, 2596 for the `String`, so 59959) with buf (ω₇), the
    digits (T + 16) and their length (T + 24), returning to 62240 (2636). -/
theorem pz_d {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T buf vt dig len : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat 1)
    (h7 : ω[7] = UInt64.ofNat 0) (hvt : vt + 32 < 4294967296)
    (rws : rdN μ (vt + 24) 8 = 2596) (r64 : rdN μ (T + 64) 8 = vt) (r72 : rdN μ (T + 72) 8 = buf)
    (r16 : rdN μ (T + 16) 8 = dig) (r24 : rdN μ (T + 24) 8 = len)
    (hrv : ∀ a, vt + 24 ≤ a → a < vt + 32 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62173 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat 2636 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = UInt64.ofNat 1 ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat dig ∧
      ω'[9] = UInt64.ofNat len := by
  have hbuf : buf < 18446744073709551616 := by rw [← r72]; exact rdN_lt64 μ _
  have hdig : dig < 18446744073709551616 := by rw [← r16]; exact rdN_lt64 μ _
  have hlen : len < 18446744073709551616 := by rw [← r24]; exact rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hT, hvt, rws, r64, r72, r16, r24, hrv, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, h6, Nat.mod_eq_of_lt hbuf, Nat.mod_eq_of_lt hdig, Nat.mod_eq_of_lt hlen]

/-- 62240 … the return, `write_str` returned `Ok`: the saved options word (T + 0) is written back to
    F + 16 (F at T + 8), `Ok` (ω₇ = 0), ω₀, ω₅, ω₆ restored from T + 96, T + 88, T + 80, the frame
    closed, and the return to t. -/
theorem pz_e {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F sv r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296) (hF : F + 24 < 4294967296)
    (hFT : F + 24 ≤ T ∨ T + 104 ≤ F)
    (h1 : ω[1] = UInt64.ofNat T) (h7 : ω[7] = UInt64.ofNat 0)
    (r0' : rdN μ (T + 96) 8 = r0) (r5 : rdN μ (T + 88) 8 = v5) (r6 : rdN μ (T + 80) 8 = v6)
    (r8 : rdN μ (T + 8) 8 = F) (rsv : rdN μ T 8 = sv)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hwF : ∀ a, F + 16 ≤ a → a < F + 24 → μ.writable a = true)
    (hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 62240 ω μ x t ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 104) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧ rdN μ' (F + 16) 8 = sv ∧
      (∀ a, a < 4294967296 → (a < F + 16 ∨ F + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrF : ∀ a, F + 16 ≤ a → a < F + 24 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwF a h1 h2)
  have hsv : sv < 18446744073709551616 := by rw [← rsv]; exact rdN_lt64 μ _
  have hv5 : v5 < 18446744073709551616 := by rw [← r5]; exact rdN_lt64 μ _
  have hv6 : v6 < 18446744073709551616 := by rw [← r6]; exact rdN_lt64 μ _
  have hr0 : r0 % 18446744073709551616 % 4294967296 = r0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hT, hF, hFT, rdN_writeN_disjoint, r0', r5, r6, r8, rsv, hret, hr0, hjt, hbt, hwF, hrF, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [h1, rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hsv, Nat.mod_eq_of_lt hv5,
      Nat.mod_eq_of_lt hv6]

end Services.Bootstrap.Fmt
