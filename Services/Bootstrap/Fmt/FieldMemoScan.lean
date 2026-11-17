import Services.Bootstrap.Fmt.N56Steps

/-!
# 57485, the memo's first scan (57485 … 57532 or 57567)

57485 formats a 128-octet memo at m (ω₇) through a `Formatter` F (ω₈). After its prologue (frame
U = sp − 80; ω₀, ω₅, ω₆ saved at U + 72, U + 64, U + 56; F to ω₅, m to ω₆) it scans the 128 octets:
an octet b, sign-extended, above 31 (32 ≤ b < 128) or 0 goes on; any other goes to the hex path
(57567). After all 128 it goes to 57532 (the search for the first 0 and `str::from_utf8`).

- `ms_entry`: 57485 … 57510;
- `ms_iter`: one octet;
- `ms_done`: the count 0, to 57532;
- `ms_loop`: the scan;
- `memo_scan`: 57485 to 57532 or 57567, writing only the frame.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 57485 … 57510: the frame at U = sp − 80 (ω₀, ω₅, ω₆ at U + 72, U + 64, U + 56), F (ω₈) to ω₅, m
    (ω₇) to ω₆ and ω₉, the count 128 in ω₇ and 31 in ω₈. -/
theorem ms_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp m F r0 v5 v6 : Nat) (hsp : 65536 + 80 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat m) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      m < 18446744073709551616 ∧ F < 18446744073709551616)
    (hw : ∀ c, sp - 80 + 56 ≤ c → c < sp → μ.writable c = true) :
    ∃ ω' μ', FreeStepsH p R 57485 ω μ x 57511 ω' μ' x 10 ∧
      ω'[1] = UInt64.ofNat (sp - 80) ∧ ω'[5] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat m ∧
      ω'[7] = UInt64.ofNat 128 ∧ ω'[8] = UInt64.ofNat 31 ∧ ω'[9] = UInt64.ofNat m ∧
      rdN μ' (sp - 80 + 72) 8 = r0 ∧ rdN μ' (sp - 80 + 64) 8 = v5 ∧ rdN μ' (sp - 80 + 56) 8 = v6 ∧
      (∀ c, c < 4294967296 → (c < sp - 80 + 56 ∨ sp ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp - 80 + 56 ≤ c → c < sp → μ.readable c = true := fun c h1 h2 =>
    Memory.readable_of_writable (hw c h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.1, Nat.mod_eq_of_lt hv.2.2.2.2]

/-- 57511 … 57530, one octet at q with k ≥ 1 left (ω₇): the count to k − 1 and q to q + 1, then on
    to 57511, or to the hex path 57567. Memory is not written. -/
theorem ms_iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (q k : Nat) (hq : q + 1 < 4294967296) (hk : 1 ≤ k ∧ k ≤ 128)
    (h7 : ω[7] = UInt64.ofNat k) (h8 : ω[8] = UInt64.ofNat 31) (h9 : ω[9] = UInt64.ofNat q)
    (hrq : μ.readable q = true) :
    ∃ ω', (FreeStepsH p R 57511 ω μ x 57511 ω' μ x 7 ∨ FreeStepsH p R 57511 ω μ x 57567 ω' μ x 9) ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (k - 1) ∧
      ω'[8] = UInt64.ofNat 31 ∧ ω'[9] = UInt64.ofNat (q + 1) := by
  have hrq' : ∀ c, q ≤ c → c < q + 1 → μ.readable c = true := fun c h1 h2 => by rw [show c = q by omega]; exact hrq
  have hb256 : rdN μ q 1 < 256 := by have := rdN_lt μ q 1; simpa using this
  generalize rb : rdN μ q 1 = b at hb256
  have hk0 : k ≠ 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · refine ⟨?_, Or.inl ?_, ?_⟩
    rotate_left
    · apply FreeStepsH.step_decode (d_57511 (p := p) (P := P))
      · pvm_simp [h7, hk0]
      pvm_go [h7, h8, h9, hq, hk, hk0, hrq, hrq', rb, sx8_signed b hb256, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h7, h8, h9]
  · refine ⟨?_, Or.inl ?_, ?_⟩
    rotate_left
    · apply FreeStepsH.step_decode (d_57511 (p := p) (P := P))
      · pvm_simp [h7, hk0]
      pvm_go [h7, h8, h9, hq, hk, hk0, hrq, hrq', rb, sx8_signed b hb256, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h7, h8, h9]
  · refine ⟨?_, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h7, h8, h9, hq, hk, hk0, hrq, hrq', rb, sx8_signed b hb256, hc, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals post_simp [h7, h8, h9]

/-- 57511 with the count 0: to 57532. -/
theorem ms_done {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 57511 ω μ x 57532 ω' μ x 1 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7]
  · refine ⟨?_, ?_, ?_⟩
    all_goals post_simp []

/-- **The scan** (57511): with k ≤ 128 octets left from q, all readable, it reaches 57532 or 57567
    within 8k + 1 steps, ω₁, ω₅, ω₆ kept and memory not written. -/
theorem ms_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (μ : Memory) :
    ∀ k, k ≤ 128 → ∀ (ω : Regs) (q : Nat), q + k < 4294967296 →
      ω[7] = UInt64.ofNat k → ω[8] = UInt64.ofNat 31 → ω[9] = UInt64.ofNat q →
      (∀ c, q ≤ c → c < q + k → μ.readable c = true) →
      ∃ ω', (FreeStepsH p R 57511 ω μ x 57532 ω' μ x (8 * k + 1) ∨
          FreeStepsH p R 57511 ω μ x 57567 ω' μ x (8 * k + 1)) ∧
        ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  intro k
  induction k with
  | zero =>
    intro _ ω q _ h7 _ _ _
    obtain ⟨ω', run, a1, a5, a6⟩ := ms_done (p := p) (P := P) (R := R) x ω μ h7
    exact ⟨ω', Or.inl run, a1, a5, a6⟩
  | succ k ih =>
    intro hk ω q hq h7 h8 h9 hr
    obtain ⟨ω1, run1, a1, a5, a6, a7, a8, a9⟩ := ms_iter (p := p) (P := P) (R := R) x ω μ q (k + 1) (by omega)
      ⟨by omega, hk⟩ h7 h8 h9 (hr q (Nat.le_refl _) (by omega))
    rcases run1 with run1 | run1
    · obtain ⟨ω2, run2, b1, b5, b6⟩ := ih (by omega) ω1 (q + 1) (by omega) (by rw [a7, show k + 1 - 1 = k by omega]) a8 a9
        (fun c h1 h2 => hr c (by omega) (by omega))
      refine ⟨ω2, ?_, b1.trans a1, b5.trans a5, b6.trans a6⟩
      rcases run2 with run2 | run2
      · exact Or.inl ((run1.trans run2).mono (by omega))
      · exact Or.inr ((run1.trans run2).mono (by omega))
    · exact ⟨ω1, Or.inr (run1.mono (by omega)), a1, a5, a6⟩

/-- **57485's prologue and first scan**: from 57485 (ω₇ = m, ω₈ = F, 128 readable octets at m) to
    57532 or the hex path 57567, the frame at U = sp − 80 (ω₀, ω₅, ω₆ at U + 72, U + 64, U + 56),
    F in ω₅, m in ω₆, only U + 56 … sp written. -/
theorem memo_scan {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp m F r0 v5 v6 : Nat) (hsp : 65536 + 80 ≤ sp ∧ sp < 4294967296) (hm : m + 128 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat m) (h8 : ω[8] = UInt64.ofNat F)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      F < 18446744073709551616)
    (hrm : ∀ c, m ≤ c → c < m + 128 → μ.readable c = true)
    (hw : ∀ c, sp - 80 + 56 ≤ c → c < sp → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 57485 ω μ x 57532 ω' μ' x 1035 ∨ FreeStepsH p R 57485 ω μ x 57567 ω' μ' x 1035) ∧
      ω'[1] = UInt64.ofNat (sp - 80) ∧ ω'[5] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat m ∧
      rdN μ' (sp - 80 + 72) 8 = r0 ∧ rdN μ' (sp - 80 + 64) 8 = v5 ∧ rdN μ' (sp - 80 + 56) 8 = v6 ∧
      (∀ c, c < 4294967296 → (c < sp - 80 + 56 ∨ sp ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a7, a8, a9, s72, s64, s56, fr1, rd1, wr1⟩ := ms_entry (p := p) (P := P) (R := R)
    x ω μ sp m F r0 v5 v6 hsp h0 h1 h5 h6 h7 h8 ⟨hv.1, hv.2.1, hv.2.2.1, by omega, hv.2.2.2⟩ hw
  obtain ⟨ω2, run2, b1, b5, b6⟩ := ms_loop (p := p) (P := P) (R := R) x μ1 128 (Nat.le_refl _) ω1 m (by omega) a7 a8
    a9 (fun c h1 h2 => by rw [rd1]; exact hrm c h1 h2)
  refine ⟨ω2, μ1, ?_, b1.trans a1, b5.trans a5, b6.trans a6, s72, s64, s56, fr1, rd1, wr1⟩
  rcases run2 with run2 | run2
  · exact Or.inl ((run1.trans run2).mono (by omega))
  · exact Or.inr ((run1.trans run2).mono (by omega))

end Services.Bootstrap.Fmt
