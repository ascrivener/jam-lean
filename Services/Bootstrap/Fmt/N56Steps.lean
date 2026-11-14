import Services.Bootstrap.Fmt.Tac

/-!
# `56340`: the per-octet checks (the steps)

56340 is the `Debug` of a 32-octet name at a (ω₇). After its prologue (frame sp = the caller's
sp − 280; ω₀, ω₅, ω₆ saved at sp + 272, sp + 264, sp + 256), it checks each octet b in turn: when b,
sign-extended, is above 31 (32 ≤ b < 128) or is 0, it goes on to the next check; otherwise it
jumps to the hex path (57346). The checks are unrolled; some keep the sign-extended octet in a
stack slot (sp + 16 … sp + 192).

- `sx8_signed`: the sign-extended octet read back as a signed integer;
- `n56_0` … `n56_31`: octet k's check, from its start to the next check's (56921 after the last),
  or to 57346. ω₁, ω₇, ω₈ are kept; only sp … sp + 200 is written.

The octets' values are not tracked further: what follows depends only on which are 0.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- An octet b, sign-extended to 64 bits and read back as a signed integer. -/
theorem sx8_signed (b : Nat) (hb : b < 256) :
    (if ((if b < 128 then (b : Int) else (b : Int) - 256) % 18446744073709551616).toNat < 9223372036854775808 then
        (((if b < 128 then (b : Int) else (b : Int) - 256) % 18446744073709551616).toNat : Int)
      else (((b : Int) - 256) % 18446744073709551616).toNat - 18446744073709551616) =
      (if b < 128 then (b : Int) else (b : Int) - 256) := by
  by_cases h : b < 128
  · simp only [h, if_true]
    have : ((b : Int) % 18446744073709551616) = b := Int.emod_eq_of_lt (by omega) (by omega)
    rw [this]; simp; omega
  · simp only [h, if_false]
    have : (((b : Int) - 256) % 18446744073709551616) = b - 256 + 18446744073709551616 := by omega
    rw [this]
    have : ((b : Int) - 256 + 18446744073709551616).toNat = b + 18446744073709551360 := by omega
    rw [this]; simp; omega

/-- Octet 0 (at a + 0): from 56356 to 56366, or to 57346. -/
theorem n56_0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56356 ω μ x 56366 ω' μ' x 7 ∨ FreeStepsH p R 56356 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ a 1 < 256 := by have := rdN_lt μ a 1; simpa using this
  generalize rb : rdN μ a 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 1 (at a + 1): from 56366 to 56378, or to 57346. -/
theorem n56_1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56366 ω μ x 56378 ω' μ' x 7 ∨ FreeStepsH p R 56366 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 1) 1 < 256 := by have := rdN_lt μ (a + 1) 1; simpa using this
  generalize rb : rdN μ (a + 1) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 2 (at a + 2): from 56378 to 56390, or to 57346. -/
theorem n56_2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56378 ω μ x 56390 ω' μ' x 7 ∨ FreeStepsH p R 56378 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 2) 1 < 256 := by have := rdN_lt μ (a + 2) 1; simpa using this
  generalize rb : rdN μ (a + 2) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 3 (at a + 3): from 56390 to 56402, or to 57346. -/
theorem n56_3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56390 ω μ x 56402 ω' μ' x 7 ∨ FreeStepsH p R 56390 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 3) 1 < 256 := by have := rdN_lt μ (a + 3) 1; simpa using this
  generalize rb : rdN μ (a + 3) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 4 (at a + 4): from 56402 to 56414, or to 57346. -/
theorem n56_4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56402 ω μ x 56414 ω' μ' x 7 ∨ FreeStepsH p R 56402 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 4) 1 < 256 := by have := rdN_lt μ (a + 4) 1; simpa using this
  generalize rb : rdN μ (a + 4) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 5 (at a + 5): from 56414 to 56426, or to 57346. -/
theorem n56_5 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56414 ω μ x 56426 ω' μ' x 7 ∨ FreeStepsH p R 56414 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 5) 1 < 256 := by have := rdN_lt μ (a + 5) 1; simpa using this
  generalize rb : rdN μ (a + 5) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 6 (at a + 6): from 56426 to 56440, or to 57346. -/
theorem n56_6 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56426 ω μ x 56440 ω' μ' x 7 ∨ FreeStepsH p R 56426 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 6) 1 < 256 := by have := rdN_lt μ (a + 6) 1; simpa using this
  generalize rb : rdN μ (a + 6) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 7 (at a + 7): from 56440 to 56452, or to 57346. -/
theorem n56_7 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56440 ω μ x 56452 ω' μ' x 7 ∨ FreeStepsH p R 56440 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 7) 1 < 256 := by have := rdN_lt μ (a + 7) 1; simpa using this
  generalize rb : rdN μ (a + 7) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

/-- Octet 8 (at a + 8): from 56452 to 56473, or to 57346. -/
theorem n56_8 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56452 ω μ x 56473 ω' μ' x 7 ∨ FreeStepsH p R 56452 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 8) 1 < 256 := by have := rdN_lt μ (a + 8) 1; simpa using this
  generalize rb : rdN μ (a + 8) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 9 (at a + 9): from 56473 to 56494, or to 57346. -/
theorem n56_9 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56473 ω μ x 56494 ω' μ' x 7 ∨ FreeStepsH p R 56473 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 9) 1 < 256 := by have := rdN_lt μ (a + 9) 1; simpa using this
  generalize rb : rdN μ (a + 9) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 10 (at a + 10): from 56494 to 56515, or to 57346. -/
theorem n56_10 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56494 ω μ x 56515 ω' μ' x 7 ∨ FreeStepsH p R 56494 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 10) 1 < 256 := by have := rdN_lt μ (a + 10) 1; simpa using this
  generalize rb : rdN μ (a + 10) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 11 (at a + 11): from 56515 to 56536, or to 57346. -/
theorem n56_11 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56515 ω μ x 56536 ω' μ' x 7 ∨ FreeStepsH p R 56515 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 11) 1 < 256 := by have := rdN_lt μ (a + 11) 1; simpa using this
  generalize rb : rdN μ (a + 11) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 12 (at a + 12): from 56536 to 56557, or to 57346. -/
theorem n56_12 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56536 ω μ x 56557 ω' μ' x 7 ∨ FreeStepsH p R 56536 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 12) 1 < 256 := by have := rdN_lt μ (a + 12) 1; simpa using this
  generalize rb : rdN μ (a + 12) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 13 (at a + 13): from 56557 to 56578, or to 57346. -/
theorem n56_13 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56557 ω μ x 56578 ω' μ' x 7 ∨ FreeStepsH p R 56557 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 13) 1 < 256 := by have := rdN_lt μ (a + 13) 1; simpa using this
  generalize rb : rdN μ (a + 13) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 14 (at a + 14): from 56578 to 56599, or to 57346. -/
theorem n56_14 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56578 ω μ x 56599 ω' μ' x 7 ∨ FreeStepsH p R 56578 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 14) 1 < 256 := by have := rdN_lt μ (a + 14) 1; simpa using this
  generalize rb : rdN μ (a + 14) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 15 (at a + 15): from 56599 to 56620, or to 57346. -/
theorem n56_15 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56599 ω μ x 56620 ω' μ' x 7 ∨ FreeStepsH p R 56599 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 15) 1 < 256 := by have := rdN_lt μ (a + 15) 1; simpa using this
  generalize rb : rdN μ (a + 15) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 16 (at a + 16): from 56620 to 56641, or to 57346. -/
theorem n56_16 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56620 ω μ x 56641 ω' μ' x 7 ∨ FreeStepsH p R 56620 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 16) 1 < 256 := by have := rdN_lt μ (a + 16) 1; simpa using this
  generalize rb : rdN μ (a + 16) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 17 (at a + 17): from 56641 to 56660, or to 57346. -/
theorem n56_17 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56641 ω μ x 56660 ω' μ' x 7 ∨ FreeStepsH p R 56641 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 17) 1 < 256 := by have := rdN_lt μ (a + 17) 1; simpa using this
  generalize rb : rdN μ (a + 17) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 18 (at a + 18): from 56660 to 56679, or to 57346. -/
theorem n56_18 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56660 ω μ x 56679 ω' μ' x 7 ∨ FreeStepsH p R 56660 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 18) 1 < 256 := by have := rdN_lt μ (a + 18) 1; simpa using this
  generalize rb : rdN μ (a + 18) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 19 (at a + 19): from 56679 to 56698, or to 57346. -/
theorem n56_19 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56679 ω μ x 56698 ω' μ' x 7 ∨ FreeStepsH p R 56679 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 19) 1 < 256 := by have := rdN_lt μ (a + 19) 1; simpa using this
  generalize rb : rdN μ (a + 19) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 20 (at a + 20): from 56698 to 56717, or to 57346. -/
theorem n56_20 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56698 ω μ x 56717 ω' μ' x 7 ∨ FreeStepsH p R 56698 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 20) 1 < 256 := by have := rdN_lt μ (a + 20) 1; simpa using this
  generalize rb : rdN μ (a + 20) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 21 (at a + 21): from 56717 to 56736, or to 57346. -/
theorem n56_21 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56717 ω μ x 56736 ω' μ' x 7 ∨ FreeStepsH p R 56717 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 21) 1 < 256 := by have := rdN_lt μ (a + 21) 1; simpa using this
  generalize rb : rdN μ (a + 21) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 22 (at a + 22): from 56736 to 56755, or to 57346. -/
theorem n56_22 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56736 ω μ x 56755 ω' μ' x 7 ∨ FreeStepsH p R 56736 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 22) 1 < 256 := by have := rdN_lt μ (a + 22) 1; simpa using this
  generalize rb : rdN μ (a + 22) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 23 (at a + 23): from 56755 to 56774, or to 57346. -/
theorem n56_23 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56755 ω μ x 56774 ω' μ' x 7 ∨ FreeStepsH p R 56755 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 23) 1 < 256 := by have := rdN_lt μ (a + 23) 1; simpa using this
  generalize rb : rdN μ (a + 23) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 24 (at a + 24): from 56774 to 56793, or to 57346. -/
theorem n56_24 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56774 ω μ x 56793 ω' μ' x 7 ∨ FreeStepsH p R 56774 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 24) 1 < 256 := by have := rdN_lt μ (a + 24) 1; simpa using this
  generalize rb : rdN μ (a + 24) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 25 (at a + 25): from 56793 to 56812, or to 57346. -/
theorem n56_25 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56793 ω μ x 56812 ω' μ' x 7 ∨ FreeStepsH p R 56793 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 25) 1 < 256 := by have := rdN_lt μ (a + 25) 1; simpa using this
  generalize rb : rdN μ (a + 25) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 26 (at a + 26): from 56812 to 56831, or to 57346. -/
theorem n56_26 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56812 ω μ x 56831 ω' μ' x 7 ∨ FreeStepsH p R 56812 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 26) 1 < 256 := by have := rdN_lt μ (a + 26) 1; simpa using this
  generalize rb : rdN μ (a + 26) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 27 (at a + 27): from 56831 to 56850, or to 57346. -/
theorem n56_27 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56831 ω μ x 56850 ω' μ' x 7 ∨ FreeStepsH p R 56831 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 27) 1 < 256 := by have := rdN_lt μ (a + 27) 1; simpa using this
  generalize rb : rdN μ (a + 27) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 28 (at a + 28): from 56850 to 56869, or to 57346. -/
theorem n56_28 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56850 ω μ x 56869 ω' μ' x 7 ∨ FreeStepsH p R 56850 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 28) 1 < 256 := by have := rdN_lt μ (a + 28) 1; simpa using this
  generalize rb : rdN μ (a + 28) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 29 (at a + 29): from 56869 to 56888, or to 57346. -/
theorem n56_29 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56869 ω μ x 56888 ω' μ' x 7 ∨ FreeStepsH p R 56869 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 29) 1 < 256 := by have := rdN_lt μ (a + 29) 1; simpa using this
  generalize rb : rdN μ (a + 29) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 30 (at a + 30): from 56888 to 56907, or to 57346. -/
theorem n56_30 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56888 ω μ x 56907 ω' μ' x 7 ∨ FreeStepsH p R 56888 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 30) 1 < 256 := by have := rdN_lt μ (a + 30) 1; simpa using this
  generalize rb : rdN μ (a + 30) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, ?_, Or.inl ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, ?_, Or.inr ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [rdN_writeN_disjoint, h1, h7]

/-- Octet 31 (at a + 31): from 56907 to 56921, or to 57346. -/
theorem n56_31 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp a : Nat) (hsp : 65536 ≤ sp ∧ sp + 200 < 4294967296) (ha : a + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat a)
    (hra : ∀ c, a ≤ c → c < a + 32 → μ.readable c = true)
    (hw : ∀ c, sp ≤ c → c < sp + 200 → μ.writable c = true) :
    ∃ ω' μ', (FreeStepsH p R 56907 ω μ x 56921 ω' μ' x 7 ∨ FreeStepsH p R 56907 ω μ x 57346 ω' μ' x 7) ∧
      ω'[1] = ω[1] ∧ ω'[7] = ω[7] ∧ ω'[8] = ω[8] ∧
      (∀ c, c < 4294967296 → (c < sp ∨ sp + 200 ≤ c) → μ'.read c = μ.read c) ∧
      (∀ c, μ'.readable c = μ.readable c) ∧ (∀ c, μ'.writable c = μ.writable c) := by
  have hr : ∀ c, sp ≤ c → c < sp + 200 → μ.readable c = true := fun c h1 h2 => Memory.readable_of_writable (hw c h1 h2)
  have hb256 : rdN μ (a + 31) 1 < 256 := by have := rdN_lt μ (a + 31) 1; simpa using this
  generalize rb : rdN μ (a + 31) 1 = b at hb256
  rw [show ω = regsNF ω [] from rfl]
  rcases (show (32 ≤ b ∧ b < 128) ∨ b = 0 ∨ ((0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256)) by omega) with hc | hc | hc
  · have hc : 32 ≤ b ∧ b < 128 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : b = 0 := by omega
    refine ⟨?_, μ, Or.inl ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]
  · have hc : (0 < b ∧ b < 32) ∨ (128 ≤ b ∧ b < 256) := by omega
    refine ⟨?_, μ, Or.inr ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, hsp, ha, hra, hw, hr, rb, sx8_signed b hb256, hc, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, fun c hc0 hc1 => ?_, fun c => ?_, fun c => ?_⟩
      all_goals post_simp [h1, h7]

end Services.Bootstrap.Fmt
