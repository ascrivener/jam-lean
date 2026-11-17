import Services.Bootstrap.Fmt.FieldPadWidth

/-!
# `<u8 as fmt::LowerHex>::fmt` (60209): the steps

The function renders the octet's hex digits, least significant first, into its 16-octet frame
from T + 7 down (T = sp − 16), looking each digit up in the table at 71060 (`0123456789abcdef`), then
calls `pad_integral` (61857) with the digits and the prefix `0x` (71076, 2 octets; not written
without `#`). An octet has one digit (b < 16) or two.

- `u8x_entry`: 60209 … 60229;
- `u8x_iter`: one digit (60230 … 60252);
- `u8x_post`: 60255 … the call of `pad_integral`;
- `u8x_ret`: 60280 … the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 60209 … 60229: a 16-octet frame at T = sp − 16 (ω₀ at T + 8), the `Formatter` (ω₈) kept in ω₂,
    the octet at v read into ω₉, the digit cursor T + 7 in ω₇, the table 71060 in ω₈ and the count
    0 in ω₁₂. -/
theorem u8x_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F) (hr0 : r0 < 18446744073709551616) (hF : F < 18446744073709551616)
    (hv : v + 1 < 4294967296) (hvf : v + 1 ≤ sp - 16 ∨ sp ≤ v)
    (hrv : μ.readable v = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 60209 ω μ x 60230 ω' μ' x 8 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[2] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp - 16 + 7) ∧ ω'[8] = UInt64.ofNat 71060 ∧ ω'[9] = UInt64.ofNat (rdN μ v 1) ∧
      ω'[12] = UInt64.ofNat 0 ∧ rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 + 8 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hrv' : ∀ a, v ≤ a → a < v + 1 → μ.readable a = true := fun a h1 h2 => by
    rw [show a = v by omega]; exact hrv
  have hb := rdN_lt μ v 1
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hr0, hF, hv, hvf, hrv, hrv', hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8]

/-- 60230 … 60252: one digit. From the cursor A (ω₇), the table (ω₈) and the value w (ω₉): the digit
    for w mod 16 is stored at A, the cursor moves to A − 1, the count (ω₁₂) goes up by one and w / 16
    goes to ω₉. The loop goes on while w / 16 ≠ 0. -/
theorem u8x_iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (A w k : Nat) (hA : 65536 ≤ A ∧ A < 4294967296) (hw64 : w < 18446744073709551616) (hk : k < 100)
    (h7 : ω[7] = UInt64.ofNat A) (h8 : ω[8] = UInt64.ofNat 71060) (h9 : ω[9] = UInt64.ofNat w)
    (h12 : ω[12] = UInt64.ofNat k)
    (hro : ∀ a, 71060 ≤ a → a < 71076 → μ.readable a = true) (hw : μ.writable A = true) :
    ∃ ω' μ', FreeStepsH p R 60230 ω μ x (if w / 16 = 0 then 60255 else 60230) ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (A - 1) ∧
      ω'[8] = UInt64.ofNat 71060 ∧ ω'[9] = UInt64.ofNat (w / 16) ∧ ω'[12] = UInt64.ofNat (k + 1) ∧
      (∀ a, a < 4294967296 → a ≠ A → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hsh : w >>> 4 = w / 16 := by rw [Nat.shiftRight_eq_div_pow]
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : w / 16 = 0
  · rw [if_pos hz]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h7, h8, h9, h12, hA, hw64, hz, hsh, hk, hro, hw, bitwise_and_m15, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [hz, hsh, h8]
  · rw [if_neg hz]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.step_decode (d_60230 (p := p) (P := P))
      · pvm_simp []
      pvm_go [h7, h8, h9, h12, hA, hw64, hz, hsh, hk, hro, hw, bitwise_and_m15, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [hz, hsh, h8]

/-- 60255 … 60274, after k digits from T + 7 down (cursor T + 7 − k): the digits' address T + 8 − k
    (ω₁₁) and count k (ω₁₂), the prefix `0x` (71076, 2), the `Formatter` (ω₂) in ω₇, and the call of
    `pad_integral` (61857), returning to 60280 (2608). -/
theorem u8x_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T F k : Nat) (hT : 65536 ≤ T ∧ T + 16 < 4294967296) (hk : 1 ≤ k ∧ k ≤ 2)
    (h1 : ω[1] = UInt64.ofNat T) (h2 : ω[2] = UInt64.ofNat F) (h12 : ω[12] = UInt64.ofNat k)
    (hF : F < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 60255 ω μ x 61857 ω' μ x 7 ∧
      ω'[0] = UInt64.ofNat 2608 ∧ ω'[1] = UInt64.ofNat T ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[10] = UInt64.ofNat 2 ∧ ω'[11] = UInt64.ofNat (T + 8 - k) ∧
      ω'[12] = UInt64.ofNat k := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h2, h12, hT, hk, hF, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h2, h12, Nat.mod_eq_of_lt hF]

/-- 60280 … the return: ω₀ reloaded from T + 8, the frame closed, the return to t. -/
theorem u8x_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t : Nat) (hT : 65536 ≤ T ∧ T + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (r8 : rdN μ (T + 8) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, T + 8 ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 60280 ω μ x t ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  have hr0 : r0 % 18446744073709551616 % 4294967296 = r0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r8, hret, hr0, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

end Services.Bootstrap.Fmt
