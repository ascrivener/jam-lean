import Services.Bootstrap.Fmt.Tac

/-!
# `Formatter::pad_integral` with plain options

`pad_integral` (61857) writes an integer's digits, already rendered into a buffer, through the
`Formatter` F. The digits sit at ω₁₁ … ω₁₁ + ω₁₂, and the prefix (`0x`, …) at ω₉ … ω₉ + ω₁₀.

With plain options (no `+`, no `#`, width 0, as `{}`, `{:?}` and `{:x}` give) it:
1. writes no sign and no prefix (`write_prefix`, 64897, returns `Ok` at once);
2. tail-calls the sink's `write_str` through the vtable at F + 8.

These are its steps:
- `pi_a`: 61857 … 64897;
- `pi_b`: `write_prefix` … 62019;
- `pi_c`: 62019 … the vtable's `write_str`.
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 61857 … 62013, plain options: `pad_integral` opens a 104-octet frame at T = sp − 104 (ω₀, ω₅, ω₆
    at T + 96, T + 88, T + 80; the digits' address and length at T + 16, T + 24; the sign word
    2⁶⁴ − 1, "none", at T + 32; no prefix at T + 40, T + 48) and calls `write_prefix` (64897) with
    the `Formatter`'s sink (F, F + 8), returning to 62019 (2628). -/
theorem pi_a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp F dig len r0 v5 v6 buf vt pl : Nat) (hsp : 65536 + 104 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat F) (h10 : ω[10] = UInt64.ofNat pl)
    (h11 : ω[11] = UInt64.ofNat dig) (h12 : ω[12] = UInt64.ofNat len)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      dig < 18446744073709551616 ∧ len < 4294967296 ∧ pl < 18446744073709551616)
    (hF : F + 24 ≤ sp - 104 ∨ sp ≤ F) (hF1 : F + 24 < 4294967296)
    (ro : rdN μ (F + 16) 4 = 1610612768) (rw0 : rdN μ (F + 20) 2 = 0)
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
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h10, h11, h12, hv, hbv, hsp, hF, hF1, ro, rw0, rb, rv, hrF, hw, hr,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rw [rdN_ones _ (sp - 104 + 32) (by omega)]
    all_goals try rw [rdN_zero _ (sp - 104 + 40) (by omega)]
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8]

/-- 64897 … 64990 and the return to 62019: `write_prefix` with no sign (ω₉ = 2⁶⁴ − 1) and no prefix
    (ω₁₀ = 0) returns `Ok` at once, writing only its 40-octet frame below T. -/
theorem pi_b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 + 40 ≤ T ∧ T < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 2628) (h1 : ω[1] = UInt64.ofNat T)
    (h9 : ω[9] = UInt64.ofNat 18446744073709551615) (h10 : ω[10] = UInt64.ofNat 0)
    (hw : ∀ a, T - 40 ≤ a → a < T → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 64897 ω μ x 62019 ω' μ' x 20 ∧
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

/-- 62019 … 62203: `write_prefix` returned `Ok`: `pad_integral` restores ω₀, ω₅, ω₆ from T + 96,
    T + 88, T + 80, closes its frame and tail-calls the sink's `write_str` (the word at vt + 24, 2596
    for the `String`, so 59959) with the buffer `buf` (ω₅), the digits (T + 16) and their length
    (T + 24). -/
theorem pi_c {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T buf vt dig len r0 v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 104 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat buf) (h6 : ω[6] = UInt64.ofNat vt)
    (h7 : ω[7] = UInt64.ofNat 0) (hvt : vt + 32 < 4294967296) (hbuf : buf < 18446744073709551616)
    (rws : rdN μ (vt + 24) 8 = 2596) (rd : rdN μ (T + 16) 8 = dig) (rl : rdN μ (T + 24) 8 = len)
    (r0' : rdN μ (T + 96) 8 = r0) (r5 : rdN μ (T + 88) 8 = v5) (r6 : rdN μ (T + 80) 8 = v6)
    (hrv : ∀ a, vt + 24 ≤ a → a < vt + 32 → μ.readable a = true)
    (hr : ∀ a, T ≤ a → a < T + 104 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 62019 ω μ x 59959 ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 104) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat buf ∧ ω'[8] = UInt64.ofNat dig ∧
      ω'[9] = UInt64.ofNat len := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hT, hvt, rws, rd, rl, r0', r5, r6, hrv, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [Nat.mod_eq_of_lt hbuf, Nat.mod_eq_of_lt (rdN_lt64 μ (T + 96)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 88)),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 80)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 16)),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 24))]

end Services.Bootstrap.Fmt
