import Services.Bootstrap.Fmt.Tac

/-!
# `<String as fmt::Write>::write_str`, the logging sink

scratch
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 59959 … 59983: `write_str` opens a 32-octet frame at sp − 32 (ω₀, ω₅, ω₆ at +24, +16, +8),
    keeps n in ω₅ and the `String` W in ω₆, reads its capacity and length and goes to the reserve
    path 60030 when cap − len < n, else on to 59986, with len in ω₉. -/
theorem ws_entry {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp W src n cap len ret v5 v6 : Nat) (hsp : 65536 + 32 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h5 : ω[5] = UInt64.ofNat v5) (h6 : ω[6] = UInt64.ofNat v6)
    (hv : ret < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hn : n < 4294967296)
    (hc : rdN μ W 8 = cap) (hl : rdN μ (W + 16) 8 = len) (hlc : len ≤ cap) (hcap : cap < 4294967296)
    (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ sp - 32 ∨ sp ≤ W)
    (hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 32 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59959 ω μ x (if cap - len < n then 60030 else 59986) ω' μ' x 10 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat (sp - 32) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat W ∧ ω'[8] = UInt64.ofNat src ∧ ω'[9] = UInt64.ofNat len ∧
      rdN μ' (sp - 32 + 24) 8 = ret ∧ rdN μ' (sp - 32 + 16) 8 = v5 ∧ rdN μ' (sp - 32 + 8) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 32 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 32 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  by_cases hb : cap - len < n
  · rw [if_pos hb]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h5, h6, hv, h1, h7, h8, h9, hsp, hw, hr, hWr, hc, hl, hb, hlc, hn, hcap, hW, hWf, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [h8, rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hv.1,
        Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2]
  · rw [if_neg hb]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h0, h5, h6, hv, h1, h7, h8, h9, hsp, hw, hr, hWr, hc, hl, hb, hlc, hn, hcap, hW, hWf, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [h8, rdN_writeN_disjoint, rdN_writeN_same8, Nat.mod_eq_of_lt hv.1,
        Nat.mod_eq_of_lt hv.2.1, Nat.mod_eq_of_lt hv.2.2]

/-- 59986: with n (ω₅) = 0, on to 60008. -/
theorem ws_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h5 : ω[5] = UInt64.ofNat 0) :
    FreeStepsH p R 59986 ω μ x 60008 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h5]

/-- 59986: with n (ω₅) > 0, on to 59989. -/
theorem ws_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (n : Nat) (h5 : ω[5] = UInt64.ofNat n) (hn : 0 < n ∧ n < 4294967296) :
    FreeStepsH p R 59986 ω μ x 59989 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h5, hn]

/-- 59989 … 59999: len (ω₉) saved at S, then `memcpy` (68729) called to copy the n octets at src
    (ω₈) to ptr + len, ptr the `String`'s buffer (at W + 8), returning to 60005 (2598). -/
theorem ws_copy {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S W n len ptr : Nat) (hS : 65536 ≤ S ∧ S + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat len) (hl : len < 4294967296) (hn : n < 4294967296)
    (hp : rdN μ (W + 8) 8 = ptr) (hpl : ptr + len < 4294967296)
    (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ S ∨ S + 8 ≤ W)
    (hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true)
    (hw : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 59989 ω μ x 68729 ω' (μ.writeN S (Num.encodeLE 8 len)) x 5 ∧
      ω'[0] = UInt64.ofNat 2598 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (ptr + len) ∧ ω'[8] = ω[8] ∧ ω'[9] = UInt64.ofNat n := by
  have hr : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h9, hS, hw, hr, hWr, hp, hl, hn, hpl, hW, hWf, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp

/-- 60005 … 60028: len reloaded from S (`ws_tail`), then from 60008 (`ws_fin`): the length
    len + n stored at W + 16, ω₇ = 0 (`Ok`), ω₀, ω₅, ω₆ restored from S + 24, S + 16, S + 8 and the
    frame closed; return to `ret`. -/
theorem ws_fin {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S W n len ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat len) (hl : len + n < 4294967296)
    (hW : W + 24 < 4294967296) (hWf : W + 24 ≤ S ∨ S + 32 ≤ W)
    (hWw : ∀ a, W + 16 ≤ a → a < W + 24 → μ.writable a = true)
    (r0 : rdN μ (S + 24) 8 = ret) (r5 : rdN μ (S + 16) 8 = v5) (r6 : rdN μ (S + 8) 8 = v6)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S ≤ a → a < S + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 60008 ω μ x t ω' (μ.writeN (W + 16) (Num.encodeLE 8 (n + len))) x 8 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 32) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h9, hS, hr, hWw, hl, hW, hWf, r0, r5, r6, hv5, hv6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp

/-- 60005: len reloaded from S into ω₉, then on to 60008. -/
theorem ws_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S len : Nat) (hS : 65536 ≤ S ∧ S + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (rl : rdN μ S 8 = len)
    (hr : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 60005 ω μ x 60008 ω' μ x 2 ∧ ω'[9] = UInt64.ofNat len ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hr, rl, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp

end Services.Bootstrap.Fmt
