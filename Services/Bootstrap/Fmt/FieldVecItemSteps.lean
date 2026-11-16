import Services.Bootstrap.Fmt.Tac

/-!
# `<&Vec<Item> as fmt::Debug>::fmt` (26504): the steps

As `FieldVecVecSteps` (26397, generated from it), for 32-octet elements (`Item`, field vtable 75816
→ 36917); ω₅ := 32 · len by one shift (`vw_b`, by hand).
-/

namespace Services.Bootstrap.Fmt

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem vw_a {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v vec ptr len r0 v5 v6 : Nat) (hsp : 196608 + 64 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v)
    (hv : r0 < 18446744073709551616 ∧ v5 < 18446744073709551616 ∧ v6 < 18446744073709551616 ∧
      v + 8 < 4294967296 ∧ vec + 24 < 4294967296)
    (hdv : sp ≤ v) (hdis : vec + 24 ≤ sp - 64 ∨ sp ≤ vec) (rv : rdN μ v 8 = vec)
    (rp : rdN μ (vec + 8) 8 = ptr) (rl : rdN μ (vec + 16) 8 = len)
    (hrv : ∀ a, v ≤ a → a < v + 8 → μ.readable a = true)
    (hrc : ∀ a, vec + 8 ≤ a → a < vec + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 64 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 26504 ω μ x 61708 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 1228 ∧ ω'[1] = UInt64.ofNat (sp - 64) ∧ ω'[5] = UInt64.ofNat len ∧
      ω'[6] = UInt64.ofNat ptr ∧ ω'[7] = UInt64.ofNat (sp - 64 + 16) ∧ ω'[8] = ω[8] ∧
      rdN μ' (sp - 64 + 56) 8 = r0 ∧ rdN μ' (sp - 64 + 48) 8 = v5 ∧ rdN μ' (sp - 64 + 40) 8 = v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 64 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hp : ptr < 18446744073709551616 := rp ▸ rdN_lt64 μ _
  have hl : len < 18446744073709551616 := rl ▸ rdN_lt64 μ _
  have hc : vec < 18446744073709551616 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, hsp, hv, hdv, hdis, rv, rp, rl, hc, hrv, hrc, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h0, h1, h5, h6, h7,
      Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hv.1, Nat.mod_eq_of_lt hv.2.1,
      Nat.mod_eq_of_lt hv.2.2.1]

theorem vw_b {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T len : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat len) (hl : 0 < len ∧ 32 * len < 18446744073709551616)
    (hw : ∀ a, T ≤ a → a < T + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 26534 ω μ x 26548 ω' μ' x 5 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (32 * len) ∧ ω'[6] = ω[6] ∧ rdN μ' T 8 = 75816 ∧
      (∀ a, a < 4294967296 → (a < T ∨ T + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 8 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hne : len ≠ 0 := by omega
  have e32 : len * 32 % 18446744073709551616 = 32 * len := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hT, hl, hne, e32, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h5, e32]
    all_goals first | (rw [rdN_lit8 _ _ _ rfl (by omega)]; decide) | (congr 1; omega) | skip

theorem vw_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (h5 : ω[5] = UInt64.ofNat 0) :
    FreeStepsH p R 26534 ω μ x 26581 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h5]

theorem vw_l {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T q : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h6 : ω[6] = UInt64.ofNat q) (hq : q + 32 < 18446744073709551616) (r0 : rdN μ T 8 = 75816)
    (hw : ∀ a, T ≤ a → a < T + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 26548 ω μ x 66019 ω' μ' x 7 ∧
      ω'[0] = UInt64.ofNat 1230 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 16) ∧ ω'[8] = UInt64.ofNat (T + 32) ∧ ω'[9] = UInt64.ofNat 75816 ∧
      rdN μ' (T + 8) 8 = q + 32 ∧ rdN μ' (T + 32) 8 = q ∧
      (∀ a, a < 4294967296 → (a < T + 8 ∨ T + 16 ≤ a) → (a < T + 32 ∨ T + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hT, hq, r0, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8, Num.decodeLE_encodeLE, h1, h6,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (show q < 18446744073709551616 by omega)]

theorem vw_n {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T m q : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (h5 : ω[5] = UInt64.ofNat m) (hm : 32 ≤ m ∧ m < 18446744073709551616) (r8 : rdN μ (T + 8) 8 = q)
    (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 26572 ω μ x (if m - 32 = 0 then 26581 else 26548) ω' μ x 3 ∧
      ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (m - 32) ∧ ω'[6] = UInt64.ofNat q := by
  have hq : q < 18446744073709551616 := r8 ▸ rdN_lt64 μ _
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : m - 32 = 0
  · rw [if_pos hz]
    have hm1 : m = 32 := by omega
    subst hm1
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hT, r8, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]
  · rw [if_neg hz]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hT, hm, hz, r8, hr, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]
      all_goals first | (congr 1; omega) | skip

theorem vw_e {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T) :
    ∃ ω', FreeStepsH p R 26581 ω μ x 66310 ω' μ x 2 ∧
      ω'[0] = UInt64.ofNat 1232 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (T + 16) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

theorem vw_r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t v5 v6 : Nat) (hT : 65536 ≤ T ∧ T + 64 < 4294967296) (h1 : ω[1] = UInt64.ofNat T)
    (r0' : rdN μ (T + 56) 8 = r0) (r5 : rdN μ (T + 48) 8 = v5) (r6 : rdN μ (T + 40) 8 = v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T ≤ a → a < T + 64 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 26591 ω μ x t ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 64) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, r0', r5, r6, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (rdN_lt64 μ (T + 48)), Nat.mod_eq_of_lt (rdN_lt64 μ (T + 40)), r5, r6]

end Services.Bootstrap.Fmt
