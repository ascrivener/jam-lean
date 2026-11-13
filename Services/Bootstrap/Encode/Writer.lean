import Services.Bootstrap.MemcpyBig
import Services.Bootstrap.Decode.U32Hash

/-!
# `Vec<u8>::extend_from_slice` (58508), without growth

The output writer of `Encode::encode_to` is a `Vec<u8>` `{cap, ptr, len}` (three words at v). The
function at 58508 appends n octets from `src`: if `cap − len < n` it first grows the vector
(58251, not covered here); otherwise it copies the octets to `ptr + len` (`memcpy`, 68729, skipped for
n = 0) and stores `len + n`. This file proves the path without growth: `extend_ok`.
-/

namespace Services.Bootstrap.Encode.Writer

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

macro "post_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

/-- A word read back from its encoding. -/
theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- 58508 … 58548: room for n > 0 octets (`len + n ≤ cap`): the function opens a 32-octet frame at
    sp − 32 (ω₀, ω₅, ω₆ at sp − 8, sp − 16, sp − 24), parks `len` at sp − 32 and calls `memcpy` of n
    octets from `src` to `ptr + len` (return address 2552). -/
theorem w1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v src n cap ptr len r0 r5 r6 : Nat) (hsp : 65536 + 32 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hv : v + 24 ≤ 4294967296)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hn : 0 < n) (hroom : len + n ≤ cap) (hcap : cap < 18446744073709551616)
    (hpl : ptr + len < 18446744073709551616)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len) (hptr : ptr < 18446744073709551616)
    (hvs : v + 24 ≤ sp - 32 ∨ sp ≤ v)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 32 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x 68729 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2552 ∧ ω'[1] = UInt64.ofNat (sp - 32) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat v ∧ ω'[7] = UInt64.ofNat (ptr + len) ∧ ω'[8] = UInt64.ofNat src ∧
      ω'[9] = UInt64.ofNat n ∧
      μ'.readN (sp - 32) 8 = Num.encodeLE 8 len ∧ μ'.readN (sp - 8) 8 = Num.encodeLE 8 r0 ∧
      μ'.readN (sp - 16) 8 = Num.encodeLE 8 r5 ∧ μ'.readN (sp - 24) 8 = Num.encodeLE 8 r6 ∧
      (∀ a, a < 4294967296 → (a < sp - 32 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) vc
  have rp := rd8 hptr vp
  have rl := rd8 (by omega) vl
  have hr : ∀ a, sp - 32 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hrv, rc, rp, rl, hv, hvs, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show sp - 32 + 24 = sp - 8 by omega, show sp - 32 + 16 = sp - 16 by omega,
      show sp - 32 + 8 = sp - 24 by omega]
    post_simp
    all_goals try assumption

/-- 58557 … 58576: the function stores `len + n` (ω₉ + ω₅) at v + 16, restores ω₀, ω₅, ω₆ from its
    frame at S and returns. -/
theorem w3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S v n len ret t r5 r6 : Nat) (hS : 65536 ≤ S ∧ S + 32 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat v)
    (h9 : ω[9] = UInt64.ofNat len)
    (hv : v + 24 ≤ 4294967296) (hvS : v + 24 ≤ S ∨ S + 32 ≤ v) (hln : len + n < 18446744073709551616)
    (s0 : μ.readN (S + 24) 8 = Num.encodeLE 8 ret)
    (s5 : μ.readN (S + 16) 8 = Num.encodeLE 8 r5) (s6 : μ.readN (S + 8) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58557 ω μ x t ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 32) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + n) ∧
      (∀ a, a < 4294967296 → (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by omega) s0
  have r5' := rd8 hr5 s5
  have r6' := rd8 hr6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h9, hS, hv, hvS, hr, hw, r0, r5', r6', hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold,
      ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (rw [Nat.add_comm]; rfl)

/-- 58554 … 58556: back from `memcpy`, the function reloads `len` from its frame at S. -/
theorem w2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S len : Nat)
    (hS : S + 8 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (hl : len < 18446744073709551616)
    (sl : μ.readN S 8 = Num.encodeLE 8 len) (hr : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 58554 ω μ x 58557 ω' μ x 2 ∧ ω'[9] = UInt64.ofNat len ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have rl := rd8 hl sl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, hr, rl, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    post_simp

/-- 58508 … 58535 for n = 0: nothing to copy; the function opens its frame and goes to 58557 with
    ω₉ = len. -/
theorem wz1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v cap len r0 r5 r6 : Nat) (hsp : 65536 + 32 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat v)
    (h9 : ω[9] = UInt64.ofNat 0) (hv : v + 24 ≤ 4294967296) (hvs : v + 24 ≤ sp - 32 ∨ sp ≤ v)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hroom : len ≤ cap) (hcap : cap < 18446744073709551616)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 32 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x 58557 ω' μ' x 11 ∧
      ω'[1] = UInt64.ofNat (sp - 32) ∧ ω'[5] = UInt64.ofNat 0 ∧ ω'[6] = UInt64.ofNat v ∧
      ω'[9] = UInt64.ofNat len ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 r5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 r6 ∧
      (∀ a, a < 4294967296 → (a < sp - 32 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) vc
  have rl := rd8 (by omega) vl
  have hr : ∀ a, sp - 32 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h9, hsp, hw, hr, hrv, rc, rl, hv, hvs, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show sp - 32 + 24 = sp - 8 by omega, show sp - 32 + 16 = sp - 16 by omega,
      show sp - 32 + 8 = sp - 24 by omega]
    post_simp
    all_goals try assumption

/-- **`memcpy` of any n** (68729), in `memcpy_big`'s form: the n octets at `dst` become the source's,
    ω₀, ω₁, ω₅, ω₆ are kept, and memory is otherwise unchanged but for the frame [sp − 48, sp). -/
theorem memcpy_any {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (ret t sp dst src n : Nat) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat dst) (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (hs : 65536 ≤ src ∧ src + n + 16 < 4294967296) (hd : 65536 ≤ dst ∧ dst + n + 16 < 4294967296)
    (hdj : dst + n + 24 ≤ src ∨ src + n + 24 ≤ dst) (hfd : sp ≤ dst ∨ dst + n + 16 ≤ sp - 48)
    (hfs : sp + 8 ≤ src ∨ src + n + 16 ≤ sp - 48)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + n → μ.writable a = true)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 68729 ω μ x t ω' μ' x (7 * n + 320) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN dst n = μ.readN src n ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + n ≤ a) → (a < sp - 48 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rcases Nat.lt_or_ge n 16 with hn | hn
  · obtain ⟨ω', run, e0, e1, -, -, -, e5, e6, -, -⟩ := memcpy_small_regs (p := p) (P := P) (R := R) x ω μ
      ret t sp dst src n h0 h1 h7 h8 h9 hn hret hjt hbt ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) hwf hr hw
    refine ⟨ω', _, run.mono (by omega), e0.trans h0, e1.trans h1, e5, e6, ?_, fun a ha h1' h2' => ?_,
      fun a => ?_, fun a => ?_⟩
    · rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]; omega)]
    · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
      unfold memcpyFrame
      repeat rw [Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
    · simp [memcpyFrame, Memory.readable_writeN]
    · simp [memcpyFrame, Memory.writable_writeN]
  · obtain ⟨ω', μ', run, e0, e1, e5, e6, ed, efr, erd, ewr⟩ := memcpy_big (p := p) (P := P) (R := R) x ω μ
      ret t sp dst src n h0 h1 h7 h8 h9 hret hjt hbt hsp hn (by omega) (by omega) hdj (by omega) hfs hr hw hwf
    exact ⟨ω', μ', run.mono (by omega), e0, e1, e5, e6, ed, efr, erd, ewr⟩

/-- **`Vec<u8>::extend_from_slice` without growth** (58508): with the vector `{cap, ptr, len}` at v
    and room for the n octets at `src` (`len + n ≤ cap`), the function appends them at `ptr + len`,
    stores `len + n` and returns, keeping ω₀, ω₁, ω₅, ω₆. Memory changes only there and in its stack
    frames [sp − 80, sp). -/
theorem extend_ok {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v src n cap ptr len ret t : Nat) (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (hroom : len + n ≤ cap) (hcap : cap < 18446744073709551616)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hv : v + 24 ≤ 4294967296) (hvs : v + 24 ≤ sp - 80 ∨ sp ≤ v)
    (hdst : 65536 ≤ ptr + len ∧ ptr + len + n + 16 < 4294967296)
    (hsrc : 65536 ≤ src ∧ src + n + 16 < 4294967296)
    (hdj : ptr + len + n + 24 ≤ src ∨ src + n + 24 ≤ ptr + len)
    (hfd : sp ≤ ptr + len ∨ ptr + len + n + 16 ≤ sp - 80)
    (hfs : sp ≤ src ∨ src + n + 16 ≤ sp - 80)
    (hvd : v + 24 ≤ ptr + len ∨ ptr + len + n ≤ v)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hwd : ∀ a, ptr + len ≤ a → a < ptr + len + n → μ.writable a = true)
    (hw : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x t ω' μ' x (7 * n + 360) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (ptr + len) n = μ.readN src n ∧ μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + n) ∧
      (∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → (a < ptr + len ∨ ptr + len + n ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have h5' := UInt64.toNat_lt ω[5]
  have h6' := UInt64.toNat_lt ω[6]
  have hr0 : ret < 18446744073709551616 := by omega
  rcases Nat.eq_zero_or_pos n with hn0 | hnp
  · subst hn0
    obtain ⟨ω1, μ1, run1, a1, a5, a6, a9, a0', a5', a6', afr, ard, awr⟩ := wz1 (p := p) (P := P) (R := R) x ω μ
      sp v cap len ret ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h9 hv (by omega) hr0 h5' h6'
      (by omega) hcap vc vl hrv (fun a h1 h2 => hw a (by omega) h2)
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bl, bfr, brd, bwr⟩ := w3 (p := p) (P := P) (R := R) x ω1 μ1
      (sp - 32) v 0 len ret t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ a1 a5 a6 a9 hv (by omega) (by omega)
      (by rw [show sp - 32 + 24 = sp - 8 by omega]; exact a0')
      (by rw [show sp - 32 + 16 = sp - 16 by omega]; exact a5')
      (by rw [show sp - 32 + 8 = sp - 24 by omega]; exact a6') h5' h6' hret hjt hbt
      (fun a h1 h2 => by rw [ard]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
      (fun a h1 h2 => by rw [awr]; exact hwv a h1 h2)
    refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), b0, by rw [b1]; congr 1; omega, by rw [b5, ← h5],
      by rw [b6, ← h6], by simp [Memory.readN], by simpa using bl, fun a h0' h1' _ h3' => ?_, fun a => by rw [brd, ard],
      fun a => by rw [bwr, awr]⟩
    rw [bfr a h0' h3', afr a h0' (by omega)]
  · obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, al, a0', a5', a6', afr, ard, awr⟩ := w1 (p := p) (P := P)
      (R := R) x ω μ sp v src n cap ptr len ret ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 hv
      hr0 h5' h6' hnp hroom hcap (by omega) vc vp vl (by omega) (by omega) hrv
      (fun a h1 h2 => hw a (by omega) h2)
    obtain ⟨ω2, μ2, run2, c0, c1, c5, c6, cd, cfr, crd, cwr⟩ := memcpy_any (p := p) (P := P) (R := R) x ω1 μ1
      2552 58554 (sp - 32) (ptr + len) src n a0 a1 a7 a8 a9 (by decide) jte_1275 bs_58554
      ⟨by omega, by omega, by omega⟩ hsrc hdst hdj (by omega) (by omega)
      (fun a h1 h2 => by rw [ard]; exact hr a h1 h2) (fun a h1 h2 => by rw [awr]; exact hwd a h1 h2)
      (fun a h1 h2 => by rw [awr]; exact hw a (by omega) (by omega))
    have back2 : ∀ a, a < 4294967296 → (a < ptr + len ∨ ptr + len + n ≤ a) → (a < sp - 80 ∨ sp - 32 ≤ a) →
        μ2.read a = μ1.read a := fun a h0 h1 h2 => cfr a h0 h1 h2
    obtain ⟨ω3, run3, d9, d0, d1, d5, d6⟩ := w2 (p := p) (P := P) (R := R) x ω2 μ2 (sp - 32) len (by omega)
      (c1) (by omega)
      (by rw [Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega) (by omega))]; exact al)
      (fun a h1 h2 => by rw [crd, ard]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
    obtain ⟨ω4, μ4, run4, e0, e1, e5, e6, el, efr, erd, ewr⟩ := w3 (p := p) (P := P) (R := R) x ω3 μ2
      (sp - 32) v n len ret t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ (d1.trans c1) (d5.trans (c5.trans a5))
      (d6.trans (c6.trans a6)) d9 hv (by omega) (by omega)
      (by rw [show sp - 32 + 24 = sp - 8 by omega, Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega)
        (by omega))]; exact a0')
      (by rw [show sp - 32 + 16 = sp - 16 by omega, Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega)
        (by omega))]; exact a5')
      (by rw [show sp - 32 + 8 = sp - 24 by omega, Memory.readN_congr (fun j hj => back2 _ (by omega) (by omega)
        (by omega))]; exact a6') h5' h6' hret hjt hbt
      (fun a h1 h2 => by rw [crd, ard]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
      (fun a h1 h2 => by rw [cwr, awr]; exact hwv a h1 h2)
    refine ⟨ω4, μ4, (run1.trans (run2.trans (run3.trans run4))).mono (by omega), e0,
      by rw [e1]; congr 1; omega, by rw [e5, ← h5], by rw [e6, ← h6], ?_, el, fun a h0' h1' h2' h3' => ?_,
      fun a => by rw [erd, crd, ard], fun a => by rw [ewr, cwr, awr]⟩
    · rw [Memory.readN_congr (fun j hj => efr _ (by omega) (by omega)), cd]
      exact Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
    · rw [efr a h0' h3', back2 a h0' h2' (h1'.elim (fun h => Or.inl h) (fun h => Or.inr (by omega))),
        afr a h0' (h1'.elim (fun h => Or.inl (by omega)) (fun h => Or.inr h))]
