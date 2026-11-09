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
