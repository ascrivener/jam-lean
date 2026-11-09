import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.DecodeU32

/-!
# `Instruction::decode` of `Designate` with no keys

`Designate { keys: BoundedVec<[u8; 336], 3·𝖢> }` (tag 13) is decoded by a helper with a 48-octet frame
at H = A − 48: it decodes the length n (`decodeU32`), checks n against 3·𝖢 (𝖢 the core count, the
16-bit word at 196616), reads the n keys into a `Vec` at H (the key reader at 1300, with a 768-octet
frame), copies it to A, and returns. `Instruction::decode` then copies the three words at A to O + 8
after the discriminant word 2^63 + 12 at O.

This file proves the case n = 0, which allocates nothing and passes the check whatever 𝖢 is:
`designate_empty`.
-/

namespace Services.Bootstrap.Decode.Designate

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag

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

theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- A word read back where it was just written. -/
theorem rdN_writeN_same8 (μ : Memory) (a v : Nat) (ha : a + 8 ≤ 4294967296) :
    rdN (μ.writeN a (Num.encodeLE 8 v)) a 8 = v % 18446744073709551616 := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]), Num.decodeLE_encodeLE]

/-- Octets read back as a word where they were just written. -/
theorem rdN_writeN_lit (μ : Memory) (a : Nat) (bs : List UInt8) (hb : bs.length = 8)
    (ha : a + 8 ≤ 4294967296) : rdN (μ.writeN a bs) a 8 = Num.decodeLE bs := by
  unfold rdN
  rw [Memory.readN_writeN_same _ _ _ _ hb (by simp only [two32]; omega)]

/-- 21657 … 21687: the decoder opens its helper frame at H = A − 48 (the return address 998, O and the
    reader at H + 40, H + 32, H + 24), keeps A (its result slot) in ω₅ and the reader in ω₆, and calls
    `decodeU32` on the reader (return address 1648). -/
theorem d1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 48 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 48 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21657 ω μ x 31894 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1648 ∧ ω'[1] = UInt64.ofNat (A - 48) ∧ ω'[5] = UInt64.ofNat A ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 998 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 48 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show A - 48 + 40 = A - 8 by omega, show A - 48 + 32 = A - 16 by omega,
      show A - 48 + 24 = A - 24 by omega])
    post_simp
    all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
    all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))

/-- 35293 … 35313: the length 0 was decoded (ω₇ = 0, ω₈ = 0): the decoder computes 3·𝖢 from the core
    count at 196616 into ω₇ and the length into ω₉. -/
theorem d2a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat 0)
    (hc : ∀ a, 196616 ≤ a → a < 196618 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 35293 ω μ x 35315 ω' μ x 8 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[9] = UInt64.ofNat 0 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h7, h8, hc, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, Option.getD_some]

/-- 35315 … 35342: the bound check passes (the length ω₉ is 0), and the key reader (1300) is called for
    no keys into a `Vec` at H (ω₇ = H = ω₁, ω₈ = the reader ω₆, ω₉ = 0), return address 1650. -/
theorem d2b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H : Nat)
    (hH : H < 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h9 : ω[9] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 35315 ω μ x 1300 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 1650 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat H ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat 0 := by
  have h9' : (ω[9]).toNat = 0 := by rw [h9]; rfl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h9', hH]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try exact h9

/-- 35293 … 35342: `d2a` then `d2b`. -/
theorem d2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H : Nat)
    (hH : H < 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (h8 : ω[8] = UInt64.ofNat 0) (hc : ∀ a, 196616 ≤ a → a < 196618 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 35293 ω μ x 1300 ω' μ x 14 ∧
      ω'[0] = UInt64.ofNat 1650 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat H ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat 0 := by
  obtain ⟨ω1, r1, a0, a1, a5, a6, a9⟩ := d2a (p := p) (P := P) (R := R) x ω μ h7 h8 hc
  obtain ⟨ω2, r2, b0, b1, b5, b6, b7, b8, b9⟩ := d2b (p := p) (P := P) (R := R) x ω1 μ H hH (a1.trans h1) a9
  exact ⟨ω2, (r1.trans r2).mono (by omega), b0, b1.trans a1, b5.trans a5, b6.trans a6, b7,
    b8.trans a6, b9⟩

/-- **The key reader with no keys** (1300, n = 0): it opens a 768-octet frame, finds nothing to read,
    stores the empty `Vec` `{cap 0, ptr 1, len 0}` at O (ω₇), restores ω₀, ω₅, ω₆ and returns. -/
theorem keys_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd ret t v5 v6 : Nat) (hsp : 65536 + 768 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat 0) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ sp - 768 ∨ sp ≤ O)
    (hw : ∀ a, sp - 768 ≤ a → a < sp → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1300 ω μ x t ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 768 ∨ sp ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 768 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hwO, hO, hOS, hret, hjt, hbt,
      rdN_writeN_disjoint, rdN_writeN_same8, rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show sp - 768 + 768 = sp by omega])
    post_simp
    all_goals try decide

/-- 35349 … 35386: the key reader stored a `Vec` `{cap, ptr, len}` at H (cap ≠ 2^64 − 1): the helper
    copies it to A (ω₅), restores ω₀, ω₅, ω₆ from H + 40, H + 32, H + 24 and returns (to 21690 for the
    return address 998). -/
theorem d3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (H A cap ptr len v5 v6 : Nat) (hH : 65536 ≤ H ∧ H + 48 < 4294967296)
    (hA : A + 24 ≤ 4294967296) (hAH : A + 24 ≤ H ∨ H + 48 ≤ A)
    (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat A)
    (hcap : cap < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sc : μ.readN H 8 = Num.encodeLE 8 cap) (sp : μ.readN (H + 8) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (H + 16) 8 = Num.encodeLE 8 len)
    (s0 : μ.readN (H + 40) 8 = Num.encodeLE 8 998) (s5 : μ.readN (H + 32) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (H + 24) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, H ≤ a → a < H + 48 → μ.readable a = true)
    (hw : ∀ a, A ≤ a → a < A + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35349 ω μ x 21690 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 998 ∧ ω'[1] = UInt64.ofNat (H + 48) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN A 8 = Num.encodeLE 8 cap ∧ μ'.readN (A + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (A + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < A ∨ A + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) sc
  have rp := rd8 hptr sp
  have rl := rd8 hlen sl
  have r0 := rd8 (by decide) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  have hc : ¬ cap = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hH, hA, hAH, hw, hr, rc, rp, rl, r0, r5, r6, hc, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- 21690 … 21739: the result at A is a `Vec` `{w₀, w₁, w₂}` (w₀ ≠ 2^64 − 1): its three words are copied
    to O + 8, the discriminant word 2^63 + 12 goes to O, and the function returns through its frame at
    A. -/
theorem d4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O w0 w1 w2 ret t v5 v6 : Nat) (hA : 65536 ≤ A ∧ A + 56 < 4294967296)
    (hO : O + 32 ≤ 4294967296) (hOA : O + 32 ≤ A ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (hw0 : w0 < 18446744073709551615)
    (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0' : μ.readN A 8 = Num.encodeLE 8 w0) (s1' : μ.readN (A + 8) 8 = Num.encodeLE 8 w1)
    (s2' : μ.readN (A + 16) 8 = Num.encodeLE 8 w2)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, A ≤ a → a < A + 56 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21690 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775820 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 w0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 w1 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0' := rd8 (by omega) s0'
  have r1' := rd8 hw1 s1'
  have r2' := rd8 hw2 s2'
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  have hw0' : ¬ w0 = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hA, hO, hOA, hw, hr, r0', r1', r2', r0, r5, r6, hw0', hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- **`Designate` with no keys**: from 20626, with tag 13 read without error and the reader
    `{ptr, len}` at rd (ω₆) holding ℰ(0) next (the octet 0), `Instruction::decode` returns
    `Designate { keys: [] }` in its slot O: the discriminant word 2^63 + 12 at O and the empty `Vec`
    `{cap 0, ptr 1, len 0}` at O + 8. Nothing is allocated, and the bound check passes whatever the core
    count at 196616 is. The reader is advanced by 1. Memory changes only in A − 816 … A + 24 (the
    helper's and the callees' frames, and the result slot at A), the reader and O … O + 32. -/
theorem designate_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 816 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 13) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hc : ∀ a, 196616 ≤ a → a < 196618 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hlen : 1 ≤ len ∧ len < 4294967296) (hzero : μ.read ptr = 0)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 816 ∨ A + 56 ≤ rd) (hpA : ptr + 32 ≤ A - 816 ∨ A + 56 ≤ ptr)
    (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hOA : O + 32 ≤ A - 816 ∨ A + 56 ≤ O) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O) (hO32 : O + 32 ≤ 4294967296)
    (hws : ∀ a, A - 816 ≤ a → a < A + 24 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true)
    (hrp : μ.readable ptr = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 650 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775820 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 1 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 0 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1) ∧
      (∀ a, a < 4294967296 → (a < A - 816 ∨ A + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by have := F.hO; omega
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 13 (by decide)
    (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    d1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1)
      (e5'.trans F.h5) (e6'.trans h6) hO64 (by omega) (fun a h1 h2 => hws a (by omega) (by omega))
  have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := by simp [Blob.encodeNat]
  obtain ⟨ω3, μ3, run3, ⟨d0, d1', -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω2 μ2 1648 35293 (A - 48) rd ptr len b0 b1 b7 (by decide) jte_823
      bs_35293 ⟨by omega, by omega⟩ hrd hptr (by omega) (by omega) hpr
      (fun a h1 h2 => by rw [bwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR8) 0 (by decide)
      (by rw [he]; simp; omega)
      (fun a h1 h2 => by rw [he] at h2; simp at h2; rw [brd, show a = ptr by omega]; exact hrp)
      (by rw [he]; simp [Memory.readN, bfr ptr (by omega) (by omega), hzero])
  rw [he] at dR0 dR8
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at dR0 dR8
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := d2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 48)
    (by omega) (by rw [d1', b1]) d7 d8 (fun a h1 h2 => by rw [drd, brd]; exact hc a h1 h2)
  have hv6 : ω4[6] = UInt64.ofNat rd := by rw [c6, d6, b6]
  obtain ⟨ω5, μ5, run5, v0, v1, v5', v6', vc, vp, vl, vfr, vrd, vwr⟩ :=
    keys_empty (p := p) (P := P) (R := R) x ω4 μ3 (A - 48) (A - 48) rd 1650 35349 A rd ⟨by omega, by omega⟩
      c0 (by rw [c1, d1', b1]) (by rw [c5, d5, b5]) hv6 c7 (by rw [c8, d6, b6]) c9 (by omega) (by omega)
      (by omega) (by decide) jte_824 bs_35349 (by omega) (Or.inr (Nat.le_refl _))
      (fun a h1 h2 => by rw [dwr, bwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [dwr, bwr]; exact hws a (by omega) (by omega))
  have hfrH : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega) (by omega)).trans (dfr a (by omega) (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fA, fA8, fA16, ffr, frd, fwr⟩ :=
    d3 (p := p) (P := P) (R := R) x ω5 μ5 (A - 48) A 0 1 0 O rd ⟨by omega, by omega⟩ (by omega) (by omega)
      v1 v5' (by decide) (by decide) (by decide) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 40 = A - 8 by omega]; exact bs0)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 32 = A - 16 by omega]; exact bs5)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 24 = A - 24 by omega]; exact bs6)
      (fun a h1 h2 => by rw [vrd, drd, brd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [vwr, dwr, bwr]; exact hws a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → (a < A - 816 ∨ A + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (ffr a h0 (by omega)).trans ((vfr a h0 (by omega) (by omega)).trans
      ((dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))))
  have rd6 : ∀ a, μ6.readable a = μ.readable a := fun a => by rw [frd, vrd, drd, brd]
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [fwr, vwr, dwr, bwr]
  obtain ⟨ω7, μ7, run7, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    d4 (p := p) (P := P) (R := R) x ω6 μ6 A O 0 1 0 ret t v5 v6 ⟨by omega, by omega⟩ hO32 (by omega)
      (by rw [f1]; congr 1; omega) f5 (by decide) (by decide) (by decide) F.hv5 F.hv6 fA fA8 fA16
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt
      (fun a h1 h2 => by
        rw [rd6]
        rcases Nat.lt_or_ge a (A + 24) with h | h
        · exact Memory.readable_of_writable (hws a (by omega) h)
        · exact F.hr a (by omega) h2)
      (fun a h1 h2 => by rw [wr6]; exact hwO a h1 h2)
  have hrd7 : ∀ j, j < 16 → μ7.read (rd + j) = μ3.read (rd + j) := fun j hj =>
    (nfr _ (by omega) (by omega)).trans ((ffr _ (by omega) (by omega)).trans (vfr _ (by omega) (by omega) (by omega)))
  refine ⟨ω7, μ7, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))).mono
    (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_, fun a => by rw [nrd, rd6],
    fun a => by rw [nwr, wr6]⟩
  · rw [Memory.readN_congr (a := rd) (n := 8) (fun j hj => hrd7 j (by omega))]; exact dR0
  · have e8 : μ7.readN (rd + 8) 8 = μ3.readN (rd + 8) 8 :=
      Memory.readN_congr (fun j hj => by rw [Nat.add_assoc]; exact hrd7 (8 + j) (by omega))
    rw [e8]; exact dR8
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact hfar a h0 h1 h2

end Services.Bootstrap.Decode.Designate
