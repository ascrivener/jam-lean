import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.DecodeU32

/-!
# `Option<Vec<u8>>::decode` and `Instruction::decode` of `LookedUp { data: Option<Vec<u8>> }`

`Option<Vec<u8>>::decode` (35937) takes ω₇ = O, the 24-octet slot for the result, and ω₈ = rd, the
reader, and opens a 56-octet frame at F = sp − 56. It reads the option's tag octet into F + 31
(`read_ok`):

* tag 0 (`None`): it stores the niche word 2^64 − 1 at O;
* tag 1 (`Some`): it decodes the length n (`decodeU32`, 31894) and reads n octets into a fresh
  `Vec<u8>` at F (`read_vec`, 3473, see `Services.Bootstrap.Decode.VecU8`), then copies the `Vec`
  `{cap, ptr, len}` to O;
* any other tag, or a failed read, gives the error word 2^64 − 2.

`LookedUp` (tag 18) calls it with O = A, its frame, and stores the variant into its slot: the
discriminant word 2^63 + 17, then the three words of the option.

This file proves `LookedUp` with `data = None` (`looked_up_none`) and with `data = Some []`
(`looked_up_empty`); neither allocates.
-/

namespace Services.Bootstrap.Decode.LookedUp

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

/-- 21807 … 21811: `LookedUp`'s decoder calls `Option<Vec<u8>>::decode` with O = A (ω₇ = ω₁) and the
    reader (ω₈ = ω₆), return address 1006. -/
theorem k1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) :
    ∃ ω', FreeStepsH p R 21807 ω μ x 35937 ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat 1006 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[1] ∧
      ω'[8] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go []
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 35937 … 35964: `Option<Vec<u8>>::decode` opens its frame at F = sp − 56 (the return address, ω₅,
    ω₆ at F + 48, F + 40, F + 32), keeps O in ω₅ and the reader in ω₆, zeroes the octet at F + 31 and
    calls the reader for 1 octet into F + 31 (return address 1682). -/
theorem o1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd ret v5 v6 : Nat) (hsp : 65536 + 56 ≤ sp ∧ sp < 4294967296)
    (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616) (hret : ret < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (hw : ∀ a, sp - 56 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35937 ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1682 ∧ ω'[1] = UInt64.ofNat (sp - 56) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (sp - 25) ∧
      ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 v6 ∧
      (∀ a, a < 4294967296 → (a < sp - 56 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, hsp, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show sp - 56 + 48 = sp - 8 by omega, show sp - 56 + 40 = sp - 16 by omega,
      show sp - 56 + 32 = sp - 24 by omega, show sp - 56 + 31 = sp - 25 by omega]); post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
    all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))

/-- 35970 … 36093: the tag read succeeded (ω₇ = 0) and is 0 (`None`): the niche word 2^64 − 1 goes to
    O (ω₅), and the function restores ω₀, ω₅, ω₆ from its frame at F and returns. -/
theorem o_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F O ret t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (hO : O + 8 ≤ 4294967296) (hOF : O + 8 ≤ F + 32 ∨ F + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (tag : μ.read (F + 31) = 0)
    (s0 : μ.readN (F + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (F + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (F + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, F + 31 ≤ a → a < F + 56 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 35970 ω μ x t ω' (μ.writeN O (Num.encodeLE 8 18446744073709551615)) x 12 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have rb : rdN μ (F + 31) 1 = 0 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h7, hF, hO, hOF, hw, hr, rb, r0, r5, r6, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    post_simp

/-- 35970 … 35988: the tag read succeeded (ω₇ = 0) and is 1 (`Some`): the length decoder (31894) is
    called on the reader (ω₇ = ω₆), return address 1684. -/
theorem o_some {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F : Nat) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0) (tag : μ.read (F + 31) = 1)
    (hr : μ.readable (F + 31) = true) :
    ∃ ω', FreeStepsH p R 35970 ω μ x 31894 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 1684 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] := by
  have rb : rdN μ (F + 31) 1 = 1 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hF, hr, rb, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 35994 … 36010: the length n < 2^32 was decoded (ω₇ = 0, ω₈ = n): `read_vec` (3473) is called for n
    octets into a `Vec` at F (ω₇ = F, ω₈ = the reader ω₆, ω₉ = n), return address 1686. -/
theorem o_len {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F n : Nat) (hF : F < 4294967296) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R 35994 ω μ x 3473 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 1686 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat F ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, h8, hF, hn]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 36016 … 36053: `read_vec` stored a `Vec` `{cap, ptr, len}` at F (cap ≠ 2^64 − 1, not its error):
    the three words are copied to O (ω₅), and the function restores ω₀, ω₅, ω₆ from its frame at F
    and returns. -/
theorem o_copy {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F O cap ptr len ret t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 56 < 4294967296)
    (hO : O + 24 ≤ 4294967296) (hOF : O + 24 ≤ F ∨ F + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat O)
    (hcap : cap < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sc : μ.readN F 8 = Num.encodeLE 8 cap) (sp : μ.readN (F + 8) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (F + 16) 8 = Num.encodeLE 8 len)
    (s0 : μ.readN (F + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (F + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (F + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, F ≤ a → a < F + 56 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36016 ω μ x t ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) sc
  have rp := rd8 hptr sp
  have rl := rd8 hlen sl
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  have hc : ¬ cap = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hF, hO, hOF, hw, hr, rc, rp, rl, r0, r5, r6, hc, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- 21817 … 21869: `Option<Vec<u8>>::decode` returned without error (the word w₀ at A is not
    2^64 − 2): `LookedUp`'s decoder copies the option's three words w₀, w₁, w₂ from A to O + 8, stores the
    discriminant word 2^63 + 17 at O, and returns through its frame at A. -/
theorem k2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O w0 w1 w2 ret t v5 v6 : Nat) (hA : 65536 ≤ A ∧ A + 56 < 4294967296)
    (hO : O + 32 ≤ 4294967296) (hOA : O + 32 ≤ A ∨ A + 56 ≤ O)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (hw0 : w0 < 18446744073709551616) (hw0' : w0 ≠ 18446744073709551614)
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
    ∃ ω' μ', FreeStepsH p R 21817 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775825 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 w0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 w1 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0' := rd8 hw0 s0'
  have r1' := rd8 hw1 s1'
  have r2' := rd8 hw2 s2'
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hA, hO, hOA, hw, hr, r0', r1', r2', r0, r5, r6, hw0', hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- A read of one octet as `read`. -/
theorem read_of_readN1 {μ ν : Memory} {a b : Nat} (h : μ.readN a 1 = ν.readN b 1) : μ.read a = ν.read b := by
  simpa [Memory.readN] using h

/-- **`LookedUp { data: None }`**: from 20626, with tag 18 read without error and the reader
    `{ptr, len}` at rd (ω₆) holding the octet 0 (`None`) next, `Instruction::decode` returns
    `LookedUp { data: None }` in its slot O: the discriminant word 2^63 + 17 at O and the niche word
    2^64 − 1 at O + 8. The reader is advanced by 1. Memory changes only in A − 144 … A + 8 (the frames
    of the callees), the reader and O … O + 32. -/
theorem looked_up_none {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 144 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 18) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296)
    (hlen : 1 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hnone : μ.read ptr = 0)
    (hrdA : rd + 16 ≤ A - 144 ∨ A + 56 ≤ rd) (hpA : ptr + 16 ≤ A - 144 ∨ A + 56 ≤ ptr)
    (hOA : O + 32 ≤ A - 144 ∨ A + 56 ≤ O) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O) (hO32 : O + 32 ≤ 4294967296)
    (hws : ∀ a, A - 144 ≤ a → a < A + 8 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true)
    (hrp : μ.readable ptr = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 120 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775825 ∧
      μ'.readN (O + 8) 8 = Num.encodeLE 8 18446744073709551615 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1) ∧
      (∀ a, a < 4294967296 → (a < A - 144 ∨ A + 8 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by have := F.hO; omega
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 18 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, run2, f0, f1, f5, f6, f7, f8⟩ := k1 (p := p) (P := P) (R := R) x ω1 μ
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    o1 (p := p) (P := P) (R := R) x ω2 μ A A rd 1006 O rd ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [f0])
      (by rw [f1, e1, F.h1]) (by rw [f5, e5, F.h5]) (by rw [f6, e6, h6]) (by rw [f7, e1, F.h1])
      (by rw [f8, e6, h6]) (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 1682 35970 (A - 56) rd (A - 25) ptr len 1 g0 g1 g7 g8 g9
      (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ hptr (by decide) hlen.1
      hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd, show a = ptr by omega]; exact hrp)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (A - 56 + 31) = 0 := by
    rw [show A - 56 + 31 = A - 25 by omega, read_of_readN1 kbuf, ← hnone]
    exact gfr ptr (by omega) (by omega)
  have hfr4 : ∀ a, A - 56 ≤ a → a < A + 56 → a ≠ A - 25 → μ4.read a = μ3.read a :=
    fun a h1 h2 h3 => kfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6⟩ := o_none (p := p) (P := P) (R := R) x ω4 μ4 (A - 56) A 1006 21817 O rd
    ⟨by omega, by omega⟩ (by omega) (by omega) (by rw [k1', g1]) (by rw [k5, g5]) k7 (by have := F.hO; omega)
    (by omega) htag
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega)), show A - 56 + 48 = A - 8 by omega]; exact gs0)
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega)), show A - 56 + 40 = A - 16 by omega]; exact gs5)
    (by rw [Memory.readN_congr (fun j hj => hfr4 _ (by omega) (by omega) (by omega)), show A - 56 + 32 = A - 24 by omega]; exact gs6)
    (by decide) jte_502 bs_21817
    (fun a h1 h2 => by rw [krd, grd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
  have two : (4294967296 : Nat) = two32 := rfl
  generalize hμ5 : μ4.writeN A (Num.encodeLE 8 18446744073709551615) = μ5 at run5
  have w5 : ∀ a, a < 4294967296 → (a < A ∨ A + 8 ≤ a) → μ5.read a = μ4.read a := fun a h1 h2 => by
    rw [← hμ5]; exact Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have hfar : ∀ a, a < 4294967296 → (a < A - 144 ∨ A + 8 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h1 h2 => (w5 a h0 (by omega)).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have rd5 : ∀ a, μ5.readable a = μ.readable a := fun a => by rw [← hμ5, Memory.readable_writeN, krd, grd]
  have wr5 : ∀ a, μ5.writable a = μ.writable a := fun a => by rw [← hμ5, Memory.writable_writeN, kwr, gwr]
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, nO, nO8, -, -, nfr, nrd, nwr⟩ :=
    k2 (p := p) (P := P) (R := R) x ω5 μ5 A O 18446744073709551615 (rdN μ5 (A + 8) 8) (rdN μ5 (A + 16) 8)
      ret t v5 v6 ⟨by omega, by omega⟩ hO32 (by omega) (by rw [m1]; congr 1; omega) (by rw [m5]) (by decide)
      (by decide) (rdN_lt64 _ _) (rdN_lt64 _ _) F.hv5 F.hv6
      (by rw [← hμ5]; exact Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32]))
      (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt (fun a h1 h2 => by rw [rd5]; exact F.hr a h1 h2)
      (fun a h1 h2 => by rw [wr5]; exact hwO a h1 h2)
  refine ⟨ω6, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    n0, n1, n5, n6, nO, nO8, ?_, ?_, ?_, fun a => by rw [nrd, rd5], fun a => by rw [nwr, wr5]⟩
  · rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega)).trans (w5 _ (by omega) (by omega)))]; exact kR0
  · rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega)).trans (w5 _ (by omega) (by omega)))]; exact kR8
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact hfar a h0 h1 h2

/-- **`LookedUp { data: Some [] }`**: from 20626, with tag 18 read without error and the reader
    `{ptr, len}` at rd (ω₆) holding the octets 1 (`Some`) and 0 (ℰ(0), the length) next,
    `Instruction::decode` returns `LookedUp { data: Some [] }` in its slot O: the discriminant word
    2^63 + 17 at O and the empty `Vec` `{cap 0, ptr 1, len 0}` at O + 8. Nothing is allocated. The
    reader is advanced by 2. Memory changes only in A − 184 … A + 24 (the frames of the callees), the
    reader and O … O + 32. -/
theorem looked_up_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 184 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 18) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 33 < 4294967296)
    (hlen : 2 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (hzero : μ.read (ptr + 1) = 0)
    (hrdA : rd + 16 ≤ A - 184 ∨ A + 56 ≤ rd) (hpA : ptr + 33 ≤ A - 184 ∨ A + 56 ≤ ptr)
    (hpr : ptr + 33 ≤ rd ∨ rd + 16 ≤ ptr)
    (hOA : O + 32 ≤ A - 184 ∨ A + 56 ≤ O) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O) (hO32 : O + 32 ≤ 4294967296)
    (hws : ∀ a, A - 184 ≤ a → a < A + 24 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 2 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 700 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775825 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 1 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 0 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 2) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 2) ∧
      (∀ a, a < 4294967296 → (a < A - 184 ∨ A + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 18 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, run2, f0, f1, f5, f6, f7, f8⟩ := k1 (p := p) (P := P) (R := R) x ω1 μ
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    o1 (p := p) (P := P) (R := R) x ω2 μ A A rd 1006 O rd ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [f0])
      (by rw [f1, e1, F.h1]) (by rw [f5, e5, F.h5]) (by rw [f6, e6, h6]) (by rw [f7, e1, F.h1])
      (by rw [f8, e6, h6]) (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 1682 35970 (A - 56) rd (A - 25) ptr len 1 g0 g1 g7 g8 g9
      (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨hptr.1, by omega⟩
      (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (A - 56 + 31) = 1 := by
    rw [show A - 56 + 31 = A - 25 by omega, read_of_readN1 kbuf, ← hsome]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := o_some (p := p) (P := P) (R := R) x ω4 μ4 (A - 56)
    ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := by simp [Blob.encodeNat]
  have hz4 : μ4.read (ptr + 1) = 0 := by
    rw [kfr _ (by omega) (by omega) (by omega) (by omega), gfr _ (by omega) (by omega)]; exact hzero
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω5 μ4 1684 35994 (A - 56) rd (ptr + 1) (len - 1) m0
      (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_841 bs_35994 ⟨by omega, by omega⟩ hrd
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact hwr a h1 h2) kR0 kR8 0 (by decide)
      (by rw [he]; simp; omega)
      (fun a h1 h2 => by rw [he] at h2; simp at h2; rw [krd, grd]; exact hrp a (by omega) (by omega))
      (by rw [he]; simp [Memory.readN, hz4])
  rw [he] at dR0 dR8
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := o_len (p := p) (P := P) (R := R) x ω6 μ6 (A - 56) 0
    (by omega) (by decide) (by rw [d1, m1, k1', g1]) d7 d8
  have hv6 : ω7[6] = UInt64.ofNat rd := by rw [o6, d6, m6, k6, g6]
  obtain ⟨ω8, μ8, run8, v0, v1, v5', v6', vc, vp, vl, vfr, vrd, vwr⟩ :=
    Services.Bootstrap.Decode.VecU8.vec_u8_empty (p := p) (P := P) (R := R) x ω7 μ6 (A - 56) (A - 56) rd
      (len - 1 - 1) 1686 36016 A rd ⟨by omega, by omega⟩ o0 (by rw [o1', d1, m1, k1', g1])
      (by rw [o5, d5, m5, k5, g5]) hv6 o7 (by rw [o8, d6, m6, k6, g6]) o9 (by omega) (by omega) (by decide) jte_842
      bs_36016 (by omega) (Or.inr (Nat.le_refl _)) hrd.2 (by omega) (rd8 (by omega) dR8)
      (fun a h1 h2 => by rw [drd, krd, grd]; exact Memory.readable_of_writable (hwr a (by omega) h2))
      (fun a h1 h2 => by rw [dwr, kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [dwr, kwr, gwr]; exact hws a (by omega) (by omega))
  have hfrA : ∀ a, A - 32 ≤ a → a < A + 56 → a ≠ A - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    o_copy (p := p) (P := P) (R := R) x ω8 μ8 (A - 56) A 0 1 0 1006 21817 O rd ⟨by omega, by omega⟩
      (by omega) (by omega) v1 v5' (by decide) (by decide) (by decide) hO64 (by omega)
      vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrA _ (by omega) (by omega) (by omega)), show A - 56 + 48 = A - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfrA _ (by omega) (by omega) (by omega)), show A - 56 + 40 = A - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfrA _ (by omega) (by omega) (by omega)), show A - 56 + 32 = A - 24 by omega]; exact gs6)
      (by decide) jte_502 bs_21817
      (fun a h1 h2 => by rw [vrd, drd, krd, grd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [vwr, dwr, kwr, gwr]; exact hws a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → (a < A - 184 ∨ A + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ9.read a = μ.read a :=
    fun a h0 h1 h2 => (cfr a h0 (by omega)).trans ((vfr a h0 (by omega) (by omega)).trans
      ((dfr a h0 (by omega) h2).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))))
  have rd9 : ∀ a, μ9.readable a = μ.readable a := fun a => by rw [crd, vrd, drd, krd, grd]
  have wr9 : ∀ a, μ9.writable a = μ.writable a := fun a => by rw [cwr, vwr, dwr, kwr, gwr]
  obtain ⟨ω10, μ10, run10, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    k2 (p := p) (P := P) (R := R) x ω9 μ9 A O 0 1 0 ret t v5 v6 ⟨by omega, by omega⟩ hO32 (by omega)
      (by rw [c1]; congr 1; omega) c5 (by decide) (by decide) (by decide) (by decide) F.hv5 F.hv6 cO cO8 cO16
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt (fun a h1 h2 => by rw [rd9]; exact F.hr a h1 h2)
      (fun a h1 h2 => by rw [wr9]; exact hwO a h1 h2)
  have hrd9 : ∀ j, j < 16 → μ10.read (rd + j) = μ6.read (rd + j) := fun j hj =>
    (nfr _ (by omega) (by omega)).trans ((cfr _ (by omega) (by omega)).trans (vfr _ (by omega) (by omega) (by omega)))
  refine ⟨ω10, μ10, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans run10))))))))).mono (by omega),
    n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_, fun a => by rw [nrd, rd9], fun a => by rw [nwr, wr9]⟩
  · rw [show ptr + 2 = ptr + 1 + 1 by omega, Memory.readN_congr (a := rd) (n := 8) (fun j hj => hrd9 j (by omega))]; exact dR0
  · have e8 : μ10.readN (rd + 8) 8 = μ6.readN (rd + 8) 8 :=
      Memory.readN_congr (fun j hj => by rw [Nat.add_assoc]; exact hrd9 (8 + j) (by omega))
    rw [show len - 2 = len - 1 - 1 by omega, e8]; exact dR8
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact hfar a h0 h1 h2

end Services.Bootstrap.Decode.LookedUp
