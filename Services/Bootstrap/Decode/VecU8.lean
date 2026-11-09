import Services.Bootstrap.Decode.Tag
import Services.Bootstrap.ReaderBig

/-!
# Reading n octets into a fresh `Vec<u8>`

The function at 3473 (`jam-codec`'s `read_vec` for `u8`, as `Vec<u8>::decode` and
`Option<Vec<u8>>::decode` use it once the length n is known) takes ω₇ = O, the 24-octet slot for
the result, ω₈ = rd, the reader `{ptr, len}`, and ω₉ = n. If n > len it stores the error word
2^64 − 1 at O. Otherwise it reads the n octets in chunks of at most 16384: before each chunk it
grows the buffer to exactly the octets so far plus the chunk (`finish_grow`, 32989, through the
allocator's `alloc` or `realloc`), then reads the chunk with the reader (58434). It stores the
`Vec` `{cap, ptr, len}` at O.

This file proves the case n = 0 (`vec_u8_empty`), and the steps of the case 1 ≤ n ≤ 16384 (one
chunk, one call of `alloc`): `v1`, `g1`, `g2`, `v2`, `v3`. `Services.Bootstrap.Decode.AllocOk` has the
call of `alloc` itself.
-/

namespace Services.Bootstrap.Decode.VecU8

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

/-- 3473 … 3595: with 1 ≤ n ≤ 16384 octets asked and at least n left in the reader, `read_vec`
    opens a 96-octet frame at S = sp − 96 (the return address, ω₅, ω₆ at S + 88, S + 80, S + 72, the
    reader at S + 16, O at S + 8, the dangling pointer 1 at S + 24, n left at S + 32 and the chunk n
    at S), finds the empty buffer too small and calls `finish_grow` (32989) for a capacity of n:
    ω₇ = S + 48 (its result), ω₈ = 0 (the old capacity), ω₉ = 1 (the old pointer), ω₁₀ = n,
    alignment and element size 1 (ω₁₁, ω₁₂), return address 88. -/
theorem v1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd n len ret v5 v6 : Nat) (hsp : 65536 + 96 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hret : ret < 18446744073709551616) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616) (hO : O < 18446744073709551616)
    (hn : 1 ≤ n ∧ n ≤ 16384) (hnl : n ≤ len) (hlen : len < 18446744073709551616)
    (hrd : rd + 16 < 4294967296) (hrdf : rd + 16 ≤ sp - 96 ∨ sp ≤ rd) (rl : rdN μ (rd + 8) 8 = len)
    (hrr : ∀ a, rd + 8 ≤ a → a < rd + 16 → μ.readable a = true)
    (hw : ∀ a, sp - 96 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3473 ω μ x 32989 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 88 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat 0 ∧
      ω'[6] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat (sp - 48) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat n ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (sp - 80) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (sp - 88) 8 = Num.encodeLE 8 O ∧ μ'.readN (sp - 64) 8 = Num.encodeLE 8 n ∧
      μ'.readN (sp - 96) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < sp - 96 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 96 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hrr, rl, hn, hnl, hrd, hrdf, rdN_writeN_disjoint,
      rdN_writeN_same8, rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show sp - 96 + 88 = sp - 8 by omega, show sp - 96 + 80 = sp - 16 by omega,
      show sp - 96 + 72 = sp - 24 by omega, show sp - 96 + 16 = sp - 80 by omega,
      show sp - 96 + 8 = sp - 88 by omega, show sp - 96 + 32 = sp - 64 by omega,
      show sp - 96 + 24 = sp - 72 by omega, show sp - 96 + 48 = sp - 48 by omega]); post_simp
    all_goals try decide

/-- 32989 … 33084: `finish_grow` with no old buffer (ω₈ = 0) and ω₁₀ = n ≥ 1 elements of one
    octet at alignment 1: it opens a 40-octet frame at F = ω₁ − 40 (its return address, ω₅, ω₆ at
    F + 32, F + 24, F + 16, the alignment 1 at F and the size n at F + 8), keeps its result slot in ω₆
    and calls `alloc` (40494) for n octets at alignment 1 (ω₇ = n, ω₈ = 1, return address 1526). -/
theorem g1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat 1) (h12 : ω[12] = UInt64.ofNat 1)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hn : 1 ≤ n ∧ n < 4294967296)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40494 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1526 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat n ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h10, h11, h12, hF, hw, hr, hn, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    rotate_left 4
    · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', rdN, PVM.Memory.readN_writeN_same, List.length_cons, List.length_nil, PVM.two32]
      decide
    post_simp
    all_goals (try simp only [show F + 40 - 40 = F by omega]); post_simp

/-- 33090 … 33150: `alloc` returned a block q ≠ 0: `finish_grow` stores `Ok` (0) at its result slot
    `res` (ω₆), q at res + 8 and the size n (from F + 8) at res + 16, restores ω₀, ω₅, ω₆ from its frame
    and returns to the address saved at F + 32. -/
theorem g2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n q r0 t v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (hres : res + 24 ≤ 4294967296) (hfr : res + 24 ≤ F ∨ F + 40 ≤ res)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat res) (h7 : ω[7] = UInt64.ofNat q)
    (hq : 0 < q ∧ q < 18446744073709551616) (hn : n < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN (F + 32) 8 = Num.encodeLE 8 r0) (s5 : μ.readN (F + 24) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (F + 16) 8 = Num.encodeLE 8 v6) (s8 : μ.readN (F + 8) 8 = Num.encodeLE 8 n)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true)
    (hw : ∀ a, res ≤ a → a < res + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 33090 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (F + 40) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN res 8 = Num.encodeLE 8 0 ∧ μ'.readN (res + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (res + 16) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < res ∨ res + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r0' := rd _ r0 (by omega) s0
  have r5 := rd _ v5 hv5 s5
  have r6 := rd _ v6 hv6 s6
  have r8 := rd _ n hn s8
  have hq0 : ¬ (UInt64.ofNat q).toNat = 0 := by rw [UInt64.toNat_ofNat_of_lt' hq.2]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hq0, hF, hres, hfr, hw, hr, r0', r5, r6, r8, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show 16 + res = res + 16 by omega]; post_simp)

/-- 3600 … 3629: `finish_grow` returned `Ok` (0 at S + 48) with the block q at S + 56: `read_vec`
    takes q as its buffer (at S + 24) and the capacity ω₆ = n (at S + 40), and calls the reader (ω₇,
    from S + 16) for the chunk n (from S) into q + ω₅ (return address 90). -/
theorem v2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S rd q n : Nat) (hS : 65536 ≤ S ∧ S + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat n)
    (hq : q < 18446744073709551616) (hn : n < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 0) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 n) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 96 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3600 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 90 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat 0 ∧
      ω'[6] = UInt64.ofNat n ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat q ∧
      ω'[9] = UInt64.ofNat n ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 q ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < S + 24 ∨ S + 32 ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd' : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r48 := rd' _ 0 (by omega) s48
  have r56 := rd' _ q hq s56
  have r0 := rd' _ n hn s0
  have r16 := rd' _ rd hrd s16
  have hr : ∀ a, S ≤ a → a < S + 96 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r48, r56, r0, r16, rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption

/-- 3635 … 3713: the read succeeded (ω₇ = 0) and nothing is left (S + 32 holds the chunk n): `read_vec`
    stores the `Vec` `{cap n (S + 40), ptr q (S + 24), len n}` at O (from S + 8), restores ω₀, ω₅, ω₆
    from S + 88, S + 80, S + 72 and returns. -/
theorem v3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O q n ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 96 < 4294967296)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ S ∨ S + 96 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 0) (h6 : ω[6] = UInt64.ofNat n)
    (h7 : ω[7] = UInt64.ofNat 0) (hq : q < 18446744073709551616) (hn : n < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 n) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 O)
    (s88 : μ.readN (S + 88) 8 = Num.encodeLE 8 ret) (s80 : μ.readN (S + 80) 8 = Num.encodeLE 8 v5)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S ≤ a → a < S + 96 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3635 ω μ x t ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd' : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r32 := rd' _ n hn s32
  have r40 := rd' _ n hn s40
  have r24 := rd' _ q hq s24
  have r8 := rd' _ O (by omega) s8
  have r88 := rd' _ ret (by omega) s88
  have r80 := rd' _ v5 hv5 s80
  have r72 := rd' _ v6 hv6 s72
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hS, hO, hOS, hw, hr, r32, r40, r24, r8, r88, r80, r72, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- **The empty `Vec<u8>`** (3473, n = 0): `read_vec` reads nothing and allocates nothing; it stores
    `{cap 0, ptr 1, len 0}` (the dangling pointer 1) at O, restores ω₀, ω₅, ω₆ and returns. -/
theorem vec_u8_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd len ret t v5 v6 : Nat) (hsp : 65536 + 96 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat 0) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ sp - 96 ∨ sp ≤ O)
    (hrd : rd + 16 < 4294967296) (hrdf : rd + 16 ≤ sp - 96 ∨ sp ≤ rd) (rl : rdN μ (rd + 8) 8 = len)
    (hrr : ∀ a, rd + 8 ≤ a → a < rd + 16 → μ.readable a = true)
    (hw : ∀ a, sp - 96 ≤ a → a < sp → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3473 ω μ x t ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 96 ∨ sp ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 96 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hwO, hO, hOS, hrr, rl, hrd, hrdf, hret, hjt, hbt,
      rdN_writeN_disjoint, rdN_writeN_same8, rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show sp - 96 + 96 = sp by omega])
    post_simp
    all_goals try decide

end Services.Bootstrap.Decode.VecU8
