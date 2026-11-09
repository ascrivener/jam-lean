import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.CodeX

/-!
# `read_vec` beyond one chunk: the steps of its loop

`read_vec` (3473) reads n octets in chunks: the first of min(n, 16384) octets, each later one of
min(left, len) octets, len the octets read so far, so the buffer doubles. Before each chunk it grows
the buffer to exactly len + chunk with `finish_grow` (32989): through `alloc` for the first, through
`realloc` (40701) for the others. This file proves the steps of a pass of the loop at 3520 and its
exits, from any chunk. Some of these addresses are in the further code facts (`HasCodeX`).
-/

namespace Services.Bootstrap.Decode.VecU8

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem rd8'' {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- 3473 … 3595, any n ≥ 1: `read_vec` opens its frame at S = sp − 96 as in `v1` and calls `finish_grow`
    for the first chunk c = min(n, 16384): ω₆ = ω₁₀ = c (the new capacity), n left at S + 32, the chunk
    at S. -/
theorem v1g {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd n len ret v5 v6 : Nat) (hsp : 65536 + 96 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hret : ret < 18446744073709551616) (hv5 : v5 < 18446744073709551616)
    (hv6 : v6 < 18446744073709551616) (hO : O < 18446744073709551616)
    (hn : 1 ≤ n) (hnl : n ≤ len) (hlen : len < 4294967296)
    (hrd : rd + 16 < 4294967296) (hrdf : rd + 16 ≤ sp - 96 ∨ sp ≤ rd) (rl : rdN μ (rd + 8) 8 = len)
    (hrr : ∀ a, rd + 8 ≤ a → a < rd + 16 → μ.readable a = true)
    (hw : ∀ a, sp - 96 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3473 ω μ x 32989 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 88 ∧ ω'[1] = UInt64.ofNat (sp - 96) ∧ ω'[5] = UInt64.ofNat 0 ∧
      ω'[6] = UInt64.ofNat (min n 16384) ∧ ω'[7] = UInt64.ofNat (sp - 48) ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat (min n 16384) ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 1 ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ret ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (sp - 80) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (sp - 88) 8 = Num.encodeLE 8 O ∧ μ'.readN (sp - 64) 8 = Num.encodeLE 8 n ∧
      μ'.readN (sp - 96) 8 = Num.encodeLE 8 (min n 16384) ∧
      (∀ a, a < 4294967296 → (a < sp - 96 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 96 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hmin : min n 16384 = if n ≤ 16384 then n else 16384 := by split <;> omega
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
    all_goals try (congr 1; omega)

/-- 3520 … 3595, the loop's head with L ≥ 1 octets read into a buffer of capacity L and `left` ≥ 1 to
    go (ω₅ = ω₇ = ω₈ = L, ω₁₀ = left): the chunk c = min(left, L) does not fit, so `read_vec` stores
    `left` at S + 32 and c at S and calls `finish_grow` for the capacity L + c (ω₆ = ω₁₀ = L + c, the old
    capacity ω₈ = L, the old buffer ω₉ from S + 24, its result slot ω₇ = S + 48). -/
theorem lh {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (S L left q : Nat) (hS : 65536 ≤ S ∧ S + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h7 : ω[7] = UInt64.ofNat L)
    (h8 : ω[8] = UInt64.ofNat L) (h10 : ω[10] = UInt64.ofNat left)
    (hL : 1 ≤ L ∧ L < 4294967296) (hl : 1 ≤ left ∧ left < 4294967296) (hq : q < 18446744073709551616)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 q)
    (hw : ∀ a, S ≤ a → a < S + 96 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3520 ω μ x 32989 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 88 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat L ∧
      ω'[6] = UInt64.ofNat (L + min left L) ∧ ω'[7] = UInt64.ofNat (S + 48) ∧ ω'[8] = UInt64.ofNat L ∧
      ω'[9] = UInt64.ofNat q ∧ ω'[10] = UInt64.ofNat (L + min left L) ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 1 ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 left ∧ μ'.readN S 8 = Num.encodeLE 8 (min left L) ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 96 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r24 := rd8'' hq s24
  have hpos : 0 < (if left ≤ L then left else L) % 18446744073709551616 := by split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, h8, h10, hS, hw, hr, hL, hl, r24, Nat.sub_self, hpos, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; split <;> omega)
    all_goals try (congr 1; omega)

/-- 32989 … 33049: `finish_grow` with an old buffer q of capacity L ≥ 1 (ω₈ = L, ω₉ = q) and the new
    capacity N ≥ 1 (ω₁₀), one-octet elements at alignment 1: it opens its frame at F = ω₁ − 40 (its
    return address, ω₅, ω₆ at F + 32, F + 24, F + 16, the alignment 1 at F and N at F + 8), keeps its
    result slot in ω₆ and calls `realloc` (40701) for q from L to N octets at alignment 1 (ω₇ = q,
    ω₈ = L, ω₉ = 1, ω₁₀ = N, return address 1524). -/
theorem g3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F res L q N r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat L)
    (h9 : ω[9] = UInt64.ofNat q) (h10 : ω[10] = UInt64.ofNat N) (h11 : ω[11] = UInt64.ofNat 1)
    (h12 : ω[12] = UInt64.ofNat 1)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hL : 1 ≤ L ∧ L < 4294967296) (hN : 1 ≤ N ∧ N < 4294967296)
    (hq : q < 18446744073709551616)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40701 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1524 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[8] = UInt64.ofNat L ∧ ω'[9] = UInt64.ofNat 1 ∧ ω'[10] = UInt64.ofNat N ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 N ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, hF, hw, hr, hL, hN, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show F + 40 - 40 = F by omega]); post_simp
    all_goals try (congr 1; omega)

/-- 40821: `realloc`'s return, to `finish_grow` (return address 1524, the jump-table entry 33055). -/
theorem realloc_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1524) : FreeStepsH p R 40821 ω μ x 33055 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- 33055 … 33150: `realloc` returned a block q ≠ 0: as `g2` from 33090, `finish_grow` stores `Ok` (0),
    q and the size N (from F + 8) at its result slot and returns. -/
theorem g2r {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
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
    ∃ ω' μ', FreeStepsH p R 33055 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (F + 40) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN res 8 = Num.encodeLE 8 0 ∧ μ'.readN (res + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (res + 16) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < res ∨ res + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0' := rd8'' (by omega) s0
  have r5 := rd8'' hv5 s5
  have r6 := rd8'' hv6 s6
  have r8 := rd8'' hn s8
  have hq0 : ¬ (UInt64.ofNat q).toNat = 0 := by rw [UInt64.toNat_ofNat_of_lt' hq.2]; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hq0, hF, hres, hfr, hw, hr, r0', r5, r6, r8, hret, hjt, hbt, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show 16 + res = res + 16 by omega]); post_simp

/-- 3600 … 3629, any L octets read so far (ω₅ = L): `finish_grow` returned `Ok` with the buffer q (at
    S + 56): `read_vec` keeps q (at S + 24) and the new capacity ω₆ (at S + 40), and calls the reader for
    the chunk c (from S) into q + L (return address 90). -/
theorem v2g {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S rd q N L c : Nat) (hS : 65536 ≤ S ∧ S + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h6 : ω[6] = UInt64.ofNat N)
    (hq : q + L < 18446744073709551616) (hN : N < 18446744073709551616) (hc : c < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 0) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 c) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 96 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3600 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 90 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat L ∧
      ω'[6] = UInt64.ofNat c ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (q + L) ∧
      ω'[9] = UInt64.ofNat c ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 q ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 N ∧
      (∀ a, a < 4294967296 → (a < S + 24 ∨ S + 32 ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r48 := rd8'' (by omega) s48
  have r56 := rd8'' (by omega) s56
  have r0 := rd8'' hc s0
  have r16 := rd8'' hrd s16
  have hr : ∀ a, S ≤ a → a < S + 96 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r48, r56, r0, r16, rdN_writeN_disjoint, rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

/-- 3635 … 3570, the loop's back edge: the read of the chunk c succeeded (ω₇ = 0) after L octets
    (ω₅ = L), and more than c were left (S + 32 holds left > c): `read_vec` goes back to 3520 with
    ω₅ = ω₇ = L + c, the capacity ω₈ (from S + 40) and left − c in ω₁₀. Memory is unchanged. -/
theorem v5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S L c left N : Nat) (hS : 65536 ≤ S ∧ S + 96 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h6 : ω[6] = UInt64.ofNat c)
    (h7 : ω[7] = UInt64.ofNat 0) (hc : c < left ∧ left < 4294967296) (hL : L + c < 4294967296)
    (hN : N < 18446744073709551616)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 left) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 N)
    (hr : ∀ a, S ≤ a → a < S + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 3635 ω μ x 3520 ω' μ x 10 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (L + c) ∧ ω'[7] = UInt64.ofNat (L + c) ∧
      ω'[8] = UInt64.ofNat N ∧ ω'[10] = UInt64.ofNat (left - c) ∧ ω'[0] = ω[0] := by
  have r32 := rd8'' (by omega) s32
  have r40 := rd8'' hN s40
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, hS, hr, r32, r40, hc, hL, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; omega)

/-- 3635 … 3713, the loop's exit: the read of the last chunk c succeeded (ω₇ = 0) after L octets
    (ω₅ = L, S + 32 holds c): `read_vec` stores the `Vec` `{cap N (S + 40), ptr q (S + 24), len L + c}`
    at O (from S + 8), restores ω₀, ω₅, ω₆ and returns. -/
theorem v3g {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O q N L c ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 96 < 4294967296)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ S ∨ S + 96 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L) (h6 : ω[6] = UInt64.ofNat c)
    (h7 : ω[7] = UInt64.ofNat 0) (hq : q < 18446744073709551616) (hN : N < 18446744073709551616)
    (hc : c < 4294967296) (hL : L + c < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 c) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 N)
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
      μ'.readN O 8 = Num.encodeLE 8 N ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (L + c) ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r32 := rd8'' (by omega) s32
  have r40 := rd8'' hN s40
  have r24 := rd8'' hq s24
  have r8 := rd8'' (by omega) s8
  have r88 := rd8'' (by omega) s88
  have r80 := rd8'' hv5 s80
  have r72 := rd8'' hv6 s72
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hS, hO, hOS, hw, hr, r32, r40, r24, r8, r88, r80, r72, hret, hjt, hbt, hc, hL,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try (congr 1; omega)

end Services.Bootstrap.Decode.VecU8
