import Services.Bootstrap.Decode.VecHash32
import Services.Bootstrap.Decode.VecHashBig

/-!
# `Vec<[u8; 32]>` of more than 512 hashes at 907, the payload in the heap

`vec_hash32_heap_big` is `VecHash32.vec_hash32_heap` (the hash reader at 907,
`RandomStorageAccumulate`'s `Ok` payload) for n > 512 elements: a port of
`VecHash.vec_hash_heap_big` (the reader at 1764). The code at 907 is that at 1764 shifted by −857
(907 … 1159: the frame, the reserve loop 957, the batch end 983, `finish_grow`'s return 1023, the
element loop 1053 … 1125) and −900 (1238 … 1297: the exit), with the jump-table return addresses 28
(after `finish_grow`, jte 13) and 30 (after a read, jte 14) instead of 48 and 50; in particular the
later batches take the same path (983 → 957 → 1001 → `finish_grow`'s `realloc` branch → 1023), with
the bound the length so far (993: ω₁₁ ← ω₇), so the buffer doubles: L ↦ L + min(left, L). Only the
in-batch "buffer full" path differs (1162 calls 50078 where 2019 inlines a grow); it is never taken.

The lemmas are those of `VecHashBig` at the shifted addresses; see there for the invariant.

Either the function returns, or the run reaches a failed allocator call (`LoopA.Exhausts`).

Not stated (unlike `vec_hash32_heap`): the globals below the allocator (`Glob`) are kept;
`realloc_call` does not record it.

GP v0.8.0: the octets are read from the service's memory by the PVM (Appendix A); the
`Vec<[u8; 32]>` is the bootstrap service's own decoding of an argument blob (§B.7: hashes).
-/

namespace Services.Bootstrap.Decode.VecHash32

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 907 … 1018, n > 512 elements asked: as `p1`, the function opens its 152-octet frame at
    S = ω₁ − 152 and, n exceeding the first batch's bound 512, calls `finish_grow` for the first batch
    c = min(n, 512) = 512 elements of 32 octets (ω₁₀ = 512, alignment 1, element size 32, result slot
    S + 96, return address 28), with n at S + 24 and ω₅, 512 at S, S + 16 and in ω₆. -/
theorem p1b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 152)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : 512 < n ∧ n < 4294967296)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 907 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 28 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (S + 96) ∧
      ω'[8] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 512 ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 32 ∧
      μ'.readN (S + 144) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (S + 136) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (S + 128) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 out ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat 512 ∧
      μ'.readN S 8 = Num.encodeLE 8 512 ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 512 ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 152 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hn' : ¬ n ≤ 512 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hn, hn', VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp

/-- 1023 … 1119, as `p5` for any batch: `finish_grow` returned `Ok` (0 at S + 96) with the block q
    (S + 104), the new capacity N at S and the bound M ≠ 0 at S + 16: the function records the `Vec`
    capacity N (S + 40) and pointer q (S + 48), the batch c (ω₆) at S + 16, zeroes S + 96 … S + 128 and
    calls the reader for 32 octets into S + 96 (return address 30). -/
theorem p5b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S c N M q rd : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat c)
    (hc : c < 18446744073709551616) (hN : N < 18446744073709551616)
    (hM : 0 < M ∧ M < 18446744073709551616) (hq : q < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (s96 : μ.readN (S + 96) 8 = Num.encodeLE 8 0) (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 N) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 M)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1023 ω μ x 58434 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 30 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat c ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 96) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 N ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < S + 16 ∨ S + 24 ≤ a) → (a < S + 40 ∨ S + 56 ≤ a) →
        (a < S + 96 ∨ S + 128 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r96 := rd8' (by decide) s96
  have r104 := rd8' hq s104
  have r0 := rd8' hN s0
  have r16 := rd8' hM.2 s16
  have r32 := rd8' hrd s32
  have hM0 : ¬ M = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, hw, hr, r96, r104, r0, r16, r32, hM0, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption

/-- `i1` without the bound n ≤ 512 (1125 … 1159, 1053 … 1119): a read of 32 octets into S + 96
    succeeded, the `Vec` {n, q, j} has room (j < n) and c ≥ 2 elements of the batch are left (ω₆): the
    element is copied to q + 32·j, the length becomes j + 1 and the reader is called again. -/
theorem i1b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j c rd : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat c) (h7 : ω[7] = UInt64.ofNat 0)
    (hjn : j < n) (hc : 2 ≤ c ∧ c < 4294967296) (hq : q + 32 * n < 4294967296)
    (hqS : q + 32 * n ≤ S ∨ S + 152 ≤ q) (hrd : rd < 18446744073709551616)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwq : ∀ a, q + 32 * j ≤ a → a < q + 32 * j + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1125 ω μ x 58434 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 30 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (c - 1) ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 96) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (q + 32 * j) 32 = μ.readN (S + 96) 32 ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 (j + 1) ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 64 ≤ a) → (a < S + 64 ∨ S + 128 ≤ a) →
        (a < q + 32 * j ∨ q + 32 * j + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r40 := rd8' (by omega) s40
  have r48 := rd8' (by omega) s48
  have r56 := rd8' (by omega) s56
  have r32 := rd8' hrd s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hS, hw, hr, hwq, hjn, hc, hq, hqS, r40, r48, r56, r32, VecU8.rdN_writeN_same8,
      VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact h1
    all_goals (rw [show q + 32 * j = j * 32 + q by omega, show S + 104 = S + 96 + 8 by omega, show S + 112 = S + 96 + 16 by omega,
      show S + 120 = S + 96 + 24 by omega]; exact HashU64.copy4g _ _ (S + 96) (j * 32 + q) (by omega))

/-- 1125 … 1159, 1053 … 1094: the read of the batch's last element (ω₆ = 1) succeeded: it is copied
    to q + 32·j, the length becomes j + 1 (S + 56 and ω₇) and the function reaches its batch end
    (983) with ω₉ = q. -/
theorem ieb {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat 1) (h7 : ω[7] = UInt64.ofNat 0)
    (hjn : j < n) (hq : q + 32 * n < 4294967296)
    (hqS : q + 32 * n ≤ S ∨ S + 152 ≤ q)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwq : ∀ a, q + 32 * j ≤ a → a < q + 32 * j + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1125 ω μ x 983 ω' μ' x 40 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (j + 1) ∧ ω'[9] = UInt64.ofNat q ∧
      μ'.readN (q + 32 * j) 32 = μ.readN (S + 96) 32 ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 (j + 1) ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 64 ≤ a) → (a < S + 64 ∨ S + 128 ≤ a) →
        (a < q + 32 * j ∨ q + 32 * j + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r40 := rd8' (by omega) s40
  have r48 := rd8' (by omega) s48
  have r56 := rd8' (by omega) s56
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hS, hw, hr, hwq, hjn, hq, hqS, r40, r48, r56, VecU8.rdN_writeN_same8,
      VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact h1
    all_goals (rw [show q + 32 * j = j * 32 + q by omega, show S + 104 = S + 96 + 8 by omega, show S + 112 = S + 96 + 16 by omega,
      show S + 120 = S + 96 + 24 by omega]; exact HashU64.copy4g _ _ (S + 96) (j * 32 + q) (by omega))

/-- 983 … 1018, the batch end with more to read: the batch of c elements is read (ω₇ = L, the
    length; S + 24 holds c + left, S + 16 holds c, left ≥ 1) and the buffer is full (S + 40, the
    capacity, holds L): the function goes back to its reserve loop (957) with the bound L (ω₁₁ ← ω₇)
    and calls `finish_grow` for the capacity L + c', c' = min(left, L) (ω₈ = L the old capacity,
    ω₉ = q the old buffer, alignment 1, element size 32, result slot S + 96, return address 28), with
    L + c' at S, L at S + 16 and left at S + 24. -/
theorem bkb {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q L c left : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L) (h9 : ω[9] = UInt64.ofNat q)
    (hL : 1 ≤ L ∧ L < 4294967296)
    (hl : 1 ≤ left ∧ c + left < 4294967296)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 (c + left)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 983 ω μ x 32989 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 28 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat left ∧
      ω'[6] = UInt64.ofNat (min left L) ∧ ω'[7] = UInt64.ofNat (S + 96) ∧ ω'[8] = UInt64.ofNat L ∧
      ω'[9] = UInt64.ofNat q ∧ ω'[10] = UInt64.ofNat (L + min left L) ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 32 ∧
      μ'.readN S 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 L ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 left ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < S + 16 ∨ S + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r24 := rd8'' (by omega) s24
  have r16 := rd8'' (by omega) s16
  have r40 := rd8'' (by omega) s40
  have hpos : 0 < (if left ≤ L then left else L) % 18446744073709551616 := by split <;> omega
  have hle : c ≤ c + left := Nat.le_add_right c left
  have hne : ¬ c + left - c = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, h9, hS, hw, hr, hL, hl, r24, r16, r40, hle, hne, Nat.sub_self, hpos, Nat.add_sub_cancel_left,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; split <;> omega)
    all_goals try (congr 1; omega)

/-- 983 … 998, 1271 … 1297, 1238 … 1269, every element read (S + 24 and S + 16 both hold the
    last batch c): the function stores the `Vec` {cap, ptr q, len} (from S + 40, S + 48, S + 56) at the
    slot `out` (S + 8), restores ω₀, ω₅, ω₆ and returns. -/
theorem exb {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S c out cap q len ret t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (hc : c < 18446744073709551616)
    (hout : out + 24 ≤ 4294967296) (hoS : out + 24 ≤ S ∨ S + 152 ≤ out)
    (hcap : cap < 4294967296) (hq : q < 4294967296) (hlen : len < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 c) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 cap) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 len) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 out)
    (s144 : μ.readN (S + 144) 8 = Num.encodeLE 8 ret) (s136 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5)
    (s128 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 983 ω μ x t ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN out 8 = Num.encodeLE 8 cap ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S + 96 ∨ S + 112 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r24 := rd8' hc s24
  have r16 := rd8' hc s16
  have r40 := rd8' (by omega) s40
  have r48 := rd8' (by omega) s48
  have r56 := rd8' (by omega) s56
  have r8 := rd8' (by omega) s8
  have r144 := rd8' (by omega) s144
  have r136 := rd8' hv5 s136
  have r128 := rd8' hv6 s128
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hout, hoS, hw, hr, hwo, r24, r16, r40, r48, r56, r8, r144, r136, r128, hcap, hq, hlen,
      hret, hjt, hbt, Nat.sub_self, rdN_writeN_disjoint, VecU8.rdN_writeN_same8, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide

/-- **One element of a batch** (58434 … 58434, or 983 after the batch's last element): with k < N
    elements in q (S + 48; capacity N at S + 40, length k at S + 56), r = N − k left in the batch (ω₆)
    and the reader rd (S + 32) at ptr₀ + 32k, the reader reads the next 32 octets into S + 96 and the
    function copies them to q + 32k. The payload and the buffer lie below the frames. -/
theorem passb {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q N k r rd ptr0 len0 : Nat) (hS : 65536 + 88 ≤ S ∧ S + 152 < 4294967296 ∧ S % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat 30) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r)
    (h7 : ω[7] = UInt64.ofNat rd) (h8 : ω[8] = UInt64.ofNat (S + 96)) (h9 : ω[9] = UInt64.ofNat 32)
    (hr : 1 ≤ r ∧ k + r = N) (hN : N < 4294967296)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 N)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 k)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * k))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * k))
    (hlen : 32 * N ≤ len0 ∧ len0 < 4294967296) (hrd : S + 152 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 32 * N + 64 ≤ S - 88) (hq : 65536 ≤ q ∧ q + 32 * N ≤ S - 88)
    (hpq : q + 32 * N ≤ ptr0 ∨ ptr0 + 32 * N ≤ q)
    (hws : ∀ a, S - 88 ≤ a → a < S + 152 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwq : ∀ a, q ≤ a → a < q + 32 * N → μ.writable a = true)
    (hra : ∀ a, ptr0 ≤ a → a < ptr0 + 32 * N → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x (if r = 1 then 983 else 58434) ω' μ' x 520 ∧
      ω'[1] = UInt64.ofNat S ∧ (r = 1 → ω'[7] = UInt64.ofNat (k + 1) ∧ ω'[9] = UInt64.ofNat q) ∧
      (r ≠ 1 → ω'[0] = UInt64.ofNat 30 ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ ω'[7] = UInt64.ofNat rd ∧
        ω'[8] = UInt64.ofNat (S + 96) ∧ ω'[9] = UInt64.ofNat 32) ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 (k + 1) ∧
      μ'.readN (q + 32 * k) 32 = μ.readN (ptr0 + 32 * k) 32 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * (k + 1)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * (k + 1)) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 56 ∨ S + 128 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        (a < q + 32 * k ∨ q + 32 * k + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ := read_big_sp (p := p) (P := P)
    (R := R) x ω μ 30 1125 S rd (S + 96) (ptr0 + 32 * k) (len0 - 32 * k) 32 h0 h1 h7 h8 h9 (by decide) jte_14
    bs_1125 ⟨by omega, by omega, hS.2.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
    (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    (Or.inr (by omega))
    (fun a h1 h2 => hws a h1 (by omega)) hwr (fun a h1 h2 => hws a (by omega) (by omega))
    (fun a h1 h2 => hra a (by omega) (by omega)) hR0 hR8
  have g' : ∀ a, S ≤ a → a < S + 96 → μ1.read a = μ.read a := fun a h1 h2 =>
    gfr a (by omega) (Or.inr h1) (Or.inl (by omega)) (Or.inl h2)
  have hrdk : μ1.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * (k + 1)) := gR0.trans (congrArg _ (by omega))
  have hrdk8 : μ1.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * (k + 1)) := gR8.trans (congrArg _ (by omega))
  have s40' : μ1.readN (S + 40) 8 = Num.encodeLE 8 N := by
    rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega))]; exact s40
  have s48' : μ1.readN (S + 48) 8 = Num.encodeLE 8 q := by
    rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega))]; exact s48
  have s56' : μ1.readN (S + 56) 8 = Num.encodeLE 8 k := by
    rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega))]; exact s56
  have s32' : μ1.readN (S + 32) 8 = Num.encodeLE 8 rd := by
    rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega))]; exact s32
  have hws1 : ∀ a, S ≤ a → a < S + 152 → μ1.writable a = true := fun a h1 h2 => by rw [gwr]; exact hws a (by omega) h2
  have hwq1 : ∀ a, q + 32 * k ≤ a → a < q + 32 * k + 32 → μ1.writable a = true := fun a h1 h2 => by
    rw [gwr]; exact hwq a (by omega) (by omega)
  have fin : ∀ (ω2 : Regs) (μ2 : Memory) (pc : Nat), FreeStepsH p R 1125 ω1 μ1 x pc ω2 μ2 x 40 →
      ω2[1] = UInt64.ofNat S →
      (r = 1 → ω2[7] = UInt64.ofNat (k + 1) ∧ ω2[9] = UInt64.ofNat q) →
      (r ≠ 1 → ω2[0] = UInt64.ofNat 30 ∧ ω2[6] = UInt64.ofNat (r - 1) ∧ ω2[7] = UInt64.ofNat rd ∧
        ω2[8] = UInt64.ofNat (S + 96) ∧ ω2[9] = UInt64.ofNat 32) →
      μ2.readN (q + 32 * k) 32 = μ1.readN (S + 96) 32 → μ2.readN (S + 56) 8 = Num.encodeLE 8 (k + 1) →
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 64 ≤ a) → (a < S + 64 ∨ S + 128 ≤ a) →
        (a < q + 32 * k ∨ q + 32 * k + 32 ≤ a) → μ2.read a = μ1.read a) →
      (∀ a, μ2.readable a = μ1.readable a) → (∀ a, μ2.writable a = μ1.writable a) →
      ∃ ω' μ', FreeStepsH p R 58434 ω μ x pc ω' μ' x 520 ∧
        ω'[1] = UInt64.ofNat S ∧ (r = 1 → ω'[7] = UInt64.ofNat (k + 1) ∧ ω'[9] = UInt64.ofNat q) ∧
        (r ≠ 1 → ω'[0] = UInt64.ofNat 30 ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ ω'[7] = UInt64.ofNat rd ∧
          ω'[8] = UInt64.ofNat (S + 96) ∧ ω'[9] = UInt64.ofNat 32) ∧
        μ'.readN (S + 56) 8 = Num.encodeLE 8 (k + 1) ∧
        μ'.readN (q + 32 * k) 32 = μ.readN (ptr0 + 32 * k) 32 ∧
        μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * (k + 1)) ∧
        μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * (k + 1)) ∧
        (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 56 ∨ S + 128 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
          (a < q + 32 * k ∨ q + 32 * k + 32 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
    intro ω2 μ2 pc run2 f1 f7 f6 fcp f56 ffr frd fwr
    refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), f1, f7, f6, f56, by rw [fcp, gbuf], ?_, ?_,
      fun a h0 h1 h2 h3 h4 => (ffr a h0 (by omega) (by omega) h4).trans
        (gfr a h0 (by omega) h3 (by omega)),
      fun a => by rw [frd, grd], fun a => by rw [fwr, gwr]⟩
    · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega) (by omega))]; exact hrdk
    · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega) (by omega))]; exact hrdk8
  by_cases hr1 : r = 1
  · subst hr1
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
    obtain ⟨ω2, μ2, run2, f1, f7, f9, fcp, f56, ffr, frd, fwr⟩ := ieb (p := p) (P := P) (R := R) x ω1 μ1
      S N q k ⟨by omega, by omega⟩ (g1.trans h1) (g6.trans h6) g7 (by omega) (by omega) (Or.inl (by omega))
      s40' s48' s56' hws1 hwq1
    exact fin ω2 μ2 983 run2 f1 (fun _ => ⟨f7, f9⟩) (fun h => absurd rfl h) fcp f56 ffr frd fwr
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hr1)]
    obtain ⟨ω2, μ2, run2, f0, f1, f6, f7, f8, f9, fcp, f56, ffr, frd, fwr⟩ := i1b (p := p) (P := P) (R := R) x
      ω1 μ1 S N q k r rd ⟨by omega, by omega⟩ (g1.trans h1) (g6.trans h6) g7 (by omega) ⟨by omega, by omega⟩
      (by omega) (Or.inl (by omega)) (by omega) s40' s48' s56' s32' hws1 hwq1
    exact fin ω2 μ2 58434 run2 f1 (fun h => absurd h hr1) (fun _ => ⟨f0, f6, f7, f8, f9⟩) fcp f56 ffr frd fwr

/-- **A batch's reads** (58434 … 983): from k < N elements in q, r = N − k left, as `passb`, the
    function reads the rest of the batch: q then holds the payload's first 32N octets, the reader is
    advanced to ptr₀ + 32N, and the batch end has ω₇ = N, ω₉ = q. -/
theorem loopb {p : ByteArray} {P : Program} [HasCode p P] (x : X)
    (S q N rd ptr0 len0 : Nat) (hS : 65536 + 88 ≤ S ∧ S + 152 < 4294967296 ∧ S % 8 = 0) (hN : N < 4294967296)
    (hlen : 32 * N ≤ len0 ∧ len0 < 4294967296) (hrd : S + 152 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 32 * N + 64 ≤ S - 88) (hq : 65536 ≤ q ∧ q + 32 * N ≤ S - 88)
    (hpq : q + 32 * N ≤ ptr0 ∨ ptr0 + 32 * N ≤ q) :
    ∀ r k (ω : Regs) (μ : Memory), ω[0] = UInt64.ofNat 30 → ω[1] = UInt64.ofNat S → ω[6] = UInt64.ofNat r →
    ω[7] = UInt64.ofNat rd → ω[8] = UInt64.ofNat (S + 96) → ω[9] = UInt64.ofNat 32 → 1 ≤ r → k + r = N →
    μ.readN (S + 32) 8 = Num.encodeLE 8 rd → μ.readN (S + 40) 8 = Num.encodeLE 8 N →
    μ.readN (S + 48) 8 = Num.encodeLE 8 q → μ.readN (S + 56) 8 = Num.encodeLE 8 k →
    μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * k) → μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * k) →
    μ.readN q (32 * k) = μ.readN ptr0 (32 * k) →
    (∀ a, S - 88 ≤ a → a < S + 152 → μ.writable a = true) →
    (∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) →
    (∀ a, q ≤ a → a < q + 32 * N → μ.writable a = true) →
    (∀ a, ptr0 ≤ a → a < ptr0 + 32 * N → μ.readable a = true) →
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x 983 ω' μ' x (520 * r) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat N ∧ ω'[9] = UInt64.ofNat q ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 N ∧
      μ'.readN q (32 * N) = μ.readN ptr0 (32 * N) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * N) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * N) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 56 ∨ S + 128 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        (a < q + 32 * k ∨ q + 32 * N ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro r
  induction r with
  | zero => intro k ω μ _ _ _ _ _ _ h; exact absurd h (by decide)
  | succ r ih =>
  intro k ω μ h0 h1 h6 h7 h8 h9 hr1 hkr s32 s40 s48 s56 hR0 hR8 hdat hws hwr hwq hra
  obtain ⟨ω1, μ1, run1, a1, a7, a6, a56, adat, aR0, aR8, afr, ard, awr⟩ :=
    passb (p := p) (P := P) (R := R) x ω μ S q N k (r + 1) rd ptr0 len0 hS h0 h1 h6 h7 h8 h9 ⟨hr1, hkr⟩ hN
      s32 s40 s48 s56 hR0 hR8 hlen hrd hptr hq hpq hws hwr hwq hra
  have hpay : ∀ a, ptr0 ≤ a → a < ptr0 + 32 * N → μ1.read a = μ.read a := fun a h1 h2 =>
    afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by rcases hpq with h | h <;> omega)
  have hdat1 : μ1.readN q (32 * (k + 1)) = μ1.readN ptr0 (32 * (k + 1)) := by
    rw [show 32 * (k + 1) = 32 * k + 32 by omega, readN_split, readN_split, adat,
      Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega))), hdat,
      Memory.readN_congr (μ' := μ1) (a := ptr0) (n := 32 * k) (fun j hj => hpay _ (by omega) (by omega)),
      Memory.readN_congr (μ' := μ1) (a := ptr0 + 32 * k) (n := 32) (fun j hj => hpay _ (by omega) (by omega))]
  by_cases hr0 : r = 0
  · subst hr0
    rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at run1
    have hk : k + 1 = N := by omega
    obtain ⟨b7, b9⟩ := a7 rfl
    refine ⟨ω1, μ1, run1.mono (by omega), a1, by rw [b7, hk], b9, by rw [a56, hk], ?_, by rw [aR0, hk],
      by rw [aR8, hk], fun a h0 h1 h2 h3 h4 => afr a h0 h1 h2 h3 (by omega), ard, awr⟩
    rw [← hk, hdat1]
    exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))] at run1
    obtain ⟨b0, b6, b7, b8, b9⟩ := a6 (by omega)
    have kS : ∀ a, S ≤ a → a < S + 56 → μ1.read a = μ.read a := fun a h1 h2 =>
      afr a (by omega) (Or.inr h1) (Or.inl h2) (Or.inl (by omega)) (Or.inr (by omega))
    obtain ⟨ω', μ', run', e1, e7, e9, e56, edat, eR0, eR8, efr, erd, ewr⟩ :=
      ih (k + 1) ω1 μ1 b0 a1 (by rw [b6]; congr 1) b7 b8 b9 (by omega) (by omega)
        (by rw [Memory.readN_congr (fun j hj => kS _ (by omega) (by omega))]; exact s32)
        (by rw [Memory.readN_congr (fun j hj => kS _ (by omega) (by omega))]; exact s40)
        (by rw [Memory.readN_congr (fun j hj => kS _ (by omega) (by omega))]; exact s48)
        a56 aR0 aR8 hdat1
        (fun a h1 h2 => by rw [awr]; exact hws a h1 h2) (fun a h1 h2 => by rw [awr]; exact hwr a h1 h2)
        (fun a h1 h2 => by rw [awr]; exact hwq a h1 h2) (fun a h1 h2 => by rw [ard]; exact hra a h1 h2)
    refine ⟨ω', μ', (run1.trans run').mono (by rw [Nat.mul_succ]; omega), e1, e7, e9, e56, ?_, eR0, eR8,
      fun a h0 h1 h2 h3 h4 => (efr a h0 h1 h2 h3 (by omega)).trans (afr a h0 h1 h2 h3 (by omega)),
      fun a => by rw [erd, ard], fun a => by rw [ewr, awr]⟩
    rw [edat]; exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll in
/-- **One later batch, the payload in the heap** (983 … 983): at the batch end with L ≥ 1 elements
    read (ω₇ = L, ω₉ = q, capacity and length L at S + 40, S + 56; S + 24, S + 16 holding c + left, c)
    and left ≥ 1 to go, q the data of an allocated chunk of ⌈32L/32⌉ + 1 units holding the payload's
    first 32L octets, the payload ptr₀ … ptr₀ + 32(L + left) inside a protected chunk (`K`: allocated,
    not q's): either the model's `realloc` of q to ⌈32(L + c')/32⌉ units (c' = min(left, L)) gives a
    block r and state `s'`, and the function reads the batch's c' elements into r, reaching the batch
    end again with length and capacity L + c', r holding the payload's first 32(L + c') octets and
    being the data of an allocated chunk of ⌈32(L + c')/32⌉ + 1 units, the context kept for `s'`,
    every protected chunk still allocated, not r's, with its data; or the run reaches a failed
    `realloc` (`Exhausts`). -/
theorem batch_heap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop) (S rd q L c left ptr0 len0 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (32 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + 32 * (L + left) ≤ d.addr + 32 * d.size)
    (hS : S0 + 360 ≤ S ∧ S + 152 ≤ S1) (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L) (h9 : ω[9] = UInt64.ofNat q)
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hn : 32 * (L + left) < 1073741760)
    (hlen : 32 * (L + left) ≤ len0 ∧ len0 < 4294967296)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 (c + left)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 L)
    (hrd : S + 152 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * L))
    (hdat : μ.readN q (32 * L) = μ.readN ptr0 (32 * L)) :
    (∃ ω' μ' s' r, FreeStepsH p (refineContractK cap env) 983 ω μ x 983 ω' μ' x
        (64 * ((32 * L + 31) / 32) + 520 * min left L + 1500) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (L + min left L) ∧ ω'[9] = UInt64.ofNat r ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 left ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 (min left L) ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 r ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 (L + min left L) ∧
      (∀ a, a < 4294967296 → (S + 8 ≤ a ∧ a < S + 16 ∨ S + 32 ≤ a ∧ a < S + 40 ∨ S + 128 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * (L + min left L)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * (L + min left L)) ∧
      μ'.readN r (32 * (L + min left L)) = μ.readN ptr0 (32 * (L + min left L)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = r ∧ d.used = true ∧ d.size = (32 * (L + min left L) + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧
        ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 983 ω μ x (64 * ((32 * L + 31) / 32) + 1500) := by
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpm, hcpu, hcpq⟩ := hK cp hcpK
  have hu : usable s q = (32 * L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  obtain ⟨hp0, -, hpT⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  -- the batch end, and finish_grow to realloc
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m0, m16, m24, fr1, rd1, wr1⟩ :=
    bkb (p := p) (P := P) (R := refineContractK cap env) x ω μ S q L c left ⟨by omega, by omega⟩ h1 h7 h9
      ⟨hL, by omega⟩ ⟨hl1, by omega⟩ s24 s16 s40 (fun a h1 h2 => hst a (by omega) (by omega))
  generalize hcdef : min left L = c' at *
  have hc1 : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    VecPairs.g3e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (S - 40) (S + 96) L q (L + c') 1 32 28
      left c' ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by decide)
      (by omega) (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 32 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcqm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (S - 40) q 1 (32 * (L + c')) pb
      S0 S1 H2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (by decide) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', b, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp3, stk3, -, -, e0, e1,
      e5, e6⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr (Exhausts.of_realloc ((run1.trans (run2.trans (run3.trans run4))).mono (by omega)) e7 hR)
  have hR1 : realloc (growTo pb) hb s q 1 ((32 * (L + c') + 31) / 32) = some (r, s', b) := hR
  have hfr := realloc_fresh H.wf ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR1
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨hr0, -, hrT⟩ := chunk_in H3.wf hcrm hcru
  rw [hcrs] at hrT
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have hcp' := keep3 cp hcpm hcpu hcpq
  have hcpr : cp.addr + 32 ≠ r := hfr cp hcpm hcpu hcpq
  have hcpne : cp ≠ cr := fun e => hcpr (by rw [e]; exact hcra)
  have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (S - 40) (S + 96) (32 * (L + c')) r 28 1023
      left c' ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n8)
      (by decide) jte_13 bs_1023
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS51 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 96 ∨ S + 120 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 h3).trans ((stk3 a h2 (by omega)).trans (fr2 a h2 (Or.inr (by omega))))
  have hS1μ : ∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < S + 16 ∨ S + 32 ≤ a) → μ1.read a = μ.read a := fr1
  obtain ⟨ω6, μ6, run6, d0, d1, d6, d7, d8, d9, d40, d48, d16, fr6, rd6, wr6⟩ :=
    p5b (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 S c' (L + c') L r rd ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c6 (by omega) (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)
      cres (by rw [show S + 104 = S + 96 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m0)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m16)
      (by rw [Memory.readN_congr (fun j hj => (hS51 _ (by omega) (by omega) (by omega)).trans
        (hS1μ _ (by omega) (by omega) (by omega)))]; exact s32)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hS60 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 16 ∨ S + 24 ≤ a) → (a < S + 40 ∨ S + 56 ≤ a) →
      (a < S + 96 ∨ S + 128 ≤ a) → μ6.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (fr6 a h2 h3 h4 h5).trans (hS51 a h1 h2 (by omega))
  have hhigh : ∀ a, a < 4294967296 → S + 128 ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (hS60 a (by omega) h0 (by omega) (by omega) (by omega)).trans (fr1 a h0 (by omega) (by omega))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha => by
    have hca := ha
    unfold InData at hca
    rw [h63 a (by omega), kp3 a ⟨cp, hcpm, hcpu, hcpq, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hdq : r + 32 * (L + c') ≤ ptr0 ∨ ptr0 + 32 * (L + c') ≤ r := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' cr hcrm hcpne with h' | h' <;> omega
  -- the batch's reads
  obtain ⟨ω7, μ7, run7, f1, f7, f9, f56, fdat, fR0, fR8, ffr, frd, fwr⟩ :=
    loopb (p := p) (P := P) (R := refineContractK cap env) x S r (L + c') rd ptr0 len0 ⟨by omega, by omega, hsp.2⟩
      (by omega) ⟨by omega, hlen.2⟩ ⟨hrd.1, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hdq c' L ω6 μ6
      d0 d1 d6 d7 d8 d9 hc1.1 rfl
      (by rw [Memory.readN_congr (fun j hj => (hS60 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (hS1μ _ (by omega) (by omega) (by omega)))]; exact s32)
      d40 d48
      (by rw [Memory.readN_congr (fun j hj => (hS60 _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (hS1μ _ (by omega) (by omega) (by omega)))]; exact s56)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (by
        rw [Memory.readN_congr (fun j hj => h63 _ (by omega)), readN_prefix (by omega) dat3,
          Memory.readN_congr (fun j hj => hlow _ (by omega) (Or.inl (by omega))), hdat]
        exact (Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)).symm)
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hcrm hcru ⟨by omega, by rw [hcrs]; omega⟩)
      (fun a h1 h2 => Memory.readable_of_writable
        (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  -- the results
  have h76 : ∀ a, S ≤ a → a < S + 56 → μ7.read a = μ6.read a := fun a h1 h2 =>
    ffr a (by omega) (Or.inr h1) (Or.inl h2) (Or.inl (by omega)) (Or.inr (by omega))
  have hlowh : ∀ a, a < 2147483648 → (a < r + 32 * L ∨ r + 32 * (L + c') ≤ a) → μ7.read a = μ3.read a :=
    fun a h2 h3 => (ffr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) h3).trans (h63 a h2)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [fwr, wr36]
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  refine Or.inl ⟨ω7, μ7, s', r, run17.mono (by omega), f1, f7, f9, ?_, ?_, ?_, ?_, f56, ?_, fR0, fR8, ?_,
    ctx_congr_data H3 hcrm (fun a h1 h2 => hlowh a h1 (by rw [hcrs] at h2; omega)) wr73,
    ⟨cr, hcrm, hcra, hcru, hcrs⟩, ?_⟩
  · rw [Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega)).trans
      (hS60 _ (by omega) (by omega) (by omega) (by omega) (by omega)))]; exact m24
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact d16
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact d40
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact d48
  · intro a h0 h1 h2
    exact (ffr a h0 (Or.inr (by omega)) (by omega) h2 (Or.inr (by omega))).trans
      ((hS60 a (by omega) h0 (by omega) (by omega) (by omega)).trans (fr1 a h0 (by omega) (by omega)))
  · rw [fdat]; exact Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)
  · intro d hd
    obtain ⟨hdm, hdu, hdq'⟩ := hK d hd
    have hdm' := keep3 d hdm hdu hdq'
    have hdr : d.addr + 32 ≠ r := hfr d hdm hdu hdq'
    have hdne : d ≠ cr := fun e => hdr (by rw [e]; exact hcra)
    refine ⟨hdm', hdu, hdr, fun a ha => ?_⟩
    have hdis := data_disj H3.wf hdm' hcrm hdne ha
    rw [hcrs] at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hdm hdu).2.2
    rw [hlowh a (by omega) (by omega), kp3 a ⟨d, hdm, hdu, hdq', ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))

/-- A step bound for the batches from L elements read with `left` to go. -/
def hashSteps (L left : Nat) : Nat := 66 * L + 650 * left + 2000 * (left / L) + 2000

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA in
/-- **The function's later batches, the payload in the heap** (from the batch end 983 to the
    return t): as `batch_heap`, with the frame's slot O (S + 8), ret, v5, v6 (S + 144, S + 136,
    S + 128) and left ≥ 1 to go. Either the function returns to t with the `Vec`
    `{cap L + left, ptr q', len L + left}` at O, q' holding the payload's first 32(L + left) octets and
    being the data of an allocated chunk of exactly ⌈32(L + left)/32⌉ + 1 units, the context kept for
    the final state, every protected chunk still allocated, not q''s, with its data, and memory from
    S + 152 up kept off the reader and O; or the run reaches a failed `realloc` (`Exhausts`). -/
theorem bloop_heap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop)
    (S O rd q L c left ptr0 len0 ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (32 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + 32 * (L + left) ≤ d.addr + 32 * d.size)
    (hS : S0 + 360 ≤ S ∧ S + 152 ≤ S1) (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L) (h9 : ω[9] = UInt64.ofNat q)
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hn : 32 * (L + left) < 1073741760)
    (hlen : 32 * (L + left) ≤ len0 ∧ len0 < 4294967296)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 O)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 (c + left)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 L)
    (s144 : μ.readN (S + 144) 8 = Num.encodeLE 8 ret) (s136 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5)
    (s128 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : S + 152 ≤ rd ∧ rd + 16 ≤ S1) (hO : S + 152 ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * L))
    (hdat : μ.readN q (32 * L) = μ.readN ptr0 (32 * L)) :
    (∃ ω' μ' s' q', FreeStepsH p (refineContractK cap env) 983 ω μ x t ω' μ' x (hashSteps L left) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (L + left) ∧
      μ'.readN q' (32 * (L + left)) = μ.readN ptr0 (32 * (L + left)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 32 * (L + left)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 32 * (L + left)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = q' ∧ d.used = true ∧ d.size = (32 * (L + left) + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ q' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → S + 152 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 983 ω μ x (hashSteps L left) := by
  induction left using Nat.strongRecOn generalizing ω μ s q L c with
  | _ left ih =>
  have hS1 := H.hS1
  rcases batch_heap (p := p) (P := P) env cap hcap1 hcap x ω μ hb s K S rd q L c left ptr0 len0 pb S0 S1 H hcq hK
      hpay hS hsp h1 h7 h9 hL hc hl1 hn hlen s24 s16 s32 s40 s56 hrd hR0 hR8 hdat with
    ⟨ω1, μ1, s', r, run1, a1, a7, a9, m24, m16, m40, m48, m56, fr1, rR0, rR8, dat1, H1, hc1, hK1⟩ | hex
  rotate_left
  · exact Or.inr (hex.mono (by unfold hashSteps; omega))
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  generalize hcdef : min left L = c' at *
  have hcc : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L ∧ (c' < left → c' = L) := by omega
  have hS1r : ∀ a, S + 8 ≤ a → a < S + 152 → (a < S + 16 ∨ S + 32 ≤ a ∧ a < S + 40 ∨ S + 128 ≤ a) →
      μ1.read a = μ.read a := fun a h1 h2 h3 => fr1 a (by omega) (by omega) (Or.inl (by omega))
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + 32 * (L + left) → μ1.read a = μ.read a := fun a h1 h2 =>
    (hK1 cp hcpK).2.2.2 a ⟨by omega, by omega⟩
  have hX : 64 * ((32 * L + 31) / 32) ≤ 64 * L := by omega
  rcases Classical.em (c' < left) with hlt | hlt
  · -- the next batches
    have hcL : c' = L := hcc.2.2.2 hlt
    have hrec := ih (left - c') (by omega) ω1 μ1 s' r (L + c') c' H1 hc1
      (fun d hd => ⟨(hK1 d hd).1, (hK1 d hd).2.1, (hK1 d hd).2.2.1⟩) ⟨cp, hcpK, hcp1, by omega⟩
      a1 a7 a9 (by omega) (by omega) (by omega) (by omega) ⟨by omega, hlen.2⟩
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s8)
      (by rw [show c' + (left - c') = left by omega]; exact m24) m16
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s32)
      m40 m56
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s144)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s136)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s128)
      rR0 rR8
      (by rw [dat1]; exact (Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))).symm)
    have hY : left / L = (left - L) / L + 1 := Nat.div_eq_sub_div (by omega) (by omega)
    have hX2 : (left - L) / (L + L) ≤ (left - L) / L := Nat.div_le_div_left (by omega) (by omega)
    have hsteps : 64 * ((32 * L + 31) / 32) + 520 * c' + 1500 + hashSteps (L + c') (left - c') ≤
        hashSteps L left := by
      subst hcL; unfold hashSteps; omega
    rcases hrec with ⟨ω', μ', s'', q', run', z0, z1, z5, z6, zO, zO8, zO16, zdat, zR0, zR8, zH, zc, zK, zfr⟩ | hex
    · have e : L + c' + (left - c') = L + left := by omega
      rw [e] at zO zO16 zdat zR0 zR8 zc
      refine Or.inl ⟨ω', μ', s'', q', (run1.trans run').mono hsteps, z0, z1, z5, z6, zO, zO8, zO16, ?_,
        zR0, zR8, zH, zc, fun d hd => ?_,
        fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans (fr1 a h0 (Or.inr (Or.inr (by omega))) h2)⟩
      · rw [zdat]
        exact Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))
      · obtain ⟨z1', z2', z3', z4'⟩ := zK d hd
        exact ⟨z1', z2', z3', fun a ha => (z4' a ha).trans ((hK1 d hd).2.2.2 a ha)⟩
    · exact Or.inr ((Exhausts.pre run1 hex).mono hsteps)
  · -- the last batch: the exit
    have hcl : c' = left := by omega
    subst hcl
    obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := hc1
    obtain ⟨hr0, -, hrT⟩ := chunk_in H1.wf hcrm hcru
    have hb1 := H1.hb0
    have hbT1 := H1.hbT
    obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, fr3, rd3, wr3⟩ :=
      exb (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 S c' O (L + c') r (L + c') ret t v5 v6
        ⟨by omega, by omega⟩ a1 (by omega) (by omega) (Or.inr hO.1) (by omega) (by omega) (by omega) hv5 hv6
        m24 m16 m40 m48 m56
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s8)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s144)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s136)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s128)
        hret hjt hbt (fun a h1 h2 => H1.st a (by omega) (by omega)) (fun a h1 h2 => H1.st a (by omega) (by omega))
    have hlowh : ∀ a, a < 2147483648 → μ3.read a = μ1.read a := fun a h2 =>
      fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    have run13 := run1.trans run3
    refine Or.inl ⟨ω3, μ3, s', r, run13.mono (by unfold hashSteps; omega), z0, z1, z5, z6, zO, zO8, zO16,
      ?_, ?_, ?_, ctx_congr_data H1 hcrm (fun a h1 _ => hlowh a h1) wr3, ⟨cr, hcrm, hcra, hcru, hcrs⟩,
      fun d hd => ?_, ?_⟩
    · rw [Memory.readN_congr (fun j hj => hlowh _ (by omega))]; exact dat1
    · rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (by omega))]; exact rR0
    · rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (by omega))]; exact rR8
    · obtain ⟨k1, k2, k3, k4⟩ := hK1 d hd
      refine ⟨k1, k2, k3, fun a ha => ?_⟩
      have hca := ha
      unfold InData at hca
      have := (chunk_in H1.wf k1 k2).2.2
      exact (hlowh a (by omega)).trans (k4 a ha)
    · intro a h0 h1 h2 h3
      exact (fr3 a h0 (Or.inr (by omega)) h3).trans (fr1 a h0 (Or.inr (Or.inr (by omega))) h2)

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA in
/-- **Reading more than 512 hashes into a fresh `Vec<[u8; 32]>`, the payload in the heap** (907,
    `RandomStorageAccumulate`'s `Ok` payload; GP v0.8.0 §B.7, each element 32 octets): as
    `vec_hash32_heap` (the `HeapCtx` setting) for 512 < n with 32n < 2³⁰ − 64, with the stack
    pointer at least S0 + 512 (the `realloc` wrapper's frames below the function's). The first 512
    elements go into the block of the model's `alloc` of 512 units; then the later batches
    (`bloop_heap`) grow the buffer with `realloc` to exactly L + min(left, L) elements per batch until
    all n are read. Either the function returns to t with the `Vec` `{cap n, ptr q, len n}` at O (the
    capacity is exactly n), q holding the payload's 32n octets and being the data of an allocated
    chunk of ⌈32n/32⌉ + 1 units that is no allocated chunk of `s`, the context kept for the final state
    `s'`, every allocated chunk of `s` kept with its data, the reader advanced by 32n, the stack from
    sp up kept off the reader and O, memory below 196608 and the access of everything from S0 up kept;
    or the run reaches a failed allocator call (`Exhausts`): the first batch's `alloc` or one of the
    `realloc`s fails.

    *Not stated:* that the globals below the allocator (`Glob`) are kept, as `vec_hash32_heap` states;
    `ReallocCall.realloc_call` does not record it. -/
theorem vec_hash32_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + 32 * n ≤ c.addr + 32 * c.size)
    (hS : S0 + 512 ≤ sp ∧ sp ≤ S1) (hsp : 2147484160 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 512 < n ∧ 32 * n < 1073741760) (hnl : 32 * n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap env) 907 ω μ x t ω' μ' x
        (267000 + hashSteps 512 (n - 512)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q (32 * n) = μ.readN ptr (32 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 32 * n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 32 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (32 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (32 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 907 ω μ x (267000 + hashSteps 512 (n - 512)) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  -- the frame S = sp − 152 and the call of finish_grow for the first batch
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a10, a11, a12, a144, a136, a128, a32, a8', a5, a6, aS, a16, a24, a56, afr,
      ard, awr⟩ := p1b (p := p) (P := P) (R := refineContractK cap env) x ω μ (sp - 152) O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 (by rw [h1]; congr 1; omega) h5 h6 h7 h8 h9 ⟨hn.1, by omega⟩ (by omega) hv5 hv6
    (by omega) (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b32, b24, b16, b8'', bfr, brd, bwr⟩ := VecHash.g1 (p := p) (P := P)
    (R := refineContractK cap env) x ω1 μ1 (sp - 192) (sp - 152 + 96) 512 28 n 512 ⟨by omega, by omega⟩ a0
    (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega) (by decide) (by omega)
    ⟨by decide, by decide⟩ (fun a h1 h2 => by rw [awr]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 192 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (bfr a h0 (by omega)).trans (afr a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [bwr, awr]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω2 μ2 s (sp - 192) (32 * 512) 1 pb S0 S1 H2
      b1 b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s1, ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ((Exhausts.of_alloc (run1.trans (run2.trans run3)) e7 hna).mono (by omega))
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (32 * 512 + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 192 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, d0, d1, d5, d6, d96, d104, d112, dfr, drd, dwr⟩ := g2 (p := p) (P := P)
    (R := refineContractK cap env) x ω3 μ3 (sp - 192) (sp - 152 + 96) (32 * 512) q 28 1023 n 512
    ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7 ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b32)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b24)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b16)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b8'')
    ⟨by decide, by decide, by decide⟩ jte_13 bs_1023
    (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
    (fun a h1 h2 => H3.st a (by omega) (by omega))
  have chain5 : ∀ a, sp - 152 ≤ a → a < sp → (a < sp - 152 + 96 ∨ sp - 152 + 120 ≤ a) →
      μ5.read a = μ1.read a := fun a h1 h2 h3 =>
    (dfr a (by omega) h3).trans ((hF a (by omega) (by omega)).trans (bfr a (by omega) (by omega)))
  -- the first read's call
  obtain ⟨ω6, μ6, run6, f0, f1, f6, f7, f8, f9, f40, f48, f16, efr, erd, ewr⟩ := p5b (p := p) (P := P)
    (R := refineContractK cap env) x ω5 μ5 (sp - 152) 512 512 512 q rd ⟨by omega, by omega⟩
    (d1.trans (congrArg _ (by omega))) d6 (by decide) (by decide) ⟨by decide, by decide⟩ (by omega) (by omega)
    d96 d104
    (by rw [Memory.readN_congr (fun j hj => chain5 _ (by omega) (by omega) (by omega))]; exact aS)
    (by rw [Memory.readN_congr (fun j hj => chain5 _ (by omega) (by omega) (by omega))]; exact a16)
    (by rw [Memory.readN_congr (fun j hj => chain5 _ (by omega) (by omega) (by omega))]; exact a32)
    (fun a h1 h2 => by rw [dwr]; exact H3.st a (by omega) (by omega))
  have chain6 : ∀ a, sp - 152 ≤ a → a < sp → (a < sp - 152 + 16 ∨ sp - 152 + 24 ≤ a) →
      (a < sp - 152 + 40 ∨ sp - 152 + 56 ≤ a) → (a < sp - 152 + 96 ∨ sp - 152 + 128 ≤ a) →
      μ6.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (efr a (by omega) h3 h4 h5).trans (chain5 a h1 h2 (by omega))
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (efr a h0 (by omega) (by omega) (by omega)).trans ((dfr a h0 (by omega)).trans
      ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (efr a (by omega) (by omega) (by omega) (by omega)).trans (dfr a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha =>
    (h63 a (by unfold InData at ha; omega)).trans ((kd cp hcpm hcpu a ha).trans
      (hlow a (by unfold InData at ha; omega) (Or.inl (by unfold InData at ha; omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [ewr, dwr]
  have hdq : q + 32 * 512 ≤ ptr ∨ ptr + 32 * 512 ≤ q := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  -- the first batch's reads
  obtain ⟨ω7, μ7, run7, g1, g7, g9, g56, gdat, gR0, gR8, gfr, grd, gwr⟩ :=
    loopb (p := p) (P := P) (R := refineContractK cap env) x (sp - 152) q 512 rd ptr len
      ⟨by omega, by omega, by omega⟩ (by decide) ⟨by omega, hlen⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ hdq 512 0 ω6 μ6 f0 f1 f6 f7 f8 f9 (by decide) (by omega)
      (by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a32)
      f40 f48
      (by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a56)
      (by rw [show ptr + 32 * 0 = ptr by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [show len - 32 * 0 = len by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      rfl
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  have h76 : ∀ a, sp - 152 ≤ a → a < sp - 152 + 56 → μ7.read a = μ6.read a := fun a h1 h2 =>
    gfr a (by omega) (Or.inr h1) (Or.inl h2) (Or.inl (by omega)) (Or.inr (by omega))
  have h7S : ∀ a, sp - 152 ≤ a → a < sp → (a < sp - 152 + 56 ∨ sp - 152 + 128 ≤ a) →
      (a < sp - 152 + 16 ∨ sp - 152 + 24 ≤ a) → (a < sp - 152 + 40 ∨ sp - 152 + 56 ≤ a) →
      μ7.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (gfr a (by omega) (Or.inr h1) h3 (Or.inl (by omega)) (Or.inr (by omega))).trans
      (chain6 a h1 h2 h4 h5 (by omega))
  have h7hi : ∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (gfr a h0 (Or.inr (by omega)) (Or.inr (by omega)) h2 (Or.inr (by omega))).trans
      (hhigh a h0 h1)
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 32 * 512 ≤ a) → μ7.read a = μ3.read a := fun a h1 h3 =>
    (gfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (by omega)).trans (h63 a h1)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [gwr, wr36]
  have H7 : HeapCtx env pb S0 S1 μ7 s1 :=
    ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr73
  have kd7 : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ7.read a = μ.read a := by
    intro d hd hu a ha
    have hdis := data_disj H3.wf (keep d hd hu) hnew (hfresh d hd hu) ha
    simp only at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlowh a (by omega) (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  -- the later batches
  have hK : ∀ d, (d ∈ chunks s ∧ d.used = true) → d ∈ chunks s1 ∧ d.used = true ∧ d.addr + 32 ≠ q := by
    intro d ⟨hd, hu⟩
    refine ⟨keep d hd hu, hu, fun e => hfresh d hd hu ?_⟩
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    exact Tiles.addr_inj ht d (keep d hd hu) _ hnew (by simp only; omega)
  have hrest := bloop_heap (p := p) (P := P) env cap hcap1 hcap x ω7 μ7 0 s1
    (fun d => d ∈ chunks s ∧ d.used = true) (sp - 152) O rd q 512 512 (n - 512) ptr len ret t v5 v6 pb S0 S1 H7
    ⟨_, hnew, by simp only; omega, rfl, rfl⟩ hK ⟨cp, ⟨hcpm, hcpu⟩, hcp1, by omega⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ g1 g7 g9 (by omega) (by omega) (by omega) (by omega) ⟨by omega, hlen⟩
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a8')
    (by rw [show 512 + (n - 512) = n by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a24)
    (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact f16)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a32)
    (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact f40)
    g56
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a144)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a136)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a128)
    hret hjt hbt hv5 hv6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hOr gR0 gR8
    (by rw [gdat, Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩),
          Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)])
  rcases hrest with ⟨ω', μ', s', q', run', y0, y1, y5, y6, yO, yO8, yO16, ydat, yR0, yR8, yH,
      ⟨cf, hcfm, hcfa, hcfu, hcfs⟩, yK, yfr⟩ | hex
  · have hn' : 512 + (n - 512) = n := by omega
    rw [hn'] at yO yO16 ydat yR0 yR8 hcfs
    have runAll := run17.trans run'
    obtain ⟨hfb, -, -⟩ := chunk_in yH.wf hcfm hcfu
    have hyb := yH.hb0
    have hcf : cf = ⟨q' - 32, (32 * n + 31) / 32 + 1, true⟩ := by
      obtain ⟨ca, cs, cu⟩ := cf
      simp only at hcfa hcfu hcfs
      rw [hcfu, hcfs]; congr 1; omega
    refine Or.inl ⟨q', s', ω', μ', runAll.mono (by omega), y0, by rw [y1]; congr 1; omega, y5, y6, yO, yO8,
      yO16, ?_, yR0, yR8, yH,
      fun c hc hu => (yK c ⟨hc, hu⟩).1, hcf ▸ hcfm, ?_, ?_, FreeStepsH.pagesOut H.bd runAll, ?_, ?_, ?_⟩
    · rw [ydat]; exact Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)
    · intro d hd hu e
      have := (yK d ⟨hd, hu⟩).2.2.1
      rw [e] at this; simp only at this; omega
    · intro c hc hu a ha
      exact ((yK c ⟨hc, hu⟩).2.2.2 a ha).trans (kd7 c hc hu a ha)
    · intro a h0 h1 h2 h3
      exact (yfr a h0 (by omega) h2 h3).trans (h7hi a h0 h1 h2)
    · intro a ha'
      obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd runAll
      refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
      unfold Memory.readable
      rw [kp _ (Or.inl (by unfold pageSize; omega))]
    · intro a ha'
      obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd runAll
      unfold Memory.writable
      rw [kp _ (Or.inr (by unfold pageSize; omega))]
  · exact Or.inr ((Exhausts.pre run17 hex).mono (by omega))

end Services.Bootstrap.Decode.VecHash32
