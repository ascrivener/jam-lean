import Services.Bootstrap.Decode.VecKey336
import Services.Bootstrap.Decode.VecPairsBig

/-!
# `Vec<[u8; 336]>` of more than 48 keys, the payload in the heap (function 1300)

`vec_key336_heap_big` is the key reader at 1300 (`VecKey336`, `Designate`'s validator keys) for
n > 48 elements in the decode loop's setting (`HeapCtx`, under `refineContractK cap`). The function's
outer loop (1349) reserves c = min(left, B) elements per batch, `left` the elements still to read
and B a bound that is 48 for the first batch and the length read so far for every later one (1393:
ω₁₂ ← ω₇, the length), so the buffer doubles: L ↦ L + min(left, L). Each reservation calls
`finish_grow` (32989, alignment 1, element size 336) for the capacity L + c (the capacity always
equals the length at the batch end, so the reservation always grows): for the first batch with no old
buffer (`alloc`, `HeapCtx.alloc_call`), for every later one with the old buffer q of L elements
(`realloc`, `ReallocCall.realloc_call`; `g3k`). Then the element loop (1495 … 1492) decodes each key
of the batch (`VecKey336.key`) and copies it to the block, in Rust's field order (`keyRot`). The
in-batch "buffer full" path (1583, `len = cap`) is never taken.

The outer loop's invariant (`bloop_heap`), at the batch end 1483: L elements read into the buffer q,
the data of an allocated chunk of ⌈336L/32⌉ + 1 units, holding the payload's first L keys rotated; a
set `K` of protected chunks (allocated, not q's, one of them holding the payload); `HeapCtx`. As in
`VecHashBig`, `realloc` keeps the protected chunks with their data and its block is never one of them
(`VecU8.realloc_fresh`). Every block is 8-aligned (`VecKey336.tiles_mod`), as the block copy needs.

Either the function returns, or the run reaches a failed allocator call (`LoopA.Exhausts`).

Not stated (unlike `vec_key336_heap`): the globals below the allocator (`Glob`) are kept;
`realloc_call` does not record it.

GP v0.8.0: the octets are read from the service's memory by the PVM (Appendix A); the
`Vec<[u8; 336]>` is the bootstrap service's own decoding of an argument blob (§B.7: a sequence of
336-octet validator keys, §6.3).
-/

namespace Services.Bootstrap.Decode.VecKey336

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Decode.VecU8
  Services.Bootstrap.Decode.Key336Memcpy

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

/-- 1300 … 1419, n > 48 keys asked: as `p1`, the function opens its 768-octet frame at S = ω₁ − 768
    and, n exceeding the first batch's bound 48, calls `finish_grow` for the first batch
    c = min(n, 48) = 48 elements of 336 octets (ω₁₀ = 48, result slot S + 64, return address 36), with
    n at S + 8 and 48 at S + 16, S + 32 and in ω₆. -/
theorem p1b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 768)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : 48 < n ∧ n < 4294967296)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1300 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 36 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat 48 ∧
      ω'[7] = UInt64.ofNat (S + 64) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 48 ∧
      ω'[11] = UInt64.ofNat 1 ∧ ω'[12] = UInt64.ofNat 336 ∧
      μ'.readN (S + 760) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (S + 752) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (S + 744) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (S + 24) 8 = Num.encodeLE 8 rd ∧
      μ'.readN S 8 = Num.encodeLE 8 out ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 48 ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 48 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 768 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hn' : ¬ n ≤ 48 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hn, hn', VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp

/-- 32989 … 33049: `finish_grow` with an old buffer q of capacity L ≥ 1 (ω₈ = L, ω₉ = q) for the new
    capacity N ≥ 1 (ω₁₀) of 336-octet elements at alignment `al`: as `VecPairs.g3e` (which needs an
    element size of at most 64), it calls `realloc` (40701) for q to 336·N octets (ω₇ = q, ω₉ = al,
    ω₁₀ = 336·N, return address 1524), 336·N also at F + 8. -/
theorem g3k {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F res L q N al r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat L)
    (h9 : ω[9] = UInt64.ofNat q) (h10 : ω[10] = UInt64.ofNat N) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat 336)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hL : 1 ≤ L ∧ L < 4294967296) (hN : 1 ≤ N ∧ 336 * N < 1073741760)
    (hal : 1 ≤ al ∧ al ≤ 32) (hq : q < 18446744073709551616)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40701 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1524 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[9] = UInt64.ofNat al ∧ ω'[10] = UInt64.ofNat (336 * N) ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (336 * N) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : 336 * N < 274877906944 := by omega
  have hEn0 : ¬ 336 * N = 0 := by omega
  have hL0 : ¬ L = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, hF, hw, hr, hL, hL0, hN, hal, hEn, hEn0,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show F + 40 - 40 = F by omega]); post_simp
    all_goals try (congr 1; omega)

/-- 1424 … 1450, as `p5` for any batch: `finish_grow` returned `Ok` (0 at S + 64) with the block q
    (S + 72), the new capacity N in ω₆, the batch c at S + 16 and the bound B ≠ 0 at S + 32: the
    function records the `Vec` capacity N (S + 40) and pointer q (S + 48), keeps q at S + 32 and goes
    to the element loop (1495) with the batch c in ω₅. -/
theorem p5b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S N c B q : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat N) (hN : N < 18446744073709551616)
    (hc : c < 18446744073709551616) (hB : 0 < B ∧ B < 18446744073709551616)
    (hq : q < 18446744073709551616)
    (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 0) (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 B)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1424 ω μ x 1495 ω' μ' x 15 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat c ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 N ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < S + 32 ∨ S + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r64 := rd8 (by decide) s64
  have r72 := rd8 hq s72
  have r16 := rd8 hc s16
  have r32 := rd8 hB.2 s32
  have hB0 : ¬ B = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, hw, hr, hB0, r64, r72, r16, r32, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals first | exact h1 | skip

/-- `b2` without the bound n ≤ 48 (1574 … 1577, 1455 … 1477): the `Vec` {n, q, j} has room (j < n):
    `memcpy` is called to copy the key S + 408 … S + 744 to q + 336·j (return address 38), with j in
    ω₆ and q kept at S + 32. -/
theorem b2b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hjn : j < n) (hq : q + 336 * n < 4294967296)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1574 ω μ x 68729 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 38 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat j ∧
      ω'[7] = UInt64.ofNat (q + 336 * j) ∧ ω'[8] = UInt64.ofNat (S + 408) ∧ ω'[9] = UInt64.ofNat 336 ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < S + 32 ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r40 := rd8 (by omega) s40
  have r48 := rd8 (by omega) s48
  have r56 := rd8 (by omega) s56
  have hjn' : ¬ j = n := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hw, hr, r40, r48, r56, hjn', VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals first | exact h1 | skip

/-- `b3a` without the bound 48 (1483 … 1492): the key was copied; c ≥ 2 elements of the batch are
    left: the length becomes j + 1 (at S + 56) and the loop goes on (1495) with c − 1 in ω₅. -/
theorem b3ab {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S j c : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat c) (h6 : ω[6] = UInt64.ofNat j) (hc : 2 ≤ c ∧ c < 4294967296)
    (hj : j < 4294967296)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1483 ω μ x 1495 ω' μ' x 5 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (c - 1) ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 (j + 1) ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 64 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hc' : ¬ (c + 18446744073709551615) % 18446744073709551616 = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hc, hc', VecU8.rdN_writeN_same8, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals first | exact h1 | skip

/-- 1483 … 1492, 1380 … 1395, 1349 … 1419, the batch end with more to read: the batch's last key was
    copied (ω₅ = 1, ω₆ = j, the capacity j + 1 at S + 40; S + 8 holding c + left, S + 16 holding c,
    left ≥ 1): the length becomes L = j + 1 (S + 56), and the function goes back to its reserve loop
    (1349) with the bound L (ω₁₂ ← ω₇) and calls `finish_grow` for the capacity L + c',
    c' = min(left, L) (ω₈ = L the old capacity, ω₉ = q from S + 32, alignment 1, element size 336,
    result slot S + 64, return address 36), with left at S + 8, c' at S + 16 and L at S + 32. -/
theorem bkk {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q j c left : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat j)
    (hj : j + 1 < 4294967296) (hl : 1 ≤ left ∧ c + left < 4294967296) (hq : q < 18446744073709551616)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (c + left)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 (j + 1)) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 q)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1483 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 36 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat left ∧
      ω'[6] = UInt64.ofNat (j + 1 + min left (j + 1)) ∧ ω'[7] = UInt64.ofNat (S + 64) ∧
      ω'[8] = UInt64.ofNat (j + 1) ∧ ω'[9] = UInt64.ofNat q ∧
      ω'[10] = UInt64.ofNat (j + 1 + min left (j + 1)) ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 336 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 (j + 1) ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 left ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 (min left (j + 1)) ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 (j + 1) ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 24 ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) →
        (a < S + 56 ∨ S + 64 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r8 := rd8 (by omega) s8
  have r16 := rd8 (by omega) s16
  have r40 := rd8 (by omega) s40
  have r32 := rd8 hq s32
  have hpos : 0 < (if left ≤ j + 1 then left else j + 1) % 18446744073709551616 := by split <;> omega
  have hle : c ≤ c + left := Nat.le_add_right c left
  have hne : ¬ c + left - c = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, hj, hl, r8, r16, r40, r32, hle, hne, Nat.sub_self, hpos,
      Nat.add_sub_cancel_left, VecU8.rdN_writeN_same8, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_,
      fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; split <;> omega)
    all_goals try (congr 1; omega)

/-- 1483 … 1492, 1380 … 1398, 1736 … 1758, 1703 … 1734: the last key was copied (ω₅ = 1, ω₆ = j)
    and nothing is left (S + 8 and S + 16 both hold the last batch c): the length becomes j + 1, and
    the function stores the `Vec` {cap, q, j + 1} (capacity from S + 40, pointer from S + 48) at the
    slot `out` (S) and returns through its frame. -/
theorem exk {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S c cap q j out r0 t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat j)
    (hj : j + 1 < 4294967296) (hc : c < 18446744073709551616) (hcap : cap < 4294967296)
    (hq : q < 4294967296) (hout : out + 24 < 4294967296)
    (hoS : out + 24 ≤ S ∨ S + 768 ≤ out)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 c) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 cap) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 out)
    (s760 : μ.readN (S + 760) 8 = Num.encodeLE 8 r0) (s752 : μ.readN (S + 752) 8 = Num.encodeLE 8 v5)
    (s744 : μ.readN (S + 744) 8 = Num.encodeLE 8 v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1483 ω μ x t ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 768) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN out 8 = Num.encodeLE 8 cap ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 (j + 1) ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 80 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r8 := rd8 hc s8
  have r16 := rd8 hc s16
  have r40 := rd8 (by omega) s40
  have r48 := rd8 (by omega) s48
  have r0' := rd8 (by omega) s0
  have r760 := rd8 (by omega) s760
  have r752 := rd8 hv5 s752
  have r744 := rd8 hv6 s744
  have hcap' : ¬ cap = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, hwo, hout, hoS, hj, hcap, hcap', r8, r16, r40, r48, r0', r760, r752, r744,
      hret, hjt, hbt, Nat.sub_self, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp


/-- Equal blocks have equal sub-blocks. -/
theorem readN_sub336 {μ μ' : Memory} {a b n i m : Nat} (h : μ'.readN a n = μ.readN b n) (hi : i + m ≤ n) :
    μ'.readN (a + i) m = μ.readN (b + i) m := by
  rw [← readN_take μ' (a + i) (n - i) m (by omega), ← readN_take μ (b + i) (n - i) m (by omega),
    ← readN_drop, ← readN_drop, h]

/-- **One key, up to its copy into the block** (`body` for any capacity; 1495 … 1477, then `memcpy`
    to 1483): with the `Vec` {N, q, j} (j < N) at S + 40 … S + 56 and the reader rd (at S + 24) at a
    key pp with ll ≥ 336 octets left, the key decoder reads the key, the function copies it to S + 408
    and from there to q + 336·j (rotated, `keyRot`), keeps q at S + 32 and reaches 1483 with ω₅ as it
    was and j in ω₆. -/
theorem bodyb {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S N q rd pp ll j c : Nat)
    (hS : 65536 + 784 ≤ S ∧ S + 768 < 4294967296 ∧ S % 8 = 0)
    (hq : 65536 ≤ q ∧ q + 336 * N + 16 < 4294967296 ∧ q % 8 = 0) (hj : j < N)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hpp : 65536 ≤ pp ∧ pp + 336 + 16 < 4294967296) (hll : 336 ≤ ll ∧ ll < 4294967296)
    (rS : rd + 16 ≤ S - 784 ∨ S + 768 ≤ rd) (pS : pp + 336 + 24 ≤ S - 784 ∨ S + 768 ≤ pp)
    (qS : q + 336 * N ≤ S - 784 ∨ S + 768 ≤ q) (rq : rd + 16 ≤ q ∨ q + 336 * N ≤ rd)
    (pr : pp + 336 ≤ rd ∨ rd + 16 ≤ pp)
    (e1 : ω[1] = UInt64.ofNat S) (e5 : ω[5] = UInt64.ofNat c) (hc : c < 18446744073709551616)
    (m40 : μ.readN (S + 40) 8 = Num.encodeLE 8 N) (m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j) (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd)
    (R0 : μ.readN rd 8 = Num.encodeLE 8 pp) (R8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 ll)
    (ws : ∀ a, S - 784 ≤ a → a < S + 768 → μ.writable a = true)
    (wr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (wq : ∀ a, q ≤ a → a < q + 336 * N → μ.writable a = true)
    (rp : ∀ a, pp ≤ a → a < pp + 336 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x 1483 ω' μ' x 8150 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat c ∧ ω'[6] = UInt64.ofNat j ∧
      μ'.readN (q + 336 * j) 336 = keyRot (μ.readN pp 336) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (pp + 336) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (ll - 336) ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < S - 784 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        (a < q + 336 * j ∨ q + 336 * j + 336 ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) → (a < S + 64 ∨ S + 744 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have hj336 : 336 * j + 336 ≤ 336 * N := by omega
  -- the key decoder
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a64, akey, aR0, aR8, afr, ard, awr⟩ := key (p := p) (P := P) (R := R) x ω μ
    S c (ω[6]).toNat rd pp ll ⟨hS0, hS1, hS8⟩ e1 e5 UInt64.ofNat_toNat.symm
    hc (UInt64.toNat_lt _) hrd hpp hll rS pS pr m24 R0 R8 ws wr rp
  -- 1551: copy the key to S + 408
  obtain ⟨ω2, run2, b0, b1', b5, b6, b7, b8, b9⟩ := b1 (p := p) (P := P) (R := R) x ω1 μ1 S (by omega) a1 a64
    (by rw [ard]; exact Memory.readable_of_writable (ws _ (by omega) (by omega)))
  obtain ⟨ω3, μ3, run3, s0, s1, s5, s6, scp, sfr, srd, swr⟩ := memcpy_s1 (p := p) (P := P) (R := R) x ω2 μ1
    42 1574 S (S + 408) (S + 65) 336 b0 b1' b7 b8 b9 (by decide) jte_20 bs_1574 ⟨by omega, by omega, by omega⟩
    (by decide) (by omega) (by omega) (by omega) (by omega) (by decide) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
  have F3 : ∀ a, S ≤ a → a < S + 64 → μ3.read a = μ.read a := fun a h1 h2 =>
    (sfr a (by omega) (by omega) (by omega)).trans (afr a (by omega) (by omega) (by omega) (by omega))
  -- 1574: the `Vec` has room; copy the key to q + 336·j
  obtain ⟨ω4, μ4, run4, c0, c1, c5, c6, c7, c8, c9, c32, cfr, crd, cwr⟩ := b2b (p := p) (P := P) (R := R) x ω3 μ3
    S N q j ⟨by omega, by omega⟩ (s1.trans rfl) hj (by omega)
    (by rw [Memory.readN_congr (fun i hi => F3 _ (by omega) (by omega))]; exact m40)
    (by rw [Memory.readN_congr (fun i hi => F3 _ (by omega) (by omega))]; exact m48)
    (by rw [Memory.readN_congr (fun i hi => F3 _ (by omega) (by omega))]; exact m56)
    (fun a h1 h2 => by rw [swr, awr]; exact ws a (by omega) (by omega))
  obtain ⟨ω5, μ5, run5, d0, d1, d5, d6, dcp, dfr, drd, dwr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R) x
    ω4 μ4 38 1483 S (q + 336 * j) (S + 408) 336 c0 c1 c7 c8 c9 (by decide) jte_18 bs_1483
    ⟨by omega, by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (fun a h1 h2 => by rw [crd, srd, ard]; exact Memory.readable_of_writable (ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [cwr, swr, awr]; exact wq a (by omega) (by omega))
    (fun a h1 h2 => by rw [cwr, swr, awr]; exact ws a (by omega) (by omega))
  have hrd5 : ∀ a, rd ≤ a → a < rd + 16 → μ5.read a = μ1.read a := fun a h1 h2 =>
    (dfr a (by omega) (by omega) (by omega)).trans ((cfr a (by omega) (by omega)).trans
      (sfr a (by omega) (by omega) (by omega)))
  refine ⟨ω5, μ5, (run1.trans (run2.trans (run3.trans (run4.trans run5)))).mono (by omega), d1,
    d5.trans (c5.trans (s5.trans (b5.trans a5))), d6.trans c6, ?_, ?_, ?_, ?_, ?_,
    fun a => by rw [drd, crd, srd, ard], fun a => by rw [dwr, cwr, swr, awr]⟩
  · rw [dcp, Memory.readN_congr (fun i hi => cfr _ (by omega) (by omega)), scp, akey]
  · rw [Memory.readN_congr (fun i hi => hrd5 _ (by omega) (by omega))]; exact aR0
  · rw [Memory.readN_congr (fun i hi => hrd5 _ (by omega) (by omega))]; exact aR8
  · rw [Memory.readN_congr (fun i hi => dfr _ (by omega) (by omega) (by omega))]; exact c32
  · intro a h0 h1 h2 h3 h4 h5
    rw [dfr a h0 h3 (by omega), cfr a h0 h4, sfr a h0 (by omega) (by omega)]
    exact afr a h0 (by omega) h2 (by omega)

/-- **A batch's keys** (1495 … 1483): from k < N keys in the block q (`Vec` {N, q, k} at S + 40 …
    S + 56), r = N − k left in the batch (ω₅) and the reader rd (at S + 24) at key k of the payload
    ptr₀, the element loop decodes the batch's remaining keys into q + 336·k … q + 336·N (each
    rotated, `keyRot`) and reaches the batch's last copy's return (1483) with ω₅ = 1, ω₆ = N − 1, q at
    S + 32 and the reader advanced to key N. -/
theorem kloop {p : ByteArray} {P : Program} [HasCode p P] (x : X)
    (S q N rd ptr0 len0 : Nat)
    (hS : 65536 + 784 ≤ S ∧ S + 768 < 4294967296 ∧ S % 8 = 0)
    (hq : 65536 ≤ q ∧ q + 336 * N + 16 < 4294967296 ∧ q % 8 = 0)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 336 * N + 16 < 4294967296) (hlen : 336 * N ≤ len0 ∧ len0 < 4294967296)
    (rS : rd + 16 ≤ S - 784 ∨ S + 768 ≤ rd) (pS : ptr0 + 336 * N + 24 ≤ S - 784 ∨ S + 768 ≤ ptr0)
    (qS : q + 336 * N ≤ S - 784 ∨ S + 768 ≤ q) (rq : rd + 16 ≤ q ∨ q + 336 * N ≤ rd)
    (pq : ptr0 + 336 * N ≤ q ∨ q + 336 * N ≤ ptr0) (pr : ptr0 + 336 * N ≤ rd ∨ rd + 16 ≤ ptr0) :
    ∀ r k (ω : Regs) (μ : Memory), ω[1] = UInt64.ofNat S → ω[5] = UInt64.ofNat r → 1 ≤ r → k + r = N →
    μ.readN (S + 40) 8 = Num.encodeLE 8 N → μ.readN (S + 48) 8 = Num.encodeLE 8 q →
    μ.readN (S + 56) 8 = Num.encodeLE 8 k → μ.readN (S + 24) 8 = Num.encodeLE 8 rd →
    μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 336 * k) → μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 336 * k) →
    (∀ a, S - 784 ≤ a → a < S + 768 → μ.writable a = true) →
    (∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) →
    (∀ a, q ≤ a → a < q + 336 * N → μ.writable a = true) →
    (∀ a, ptr0 ≤ a → a < ptr0 + 336 * N → μ.readable a = true) →
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x 1483 ω' μ' x (8200 * r) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat 1 ∧ ω'[6] = UInt64.ofNat (N - 1) ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧
      (∀ i, k ≤ i → i < N → μ'.readN (q + 336 * i) 336 = keyRot (μ.readN (ptr0 + 336 * i) 336)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 336 * N) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 336 * N) ∧
      (∀ a, a < 4294967296 → (a < S - 784 ∨ S ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) → (a < S + 56 ∨ S + 744 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → (a < q + 336 * k ∨ q + 336 * N ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro r
  induction r with
  | zero => intro k ω μ _ _ h; exact absurd h (by decide)
  | succ r ih =>
  intro k ω μ h1 h5 hr1 hkr s40 s48 s56 s24 hR0 hR8 hws hwr hwq hra
  obtain ⟨ω1, μ1, run1, a1, a5, a6, akey, aR0, aR8, a32, afr, ard, awr⟩ := bodyb (p := p) (P := P) (R := R) x ω μ
    S N q rd (ptr0 + 336 * k) (len0 - 336 * k) k (r + 1) hS hq (by omega) hrd ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ rS (by omega) qS rq (by omega) h1 h5 (by omega) s40 s48 s56 s24 hR0 hR8 hws hwr hwq
    (fun a h1 h2 => hra a (by omega) (by omega))
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + 336 * N → μ1.read a = μ.read a := fun a h1 h2 =>
    afr a (by omega) (by omega) (by omega) (by rcases pq with h | h <;> omega) (by omega) (by omega)
  by_cases hr0 : r = 0
  · subst hr0
    refine ⟨ω1, μ1, run1.mono (by omega), a1, a5, a6.trans (congrArg _ (by omega)), a32, ?_,
      aR0.trans (congrArg _ (by omega)), aR8.trans (congrArg _ (by omega)),
      fun a h0 h1 h2 h3 h4 h5 => afr a h0 h1 h4 (by omega) h2 (by omega), ard, awr⟩
    intro i hi1 hi2
    rw [show i = k by omega]; exact akey
  · obtain ⟨ω2, μ2, run2, b1', b5, b56, bfr, brd, bwr⟩ := b3ab (p := p) (P := P) (R := R) x ω1 μ1 S k (r + 1)
      ⟨by omega, by omega⟩ a1 a5 a6 ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => by rw [awr]; exact hws a (by omega) h2)
    have back : ∀ a, a < 4294967296 → (a < S - 784 ∨ S ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) →
        (a < S + 56 ∨ S + 744 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        (a < q + 336 * k ∨ q + 336 * k + 336 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 h3 h4 h5 =>
      (bfr a h0 (by omega)).trans (afr a h0 h1 h4 h5 h2 (by omega))
    have hS' : ∀ a, S + 24 ≤ a → a < S + 32 ∨ (S + 40 ≤ a ∧ a < S + 56) → μ2.read a = μ.read a := fun a h1 h2 =>
      back a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨ω', μ', run', e1, e5, e6, e32, edat, eR0, eR8, efr, erd, ewr⟩ :=
      ih (k + 1) ω2 μ2 b1' (b5.trans (congrArg _ (by omega))) (by omega) (by omega)
        (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega))]; exact s40)
        (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega))]; exact s48)
        b56
        (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega))]; exact s24)
        (by rw [Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega))]
            exact aR0.trans (congrArg _ (by omega)))
        (by rw [Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega))]
            exact aR8.trans (congrArg _ (by omega)))
        (fun a h1 h2 => by rw [bwr, awr]; exact hws a h1 h2) (fun a h1 h2 => by rw [bwr, awr]; exact hwr a h1 h2)
        (fun a h1 h2 => by rw [bwr, awr]; exact hwq a h1 h2) (fun a h1 h2 => by rw [brd, ard]; exact hra a h1 h2)
    have hpay2 : ∀ a, ptr0 ≤ a → a < ptr0 + 336 * N → μ2.read a = μ.read a := fun a h1 h2 =>
      back a (by omega) (by omega) (by omega) (by omega) (by omega) (by rcases pq with h | h <;> omega)
    refine ⟨ω', μ', (run1.trans (run2.trans run')).mono (by rw [Nat.mul_succ]; omega), e1, e5, e6, e32, ?_, eR0,
      eR8, fun a h0 h1 h2 h3 h4 h5 => (efr a h0 h1 h2 h3 h4 (by omega)).trans (back a h0 h1 h2 h3 h4 (by omega)),
      fun a => by rw [erd, brd, ard], fun a => by rw [ewr, bwr, awr]⟩
    intro i hi1 hi2
    rcases Nat.lt_or_ge k i with hk | hk
    · rw [edat i (by omega) hi2]
      exact congrArg _ (Memory.readN_congr (fun j hj => hpay2 _ (by omega) (by omega)))
    · rw [show i = k by omega, Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)), Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]
      exact akey

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll in
/-- **One later batch, the payload in the heap** (1483 … 1483): at the batch end with L ≥ 1 keys
    read (the last key's copy returned: ω₅ = 1, ω₆ = L − 1; capacity L at S + 40, q at S + 32; S + 8,
    S + 16 holding c + left, c) and left ≥ 1 to go, q the data of an allocated chunk of ⌈336L/32⌉ + 1
    units holding the payload's first L keys rotated, the payload ptr₀ … ptr₀ + 336(L + left) inside a
    protected chunk (`K`: allocated, not q's): either the model's `realloc` of q to ⌈336(L + c')/32⌉
    units (c' = min(left, L)) gives a block r and state `s'`, and the function decodes the batch's c'
    keys into r, reaching the batch end again with capacity L + c', r holding the payload's first
    L + c' keys rotated and being the data of an allocated chunk of ⌈336(L + c')/32⌉ + 1 units, the
    context kept for `s'`, every protected chunk still allocated, not r's, with its data; or the run
    reaches a failed `realloc` (`Exhausts`). -/
theorem batchk {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop) (S rd q L c left ptr0 len0 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (336 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + 336 * (L + left) ≤ d.addr + 32 * d.size)
    (hS : S0 + 784 ≤ S ∧ S + 768 ≤ S1) (hsp : 2147484480 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat (L - 1))
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hn : 336 * (L + left) < 1073741760)
    (hlen : 336 * (L + left) ≤ len0 ∧ len0 < 4294967296)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (c + left)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 q)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (hrd : S + 768 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 336 * L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 336 * L))
    (hdat : ∀ i, i < L → μ.readN (q + 336 * i) 336 = keyRot (μ.readN (ptr0 + 336 * i) 336)) :
    (∃ ω' μ' s' r, FreeStepsH p (refineContractK cap env) 1483 ω μ x 1483 ω' μ' x
        (64 * ((336 * L + 31) / 32) + 8200 * min left L + 1500) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat 1 ∧ ω'[6] = UInt64.ofNat (L + min left L - 1) ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 left ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 (min left L) ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 r ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (S ≤ a ∧ a < S + 8 ∨ S + 24 ≤ a ∧ a < S + 32 ∨ S + 744 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 336 * (L + min left L)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 336 * (L + min left L)) ∧
      (∀ i, i < L + min left L → μ'.readN (r + 336 * i) 336 = keyRot (μ.readN (ptr0 + 336 * i) 336)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = r ∧ d.used = true ∧ d.size = (336 * (L + min left L) + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧
        ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 1483 ω μ x (64 * ((336 * L + 31) / 32) + 1500) := by
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpm, hcpu, hcpq⟩ := hK cp hcpK
  have hu : usable s q = (336 * L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  obtain ⟨hp0, -, hpT⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  have eL : L - 1 + 1 = L := by omega
  -- the batch end, and finish_grow to realloc
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m56, m8, m16, m32, fr1, rd1, wr1⟩ :=
    bkk (p := p) (P := P) (R := refineContractK cap env) x ω μ S q (L - 1) c left ⟨by omega, by omega⟩ h1 h5 h6
      (by omega) ⟨hl1, by omega⟩ (by omega) s8 s16 (by rw [eL]; exact s40) s32
      (fun a h1 h2 => hst a (by omega) (by omega))
  rw [eL] at a6 a8 a10 m56 m16 m32
  generalize hcdef : min left L = c' at *
  have hc1 : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g3k (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (S - 40) (S + 64) L q (L + c') 1 36
      left (L + c') ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ ⟨by decide, by decide⟩
      (by omega) (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 768 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega) (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcqm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (S - 40) q 1 (336 * (L + c')) pb
      S0 S1 H2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (by decide) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', b, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp3, stk3, -, -, e0, e1,
      e5, e6⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr (Exhausts.of_realloc ((run1.trans (run2.trans (run3.trans run4))).mono (by omega)) e7 hR)
  have hR1 : realloc (growTo pb) hb s q 1 ((336 * (L + c') + 31) / 32) = some (r, s', b) := hR
  have hfr := realloc_fresh H.wf ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR1
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨hr0, -, hrT⟩ := chunk_in H3.wf hcrm hcru
  rw [hcrs] at hrT
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have hr8 : r % 8 = 0 := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    have := tiles_mod _ _ ht _ hcrm
    have := H3.wf.2.1
    omega
  have hcp' := keep3 cp hcpm hcpu hcpq
  have hcpr : cp.addr + 32 ≠ r := hfr cp hcpm hcpu hcpq
  have hcpne : cp ≠ cr := fun e => hcpr (by rw [e]; exact hcra)
  have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (S - 40) (S + 64) (336 * (L + c')) r 36 1424
      left (L + c') ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n8)
      (by decide) jte_17 bs_1424
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS51 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 64 ∨ S + 88 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 h3).trans ((stk3 a h2 (by omega)).trans (fr2 a h2 (Or.inr (by omega))))
  obtain ⟨ω6, μ6, run6, d1, d5, d40, d48, d32, fr6, rd6, wr6⟩ :=
    p5b (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 S (L + c') c' L r ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c6 (by omega) (by omega) ⟨by omega, by omega⟩ (by omega)
      cres (by rw [show S + 72 = S + 64 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m16)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m32)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hS61 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 32 ∨ S + 56 ≤ a) → (a < S + 64 ∨ S + 88 ≤ a) →
      μ6.read a = μ1.read a := fun a h1 h2 h3 h4 => (fr6 a h2 h3).trans (hS51 a h1 h2 h4)
  have hhigh : ∀ a, a < 4294967296 → S + 768 ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (hS61 a (by omega) h0 (by omega) (by omega)).trans (fr1 a h0 (by omega) (by omega) (by omega))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha => by
    have hca := ha
    unfold InData at hca
    rw [h63 a (by omega), kp3 a ⟨cp, hcpm, hcpu, hcpq, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have rd36 : ∀ a, μ6.readable a = μ3.readable a := fun a => by rw [rd6, rd5]
  have hdq : ptr0 + 336 * (L + c') ≤ r ∨ r + 336 * (L + c') ≤ ptr0 := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' cr hcrm hcpne with h' | h' <;> omega
  -- the batch's keys
  obtain ⟨ω7, μ7, run7, f1, f5, f6, f32, fdat, fR0, fR8, ffr, frd, fwr⟩ :=
    kloop (p := p) (P := P) (R := refineContractK cap env) x S r (L + c') rd ptr0 len0
      ⟨by omega, by omega, hsp.2⟩ ⟨by omega, by omega, hr8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, hlen.2⟩ (Or.inr hrd.1) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hdq
      (Or.inl (by omega)) c' L ω6 μ6 d1 d5 hc1.1 rfl d40 d48
      (by rw [Memory.readN_congr (fun j hj => hS61 _ (by omega) (by omega) (by omega) (by omega))]; exact m56)
      (by rw [Memory.readN_congr (fun j hj => (hS61 _ (by omega) (by omega) (by omega) (by omega)).trans
        (fr1 _ (by omega) (by omega) (by omega) (by omega)))]; exact s24)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hcrm hcru ⟨by omega, by rw [hcrs]; omega⟩)
      (fun a h1 h2 => by
        rw [rd36]; exact Memory.readable_of_writable (heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  -- the results
  have h76 : ∀ a, S ≤ a → a < S + 32 ∨ (S + 40 ≤ a ∧ a < S + 56) → μ7.read a = μ6.read a := fun a h1 h2 =>
    ffr a (by omega) (Or.inr h1) (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))
  have hlowh : ∀ a, a < 2147483648 → (a < r + 336 * L ∨ r + 336 * (L + c') ≤ a) → μ7.read a = μ3.read a :=
    fun a h2 h3 => (ffr a (by omega) (Or.inl (by omega)) (by omega) (by omega) (Or.inl (by omega)) h3).trans
      (h63 a h2)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [fwr, wr36]
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  refine Or.inl ⟨ω7, μ7, s', r, run17.mono (by omega), f1, f5, f6, ?_, ?_, ?_, ?_, f32, ?_, fR0, fR8, ?_,
    ctx_congr_data H3 hcrm (fun a h1 h2 => hlowh a h1 (by rw [hcrs] at h2; omega)) wr73,
    ⟨cr, hcrm, hcra, hcru, hcrs⟩, ?_⟩
  · rw [Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega)).trans
      (hS61 _ (by omega) (by omega) (by omega) (by omega)))]; exact m8
  · rw [Memory.readN_congr (fun j hj => (h76 _ (by omega) (by omega)).trans
      (hS61 _ (by omega) (by omega) (by omega) (by omega)))]; exact m16
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact d40
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact d48
  · intro a h0 h1 h2
    exact (ffr a h0 (Or.inr (by omega)) (by omega) (by omega) h2 (Or.inr (by omega))).trans
      ((hS61 a (by omega) h0 (by omega) (by omega)).trans (fr1 a h0 (by omega) (by omega) (by omega)))
  · intro i hi
    rcases Nat.lt_or_ge i L with hiL | hiL
    · have e3 := readN_sub336 (i := 336 * i) (m := 336) (readN_prefix (n := 336 * L) (by omega) dat3) (by omega)
      rw [Memory.readN_congr (fun j hj => hlowh _ (by omega) (by omega)), e3,
        Memory.readN_congr (fun j hj => hlow _ (by omega) (Or.inl (by omega))), hdat i hiL]
    · rw [fdat i hiL hi]
      exact congrArg _ (Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩))
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

/-- A step bound for the batches from L keys read with `left` to go. -/
def keySteps (L left : Nat) : Nat := 700 * L + 9600 * left + 2000 * (left / L) + 2000

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA in
/-- **The function's later batches, the payload in the heap** (from the batch end 1483 to the return
    t): as `batchk`, with the slot O (at S), the `Vec`'s pointer q at S + 48, ret, v5, v6 (S + 760,
    S + 752, S + 744) and left ≥ 1 to go. Either the function returns to t with the `Vec`
    `{cap L + left, ptr q', len L + left}` at O, q' holding the payload's first L + left keys rotated
    and being the data of an allocated chunk of exactly ⌈336(L + left)/32⌉ + 1 units, the context kept
    for the final state, every protected chunk still allocated, not q''s, with its data, and memory
    from S + 768 up kept off the reader and O; or the run reaches a failed `realloc` (`Exhausts`). -/
theorem bloopk {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop)
    (S O rd q L c left ptr0 len0 ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (336 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + 336 * (L + left) ≤ d.addr + 32 * d.size)
    (hS : S0 + 784 ≤ S ∧ S + 768 ≤ S1) (hsp : 2147484480 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat (L - 1))
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hn : 336 * (L + left) < 1073741760)
    (hlen : 336 * (L + left) ≤ len0 ∧ len0 < 4294967296)
    (s0 : μ.readN S 8 = Num.encodeLE 8 O)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 (c + left)) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 c)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 q)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 L)
    (s760 : μ.readN (S + 760) 8 = Num.encodeLE 8 ret) (s752 : μ.readN (S + 752) 8 = Num.encodeLE 8 v5)
    (s744 : μ.readN (S + 744) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : S + 768 ≤ rd ∧ rd + 16 ≤ S1) (hO : S + 768 ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 336 * L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 336 * L))
    (hdat : ∀ i, i < L → μ.readN (q + 336 * i) 336 = keyRot (μ.readN (ptr0 + 336 * i) 336)) :
    (∃ ω' μ' s' q', FreeStepsH p (refineContractK cap env) 1483 ω μ x t ω' μ' x (keySteps L left) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 768) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (L + left) ∧
      (∀ i, i < L + left → μ'.readN (q' + 336 * i) 336 = keyRot (μ.readN (ptr0 + 336 * i) 336)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 336 * (L + left)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 336 * (L + left)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = q' ∧ d.used = true ∧ d.size = (336 * (L + left) + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ q' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → S + 768 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 1483 ω μ x (keySteps L left) := by
  induction left using Nat.strongRecOn generalizing ω μ s q L c with
  | _ left ih =>
  have hS1 := H.hS1
  rcases batchk (p := p) (P := P) env cap hcap1 hcap x ω μ hb s K S rd q L c left ptr0 len0 pb S0 S1 H hcq hK
      hpay hS hsp h1 h5 h6 hL hc hl1 hn hlen s8 s16 s24 s32 s40 hrd hR0 hR8 hdat with
    ⟨ω1, μ1, s', r, run1, a1, a5, a6, m8, m16, m40, m48, m32, fr1, rR0, rR8, dat1, H1, hc1, hK1⟩ | hex
  rotate_left
  · exact Or.inr (hex.mono (by unfold keySteps; omega))
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  generalize hcdef : min left L = c' at *
  have hcc : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L ∧ (c' < left → c' = L) := by omega
  have hS1r : ∀ a, S ≤ a → a < S + 768 → (a < S + 8 ∨ S + 24 ≤ a ∧ a < S + 32 ∨ S + 744 ≤ a) →
      μ1.read a = μ.read a := fun a h1 h2 h3 => fr1 a (by omega) (by omega) (Or.inl (by omega))
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + 336 * (L + left) → μ1.read a = μ.read a := fun a h1 h2 =>
    (hK1 cp hcpK).2.2.2 a ⟨by omega, by omega⟩
  rcases Classical.em (c' < left) with hlt | hlt
  · -- the next batches
    have hcL : c' = L := hcc.2.2.2 hlt
    have hrec := ih (left - c') (by omega) ω1 μ1 s' r (L + c') c' H1 hc1
      (fun d hd => ⟨(hK1 d hd).1, (hK1 d hd).2.1, (hK1 d hd).2.2.1⟩) ⟨cp, hcpK, hcp1, by omega⟩
      a1 a5 a6 (by omega) (by omega) (by omega) (by omega) ⟨by omega, hlen.2⟩
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s0)
      (by rw [show c' + (left - c') = left by omega]; exact m8) m16
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s24)
      m32 m40
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s760)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s752)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s744)
      rR0 rR8
      (fun i hi => by
        rw [dat1 i hi]; exact congrArg _ (Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))).symm)
    have hY : left / L = (left - L) / L + 1 := Nat.div_eq_sub_div (by omega) (by omega)
    have hX2 : (left - L) / (L + L) ≤ (left - L) / L := Nat.div_le_div_left (by omega) (by omega)
    have hsteps : 64 * ((336 * L + 31) / 32) + 8200 * c' + 1500 + keySteps (L + c') (left - c') ≤
        keySteps L left := by
      subst hcL; unfold keySteps; omega
    rcases hrec with ⟨ω', μ', s'', q', run', z0, z1, z5, z6, zO, zO8, zO16, zdat, zR0, zR8, zH, zc, zK, zfr⟩ | hex
    · have e : L + c' + (left - c') = L + left := by omega
      rw [e] at zO zO16 zdat zR0 zR8 zc
      refine Or.inl ⟨ω', μ', s'', q', (run1.trans run').mono hsteps, z0, z1, z5, z6, zO, zO8, zO16, ?_,
        zR0, zR8, zH, zc, fun d hd => ?_,
        fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans (fr1 a h0 (Or.inr (Or.inr (by omega))) h2)⟩
      · intro i hi
        rw [zdat i hi]
        exact congrArg _ (Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega)))
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
      exk (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 S c' (L + c') r (L + c' - 1) O ret t v5 v6
        ⟨by omega, by omega⟩ a1 a5 a6 (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inr hO.1) hv5 hv6 m8 m16 m40 m48
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s0)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s760)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s752)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s744)
        hret hjt hbt (fun a h1 h2 => H1.st a (by omega) (by omega)) (fun a h1 h2 => H1.st a (by omega) (by omega))
    rw [show L + c' - 1 + 1 = L + c' by omega] at zO16
    have hlowh : ∀ a, a < 2147483648 → μ3.read a = μ1.read a := fun a h2 =>
      fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    have run13 := run1.trans run3
    refine Or.inl ⟨ω3, μ3, s', r, run13.mono (by unfold keySteps; omega), z0, z1, z5, z6, zO, zO8, zO16,
      ?_, ?_, ?_, ctx_congr_data H1 hcrm (fun a h1 _ => hlowh a h1) wr3, ⟨cr, hcrm, hcra, hcru, hcrs⟩,
      fun d hd => ?_, ?_⟩
    · intro i hi
      have := (chunk_in H1.wf hcrm hcru).2.2
      rw [Memory.readN_congr (fun j hj => hlowh _ (by rw [hcrs] at this; omega))]; exact dat1 i hi
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
/-- **Reading more than 48 keys into a fresh `Vec<[u8; 336]>`, the payload in the heap** (1300,
    `Designate`'s keys; GP v0.8.0 §B.7, each element 336 octets): as `vec_key336_heap` (the `HeapCtx`
    setting, the same stack bounds) for 48 < n with 336n < 2³⁰ − 64. The first 48 keys go into the
    block of the model's `alloc` of ⌈336·48/32⌉ units; then the later batches (`bloopk`) grow the
    buffer with `realloc` to exactly L + min(left, L) elements per batch until all n are read. Either
    the function returns to t with the `Vec` `{cap n, ptr q, len n}` at O (the capacity is exactly n),
    the keys at q in their in-memory layout (`keysRot`), q the data of an allocated chunk of
    ⌈336n/32⌉ + 1 units that is no allocated chunk of `s`, the context kept for the final state `s'`,
    every allocated chunk of `s` kept with its data, the reader advanced by 336n, the stack from sp up
    kept off the reader and O, memory below 196608 and the access of everything from S0 up kept; or
    the run reaches a failed allocator call (`Exhausts`): the first batch's `alloc` or one of the
    `realloc`s fails.

    *Not stated:* that the globals below the allocator (`Glob`) are kept, as `vec_key336_heap` states;
    `ReallocCall.realloc_call` does not record it. -/
theorem vec_key336_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + 336 * n ≤ c.addr + 32 * c.size)
    (hS : S0 + 1600 ≤ sp ∧ sp ≤ S1) (hsp : 2147485248 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 48 < n ∧ 336 * n < 1073741760) (hnl : 336 * n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap env) 1300 ω μ x t ω' μ' x
        (395000 + keySteps 48 (n - 48)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q (336 * n) = keysRot n (μ.readN ptr (336 * n)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 336 * n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 336 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (336 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (336 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 1300 ω μ x (395000 + keySteps 48 (n - 48)) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  -- the frame S = sp − 768 and the call of finish_grow for the first batch
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a10, a11, a12, a760, a752, a744, a24, aS, a8', a16, a32, a56, afr,
      ard, awr⟩ := p1b (p := p) (P := P) (R := refineContractK cap env) x ω μ (sp - 768) O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 (by rw [h1]; congr 1; omega) h5 h6 h7 h8 h9 ⟨hn.1, by omega⟩ (by omega) hv5 hv6
    (by omega) (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b32, b24, b16, b8'', bfr, brd, bwr⟩ := g1k (p := p) (P := P)
    (R := refineContractK cap env) x ω1 μ1 (sp - 808) (sp - 768 + 64) 48 36 n 48 ⟨by omega, by omega⟩ a0
    (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega) (by decide) (by omega)
    ⟨by decide, by decide⟩ (fun a h1 h2 => by rw [awr]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 808 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (bfr a h0 (by omega)).trans (afr a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [bwr, awr]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω2 μ2 s (sp - 808) (336 * 48) 1 pb S0 S1 H2
      b1 b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s1, ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ((Exhausts.of_alloc (run1.trans (run2.trans run3)) e7 hna).mono (by omega))
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (336 * 48 + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have hq32 : (q - 32) % 32 = 0 := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    have := tiles_mod _ _ ht _ hnew
    simp only at this
    have := H3.wf.2.1
    omega
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 808 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, d0, d1, d5, d6, d96, d104, d112, dfr, drd, dwr⟩ := g2 (p := p) (P := P)
    (R := refineContractK cap env) x ω3 μ3 (sp - 808) (sp - 768 + 64) (336 * 48) q 36 1424 n 48
    ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7 ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b32)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b24)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b16)
    (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact b8'')
    ⟨by decide, by decide, by decide⟩ jte_17 bs_1424
    (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
    (fun a h1 h2 => H3.st a (by omega) (by omega))
  have chain5 : ∀ a, sp - 768 ≤ a → a < sp → (a < sp - 768 + 64 ∨ sp - 768 + 88 ≤ a) →
      μ5.read a = μ1.read a := fun a h1 h2 h3 =>
    (dfr a (by omega) h3).trans ((hF a (by omega) (by omega)).trans (bfr a (by omega) (by omega)))
  -- to the element loop
  obtain ⟨ω6, μ6, run6, f1, f5, f40, f48, f32, efr, erd, ewr⟩ := p5b (p := p) (P := P)
    (R := refineContractK cap env) x ω5 μ5 (sp - 768) 48 48 48 q ⟨by omega, by omega⟩
    (d1.trans (congrArg _ (by omega))) d6 (by decide) (by decide) ⟨by decide, by decide⟩ (by omega) d96 d104
    (by rw [Memory.readN_congr (fun j hj => chain5 _ (by omega) (by omega) (by omega))]; exact a16)
    (by rw [Memory.readN_congr (fun j hj => chain5 _ (by omega) (by omega) (by omega))]; exact a32)
    (fun a h1 h2 => by rw [dwr]; exact H3.st a (by omega) (by omega))
  have chain6 : ∀ a, sp - 768 ≤ a → a < sp → (a < sp - 768 + 32 ∨ sp - 768 + 56 ≤ a) →
      (a < sp - 768 + 64 ∨ sp - 768 + 88 ≤ a) → μ6.read a = μ1.read a := fun a h1 h2 h3 h4 =>
    (efr a (by omega) h3).trans (chain5 a h1 h2 h4)
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (efr a h0 (by omega)).trans ((dfr a h0 (by omega)).trans
      ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (efr a (by omega) (by omega)).trans (dfr a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha =>
    (h63 a (by unfold InData at ha; omega)).trans ((kd cp hcpm hcpu a ha).trans
      (hlow a (by unfold InData at ha; omega) (Or.inl (by unfold InData at ha; omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [ewr, dwr]
  have rd36 : ∀ a, μ6.readable a = μ3.readable a := fun a => by rw [erd, drd]
  have hdq : ptr + 336 * 48 ≤ q ∨ q + 336 * 48 ≤ ptr := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  -- the first batch's keys
  obtain ⟨ω7, μ7, run7, g1, g5, g6, g32, gdat, gR0, gR8, gfr, grd, gwr⟩ :=
    kloop (p := p) (P := P) (R := refineContractK cap env) x (sp - 768) q 48 rd ptr len
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, hlen⟩ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)) hdq
      (Or.inl (by omega)) 48 0 ω6 μ6 f1 f5 (by decide) (by omega) f40 f48
      (by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a56)
      (by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a24)
      (by rw [show ptr + 336 * 0 = ptr by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]
          exact hR0)
      (by rw [show len - 336 * 0 = len by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]
          exact hR8)
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩)
      (fun a h1 h2 => by
        rw [rd36]; exact Memory.readable_of_writable (heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  have h7S : ∀ a, sp - 768 ≤ a → a < sp → (a < sp - 768 + 32 ∨ sp - 768 + 56 ≤ a) →
      (a < sp - 768 + 56 ∨ sp - 768 + 744 ≤ a) → μ7.read a = μ1.read a := fun a h1 h2 h3 h4 =>
    (gfr a (by omega) (Or.inr (by omega)) (by omega) h4 (Or.inl (by omega)) (Or.inr (by omega))).trans
      (chain6 a h1 h2 h3 (by omega))
  have h76 : ∀ a, sp - 768 + 40 ≤ a → a < sp - 768 + 56 → μ7.read a = μ6.read a := fun a h1 h2 =>
    gfr a (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl h2) (Or.inl (by omega)) (Or.inr (by omega))
  have h7hi : ∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (gfr a h0 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) h2
      (Or.inr (by omega))).trans (hhigh a h0 h1)
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 336 * 48 ≤ a) → μ7.read a = μ3.read a := fun a h1 h3 =>
    (gfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by omega)).trans (h63 a h1)
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
  have hrest := bloopk (p := p) (P := P) env cap hcap1 hcap x ω7 μ7 0 s1
    (fun d => d ∈ chunks s ∧ d.used = true) (sp - 768) O rd q 48 48 (n - 48) ptr len ret t v5 v6 pb S0 S1 H7
    ⟨_, hnew, by simp only; omega, rfl, rfl⟩ hK ⟨cp, ⟨hcpm, hcpu⟩, hcp1, by omega⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ g1 g5 g6 (by omega) (by omega) (by omega) (by omega) ⟨by omega, hlen⟩
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact aS)
    (by rw [show 48 + (n - 48) = n by omega,
          Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact a8')
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact a16)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact a24)
    g32
    (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega))]; exact f40)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact a760)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact a752)
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega))]; exact a744)
    hret hjt hbt hv5 hv6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hOr gR0 gR8
    (fun i hi => by
      rw [gdat i (by omega) hi, Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩),
        Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)])
  rcases hrest with ⟨ω', μ', s', q', run', y0, y1, y5, y6, yO, yO8, yO16, ydat, yR0, yR8, yH,
      ⟨cf, hcfm, hcfa, hcfu, hcfs⟩, yK, yfr⟩ | hex
  · have hn' : 48 + (n - 48) = n := by omega
    rw [hn'] at yO yO16 ydat yR0 yR8 hcfs
    have runAll := run17.trans run'
    obtain ⟨hfb, -, -⟩ := chunk_in yH.wf hcfm hcfu
    have hyb := yH.hb0
    have hcf : cf = ⟨q' - 32, (336 * n + 31) / 32 + 1, true⟩ := by
      obtain ⟨ca, cs, cu⟩ := cf
      simp only at hcfa hcfu hcfs
      rw [hcfu, hcfs]; congr 1; omega
    refine Or.inl ⟨q', s', ω', μ', runAll.mono (by omega), y0, by rw [y1]; congr 1; omega, y5, y6, yO, yO8,
      yO16, ?_, yR0, yR8, yH,
      fun c hc hu => (yK c ⟨hc, hu⟩).1, hcf ▸ hcfm, ?_, ?_, FreeStepsH.pagesOut H.bd runAll, ?_, ?_, ?_⟩
    · refine readN_of_keys μ μ' n q' ptr (fun k hk => ?_)
      rw [ydat k hk]
      exact congrArg _ (Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩))
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

end Services.Bootstrap.Decode.VecKey336
