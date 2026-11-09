import Services.Bootstrap.Decode.HeapCtx
import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.Decode.HashU64
import Services.Bootstrap.ReaderBig

/-!
# Decoding `count` hashes into a fresh `Vec<[u8; 32]>` (function 1764)

The function at 1764 takes a result slot (ω₇), the reader (ω₈) and a count n (ω₉), and reads n
32-octet values into a new `Vec`: chunks of at most 512 elements, each grown into by `finish_grow`
(32989), then one `read` (58434) of 32 octets a element into a stack buffer, copied to the `Vec`'s
block. On success it writes the `Vec` {capacity, pointer, length} to the slot.

Here: n ≤ 512 (one chunk, one allocation).
-/

namespace Services.Bootstrap.Decode.VecHash

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 1764 … 1875: with 1 ≤ n ≤ 512 elements asked, the function opens its 152-octet frame at
    S = ω₁ − 152 (return address, ω₅, ω₆ at S + 144, S + 136, S + 128; the reader at S + 32; the slot
    at S + 8; an empty `Vec` {0, 1, 0} at S + 40) and calls `finish_grow` for n elements of 32
    octets (result slot S + 96, return address 48). -/
theorem p1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 152)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : 1 ≤ n ∧ n ≤ 512)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1764 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 48 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (S + 96) ∧
      ω'[8] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat n ∧ ω'[11] = UInt64.ofNat 1 ∧
      ω'[12] = UInt64.ofNat 32 ∧
      μ'.readN (S + 144) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (S + 136) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (S + 128) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 rd ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 out ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧
      μ'.readN S 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 512 ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 152 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hn, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp

/-- 32989 … 33084 (`VecU8.g1` for elements of 32 octets): `finish_grow` with no old buffer and
    ω₁₀ = n ≥ 1 elements of 32 octets at alignment 1 opens its 40-octet frame at F = ω₁ − 40 and calls
    `alloc` (40494) for 32·n octets at alignment 1 (return address 1526). -/
theorem g1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat 1) (h12 : ω[12] = UInt64.ofNat 32)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hn : 1 ≤ n ∧ 32 * n < 4294967296)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40494 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1526 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat (32 * n) ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (32 * n) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h10, h11, h12, hF, hw, hr, hn, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- 1880 … 1976: `finish_grow` returned `Ok` (0 at S + 96) with the block q at S + 104: the function
    records the `Vec` {n, q, 0} (capacity at S + 40, pointer at S + 48), the chunk n at S + 16, zeroes
    S + 96 … S + 128 and calls the reader for 32 octets into S + 96 (return address 50). -/
theorem p5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat n)
    (hn : 1 ≤ n ∧ n ≤ 512) (hq : q < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (s96 : μ.readN (S + 96) 8 = Num.encodeLE 8 0) (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 n) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 512)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1880 ω μ x 58434 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 50 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 96) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < S + 16 ∨ S + 24 ≤ a) → (a < S + 40 ∨ S + 56 ≤ a) →
        (a < S + 96 ∨ S + 128 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rd8 : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r96 := rd8 _ 0 (by decide) s96
  have r104 := rd8 _ q hq s104
  have r0 := rd8 _ n (by omega) s0
  have r16 := rd8 _ 512 (by decide) s16
  have r32 := rd8 _ rd hrd s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, hn, r96, r104, r0, r16, r32, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals first | exact h1 | exact h5 | exact h6

/-- 1982 … 2016 then 1910 … 1976: a read of 32 octets into S + 96 succeeded (ω₇ = 0), the `Vec`
    {n, q, j} has room (j < n) and c ≥ 2 elements of the chunk are left (ω₆): the element is copied
    to q + 32·j, the length becomes j + 1, and the reader is called again for 32 octets into
    S + 96 (return address 50). -/
theorem i1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j c rd : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat c) (h7 : ω[7] = UInt64.ofNat 0)
    (hjn : j < n) (hn : n ≤ 512) (hc : 2 ≤ c ∧ c ≤ 512) (hq : q + 32 * n < 4294967296)
    (hqS : q + 32 * n ≤ S ∨ S + 152 ≤ q) (hrd : rd < 18446744073709551616)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwq : ∀ a, q + 32 * j ≤ a → a < q + 32 * j + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1982 ω μ x 58434 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 50 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (c - 1) ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 96) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (q + 32 * j) 32 = μ.readN (S + 96) 32 ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 (j + 1) ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 64 ≤ a) → (a < S + 64 ∨ S + 128 ≤ a) →
        (a < q + 32 * j ∨ q + 32 * j + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rd8 : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r40 := rd8 _ n (by omega) s40
  have r48 := rd8 _ q (by omega) s48
  have r56 := rd8 _ j (by omega) s56
  have r32 := rd8 _ rd hrd s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hS, hw, hr, hwq, hjn, hn, hc, hq, hqS, r40, r48, r56, r32, VecU8.rdN_writeN_same8,
      VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact h1
    all_goals (rw [show q + 32 * j = j * 32 + q by omega, show S + 104 = S + 96 + 8 by omega, show S + 112 = S + 96 + 16 by omega,
      show S + 120 = S + 96 + 24 by omega]; exact HashU64.copy4g _ _ (S + 96) (j * 32 + q) (by omega))

/-- 1982 … 2016, 1910 … 1951, 1840 … 1855, 2171 … 2197, 2138 … 2169: the read of the last element
    (j + 1 = n, the chunk's last, ω₆ = 1) succeeded: it is copied to q + 32·j, the length becomes n,
    nothing is left, and the function stores the `Vec` {n, q, n} at the slot `out` (capacity, pointer,
    length) and returns through its frame. -/
theorem i2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j out r0 t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat 1) (h7 : ω[7] = UInt64.ofNat 0)
    (hjn : j + 1 = n) (hn : n ≤ 512) (hq : q + 32 * n < 4294967296)
    (hqS : q + 32 * n ≤ S ∨ S + 152 ≤ q) (hout : out + 24 < 4294967296)
    (hoS : out + 24 ≤ S ∨ S + 152 ≤ out) (hoq : out + 24 ≤ q ∨ q + 32 * n ≤ out)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j) (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 out)
    (s144 : μ.readN (S + 144) 8 = Num.encodeLE 8 r0) (s136 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5)
    (s128 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true)
    (hwq : ∀ a, q + 32 * j ≤ a → a < q + 32 * j + 32 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1982 ω μ x t ω' μ' x 70 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN (q + 32 * j) 32 = μ.readN (S + 96) 32 ∧
      μ'.readN out 8 = Num.encodeLE 8 n ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 112 ≤ a) →
        (a < q + 32 * j ∨ q + 32 * j + 32 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 152 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have rd8 : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have r40 := rd8 _ n (by omega) s40
  have r48 := rd8 _ q (by omega) s48
  have r56 := rd8 _ j (by omega) s56
  have r24 := rd8 _ n (by omega) s24
  have r16 := rd8 _ n (by omega) s16
  have r8 := rd8 _ out (by omega) s8
  have r144 := rd8 _ r0 (by omega) s144
  have r136 := rd8 _ v5 hv5 s136
  have r128 := rd8 _ v6 hv6 s128
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hS, hw, hr, hwq, hwo, hjn, hn, hq, hqS, hout, hoS, hoq, r40, r48, r56, r24, r16, r8,
      r144, r136, r128, hret, hjt, hbt, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (rw [show q + 32 * j = j * 32 + q by omega, show S + 104 = S + 96 + 8 by omega,
      show S + 112 = S + 96 + 16 by omega,
      show S + 120 = S + 96 + 24 by omega]; exact HashU64.copy4g _ _ (S + 96) (j * 32 + q) (by omega))

/-- The state at each call of the reader in the element loop, after j of the n elements: the
    registers the call needs, the function's frame, the reader at element j, the elements from j on
    still in the payload, and the first j already in the block q. -/
structure LoopSt (S n q rd ptr len out r0 v5 v6 j : Nat) (P : Nat → List UInt8) (ω : Regs) (μ : Memory) :
    Prop where
  e0 : ω[0] = UInt64.ofNat 50
  e1 : ω[1] = UInt64.ofNat S
  e6 : ω[6] = UInt64.ofNat (n - j)
  e7 : ω[7] = UInt64.ofNat rd
  e8 : ω[8] = UInt64.ofNat (S + 96)
  e9 : ω[9] = UInt64.ofNat 32
  m40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n
  m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q
  m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j
  m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd
  m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n
  m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n
  m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 out
  m144 : μ.readN (S + 144) 8 = Num.encodeLE 8 r0
  m136 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5
  m128 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6
  R0 : μ.readN rd 8 = Num.encodeLE 8 (ptr + 32 * j)
  R8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len - 32 * j)
  pay : ∀ k, j ≤ k → k < n → μ.readN (ptr + 32 * k) 32 = P k
  done : ∀ k, k < j → μ.readN (q + 32 * k) 32 = P k
  ws : ∀ a, S - 88 ≤ a → a < S + 152 → μ.writable a = true
  wr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true
  wq : ∀ a, q ≤ a → a < q + 32 * n → μ.writable a = true
  wo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true
  rp : ∀ a, ptr ≤ a → a < ptr + 32 * n → μ.readable a = true

/-- The bounds and separations the element loop needs: the frame S − 88 … S + 152 (the function's
    and the reader's), the reader rd, the block q … q + 32·n, the slot out and the payload apart. -/
structure Bnd (S n q rd ptr len out : Nat) : Prop where
  hS : 65536 + 88 ≤ S ∧ S + 152 < 4294967296 ∧ S % 8 = 0
  hn : 1 ≤ n ∧ n ≤ 512
  hq : 65536 ≤ q ∧ q + 32 * n < 4294967296
  hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296
  hptr : 65536 ≤ ptr ∧ ptr + 32 * n + 16 < 4294967296
  hlen : 32 * n ≤ len ∧ len < 4294967296
  hout : out + 24 < 4294967296
  rS : rd + 16 ≤ S - 88 ∨ S + 152 ≤ rd
  pS : ptr + 32 * n + 24 ≤ S - 88 ∨ S + 152 ≤ ptr
  qS : q + 32 * n ≤ S - 88 ∨ S + 152 ≤ q
  oS : out + 24 ≤ S - 88 ∨ S + 152 ≤ out
  rq : rd + 16 ≤ q ∨ q + 32 * n ≤ rd
  ro : rd + 16 ≤ out ∨ out + 24 ≤ rd
  oq : out + 24 ≤ q ∨ q + 32 * n ≤ out
  pq : ptr + 32 * n ≤ q ∨ q + 32 * n ≤ ptr
  pr : ptr + 32 * n ≤ rd ∨ rd + 16 ≤ ptr
  po : ptr + 32 * n ≤ out ∨ out + 24 ≤ ptr

/-- The memory the loop may change: the frames, the reader, the block and the slot. -/
def LFrame (S n q rd out : Nat) (μ μ' : Memory) : Prop :=
  (∀ a, a < 4294967296 → (a < S - 88 ∨ S + 152 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < q ∨ q + 32 * n ≤ a) →
    (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
  (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **One element, more to come**: from `LoopSt` after j < n − 1 elements, the reader reads element
    j into S + 96, the function copies it to q + 32·j, and calls the reader again: `LoopSt` after j + 1. -/
theorem one {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd ptr len out r0 v5 v6 j : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hj : j + 1 < n) (h : LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x 58434 ω' μ' x 520 ∧ LoopSt S n q rd ptr len out r0 v5 v6 (j + 1) Pl ω' μ' ∧
      LFrame S n q rd out μ μ' := by
  obtain ⟨hS1, hS2, hS3⟩ := B.hS
  have := B.hn; have := B.hq; have := B.hrd; have := B.hptr; have := B.hlen; have := B.hout
  have := B.rS; have := B.pS; have := B.qS; have := B.oS; have := B.rq; have := B.ro; have := B.oq
  have := B.pq; have := B.pr; have := B.po
  obtain ⟨e0, e1, e6, e7, e8, e9, m40, m48, m56, m32, m24, m16, m8, m144, m136, m128, R0, R8, pay, done, ws, wr,
    wq, wo, rp⟩ := h
  obtain ⟨ω1, μ1, run1, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ := read_big_sp (p := p) (P := P)
    (R := R) x ω μ 50 1982 S rd (S + 96) (ptr + 32 * j) (len - 32 * j) 32 e0 e1 e7 e8 e9 (by decide) jte_24 bs_1982
    ⟨by omega, by omega, by omega⟩ B.hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => ws a h1 (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
    (fun a h1 h2 => rp a (by omega) (by omega)) R0 R8
  have g' : ∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < S + 96 ∨ S + 128 ≤ a) → μ1.read a = μ.read a := fun a h0 h1 h2 h3 => gfr a h0 (by omega) h2 h3
  obtain ⟨ω2, μ2, run2, f0, f1, f6, f7, f8, f9, fcp, f56, ffr, frd, fwr⟩ := i1 (p := p) (P := P) (R := R) x ω1 μ1
    S n q j (n - j) rd ⟨by omega, by omega⟩ (g1.trans e1) (g6.trans e6) g7 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
    (by rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega) (by omega) (by omega))]; exact m40)
    (by rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega) (by omega) (by omega))]; exact m48)
    (by rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega) (by omega) (by omega))]; exact m56)
    (by rw [Memory.readN_congr (fun i hi => g' _ (by omega) (by omega) (by omega) (by omega))]; exact m32)
    (fun a h1 h2 => by rw [gwr]; exact ws a (by omega) h2)
    (fun a h1 h2 => by rw [gwr]; exact wq a (by omega) (by omega))
  have back : ∀ a, a < 4294967296 → (a < S - 88 ∨ S + 152 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < q + 32 * j ∨ q + 32 * j + 32 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (ffr a h0 (by omega) (by omega) h3).trans (g' a h0 (by omega) h2 (by omega))
  have hS' : ∀ a, S + 8 ≤ a → a < S + 56 ∨ S + 128 ≤ a → a < S + 152 → μ2.read a = μ.read a := fun a h1 h2 h3 =>
    (ffr a (by omega) (by omega) (by omega) (by omega)).trans (g' a (by omega) (by omega) (by omega) (by omega))
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), ⟨f0, f1, ?_, f7, f8, f9, ?_, ?_, f56, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact f6.trans (congrArg UInt64.ofNat (by omega))
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m40
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m48
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m32
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m24
  · rw [Memory.readN_congr (fun i hi => (ffr _ (by omega) (by omega) (by omega) (by omega)).trans
      (g' _ (by omega) (by omega) (by omega) (by omega)))]; exact m16
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m8
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m144
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m136
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m128
  · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega) (by omega))]
    exact gR0.trans (congrArg (Num.encodeLE 8) (by omega))
  · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega) (by omega))]
    exact gR8.trans (congrArg (Num.encodeLE 8) (by omega))
  · intro k h1 h2
    rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by omega))]
    exact pay k (by omega) h2
  · intro k hk
    rcases Nat.lt_or_ge k j with hk' | hk'
    · rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by omega))]
      exact done k hk'
    · rw [show k = j by omega, fcp, gbuf]; exact pay j (by omega) (by omega)
  · intro a h1 h2; rw [fwr, gwr]; exact ws a h1 h2
  · intro a h1 h2; rw [fwr, gwr]; exact wr a h1 h2
  · intro a h1 h2; rw [fwr, gwr]; exact wq a h1 h2
  · intro a h1 h2; rw [fwr, gwr]; exact wo a h1 h2
  · intro a h1 h2; rw [frd, grd]; exact rp a h1 h2
  · intro a h0 h1 h2 h3 h4; exact back a h0 h1 h2 (by omega)
  · intro a; rw [frd, grd]
  · intro a; rw [fwr, gwr]

/-- What the loop leaves when it returns: the function's return through its frame, the `Vec` {n, q, n}
    in the slot, all n elements in the block, and the reader past them. -/
def Done (S n q rd ptr len out r0 v5 v6 : Nat) (Pl : Nat → List UInt8) (μ0 : Memory) (ω' : Regs) (μ' : Memory) :
    Prop :=
  ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
    ω'[6] = UInt64.ofNat v6 ∧
    μ'.readN out 8 = Num.encodeLE 8 n ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
    μ'.readN (out + 16) 8 = Num.encodeLE 8 n ∧ (∀ k, k < n → μ'.readN (q + 32 * k) 32 = Pl k) ∧
    μ'.readN rd 8 = Num.encodeLE 8 (ptr + 32 * n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 32 * n) ∧
    LFrame S n q rd out μ0 μ'

/-- **The last element**: from `LoopSt` after n − 1 elements, the reader reads the last, the function
    copies it, stores the `Vec` and returns. -/
theorem last {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd ptr len out r0 t v5 v6 j : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hj : j + 1 = n) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (h : LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ) :
    ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x 550 ∧ Done S n q rd ptr len out r0 v5 v6 Pl μ ω' μ' := by
  obtain ⟨hS1, hS2, hS3⟩ := B.hS
  have := B.hn; have := B.hq; have := B.hrd; have := B.hptr; have := B.hlen; have := B.hout
  have := B.rS; have := B.pS; have := B.qS; have := B.oS; have := B.rq; have := B.ro; have := B.oq
  have := B.pq; have := B.pr; have := B.po
  obtain ⟨e0, e1, e6, e7, e8, e9, m40, m48, m56, m32, m24, m16, m8, m144, m136, m128, R0, R8, pay, done, ws, wr,
    wq, wo, rp⟩ := h
  obtain ⟨ω1, μ1, run1, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ := read_big_sp (p := p) (P := P)
    (R := R) x ω μ 50 1982 S rd (S + 96) (ptr + 32 * j) (len - 32 * j) 32 e0 e1 e7 e8 e9 (by decide) jte_24 bs_1982
    ⟨by omega, by omega, by omega⟩ B.hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => ws a h1 (by omega)) wr (fun a h1 h2 => ws a (by omega) (by omega))
    (fun a h1 h2 => rp a (by omega) (by omega)) R0 R8
  have g' : ∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < S + 96 ∨ S + 128 ≤ a) → μ1.read a = μ.read a := fun a h0 h1 h2 h3 => gfr a h0 (by omega) h2 h3
  have gS : ∀ a, S ≤ a → a < S + 96 ∨ S + 128 ≤ a → a < S + 152 → μ1.read a = μ.read a := fun a h1 h2 h3 =>
    g' a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, fcp, fo0, fo8, fo16, ffr, frd, fwr⟩ := i2 (p := p) (P := P) (R := R) x
    ω1 μ1 S n q j out r0 t v5 v6 ⟨by omega, by omega⟩ (g1.trans e1)
    (g6.trans (e6.trans (congrArg UInt64.ofNat (by omega)))) g7 hj (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hv5 hv6
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m40)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m48)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m56)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m24)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m16)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m8)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m144)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m136)
    (by rw [Memory.readN_congr (fun i hi => gS _ (by omega) (by omega) (by omega))]; exact m128)
    hret hjt hbt
    (fun a h1 h2 => by rw [gwr]; exact ws a (by omega) h2)
    (fun a h1 h2 => by rw [gwr]; exact wq a (by omega) (by omega))
    (fun a h1 h2 => by rw [gwr]; exact wo a h1 h2)
  have back : ∀ a, a < 4294967296 → (a < S - 88 ∨ S + 152 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < q + 32 * j ∨ q + 32 * j + 32 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 h3 h4 => (ffr a h0 (by omega) h3 h4).trans (g' a h0 (by omega) h2 (by omega))
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), f0, f1, f5, f6, fo0, fo8, fo16, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_or_ge k j with hk' | hk'
    · rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by omega) (by omega))]
      exact done k hk'
    · rw [show k = j by omega, fcp, gbuf]; exact pay j (by omega) (by omega)
  · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega) (by omega))]
    exact gR0.trans (congrArg (Num.encodeLE 8) (by omega))
  · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega) (by omega))]
    exact gR8.trans (congrArg (Num.encodeLE 8) (by omega))
  · intro a h0 h1 h2 h3 h4; exact back a h0 h1 h2 (by omega) h4
  · intro a; rw [frd, grd]
  · intro a; rw [fwr, gwr]

/-- **The element loop**: from `LoopSt` after j < n elements, the loop reads the rest and returns
    (`Done`). -/
theorem elems {p : ByteArray} {P : Program} [HasCode p P] (x : X)
    (S n q rd ptr len out r0 t v5 v6 : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true) :
    ∀ r j (ω : Regs) (μ : Memory), n - j = r → j < n → LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ →
      ∃ ω' μ', FreeStepsH p R 58434 ω μ x t ω' μ' x (550 * r) ∧ Done S n q rd ptr len out r0 v5 v6 Pl μ ω' μ' := by
  intro r
  induction r with
  | zero => intro j ω μ hr hj; omega
  | succ r ih =>
    intro j ω μ hr hj h
    by_cases hlast : j + 1 = n
    · obtain ⟨ω', μ', run, hd⟩ := last (p := p) (P := P) (R := R) x ω μ S n q rd ptr len out r0 t v5 v6 j Pl B
        hlast hv5 hv6 hret hjt hbt h
      exact ⟨ω', μ', run.mono (by rw [Nat.mul_succ]; omega), hd⟩
    · obtain ⟨ω1, μ1, run1, h1, f1⟩ := one (p := p) (P := P) (R := R) x ω μ S n q rd ptr len out r0 v5 v6 j Pl B
        (by omega) h
      obtain ⟨ω2, μ2, run2, d0, d1, d5, d6, dO, dO8, dO16, dall, dR0, dR8, f2⟩ :=
        ih (j + 1) ω1 μ1 (by omega) (by omega) h1
      exact ⟨ω2, μ2, (run1.trans run2).mono (by rw [Nat.mul_succ]; omega), d0, d1, d5, d6, dO, dO8, dO16, dall,
        dR0, dR8, fun a h0 ha hb hc hd => (f2.1 a h0 ha hb hc hd).trans (f1.1 a h0 ha hb hc hd),
        fun a => (f2.2.1 a).trans (f1.2.1 a), fun a => (f2.2.2 a).trans (f1.2.2 a)⟩

end Services.Bootstrap.Decode.VecHash
