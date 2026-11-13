import Services.Bootstrap.Decode.VecHash
import Services.Bootstrap.Decode.VecPairs

/-!
# `Vec<[u8; 32]>`: the hash reader at 907

The element reader at 907 (`RandomStorageAccumulate`'s `Ok` payload, GP v0.8.0 §B.7: a sequence of
32-octet hashes) takes the result slot O (ω₇), the reader rd (ω₈) and the count n (ω₉) and reads n
32-octet elements into a fresh `Vec` (alignment 1, element size 32): it reserves min(n, 512) elements
through `finish_grow` (32989), then per element reads 32 octets (58434) into a stack buffer and copies
them to the `Vec`'s block, and finally writes the `Vec` `{cap, ptr, len}` to O. Its code is that of the
function at 1764 (`VecHash`, 152-octet frame) shifted by −857 (the element loop) and −900 (the exit),
except for the jump-table return addresses (28 after `finish_grow`, 30 after a read).

Here: 1 ≤ n ≤ 512 (one reservation batch, one allocation).
-/

namespace Services.Bootstrap.Decode.VecHash32

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 907 … 1018: with 1 ≤ n ≤ 512 elements asked, the function opens its 152-octet frame at
    S = ω₁ − 152 (return address, ω₅, ω₆ at S + 144, S + 136, S + 128; the reader at S + 32; the slot
    at S + 8; an empty `Vec` {0, 1, 0} at S + 40) and calls `finish_grow` for n elements of 32
    octets (result slot S + 96, return address 28). -/
theorem p1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 152)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : 1 ≤ n ∧ n ≤ 512)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 907 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 28 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (S + 96) ∧
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

/-- 1023 … 1119: `finish_grow` returned `Ok` (0 at S + 96) with the block q at S + 104: the function
    records the `Vec` {n, q, 0} (capacity at S + 40, pointer at S + 48), the chunk n at S + 16, zeroes
    S + 96 … S + 128 and calls the reader for 32 octets into S + 96 (return address 30). -/
theorem p5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat n)
    (hn : 1 ≤ n ∧ n ≤ 512) (hq : q < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (s96 : μ.readN (S + 96) 8 = Num.encodeLE 8 0) (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 q)
    (s0 : μ.readN S 8 = Num.encodeLE 8 n) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 512)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S ≤ a → a < S + 152 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1023 ω μ x 58434 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 30 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧
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

/-- 1125 … 1159 then 1053 … 1119: a read of 32 octets into S + 96 succeeded (ω₇ = 0), the `Vec`
    {n, q, j} has room (j < n) and c ≥ 2 elements of the chunk are left (ω₆): the element is copied
    to q + 32·j, the length becomes j + 1, and the reader is called again for 32 octets into
    S + 96 (return address 30). -/
theorem i1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j c rd : Nat) (hS : 65536 ≤ S ∧ S + 152 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat c) (h7 : ω[7] = UInt64.ofNat 0)
    (hjn : j < n) (hn : n ≤ 512) (hc : 2 ≤ c ∧ c ≤ 512) (hq : q + 32 * n < 4294967296)
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

/-- 1125 … 1159, 1053 … 1094, 983 … 998, 1271 … 1297, 1238 … 1269: the read of the last element
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
    ∃ ω' μ', FreeStepsH p R 1125 ω μ x t ω' μ' x 70 ∧
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
  e0 : ω[0] = UInt64.ofNat 30
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
    (R := R) x ω μ 30 1125 S rd (S + 96) (ptr + 32 * j) (len - 32 * j) 32 e0 e1 e7 e8 e9 (by decide) jte_14 bs_1125
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
    (R := R) x ω μ 30 1125 S rd (S + 96) (ptr + 32 * j) (len - 32 * j) 32 e0 e1 e7 e8 e9 (by decide) jte_14 bs_1125
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


/-- n consecutive 32-octet elements equal one by one make the whole 32·n octets equal. -/
theorem readN_of_elems (μ μ' : Memory) (q ptr : Nat) :
    ∀ n, (∀ k, k < n → μ'.readN (q + 32 * k) 32 = μ.readN (ptr + 32 * k) 32) →
      μ'.readN q (32 * n) = μ.readN ptr (32 * n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [Nat.mul_succ, Memory.readN_split, Memory.readN_split, ih (fun k hk => h k (by omega)), h n (by omega)]

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.LoopA in
/-- **Reading 1 … 512 hashes into a fresh `Vec<[u8; 32]>`, the payload in the heap** (907,
    `RandomStorageAccumulate`'s `Ok` payload; GP v0.8.0 §B.7, each element 32 octets): with ω₇ = O,
    ω₈ = rd, ω₉ = n, the allocator's context `HeapCtx` (under `refineContractK cap`, cap ≥ 2²⁷) and the
    32n payload octets inside an allocated chunk's data, either the model's `alloc` of ⌈32n/32⌉ = n
    units gives `(q, s')` and the reader returns to t with the `Vec` `{cap n, ptr q, len n}` at O (the
    capacity at O, the pointer at O + 8, the length at O + 16), the 32n payload octets at q, the reader
    advanced by 32n, the context kept for `s'` and every allocated chunk of `s` kept with its data; or
    the model's `alloc` fails and the run reaches the `alloc` wrapper's return (40611) with null. -/
theorem vec_hash32_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + 32 * n ≤ c.addr + 32 * c.size)
    (hS : S0 + 360 ≤ sp ∧ sp ≤ S1) (hsp : 2147484008 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ n ∧ n ≤ 512) (hnl : 32 * n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((32 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 907 ω μ x t ω' μ' x (550 * n + 700) ∧
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    (alloc (growTo pb) hb 1 ((32 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 907 ω μ x 40611 ω' μ' x (550 * n + 700) ∧
      ω'[7] = UInt64.ofNat 0) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  -- the frame S = sp − 152 and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a10, a11, a12, a144, a136, a128, a32, a8', a5, a6, aS, a16, a24, a56, afr,
      ard, awr⟩ := p1 (p := p) (P := P) (R := refineContractK cap env) x ω μ (sp - 152) O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 (by rw [h1]; congr 1; omega) h5 h6 h7 h8 h9 hn (by omega) hv5 hv6 (by omega) (by omega)
    (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b32, b24, b16, b8'', bfr, brd, bwr⟩ := VecHash.g1 (p := p) (P := P)
    (R := refineContractK cap env) x ω1 μ1 (sp - 192) (sp - 152 + 96) n 28 n n ⟨by omega, by omega⟩ a0
    (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega) (by omega) (by omega)
    ⟨hn.1, by omega⟩ (fun a h1 h2 => by rw [awr]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 192 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (bfr a h0 (by omega)).trans (afr a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [bwr, awr]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 192) (32 * n) 1 pb S0 S1 H2 b1
      b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ⟨hna, ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), e7⟩
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (32 * n + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  rw [hbase'] at hqb hqT hqT'
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 192 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, d0, d1, d5, d6, d96, d104, d112, dfr, drd, dwr⟩ := g2 (p := p) (P := P)
    (R := refineContractK cap env) x ω3 μ3 (sp - 192) (sp - 152 + 96) (32 * n) q 28 1023 n n ⟨by omega, by omega⟩
    (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7 ⟨by omega, by omega⟩ (by omega) (by omega)
    (by omega)
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
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, f40, f48, f16, efr, erd, ewr⟩ := p5 (p := p) (P := P)
    (R := refineContractK cap env) x ω5 μ5 (sp - 152) n q rd ⟨by omega, by omega⟩
    (d1.trans (congrArg _ (by omega))) d5 d6 hn (by omega) (by omega) d96 d104
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
  have rd36 : ∀ a, μ6.readable a = μ3.readable a := fun a => by rw [erd, drd]
  have hdq : ptr + 32 * n ≤ q ∨ q + 32 * n ≤ ptr := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  -- the loop
  have L : LoopSt (sp - 152) n q rd ptr len O ret v5 v6 0 (fun k => μ.readN (ptr + 32 * k) 32) ω6 μ6 :=
    ⟨f0, f1, f6.trans (congrArg _ (by omega)), f7, f8, f9, f40, f48,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a56,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a32,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a24,
      f16,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a8',
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a144,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a136,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact a128,
      by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0.trans (congrArg _ (by omega)),
      by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8.trans (congrArg _ (by omega)),
      fun k _ hk => Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩),
      fun k hk => absurd hk (Nat.not_lt_zero _),
      fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega),
      fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega),
      fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩,
      fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega),
      fun a h1 h2 => by
        rw [rd36]; exact Memory.readable_of_writable (heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩)⟩
  have B : Bnd (sp - 152) n q rd ptr len O :=
    ⟨⟨by omega, by omega, by omega⟩, hn, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
      ⟨hnl, hlen⟩, by omega, Or.inr (by omega), Or.inl (by omega), Or.inl (by omega), Or.inr (by omega),
      Or.inr (by omega), hOr.symm, Or.inr (by omega), hdq, Or.inl (by omega), Or.inl (by omega)⟩
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, gO, gO8, gO16, gall, gR0, gR8, gfr⟩ := elems (p := p) (P := P)
    (R := refineContractK cap env) x (sp - 152) n q rd ptr len O ret t v5 v6 _ B hv5 hv6 hret hjt hbt n 0 ω6 μ6
    (by omega) hn.1 L
  -- the heap after the loop
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 32 * n ≤ a) → μ7.read a = μ3.read a := fun a h1 h3 =>
    (gfr.1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3 (Or.inl (by omega))).trans (h63 a h1)
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  have wr7 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [gfr.2.2, wr36]
  refine Or.inl ⟨q, s', ω7, μ7, ha, run17.mono (by omega), g0, by rw [g1]; congr 1; omega, g5, g6, gO, gO8, gO16,
    ?_, gR0, gR8, ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr7, keep, hnew,
    hfresh, ?_, FreeStepsH.pagesOut H.bd run17, ?_, ?_, ?_, ?_⟩
  · exact readN_of_elems μ μ7 q ptr n gall
  · intro d hd hu a ha
    have hdis := data_disj H3.wf (keep d hd hu) hnew (hfresh d hd hu) ha
    simp only at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlowh a (by omega) (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a h0 h1 h2 h3
    rw [gfr.1 a h0 (Or.inr (by omega)) h2 (Or.inr (by omega)) h3]
    exact hhigh a h0 h1
  · intro a ha'
    obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run17
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
    unfold Memory.readable
    rw [kp _ (Or.inl (by unfold pageSize; omega))]
  · intro a ha'
    have hg := ha'
    unfold Glob at hg
    have ht3 := H3.wf.2.2.2.1
    unfold TilesOk at ht3
    have hb3 := H3.hb0
    rw [hlowh a (by omega) (Or.inl (by omega)),
      hk.glob (fun b ⟨c, hc, e⟩ => Or.inr (by have := (ht3.mem_lt c hc).1; omega)) a ha']
    exact hlow a (by omega) (Or.inl (by omega))
  · intro a ha'
    obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd run17
    have := H.hSb
    unfold Memory.writable
    rw [kp _ (Or.inr (by unfold pageSize; omega))]

end Services.Bootstrap.Decode.VecHash32
