import Services.Bootstrap.Decode.VecHash32
import Services.Bootstrap.Decode.Key336Memcpy
import Services.Bootstrap.Memzero

/-!
# `Vec<[u8; 336]>`: the key reader at 1300

The element reader at 1300 (`Designate`'s keys, GP v0.8.0 §B.7: a sequence of 336-octet validator
keys) takes the result slot O (ω₇), the reader rd (ω₈) and the count n (ω₉) and reads n keys into a
fresh `Vec` (alignment 1, element size 336), with a 768-octet frame at S = sp − 768: it reserves
min(n, 48) elements through `finish_grow` (32989), then per element runs the key decoder (1496 …
1547, then 35493 … 35821, a 696-octet frame at K = S − 696) into the slot S + 64, copies the key from
S + 65 to S + 408 (`memcpy`, 68729) and from there to the `Vec`'s block, and finally writes the `Vec`
`{cap, ptr, len}` to O.

The key decoder reads the key's four fields in payload order, 32 octets (58434) into K, 32 into K,
144 into K and 128 into K + 544, and assembles the key at K as the last field (128 octets) followed by
the first three (32 + 32 + 144): Rust's layout of the key struct, which puts its largest field first.
So each 336-octet element in the block is its payload octets rotated: `keyRot e = e.drop 208 ++
e.take 208`.

Here: 1 ≤ n ≤ 48 (one reservation batch, one allocation).
-/

namespace Services.Bootstrap.Decode.VecKey336

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Key336Memcpy

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {X : Type} {R : HostRel X}

theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- 1300 … 1419: with 1 ≤ n ≤ 48 keys asked, the function opens its 768-octet frame at S = ω₁ − 768
    (return address, ω₅, ω₆ at S + 760, S + 752, S + 744; the reader at S + 24; the slot at S; an empty
    `Vec` {0, 1, 0} at S + 40) and calls `finish_grow` for n elements of 336 octets (result slot S + 64,
    return address 36). -/
theorem p1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S out rd n r0 v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (S + 768)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n) (hn : 1 ≤ n ∧ n ≤ 48)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1300 ω μ x 32989 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 36 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧
      ω'[7] = UInt64.ofNat (S + 64) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat n ∧
      ω'[11] = UInt64.ofNat 1 ∧ ω'[12] = UInt64.ofNat 336 ∧
      μ'.readN (S + 760) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (S + 752) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (S + 744) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (S + 24) 8 = Num.encodeLE 8 rd ∧
      μ'.readN S 8 = Num.encodeLE 8 out ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 48 ∧
      μ'.readN (S + 56) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 768 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hn, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_,
      fun a => ?_, fun a => ?_⟩
    post_simp

/-- 32989 … 33084, `finish_grow` with no old buffer (ω₈ = 0) for 1 ≤ n ≤ 48 elements of 336 octets at
    alignment 1: as `VecPairs.g1e`, it calls `alloc` (40494) for 336·n octets (return address 1526). -/
theorem g1k {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (F res n r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat n) (h11 : ω[11] = UInt64.ofNat 1) (h12 : ω[12] = UInt64.ofNat 336)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hn : 1 ≤ n ∧ n ≤ 48)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40494 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1526 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat (336 * n) ∧ ω'[8] = UInt64.ofNat 1 ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (336 * n) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : 336 * n < 274877906944 := by omega
  have hEn0 : ¬ 336 * n = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h10, h11, h12, hF, hw, hr, hn, hEn, hEn0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
      PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
      PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
    all_goals first
      | (rw [VecU8.rdN_writeN_same8 _ _ _ (by omega), Nat.mod_eq_of_lt (by omega)])
      | (rw [VecU8.rdN_writeN_lit _ _ _ (by rfl) (by omega)]; rfl)

/-- 1424 … 1450: `finish_grow` returned `Ok` (0 at S + 64) with the block q at S + 72: the function
    records the `Vec` {n, q, 0} (capacity at S + 40, pointer at S + 48), keeps q at S + 32 and goes to
    the element loop (1495) with the n elements of the batch in ω₅. -/
theorem p5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat n) (hn : 1 ≤ n ∧ n ≤ 48)
    (hq : q < 18446744073709551616)
    (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 0) (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 q)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n) (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 48)
    (hw : ∀ a, S ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1424 ω μ x 1495 ω' μ' x 15 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat n ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 n ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → (a < S + 32 ∨ S + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r64 := rd8 (by decide) s64
  have r72 := rd8 hq s72
  have r16 := rd8 (by omega) s16
  have r32 := rd8 (by decide) s32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, hw, hr, hn, r64, r72, r16, r32, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals first | exact h1 | exact h6

/-- 1495 … 1547: an element (c ≥ 1 of the batch left in ω₅): the key decoder is entered with its
    696-octet frame at K = S − 696 (return address 40, ω₅ = c and ω₆ at K + 688, K + 680, K + 672), the
    slot S + 64 in ω₅ and the reader (from S + 24) in ω₆; it zeroes K … K + 32 and calls the reader
    for 32 octets into K (return address 1656). -/
theorem e0 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S c v rd : Nat) (hS : 65536 + 696 ≤ S ∧ S + 768 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat c) (h6 : ω[6] = UInt64.ofNat v)
    (hc : c < 18446744073709551616) (hv : v < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd)
    (hw : ∀ a, S - 696 ≤ a → a < S + 768 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x 58434 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 1656 ∧ ω'[1] = UInt64.ofNat (S - 696) ∧ ω'[5] = UInt64.ofNat (S + 64) ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S - 696) ∧
      ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (S - 696 + 688) 8 = Num.encodeLE 8 40 ∧ μ'.readN (S - 696 + 680) 8 = Num.encodeLE 8 c ∧
      μ'.readN (S - 696 + 672) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S - 696 ∨ S - 696 + 32 ≤ a) → (a < S - 24 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S - 696 ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r24 := rd8 hrd s24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r24, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show S - 696 + 688 = S - 8 by omega, show S - 696 + 680 = S - 16 by omega,
      show S - 696 + 672 = S - 24 by omega])
    post_simp

/-- 35493 … 35542: the first field's read succeeded (ω₇ = 0): its 32 octets are copied from K to
    K + 336, K … K + 32 is zeroed, and the reader is called for 32 octets into K (return address 1658). -/
theorem k1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K rd : Nat) (hrd : rd < 18446744073709551616) (hK : 65536 ≤ K ∧ K + 696 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat K) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, K ≤ a → a < K + 696 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35493 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1658 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat K ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (K + 336) 32 = μ.readN K 32 ∧
      (∀ a, a < 4294967296 → (a < K ∨ K + 32 ≤ a) → (a < K + 336 ∨ K + 368 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, K ≤ a → a < K + 696 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hK, hw, hr, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact h1
    all_goals try exact h6
    all_goals (rw [show K + 344 = K + 336 + 8 by omega, show K + 352 = K + 336 + 16 by omega,
      show K + 360 = K + 336 + 24 by omega]; exact HashU64.copy4g _ _ K (K + 336) (by omega))

/-- 35548 … 35586: the second field's read succeeded: its 32 octets are copied from K to K + 368, and
    `memset` is called to zero K … K + 144 (return address 1660). -/
theorem k2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K : Nat) (hK : 65536 ≤ K ∧ K + 696 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat K) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, K ≤ a → a < K + 696 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35548 ω μ x 70133 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1660 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat K ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 144 ∧
      μ'.readN (K + 368) 32 = μ.readN K 32 ∧
      (∀ a, a < 4294967296 → (a < K + 368 ∨ K + 400 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, K ≤ a → a < K + 696 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hK, hw, hr, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact h1
    all_goals (rw [show K + 376 = K + 368 + 8 by omega, show K + 384 = K + 368 + 16 by omega,
      show K + 392 = K + 368 + 24 by omega]; exact HashU64.copy4g _ _ K (K + 368) (by omega))

/-- 35593 … 35601: the reader is called for 144 octets into K (return address 1662). -/
theorem k3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K rd : Nat) (hrd : rd < 18446744073709551616) (hK : K < 4294967296) (h1 : ω[1] = UInt64.ofNat K) (h6 : ω[6] = UInt64.ofNat rd) :
    ∃ ω', FreeStepsH p R 35593 ω μ x 58434 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1662 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat K ∧ ω'[9] = UInt64.ofNat 144 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1 | exact h6 | skip

/-- 35607 … 35620: the third field's read succeeded: `memcpy` is called to copy K … K + 144 to K + 400
    (return address 1664). -/
theorem k4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K : Nat) (hK : K + 696 < 4294967296) (h1 : ω[1] = UInt64.ofNat K) (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 35607 ω μ x 68729 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1664 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (K + 400) ∧ ω'[8] = UInt64.ofNat K ∧ ω'[9] = UInt64.ofNat 144 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1

/-- 35627 … 35637: `memset` is called to zero K + 544 … K + 672 (return address 1666). -/
theorem k5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K : Nat) (hK : K + 696 < 4294967296) (h1 : ω[1] = UInt64.ofNat K) :
    ∃ ω', FreeStepsH p R 35627 ω μ x 70133 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1666 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (K + 544) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1

/-- 35644 … 35654: the reader is called for 128 octets into K + 544 (return address 1668). -/
theorem k6 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K rd : Nat) (hrd : rd < 18446744073709551616) (hK : K + 696 < 4294967296) (h1 : ω[1] = UInt64.ofNat K) (h6 : ω[6] = UInt64.ofNat rd) :
    ∃ ω', FreeStepsH p R 35644 ω μ x 58434 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1668 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (K + 544) ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1 | exact h6 | skip

/-- 35660, 35687 … 35697: the last field's read succeeded: `memcpy` is called to copy K + 544 … K + 672
    to K (return address 1670). -/
theorem k7 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K : Nat) (hK : K + 696 < 4294967296) (h1 : ω[1] = UInt64.ofNat K) (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 35660 ω μ x 68729 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 1670 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat K ∧ ω'[8] = UInt64.ofNat (K + 544) ∧ ω'[9] = UInt64.ofNat 128 := by
  have h7' : (ω[7]).toNat = 0 := by rw [h7]; rfl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, h7']
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1

/-- 35704 … 35780: the first two fields are copied from K + 336 and K + 368 to K + 128 and K + 160, and
    `memcpy` is called to copy K + 400 … K + 544 to K + 192 (return address 1672). -/
theorem k8 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K : Nat) (hK : 65536 ≤ K ∧ K + 696 < 4294967296) (h1 : ω[1] = UInt64.ofNat K)
    (hw : ∀ a, K ≤ a → a < K + 696 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 35704 ω μ x 68729 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1672 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (K + 192) ∧ ω'[8] = UInt64.ofNat (K + 400) ∧ ω'[9] = UInt64.ofNat 144 ∧
      μ'.readN (K + 128) 32 = μ.readN (K + 336) 32 ∧ μ'.readN (K + 160) 32 = μ.readN (K + 368) 32 ∧
      (∀ a, a < 4294967296 → (a < K + 128 ∨ K + 192 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, K ≤ a → a < K + 696 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hK, hw, hr, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact h1
    · rw [show K + 136 = K + 128 + 8 by omega, show K + 144 = K + 128 + 16 by omega,
        show K + 152 = K + 128 + 24 by omega, show K + 344 = K + 336 + 8 by omega,
        show K + 352 = K + 336 + 16 by omega, show K + 360 = K + 336 + 24 by omega]
      exact HashU64.copy4g _ _ (K + 336) (K + 128) (by omega)
    · rw [show K + 168 = K + 160 + 8 by omega, show K + 176 = K + 160 + 16 by omega,
        show K + 184 = K + 160 + 24 by omega, show K + 376 = K + 368 + 8 by omega,
        show K + 384 = K + 368 + 16 by omega, show K + 392 = K + 368 + 24 by omega]
      exact HashU64.copy4g _ _ (K + 368) (K + 160) (by omega)

/-- 35787 … 35796: `memcpy` is called to copy the assembled key K … K + 336 to o + 1, after the slot's
    tag octet o (ω₅; return address 1674). -/
theorem k9 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K o : Nat) (hK : K < 4294967296) (ho : o + 1 < 4294967296) (h1 : ω[1] = UInt64.ofNat K)
    (h5 : ω[5] = UInt64.ofNat o) :
    ∃ ω', FreeStepsH p R 35787 ω μ x 68729 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1674 ∧ ω'[1] = UInt64.ofNat K ∧ ω'[5] = UInt64.ofNat o ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (o + 1) ∧ ω'[8] = UInt64.ofNat K ∧ ω'[9] = UInt64.ofNat 336 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1 | exact h5

/-- 35803 … 35821: the slot's tag octet o becomes 0 (`Ok`), ω₀, ω₅, ω₆ are restored from K + 688,
    K + 680, K + 672, the frame is closed and the decoder returns (return address 40, to 1551). -/
theorem k10 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (K o c v : Nat) (hK : 65536 ≤ K ∧ K + 696 < 4294967296) (ho : o < 4294967296)
    (hoK : o + 1 ≤ K + 672 ∨ K + 696 ≤ o)
    (h1 : ω[1] = UInt64.ofNat K) (h5 : ω[5] = UInt64.ofNat o)
    (hc : c < 18446744073709551616) (hv : v < 18446744073709551616)
    (s0 : μ.readN (K + 688) 8 = Num.encodeLE 8 40) (s5 : μ.readN (K + 680) 8 = Num.encodeLE 8 c)
    (s6 : μ.readN (K + 672) 8 = Num.encodeLE 8 v)
    (hr : ∀ a, K + 672 ≤ a → a < K + 696 → μ.readable a = true) (hwo : μ.writable o = true) :
    ∃ ω' μ', FreeStepsH p R 35803 ω μ x 1551 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 40 ∧ ω'[1] = UInt64.ofNat (K + 696) ∧ ω'[5] = UInt64.ofNat c ∧
      ω'[6] = UInt64.ofNat v ∧ rdN μ' o 1 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ o → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by decide) s0
  have r5 := rd8 hc s5
  have r6 := rd8 hv s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hK, ho, hoK, hwo, hr, r0, r5, r6, jte_19, bs_1551, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (unfold rdN; rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp only [two32, List.length_cons, List.length_nil]; omega)]; rfl)

/-- 1551 … 1568: the key decoder returned `Ok` (the octet 0 at S + 64): `memcpy` is called to copy the
    key S + 65 … S + 401 to S + 408 (return address 42). -/
theorem b1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S : Nat) (hS : S + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h64 : rdN μ (S + 64) 1 = 0)
    (hr : μ.readable (S + 64) = true) :
    ∃ ω', FreeStepsH p R 1551 ω μ x 68729 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 42 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 408) ∧ ω'[8] = UInt64.ofNat (S + 65) ∧ ω'[9] = UInt64.ofNat 336 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h64, hr, hS, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals first | exact h1 | skip

/-- 1574 … 1577, 1455 … 1477: the `Vec` {n, q, j} has room (j < n): `memcpy` is called to copy the key
    S + 408 … S + 744 to q + 336·j (return address 38), with j in ω₆ and q kept at S + 32. -/
theorem b2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hjn : j < n) (hn : n ≤ 48) (hq : q + 336 * n < 4294967296)
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

/-- 1483 … 1492: the key was copied; c ≥ 2 elements of the batch are left: the length becomes j + 1
    (at S + 56) and the loop goes on (1495) with c − 1 in ω₅. -/
theorem b3a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S j c : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat c) (h6 : ω[6] = UInt64.ofNat j) (hc : 2 ≤ c ∧ c ≤ 48) (hj : j < 48)
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

/-- 1483 … 1492, 1380 … 1398, 1736 … 1758, 1703 … 1734: the last key was copied (c = 1, j + 1 = n):
    the batch is done and nothing is left, so the function stores the `Vec` {n, q, n} at the slot
    `out` (capacity, pointer, length) and returns through its frame. -/
theorem b3b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q j out r0 t v5 v6 : Nat) (hS : 65536 ≤ S ∧ S + 768 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 1) (h6 : ω[6] = UInt64.ofNat j)
    (hjn : j + 1 = n) (hn : n ≤ 48) (hq : q < 4294967296) (hout : out + 24 < 4294967296)
    (hoS : out + 24 ≤ S ∨ S + 768 ≤ out)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n) (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n)
    (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q)
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
      μ'.readN out 8 = Num.encodeLE 8 n ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 n ∧
      (∀ a, a < 4294967296 → (a < S + 56 ∨ S + 80 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 768 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r8 := rd8 (by omega) s8
  have r16 := rd8 (by omega) s16
  have r40 := rd8 (by omega) s40
  have r48 := rd8 (by omega) s48
  have r0' := rd8 (by omega) s0
  have r760 := rd8 (by omega) s760
  have r752 := rd8 hv5 s752
  have r744 := rd8 hv6 s744
  have hn' : ¬ n = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, hwo, hout, hoS, hjn, hn, hn', r8, r16, r40, r48, r0', r760, r752, r744,
      hret, hjt, hbt, VecU8.rdN_writeN_same8, VecU8.rdN_writeN_lit, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp

/-- A key's in-memory layout (Rust's layout of the key struct): its last 128 octets (the metadata,
    GP v0.8.0 §6.3), then its first 208 (the Bandersnatch, Ed25519 and BLS keys). -/
def keyRot (e : List UInt8) : List UInt8 := e.drop 208 ++ e.take 208

theorem keyRot_readN (μ : Memory) (a : Nat) :
    keyRot (μ.readN a 336) = μ.readN (a + 208) 128 ++ μ.readN a 208 := by
  rw [show (336 : Nat) = 208 + 128 from rfl, Memory.readN_split]
  unfold keyRot
  rw [List.drop_left' (Memory.length_readN _ _ _), List.take_left' (Memory.length_readN _ _ _)]

/-- **The key decoder** (1495 … 1547, 35493 … 35821): from the element loop with the reader at rd
    (at S + 24) holding a payload `{pp, ll}` with at least 336 octets, it reads the key's four fields
    (32, 32, 144 and 128 octets) and returns to 1551 with `Ok` (the octet 0 at S + 64) and the key at
    S + 65 in its in-memory layout (`keyRot`), the reader advanced by 336, ω₁, ω₅, ω₆ as they were.
    Memory changes only in S − 784 … S (the decoder's and its callees' frames), S + 64 … S + 401 and
    the reader. -/
theorem key {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S c v rd pp ll : Nat) (hS : 65536 + 784 ≤ S ∧ S + 768 < 4294967296 ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat c) (h6 : ω[6] = UInt64.ofNat v)
    (hc : c < 18446744073709551616) (hv : v < 18446744073709551616)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hpp : 65536 ≤ pp ∧ pp + 336 + 16 < 4294967296)
    (hll : 336 ≤ ll ∧ ll < 4294967296)
    (hrS : rd + 16 ≤ S - 784 ∨ S + 768 ≤ rd) (hpS : pp + 336 + 24 ≤ S - 784 ∨ S + 768 ≤ pp)
    (hpr : pp + 336 ≤ rd ∨ rd + 16 ≤ pp)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 pp) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 ll)
    (hws : ∀ a, S - 784 ≤ a → a < S + 768 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hrp : ∀ a, pp ≤ a → a < pp + 336 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x 1551 ω' μ' x 6100 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat c ∧ ω'[6] = UInt64.ofNat v ∧
      rdN μ' (S + 64) 1 = 0 ∧ μ'.readN (S + 65) 336 = keyRot (μ.readN pp 336) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (pp + 336) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (ll - 336) ∧
      (∀ a, a < 4294967296 → (a < S - 784 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < S + 64 ∨ S + 401 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  -- the decoder's entry
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a688, a680, a672, afr, ard, awr⟩ :=
    e0 (p := p) (P := P) (R := R) x ω μ S c v rd ⟨by omega, by omega⟩ h1 h5 h6 hc hv (by omega) s24
      (fun a h1 h2 => hws a (by omega) h2)
  have F1 : ∀ a, a < 4294967296 → (a < S - 784 ∨ S ≤ a) → μ1.read a = μ.read a :=
    fun a h0 h1 => afr a h0 (by omega) (by omega)
  -- field 1: 32 octets into K
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ := read_big_sp (p := p) (P := P)
    (R := R) x ω1 μ1 1656 35493 (S - 696) rd (S - 696) pp ll 32 a0 a1 a7 a8 a9 (by decide) jte_827 bs_35493
    ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [awr]; exact hws a (by omega) (by omega)) (fun a h1 h2 => by rw [awr]; exact hwr a h1 h2)
    (fun a h1 h2 => by rw [awr]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [ard]; exact hrp a h1 (by omega))
    (by rw [Memory.readN_congr (fun j hj => F1 _ (by omega) (by omega))]; exact hR0)
    (by rw [Memory.readN_congr (fun j hj => F1 _ (by omega) (by omega))]; exact hR8)
  have hw2 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [gwr, awr]
  have hr2 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [grd, ard]
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, c336, cfr, crd, cwr⟩ := k1 (p := p) (P := P) (R := R) x ω2 μ2
    (S - 696) rd (by omega) ⟨by omega, by omega⟩ (g1.trans a1) (g6.trans a6) g7
    (fun a h1 h2 => by rw [hw2]; exact hws a (by omega) (by omega))
  -- field 2: 32 octets into K
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, dR0, dR8, dbuf, dfr, drd, dwr⟩ := read_big_sp (p := p) (P := P)
    (R := R) x ω3 μ3 1658 35548 (S - 696) rd (S - 696) (pp + 32) (ll - 32) 32 c0 c1 c7 c8 c9 (by decide) jte_828
    bs_35548 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [cwr, hw2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [cwr, hw2]; exact hwr a h1 h2)
    (fun a h1 h2 => by rw [cwr, hw2]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [crd, hr2]; exact hrp a (by omega) (by omega))
    (by rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega))]; exact gR0)
    (by rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have hw4 : ∀ a, μ4.writable a = μ.writable a := fun a => by rw [dwr, cwr, hw2]
  have hr4 : ∀ a, μ4.readable a = μ.readable a := fun a => by rw [drd, crd, hr2]
  obtain ⟨ω5, μ5, run5, e0', e1, e5, e6, e7, e8, e9, e368, efr, erd, ewr⟩ := k2 (p := p) (P := P) (R := R) x ω4 μ4
    (S - 696) ⟨by omega, by omega⟩ (d1.trans c1) d7 (fun a h1 h2 => by rw [hw4]; exact hws a (by omega) (by omega))
  -- zero K … K + 144
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, -, ffr, frd, fwr⟩ := Memzero.memzero (p := p) (P := P) (R := R) x ω5 μ5
    (S - 696) 144 1660 35593 (by omega) ⟨by decide, by decide⟩ (by omega) e0' e7 e8 e9 (by decide) jte_829
    bs_35593 (fun a h1 h2 => by rw [ewr, hw4]; exact hws a (by omega) (by omega))
  have hw6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [fwr, ewr, hw4]
  have hr6 : ∀ a, μ6.readable a = μ.readable a := fun a => by rw [frd, erd, hr4]
  have w6 : ω6[6] = UInt64.ofNat rd := f6.trans (e6.trans (d6.trans c6))
  obtain ⟨ω7, run7, k30, k31, k35, k36, k37, k38, k39⟩ := k3 (p := p) (P := P) (R := R) x ω6 μ6 (S - 696) rd
    (by omega) (by omega) (f1.trans e1) w6
  -- field 3: 144 octets into K
  have m6rd : ∀ a, rd ≤ a → a < rd + 16 → μ6.read a = μ4.read a := fun a h1 h2 =>
    (ffr _ (by omega) (by omega)).trans (efr _ (by omega) (by omega))
  obtain ⟨ω8, μ8, run8, g0', g1', g5', g6', g7', hR0', hR8', gbuf', gfr', grd', gwr'⟩ := read_big_sp (p := p)
    (P := P) (R := R) x ω7 μ6 1662 35607 (S - 696) rd (S - 696) (pp + 64) (ll - 64) 144 k30 k31 k37 k38 k39
    (by decide) jte_830 bs_35607 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [hw6]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hw6]; exact hwr a h1 h2)
    (fun a h1 h2 => by rw [hw6]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hr6]; exact hrp a (by omega) (by omega))
    (by rw [Memory.readN_congr (fun j hj => m6rd _ (by omega) (by omega))]; exact dR0.trans (congrArg _ (by omega)))
    (by rw [Memory.readN_congr (fun j hj => m6rd _ (by omega) (by omega))]; exact dR8.trans (congrArg _ (by omega)))
  have hw8 : ∀ a, μ8.writable a = μ.writable a := fun a => by rw [gwr', hw6]
  have hr8 : ∀ a, μ8.readable a = μ.readable a := fun a => by rw [grd', hr6]
  obtain ⟨ω9, run9, k40, k41, k45, k46, k47, k48, k49⟩ := k4 (p := p) (P := P) (R := R) x ω8 μ8 (S - 696)
    (by omega) (g1'.trans k31) g7'
  -- copy K … K + 144 to K + 400
  obtain ⟨ω10, μ10, run10, l0, l1, l5, l6, lcp, lfr, lrd, lwr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R) x
    ω9 μ8 1664 35627 (S - 696) (S - 696 + 400) (S - 696) 144 k40 k41 k47 k48 k49 (by decide) jte_831 bs_35627
    ⟨by omega, by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (fun a h1 h2 => by rw [hr8]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [hw8]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hw8]; exact hws a (by omega) (by omega))
  have hw10 : ∀ a, μ10.writable a = μ.writable a := fun a => by rw [lwr, hw8]
  have hr10 : ∀ a, μ10.readable a = μ.readable a := fun a => by rw [lrd, hr8]
  obtain ⟨ω11, run11, k50, k51, k55, k56, k57, k58, k59⟩ := k5 (p := p) (P := P) (R := R) x ω10 μ10 (S - 696)
    (by omega) l1
  -- zero K + 544 … K + 672
  obtain ⟨ω12, μ12, run12, f0', f1', f5', f6', -, ffr', frd', fwr'⟩ := Memzero.memzero (p := p) (P := P) (R := R) x
    ω11 μ10 (S - 696 + 544) 128 1666 35644 (by omega) ⟨by decide, by decide⟩ (by omega) k50 k57 k58 k59 (by decide)
    jte_832 bs_35644 (fun a h1 h2 => by rw [hw10]; exact hws a (by omega) (by omega))
  have hw12 : ∀ a, μ12.writable a = μ.writable a := fun a => by rw [fwr', hw10]
  have hr12 : ∀ a, μ12.readable a = μ.readable a := fun a => by rw [frd', hr10]
  have w12 : ω12[6] = UInt64.ofNat rd := f6'.trans (k56.trans (l6.trans (k46.trans (g6'.trans k36))))
  obtain ⟨ω13, run13, k60, k61, k65, k66, k67, k68, k69⟩ := k6 (p := p) (P := P) (R := R) x ω12 μ12 (S - 696) rd
    (by omega) (by omega) (f1'.trans k51) w12
  -- field 4: 128 octets into K + 544
  have m12rd : ∀ a, rd ≤ a → a < rd + 16 → μ12.read a = μ8.read a := fun a h1 h2 =>
    (ffr' _ (by omega) (by omega)).trans (lfr _ (by omega) (by omega) (by omega))
  obtain ⟨ω14, μ14, run14, q0, q1, q5, q6, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩ := read_big_sp (p := p)
    (P := P) (R := R) x ω13 μ12 1668 35660 (S - 696) rd (S - 696 + 544) (pp + 208) (ll - 208) 128 k60 k61 k67 k68
    k69 (by decide) jte_833 bs_35660 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [hw12]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hw12]; exact hwr a h1 h2)
    (fun a h1 h2 => by rw [hw12]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hr12]; exact hrp a (by omega) (by omega))
    (by rw [Memory.readN_congr (fun j hj => m12rd _ (by omega) (by omega))]; exact hR0'.trans (congrArg _ (by omega)))
    (by rw [Memory.readN_congr (fun j hj => m12rd _ (by omega) (by omega))]; exact hR8'.trans (congrArg _ (by omega)))
  have hw14 : ∀ a, μ14.writable a = μ.writable a := fun a => by rw [qwr, hw12]
  have hr14 : ∀ a, μ14.readable a = μ.readable a := fun a => by rw [qrd, hr12]
  obtain ⟨ω15, run15, k70, k71, k75, k76, k77, k78, k79⟩ := k7 (p := p) (P := P) (R := R) x ω14 μ14 (S - 696)
    (by omega) (q1.trans k61) q7
  -- copy K + 544 … K + 672 to K
  obtain ⟨ω16, μ16, run16, n0, n1, n5, n6, ncp, nfr, nrd, nwr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R) x
    ω15 μ14 1670 35704 (S - 696) (S - 696) (S - 696 + 544) 128 k70 k71 k77 k78 k79 (by decide) jte_834 bs_35704
    ⟨by omega, by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (fun a h1 h2 => by rw [hr14]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [hw14]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hw14]; exact hws a (by omega) (by omega))
  have hw16 : ∀ a, μ16.writable a = μ.writable a := fun a => by rw [nwr, hw14]
  have hr16 : ∀ a, μ16.readable a = μ.readable a := fun a => by rw [nrd, hr14]
  obtain ⟨ω17, μ17, run17, o0, o1, o5, o6, o7, o8, o9, o128, o160, ofr, ord, owr⟩ := k8 (p := p) (P := P) (R := R)
    x ω16 μ16 (S - 696) ⟨by omega, by omega⟩ n1 (fun a h1 h2 => by rw [hw16]; exact hws a (by omega) (by omega))
  have hw17 : ∀ a, μ17.writable a = μ.writable a := fun a => by rw [owr, hw16]
  have hr17 : ∀ a, μ17.readable a = μ.readable a := fun a => by rw [ord, hr16]
  -- copy K + 400 … K + 544 to K + 192
  obtain ⟨ω18, μ18, run18, t0, t1, t5, t6, tcp, tfr, trd, twr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R) x
    ω17 μ17 1672 35787 (S - 696) (S - 696 + 192) (S - 696 + 400) 144 o0 o1 o7 o8 o9 (by decide) jte_835 bs_35787
    ⟨by omega, by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (fun a h1 h2 => by rw [hr17]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [hw17]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hw17]; exact hws a (by omega) (by omega))
  have hw18 : ∀ a, μ18.writable a = μ.writable a := fun a => by rw [twr, hw17]
  have hr18 : ∀ a, μ18.readable a = μ.readable a := fun a => by rw [trd, hr17]
  have w18 : ω18[5] = UInt64.ofNat (S + 64) := t5.trans (o5.trans (n5.trans (k75.trans (q5.trans (k65.trans
    (f5'.trans (k55.trans (l5.trans (k45.trans (g5'.trans (k35.trans (f5.trans (e5.trans (d5.trans (c5.trans
    (g5.trans a5))))))))))))))))
  have w18' : ω18[6] = UInt64.ofNat rd := t6.trans (o6.trans (n6.trans (k76.trans (q6.trans k66))))
  obtain ⟨ω19, run19, k90, k91, k95, k96, k97, k98, k99⟩ := k9 (p := p) (P := P) (R := R) x ω18 μ18 (S - 696)
    (S + 64) (by omega) (by omega) t1 w18
  -- copy the key K … K + 336 to S + 65
  obtain ⟨ω20, μ20, run20, u0, u1, u5, u6, ucp, ufr, urd, uwr⟩ := memcpy_d1 (p := p) (P := P) (R := R) x
    ω19 μ18 1674 35803 (S - 696) (S + 64 + 1) (S - 696) 336 k90 k91 k97 k98 k99 (by decide) jte_836 bs_35803
    ⟨by omega, by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (fun a h1 h2 => by rw [hr18]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [hw18]; exact hws a (by omega) (by omega))
    (fun a h1 h2 => by rw [hw18]; exact hws a (by omega) (by omega))
  have hw20 : ∀ a, μ20.writable a = μ.writable a := fun a => by rw [uwr, hw18]
  have hr20 : ∀ a, μ20.readable a = μ.readable a := fun a => by rw [urd, hr18]
  -- the memory from μ1 to μ20 off the frames, the reader and the slot
  have G : ∀ a, a < 4294967296 → (a < S - 784 ∨ S - 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < S + 64 ∨ S + 401 ≤ a) → μ20.read a = μ1.read a := fun a h0 h1 h2 h3 =>
    (ufr a h0 (by omega) (by omega)).trans ((tfr a h0 (by omega) (by omega)).trans ((ofr a h0 (by omega)).trans
      ((nfr a h0 (by omega) (by omega)).trans ((qfr a h0 (by omega) h2 (by omega)).trans ((ffr' a h0 (by omega)).trans
      ((lfr a h0 (by omega) (by omega)).trans ((gfr' a h0 (by omega) h2 (by omega)).trans ((ffr a h0 (by omega)).trans
      ((efr a h0 (by omega)).trans ((dfr a h0 (by omega) h2 (by omega)).trans ((cfr a h0 (by omega) (by omega)).trans
      (gfr a h0 (by omega) h2 (by omega)))))))))))))
  have Gs : ∀ a, S - 24 ≤ a → a < S → μ20.read a = μ1.read a := fun a h1 h2 =>
    G a (by omega) (Or.inr h1) (by omega) (by omega)
  obtain ⟨ω21, μ21, run21, v0, v1, v5', v6', v64, vfr, vrd, vwr⟩ := k10 (p := p) (P := P) (R := R) x ω20 μ20
    (S - 696) (S + 64) c v ⟨by omega, by omega⟩ (by omega) (by omega) u1 (u5.trans k95) hc hv
    (by rw [Memory.readN_congr (fun j hj => Gs _ (by omega) (by omega))]; exact a688)
    (by rw [Memory.readN_congr (fun j hj => Gs _ (by omega) (by omega))]; exact a680)
    (by rw [Memory.readN_congr (fun j hj => Gs _ (by omega) (by omega))]; exact a672)
    (fun a h1 h2 => by rw [hr20]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
    (by rw [hw20]; exact hws _ (by omega) (by omega))
  -- the payload in μ1
  have P1 : ∀ a, pp ≤ a → a < pp + 336 → μ1.read a = μ.read a := fun a h1 h2 => F1 a (by omega) (by omega)
  -- the fields
  have T1 : μ17.readN (S - 696 + 128) 32 = μ.readN pp 32 := by
    rw [o128, Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega)).trans
      ((qfr _ (by omega) (by omega) (by omega) (by omega)).trans ((ffr' _ (by omega) (by omega)).trans
      ((lfr _ (by omega) (by omega) (by omega)).trans ((gfr' _ (by omega) (by omega) (by omega) (by omega)).trans
      ((ffr _ (by omega) (by omega)).trans ((efr _ (by omega) (by omega)).trans
      (dfr _ (by omega) (by omega) (by omega) (by omega)))))))))]
    rw [c336, gbuf, Memory.readN_congr (fun j hj => P1 _ (by omega) (by omega))]
  have T2 : μ17.readN (S - 696 + 160) 32 = μ.readN (pp + 32) 32 := by
    rw [o160, Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega)).trans
      ((qfr _ (by omega) (by omega) (by omega) (by omega)).trans ((ffr' _ (by omega) (by omega)).trans
      ((lfr _ (by omega) (by omega) (by omega)).trans ((gfr' _ (by omega) (by omega) (by omega) (by omega)).trans
      (ffr _ (by omega) (by omega)))))))]
    rw [e368, dbuf, Memory.readN_congr (fun j hj => (cfr _ (by omega) (by omega) (by omega)).trans
      ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans (P1 _ (by omega) (by omega))))]
  have T3 : μ18.readN (S - 696 + 192) 144 = μ.readN (pp + 64) 144 := by
    rw [tcp, Memory.readN_congr (fun j hj => (ofr _ (by omega) (by omega)).trans
      ((nfr _ (by omega) (by omega) (by omega)).trans ((qfr _ (by omega) (by omega) (by omega) (by omega)).trans
      (ffr' _ (by omega) (by omega)))))]
    rw [lcp, gbuf', Memory.readN_congr (fun j hj => (ffr _ (by omega) (by omega)).trans
      ((efr _ (by omega) (by omega)).trans ((dfr _ (by omega) (by omega) (by omega) (by omega)).trans
      ((cfr _ (by omega) (by omega) (by omega)).trans ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans
      (P1 _ (by omega) (by omega)))))))]
  have T4 : μ18.readN (S - 696) 128 = μ.readN (pp + 208) 128 := by
    rw [Memory.readN_congr (fun j hj => (tfr _ (by omega) (by omega) (by omega)).trans (ofr _ (by omega) (by omega)))]
    rw [ncp, qbuf, Memory.readN_congr (fun j hj => (ffr' _ (by omega) (by omega)).trans
      ((lfr _ (by omega) (by omega) (by omega)).trans ((gfr' _ (by omega) (by omega) (by omega) (by omega)).trans
      ((ffr _ (by omega) (by omega)).trans ((efr _ (by omega) (by omega)).trans
      ((dfr _ (by omega) (by omega) (by omega) (by omega)).trans ((cfr _ (by omega) (by omega) (by omega)).trans
      ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans (P1 _ (by omega) (by omega))))))))))]
  have T12 : μ18.readN (S - 696 + 128) 32 = μ.readN pp 32 := by
    rw [Memory.readN_congr (fun j hj => tfr _ (by omega) (by omega) (by omega))]; exact T1
  have T22 : μ18.readN (S - 696 + 160) 32 = μ.readN (pp + 32) 32 := by
    rw [Memory.readN_congr (fun j hj => tfr _ (by omega) (by omega) (by omega))]; exact T2
  have hkey : μ18.readN (S - 696) 336 = keyRot (μ.readN pp 336) := by
    rw [keyRot_readN, ← T4, show (336 : Nat) = 128 + 208 from rfl, Memory.readN_split μ18 (S - 696) 128 208]
    congr 1
    rw [show (208 : Nat) = 32 + 176 from rfl, Memory.readN_split μ18, Memory.readN_split μ,
      show (176 : Nat) = 32 + 144 from rfl, Memory.readN_split μ18, Memory.readN_split μ,
      show S - 696 + 128 + 32 = S - 696 + 160 by omega, show S - 696 + 128 + 32 + 32 = S - 696 + 192 by omega,
      show pp + 32 + 32 = pp + 64 by omega, T12, T22, T3]
  have hrd21 : ∀ a, rd ≤ a → a < rd + 16 → μ21.read a = μ14.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega)).trans ((ufr a (by omega) (by omega) (by omega)).trans
      ((tfr a (by omega) (by omega) (by omega)).trans ((ofr a (by omega) (by omega)).trans
      (nfr a (by omega) (by omega) (by omega)))))
  refine ⟨ω21, μ21, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
    (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans (run15.trans (run16.trans
    (run17.trans (run18.trans (run19.trans (run20.trans run21)))))))))))))))))))).mono (by omega),
    v1.trans (congrArg _ (by omega)), v5', v6', v64, ?_, ?_, ?_, ?_, fun a => by rw [vrd, hr20],
    fun a => by rw [vwr, hw20]⟩
  · rw [Memory.readN_congr (fun j hj => vfr _ (by omega) (by omega)), show S + 65 = S + 64 + 1 by omega, ucp]
    exact hkey
  · rw [Memory.readN_congr (fun j hj => hrd21 _ (by omega) (by omega))]; exact qR0.trans (congrArg _ (by omega))
  · rw [Memory.readN_congr (fun j hj => hrd21 _ (by omega) (by omega))]; exact qR8.trans (congrArg _ (by omega))
  · intro a h0 h1 h2 h3
    rw [vfr a h0 (by omega), G a h0 (by omega) h2 h3]
    exact afr a h0 (by omega) (by omega)

/-- The state at each element of the loop (1495), after j of the n keys: the frame, the reader at key
    j, the keys from j on still in the payload, and the first j already in the block q (rotated). -/
structure LoopSt (S n q rd ptr len out r0 v5 v6 j : Nat) (Pl : Nat → List UInt8) (ω : Regs) (μ : Memory) :
    Prop where
  e1 : ω[1] = UInt64.ofNat S
  e5 : ω[5] = UInt64.ofNat (n - j)
  m40 : μ.readN (S + 40) 8 = Num.encodeLE 8 n
  m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 q
  m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 j
  m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 rd
  m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n
  m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n
  m0 : μ.readN S 8 = Num.encodeLE 8 out
  m760 : μ.readN (S + 760) 8 = Num.encodeLE 8 r0
  m752 : μ.readN (S + 752) 8 = Num.encodeLE 8 v5
  m744 : μ.readN (S + 744) 8 = Num.encodeLE 8 v6
  R0 : μ.readN rd 8 = Num.encodeLE 8 (ptr + 336 * j)
  R8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len - 336 * j)
  pay : ∀ k, j ≤ k → k < n → μ.readN (ptr + 336 * k) 336 = Pl k
  done : ∀ k, k < j → μ.readN (q + 336 * k) 336 = keyRot (Pl k)
  ws : ∀ a, S - 784 ≤ a → a < S + 768 → μ.writable a = true
  wr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true
  wq : ∀ a, q ≤ a → a < q + 336 * n → μ.writable a = true
  wo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true
  rp : ∀ a, ptr ≤ a → a < ptr + 336 * n → μ.readable a = true

/-- The bounds and separations the element loop needs: the frames S − 784 … S + 768, the reader rd,
    the block q … q + 336·n (8-aligned), the slot out and the payload apart. -/
structure Bnd (S n q rd ptr len out : Nat) : Prop where
  hS : 65536 + 784 ≤ S ∧ S + 768 < 4294967296 ∧ S % 8 = 0
  hn : 1 ≤ n ∧ n ≤ 48
  hq : 65536 ≤ q ∧ q + 336 * n + 16 < 4294967296 ∧ q % 8 = 0
  hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296
  hptr : 65536 ≤ ptr ∧ ptr + 336 * n + 16 < 4294967296
  hlen : 336 * n ≤ len ∧ len < 4294967296
  hout : out + 24 < 4294967296
  rS : rd + 16 ≤ S - 784 ∨ S + 768 ≤ rd
  pS : ptr + 336 * n + 24 ≤ S - 784 ∨ S + 768 ≤ ptr
  qS : q + 336 * n ≤ S - 784 ∨ S + 768 ≤ q
  oS : out + 24 ≤ S - 784 ∨ S + 768 ≤ out
  rq : rd + 16 ≤ q ∨ q + 336 * n ≤ rd
  ro : rd + 16 ≤ out ∨ out + 24 ≤ rd
  oq : out + 24 ≤ q ∨ q + 336 * n ≤ out
  pq : ptr + 336 * n ≤ q ∨ q + 336 * n ≤ ptr
  pr : ptr + 336 * n ≤ rd ∨ rd + 16 ≤ ptr
  po : ptr + 336 * n ≤ out ∨ out + 24 ≤ ptr

/-- The memory the loop may change: the frames, the reader, the block and the slot. -/
def LFrame (S n q rd out : Nat) (μ μ' : Memory) : Prop :=
  (∀ a, a < 4294967296 → (a < S - 784 ∨ S + 768 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < q ∨ q + 336 * n ≤ a) →
    (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
  (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **One key, up to its copy into the block** (1495 … 1477, then `memcpy` to 1483): from `LoopSt`
    after j < n keys, the key decoder reads key j, the function copies it to S + 408 and from there to
    q + 336·j, and reaches 1483 with c = n − j in ω₅ and j in ω₆. -/
theorem body {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd ptr len out r0 v5 v6 j : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hj : j < n) (h : LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ) :
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x 1483 ω' μ' x 8150 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (n - j) ∧ ω'[6] = UInt64.ofNat j ∧
      μ'.readN (q + 336 * j) 336 = keyRot (Pl j) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 336 * (j + 1)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 336 * (j + 1)) ∧
      (∀ a, a < 4294967296 → (a < S - 784 ∨ S ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        (a < q + 336 * j ∨ q + 336 * j + 336 ≤ a) → (a < S + 32 ∨ S + 40 ≤ a) → (a < S + 64 ∨ S + 744 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := B.hS
  have := B.hn; have := B.hq; have := B.hrd; have := B.hptr; have := B.hlen; have := B.hout
  have := B.rS; have := B.pS; have := B.qS; have := B.oS; have := B.rq; have := B.ro; have := B.oq
  have := B.pq; have := B.pr; have := B.po
  obtain ⟨e1, e5, m40, m48, m56, m24, m8, m16, m0, m760, m752, m744, R0, R8, pay, done, ws, wr, wq, wo, rp⟩ := h
  have hj336 : 336 * j + 336 ≤ 336 * n := by omega
  -- the key decoder
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a64, akey, aR0, aR8, afr, ard, awr⟩ := key (p := p) (P := P) (R := R) x ω μ
    S (n - j) (ω[6]).toNat rd (ptr + 336 * j) (len - 336 * j) ⟨hS0, hS1, hS8⟩ e1 e5 UInt64.ofNat_toNat.symm
    (by omega) (UInt64.toNat_lt _) B.hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ B.rS (by omega) (by omega) m24
    R0 R8 ws wr (fun a h1 h2 => rp a (by omega) (by omega))
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
  obtain ⟨ω4, μ4, run4, c0, c1, c5, c6, c7, c8, c9, c32, cfr, crd, cwr⟩ := b2 (p := p) (P := P) (R := R) x ω3 μ3
    S n q j ⟨by omega, by omega⟩ (s1.trans rfl) hj B.hn.2 (by omega)
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
    d5.trans (c5.trans (s5.trans (b5.trans a5))), d6.trans c6, ?_, ?_, ?_, ?_,
    fun a => by rw [drd, crd, srd, ard], fun a => by rw [dwr, cwr, swr, awr]⟩
  · rw [dcp, Memory.readN_congr (fun i hi => cfr _ (by omega) (by omega)), scp, akey, pay j (by omega) hj]
  · rw [Memory.readN_congr (fun i hi => hrd5 _ (by omega) (by omega))]
    exact aR0.trans (congrArg _ (by omega))
  · rw [Memory.readN_congr (fun i hi => hrd5 _ (by omega) (by omega))]
    exact aR8.trans (congrArg _ (by omega))
  · intro a h0 h1 h2 h3 h4 h5
    rw [dfr a h0 h3 (by omega), cfr a h0 h4, sfr a h0 (by omega) (by omega)]
    exact afr a h0 (by omega) h2 (by omega)

/-- **One key, more to come**: from `LoopSt` after j < n − 1 keys, the function reads key j, copies it
    to q + 336·j and goes on: `LoopSt` after j + 1. -/
theorem one {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd ptr len out r0 v5 v6 j : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hj : j + 1 < n) (h : LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ) :
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x 1495 ω' μ' x 8200 ∧ LoopSt S n q rd ptr len out r0 v5 v6 (j + 1) Pl ω' μ' ∧
      LFrame S n q rd out μ μ' := by
  obtain ⟨hS0, hS1, hS8⟩ := B.hS
  have := B.hn; have := B.hq; have := B.hrd; have := B.hptr; have := B.hlen; have := B.hout
  have := B.rS; have := B.pS; have := B.qS; have := B.oS; have := B.rq; have := B.ro; have := B.oq
  have := B.pq; have := B.pr; have := B.po
  obtain ⟨ω1, μ1, run1, a1, a5, a6, akey, aR0, aR8, afr, ard, awr⟩ := body (p := p) (P := P) (R := R) x ω μ S n q
    rd ptr len out r0 v5 v6 j Pl B (by omega) h
  obtain ⟨e1, e5, m40, m48, m56, m24, m8, m16, m0, m760, m752, m744, R0, R8, pay, done, ws, wr, wq, wo, rp⟩ := h
  obtain ⟨ω2, μ2, run2, b1', b5, b56, bfr, brd, bwr⟩ := b3a (p := p) (P := P) (R := R) x ω1 μ1 S j (n - j)
    ⟨by omega, by omega⟩ a1 a5 a6 ⟨by omega, by omega⟩ (by omega)
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) h2)
  have back : ∀ a, a < 4294967296 → (a < S - 784 ∨ S + 768 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < q + 336 * j ∨ q + 336 * j + 336 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (bfr a h0 (by omega)).trans (afr a h0 (by omega) h2 h3 (by omega) (by omega))
  have hS' : ∀ a, S ≤ a → a < S + 32 ∨ (S + 40 ≤ a ∧ a < S + 56) ∨ S + 744 ≤ a → a < S + 768 →
      μ2.read a = μ.read a := fun a h1 h2 h3 =>
    (bfr a (by omega) (by omega)).trans (afr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), ⟨b1', b5.trans (congrArg _ (by omega)), ?_, ?_, b56, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m40
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m48
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m24
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m8
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m16
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m0
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m760
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m752
  · rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m744
  · rw [Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega))]; exact aR0
  · rw [Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega))]; exact aR8
  · intro k h1 h2
    rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by omega))]
    exact pay k (by omega) h2
  · intro k hk
    rcases Nat.lt_or_ge k j with hk' | hk'
    · rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by omega))]
      exact done k hk'
    · rw [show k = j by omega, Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega))]; exact akey
  · intro a h1 h2; rw [bwr, awr]; exact ws a h1 h2
  · intro a h1 h2; rw [bwr, awr]; exact wr a h1 h2
  · intro a h1 h2; rw [bwr, awr]; exact wq a h1 h2
  · intro a h1 h2; rw [bwr, awr]; exact wo a h1 h2
  · intro a h1 h2; rw [brd, ard]; exact rp a h1 h2
  · intro a h0 h1 h2 h3 h4; exact back a h0 h1 h2 (by omega)
  · intro a; rw [brd, ard]
  · intro a; rw [bwr, awr]

/-- What the loop leaves when it returns: the function's return through its frame, the `Vec` {n, q, n}
    in the slot, all n keys in the block (rotated), and the reader past them. -/
def Done (S n q rd ptr len out r0 v5 v6 : Nat) (Pl : Nat → List UInt8) (μ0 : Memory) (ω' : Regs) (μ' : Memory) :
    Prop :=
  ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (S + 768) ∧ ω'[5] = UInt64.ofNat v5 ∧
    ω'[6] = UInt64.ofNat v6 ∧
    μ'.readN out 8 = Num.encodeLE 8 n ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 q ∧
    μ'.readN (out + 16) 8 = Num.encodeLE 8 n ∧ (∀ k, k < n → μ'.readN (q + 336 * k) 336 = keyRot (Pl k)) ∧
    μ'.readN rd 8 = Num.encodeLE 8 (ptr + 336 * n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 336 * n) ∧
    LFrame S n q rd out μ0 μ'

/-- **The last key**: from `LoopSt` after n − 1 keys, the function reads and copies the last key,
    stores the `Vec` and returns. -/
theorem last {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S n q rd ptr len out r0 t v5 v6 j : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hj : j + 1 = n) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (h : LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ) :
    ∃ ω' μ', FreeStepsH p R 1495 ω μ x t ω' μ' x 8200 ∧ Done S n q rd ptr len out r0 v5 v6 Pl μ ω' μ' := by
  obtain ⟨hS0, hS1, hS8⟩ := B.hS
  have := B.hn; have := B.hq; have := B.hrd; have := B.hptr; have := B.hlen; have := B.hout
  have := B.rS; have := B.pS; have := B.qS; have := B.oS; have := B.rq; have := B.ro; have := B.oq
  have := B.pq; have := B.pr; have := B.po
  obtain ⟨ω1, μ1, run1, a1, a5, a6, akey, aR0, aR8, afr, ard, awr⟩ := body (p := p) (P := P) (R := R) x ω μ S n q
    rd ptr len out r0 v5 v6 j Pl B (by omega) h
  obtain ⟨e1, e5, m40, m48, m56, m24, m8, m16, m0, m760, m752, m744, R0, R8, pay, done, ws, wr, wq, wo, rp⟩ := h
  have hS' : ∀ a, S ≤ a → a < S + 32 ∨ (S + 40 ≤ a ∧ a < S + 64) ∨ S + 744 ≤ a → a < S + 768 →
      μ1.read a = μ.read a := fun a h1 h2 h3 =>
    afr a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, fo0, fo8, fo16, ffr, frd, fwr⟩ := b3b (p := p) (P := P) (R := R) x ω1 μ1
    S n q j out r0 t v5 v6 ⟨by omega, by omega⟩ a1 (a5.trans (congrArg _ (by omega))) a6 hj B.hn.2 (by omega)
    (by omega) (by omega) hv5 hv6
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m8)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m16)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m40)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m48)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m0)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m760)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m752)
    (by rw [Memory.readN_congr (fun i hi => hS' _ (by omega) (by omega) (by omega))]; exact m744)
    hret hjt hbt (fun a h1 h2 => by rw [awr]; exact ws a (by omega) h2)
    (fun a h1 h2 => by rw [awr]; exact wo a h1 h2)
  have back : ∀ a, a < 4294967296 → (a < S - 784 ∨ S + 768 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
      (a < q + 336 * j ∨ q + 336 * j + 336 ≤ a) → (a < out ∨ out + 24 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 h3 h4 => (ffr a h0 (by omega) h4).trans (afr a h0 (by omega) h2 h3 (by omega) (by omega))
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), f0, f1, f5, f6, fo0, fo8, fo16, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases Nat.lt_or_ge k j with hk' | hk'
    · rw [Memory.readN_congr (fun i hi => back _ (by omega) (by omega) (by omega) (by omega) (by omega))]
      exact done k hk'
    · rw [show k = j by omega, Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega))]; exact akey
  · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega))]
    exact aR0.trans (congrArg _ (by omega))
  · rw [Memory.readN_congr (fun i hi => ffr _ (by omega) (by omega) (by omega))]
    exact aR8.trans (congrArg _ (by omega))
  · intro a h0 h1 h2 h3 h4; exact back a h0 h1 h2 (by omega) h4
  · intro a; rw [frd, ard]
  · intro a; rw [fwr, awr]

/-- **The element loop**: from `LoopSt` after j < n keys, the loop reads the rest and returns (`Done`). -/
theorem elems {p : ByteArray} {P : Program} [HasCode p P] (x : X)
    (S n q rd ptr len out r0 t v5 v6 : Nat) (Pl : Nat → List UInt8) (B : Bnd S n q rd ptr len out)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0)
    (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true) :
    ∀ r j (ω : Regs) (μ : Memory), n - j = r → j < n → LoopSt S n q rd ptr len out r0 v5 v6 j Pl ω μ →
      ∃ ω' μ', FreeStepsH p R 1495 ω μ x t ω' μ' x (8200 * r) ∧ Done S n q rd ptr len out r0 v5 v6 Pl μ ω' μ' := by
  intro r
  induction r with
  | zero => intro j ω μ hr hj; omega
  | succ r ih =>
    intro j ω μ hr hj h
    rcases Nat.lt_or_ge (j + 1) n with hlast | hlast
    · obtain ⟨ω1, μ1, run1, h1, f1⟩ := one (p := p) (P := P) (R := R) x ω μ S n q rd ptr len out r0 v5 v6 j Pl B
        hlast h
      obtain ⟨ω2, μ2, run2, d0, d1, d5, d6, dO, dO8, dO16, dall, dR0, dR8, f2⟩ :=
        ih (j + 1) ω1 μ1 (by omega) hlast h1
      exact ⟨ω2, μ2, (run1.trans run2).mono (by rw [Nat.mul_succ]; omega), d0, d1, d5, d6, dO, dO8, dO16, dall,
        dR0, dR8, fun a h0 ha hb hc hd => (f2.1 a h0 ha hb hc hd).trans (f1.1 a h0 ha hb hc hd),
        fun a => (f2.2.1 a).trans (f1.2.1 a), fun a => (f2.2.2 a).trans (f1.2.2 a)⟩
    · obtain ⟨ω', μ', run, hd⟩ := last (p := p) (P := P) (R := R) x ω μ S n q rd ptr len out r0 t v5 v6 j Pl B
        (by omega) hv5 hv6 hret hjt hbt h
      exact ⟨ω', μ', run.mono (by rw [Nat.mul_succ]; omega), hd⟩

/-- The keys' in-memory layout: each of the n 336-octet keys rotated (`keyRot`). -/
def keysRot : Nat → List UInt8 → List UInt8
  | 0, _ => []
  | k + 1, l => keyRot (l.take 336) ++ keysRot k (l.drop 336)

/-- n consecutive keys, each the rotation of its payload, make the whole 336·n octets the payload's
    `keysRot`. -/
theorem readN_of_keys (μ μ' : Memory) :
    ∀ n q ptr, (∀ k, k < n → μ'.readN (q + 336 * k) 336 = keyRot (μ.readN (ptr + 336 * k) 336)) →
      μ'.readN q (336 * n) = keysRot n (μ.readN ptr (336 * n)) := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro q ptr h
    rw [show 336 * (n + 1) = 336 + 336 * n by omega, Memory.readN_split, Memory.readN_split, keysRot,
      List.take_left' (Memory.length_readN _ _ _), List.drop_left' (Memory.length_readN _ _ _)]
    congr 1
    · simpa using h 0 (by omega)
    · exact ih (q + 336) (ptr + 336) (fun k hk => by
        rw [show q + 336 + 336 * k = q + 336 * (k + 1) by omega,
          show ptr + 336 + 336 * k = ptr + 336 * (k + 1) by omega]
        exact h (k + 1) (by omega))

/-- Allocated chunks start at the heap base modulo 32. -/
theorem tiles_mod {limit : Nat} : ∀ (cs : List Picoalloc.Chunk) (a : Nat), Picoalloc.Tiles a limit cs →
    ∀ c ∈ cs, c.addr % 32 = a % 32 := by
  intro cs
  induction cs with
  | nil => intro a _ c hc; simp at hc
  | cons d ds ih =>
    intro a ht c hc
    obtain ⟨h1, -, h3⟩ := ht
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h1 ▸ rfl
    · rw [ih _ h3 c hc']; omega

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.LoopA in
/-- **Reading 1 … 48 keys into a fresh `Vec<[u8; 336]>`, the payload in the heap** (1300, `Designate`'s
    keys; GP v0.8.0 §B.7, each element 336 octets): with ω₇ = O, ω₈ = rd, ω₉ = n, the allocator's context
    `HeapCtx` (under `refineContractK cap`, cap ≥ 2²⁷) and the 336n payload octets inside an allocated
    chunk's data, either the model's `alloc` of ⌈336n/32⌉ units (the code asks `finish_grow` for n
    elements of 336 octets at alignment 1) gives `(q, s')` and the reader returns to t with the `Vec`
    `{cap n, ptr q, len n}` at O (the capacity at O, the pointer at O + 8, the length at O + 16), the
    keys at q in their in-memory layout (`keysRot`: each key's last 128 octets, then its first 208), the
    reader advanced by 336n, the context kept for `s'` and every allocated chunk of `s` kept with its
    data; or the model's `alloc` fails and the run reaches the `alloc` wrapper's return (40611) with
    null. -/
theorem vec_key336_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + 336 * n ≤ c.addr + 32 * c.size)
    (hS : S0 + 1600 ≤ sp ∧ sp ≤ S1) (hsp : 2147485248 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1 ≤ n ∧ n ≤ 48) (hnl : 336 * n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', alloc (growTo pb) hb 1 ((336 * n + 31) / 32) s = some (q, s') ∧
      FreeStepsH p (refineContractK cap env) 1300 ω μ x t ω' μ' x (8200 * n + 1000) ∧
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
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    (alloc (growTo pb) hb 1 ((336 * n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 1300 ω μ x 40611 ω' μ' x (8200 * n + 1000) ∧
      ω'[7] = UInt64.ofNat 0) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hst := H.st
  -- the frame S = sp − 768 and the call of finish_grow
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a10, a11, a12, a760, a752, a744, a24, aS, a8', a16, a32, a56, afr,
      ard, awr⟩ := p1 (p := p) (P := P) (R := refineContractK cap env) x ω μ (sp - 768) O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 (by rw [h1]; congr 1; omega) h5 h6 h7 h8 h9 hn (by omega) hv5 hv6 (by omega) (by omega)
    (fun a h1 h2 => hst a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b32, b24, b16, b8'', bfr, brd, bwr⟩ := g1k (p := p) (P := P)
    (R := refineContractK cap env) x ω1 μ1 (sp - 808) (sp - 768 + 64) n 36 n n ⟨by omega, by omega⟩ a0
    (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega) (by omega) (by omega)
    hn (fun a h1 h2 => by rw [awr]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 808 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (bfr a h0 (by omega)).trans (afr a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [bwr, awr]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (sp - 808) (336 * n) 1 pb S0 S1 H2 b1
      b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s', ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ⟨hna, ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), e7⟩
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (336 * n + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hbase' : s'.base = s.base := alloc_base H.wf ha
  have hq32 : (q - 32) % 32 = 0 := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    have := tiles_mod _ _ ht _ hnew
    simp only at this
    have := H3.wf.2.1
    omega
  rw [hbase'] at hqb hqT hqT'
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 808 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, d0, d1, d5, d6, d96, d104, d112, dfr, drd, dwr⟩ := g2 (p := p) (P := P)
    (R := refineContractK cap env) x ω3 μ3 (sp - 808) (sp - 768 + 64) (336 * n) q 36 1424 n n ⟨by omega, by omega⟩
    (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7 ⟨by omega, by omega⟩ (by omega) (by omega)
    (by omega)
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
  obtain ⟨ω6, μ6, run6, f1, f5, f6, f40, f48, f32, efr, erd, ewr⟩ := p5 (p := p) (P := P)
    (R := refineContractK cap env) x ω5 μ5 (sp - 768) n q ⟨by omega, by omega⟩
    (d1.trans (congrArg _ (by omega))) d6 hn (by omega) d96 d104
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
  have hdq : ptr + 336 * n ≤ q ∨ q + 336 * n ≤ ptr := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  -- the loop
  have L : LoopSt (sp - 768) n q rd ptr len O ret v5 v6 0 (fun k => μ.readN (ptr + 336 * k) 336) ω6 μ6 :=
    ⟨f1, f5.trans (congrArg _ (by omega)), f40, f48,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a56,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a24,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a8',
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a16,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact aS,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a760,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a752,
      by rw [Memory.readN_congr (fun j hj => chain6 _ (by omega) (by omega) (by omega) (by omega))]; exact a744,
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
  have B : Bnd (sp - 768) n q rd ptr len O :=
    ⟨⟨by omega, by omega, by omega⟩, hn, ⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
      ⟨hnl, hlen⟩, by omega, Or.inr (by omega), Or.inl (by omega), Or.inl (by omega), Or.inr (by omega),
      Or.inr (by omega), hOr.symm, Or.inr (by omega), hdq, Or.inl (by omega), Or.inl (by omega)⟩
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, gO, gO8, gO16, gall, gR0, gR8, gfr⟩ := elems (p := p) (P := P)
    (R := refineContractK cap env) x (sp - 768) n q rd ptr len O ret t v5 v6 _ B hv5 hv6 hret hjt hbt n 0 ω6 μ6
    (by omega) hn.1 L
  -- the heap after the loop
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 336 * n ≤ a) → μ7.read a = μ3.read a := fun a h1 h3 =>
    (gfr.1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) h3 (Or.inl (by omega))).trans (h63 a h1)
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  have wr7 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [gfr.2.2, wr36]
  refine Or.inl ⟨q, s', ω7, μ7, ha, run17.mono (by omega), g0, by rw [g1]; congr 1; omega, g5, g6, gO, gO8, gO16,
    ?_, gR0, gR8, ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr7, keep, hnew,
    hfresh, ?_, FreeStepsH.pagesOut H.bd run17, ?_, ?_, ?_, ?_⟩
  · exact readN_of_keys μ μ7 n q ptr gall
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

end Services.Bootstrap.Decode.VecKey336
