import Services.Bootstrap.Decode.U32Hash
import Services.Bootstrap.Memzero

/-!
# `Instruction::decode`: `Transfer { destination, amount, gas_limit, memo }`

`Transfer` (tag 2, encoded as `[2] ++ u32 ++ u64 ++ u64 ++ memo`, the memo 128 octets) is decoded with a
176-octet frame at S = A − 176: the `u32` is read into S + 24 and parked, sign-extended, as a word at
S + 16; the first `u64` is read into S + 24 and parked at S + 8, the second read into S + 24 and parked
at S; then S + 24 … S + 152 is zeroed (`memzero`), the memo read into it (`read_big_sp`) and copied to
O + 8 (`memcpy_big_aligned`). The variant is stored as the discriminant word 2^63 + 1 at O, the memo at
O + 8, the `u64`s at O + 136 and O + 144 and the `u32` at O + 152.
-/

namespace Services.Bootstrap.Decode.Transfer

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21132 … 21175: `Transfer`'s decoder opens a 176-octet frame at S = A − 176 saving the return
    address 964, O and the reader at S + 168, S + 160, S + 152, zeroes S + 24 … S + 28 and calls the
    reader for 4 octets into S + 24 (return address 1072). -/
theorem t1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 176 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 176 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21132 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1072 ∧ ω'[1] = UInt64.ofNat (A - 176) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 152) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 964 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 176 + 168 = A - 8 by omega, show A - 176 + 160 = A - 16 by omega,
      show A - 176 + 152 = A - 24 by omega, show A - 176 + 24 = A - 152 by omega]; post_simp)

/-- 22997 … 23018: the `u32` read succeeded (ω₇ = 0): it is parked, sign-extended, as a word at S + 16;
    S + 24 … S + 32 is zeroed and the reader called for 8 octets into S + 24 (return address 1074). -/
theorem t2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 32 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (S + 24) 4 = Num.encodeLE 4 v)
    (hw : ∀ a, S + 16 ≤ a → a < S + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 22997 ω μ x 58434 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 1074 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      (μ'.readN (S + 16) 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < S + 16 ∨ S + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 24) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, S + 16 ≤ a → a < S + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 23025 … 23046 (and, with `P0 = S`, 23053 … 23060): a `u64` read succeeded (ω₇ = 0): it is parked at
    S + 8; S + 24 … S + 32 is zeroed and the reader called for 8 octets into S + 24 (return address
    1076). -/
theorem t3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 32 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (sv : μ.readN (S + 24) 8 = Num.encodeLE 8 v)
    (hw0 : ∀ a, S + 8 ≤ a → a < S + 16 → μ.writable a = true)
    (hw : ∀ a, S + 24 ≤ a → a < S + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 23025 ω μ x 58434 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 1076 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 24) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 16 ≤ a) → (a < S + 24 ∨ S + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 24) 8 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  have hr : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hw0, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 23053 … 23071: the second `u64` read succeeded (ω₇ = 0): it is parked at S, and `memzero` is called
    for the 128 octets at S + 24 (return address 1078). -/
theorem t4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 32 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (sv : μ.readN (S + 24) 8 = Num.encodeLE 8 v)
    (hw0 : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hr : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23053 ω μ x 70133 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1078 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 24) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 128 ∧
      μ'.readN S 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 24) 8 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw0, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 23078 … 23087: after `memzero`, the reader is called for the 128-octet memo into S + 24 (return
    address 1080). -/
theorem t5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 32 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 23078 ω μ x 58434 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat 1080 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 24) ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 23094 then 23121 … 23131: the memo read succeeded (ω₇ = 0): `memcpy` is called to copy the 128
    octets at S + 24 to O + 8 (return address 1082). -/
theorem t6 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O : Nat)
    (hS : S + 32 ≤ 4294967296) (hO : O + 8 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 23094 ω μ x 68729 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1082 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (O + 8) ∧ ω'[8] = UInt64.ofNat (S + 24) ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h7, hS, hO]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 23138 … 23186 then 21179 … 21191: the memo is in place: the decoder stores `Transfer`'s
    discriminant word 2^63 + 1 at O, the `u64`s (S + 8 and S) at O + 136 and O + 144 and the `u32` (the
    low four octets of the word at S + 16) at O + 152, pops its frame through 964 to 21179 and returns
    through its frame at A = S + 176. -/
theorem t7 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 a g w o6 : Nat) (hA : S + 176 + 56 < 4294967296) (hO : O + 156 ≤ 4294967296)
    (hOS : O + 156 ≤ S ∨ S + 232 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (ha : a < 18446744073709551616) (hg : g < 18446744073709551616) (hw64 : w < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sa : μ.readN (S + 8) 8 = Num.encodeLE 8 a) (sg : μ.readN S 8 = Num.encodeLE 8 g)
    (sw : μ.readN (S + 16) 8 = Num.encodeLE 8 w)
    (sr : μ.readN (S + 168) 8 = Num.encodeLE 8 964) (sO : μ.readN (S + 160) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 152) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 224) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 216) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 208) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ x, O ≤ x → x < O + 156 → μ.writable x = true)
    (hr : ∀ x, S ≤ x → x < S + 232 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 23138 ω μ x t ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 232) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775809 ∧
      μ'.readN (O + 136) 8 = Num.encodeLE 8 a ∧ μ'.readN (O + 144) 8 = Num.encodeLE 8 g ∧
      μ'.readN (O + 152) 4 = Num.encodeLE 4 w ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 8 ≤ x) → (x < O + 136 ∨ O + 156 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have ra := rd _ a ha sa
  have rg := rd _ g hg sg
  have rw0 := rd _ w hw64 sw
  have rr := rd _ 964 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 176 + 48) 8 = ret := by rw [show S + 176 + 48 = S + 224 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 176 + 40) 8 = v5 := by rw [show S + 176 + 40 = S + 216 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 176 + 32) 8 = v6 := by rw [show S + 176 + 32 = S + 208 by omega]; exact rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hA, hO, hOS, hw, hr, ra, rg, rw0, rr, rO, ro6, r0, r5, r6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 ha2 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try exact encodeLE_mod 4 w

/-- **`Transfer`**: from 20626, with tag 2 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding at least 148 more octets, `Instruction::decode` returns
    `Transfer { destination, amount, gas_limit, memo }` in its slot O: the discriminant word 2^63 + 1 at
    O, the 128-octet memo (from ptr + 20) at O + 8, the `u64`s (from ptr + 4 and ptr + 12) at O + 136 and
    O + 144, and the `u32` (from ptr) at O + 152. The reader is advanced by 148. Memory changes only in
    A − 264 … A (the decoder's frame and its callees'), the reader and O … O + 156. -/
theorem transfer {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 264 ≤ A ∧ A % 8 = 0) (hO8 : O % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 2) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 172 < 4294967296)
    (hlen : 148 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 264 ∨ A + 56 ≤ rd) (hpA : ptr + 172 ≤ A - 264 ∨ A + 56 ≤ ptr)
    (hOA' : O + 156 ≤ A - 264 ∨ A + 56 ≤ O) (hOr : O + 156 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 148 ≤ rd ∨ rd + 16 ≤ ptr) (hO : O + 172 ≤ 4294967296)
    (hws : ∀ a, A - 264 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 156 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 148 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 2100 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775809 ∧ μ'.readN (O + 8) 128 = μ.readN (ptr + 20) 128 ∧
      μ'.readN (O + 136) 8 = μ.readN (ptr + 4) 8 ∧ μ'.readN (O + 144) 8 = μ.readN (ptr + 12) 8 ∧
      μ'.readN (O + 152) 4 = μ.readN ptr 4 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 148) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 148) ∧
      (∀ a, a < 4294967296 → (a < A - 264 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 156 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have dl : ∀ q, Num.decodeLE (μ.readN q 8) < 18446744073709551616 := fun q => by
    have := decodeLE_lt (μ.readN q 8); simpa [Memory.length_readN] using this
  have el : ∀ (m : Memory) q, Num.encodeLE 8 (Num.decodeLE (m.readN q 8)) = m.readN q 8 := fun m q => by
    have := encodeLE_decodeLE (m.readN q 8); simpa [Memory.length_readN] using this
  have dl4 : ∀ q, Num.decodeLE (μ.readN q 4) < 4294967296 := fun q => by
    have := decodeLE_lt (μ.readN q 4); simpa [Memory.length_readN] using this
  have el4 : ∀ q, Num.encodeLE 4 (Num.decodeLE (μ.readN q 4)) = μ.readN q 4 := fun q => by
    have := encodeLE_decodeLE (μ.readN q 4); simpa [Memory.length_readN] using this
  -- the dispatch and the frame
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 2 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f88, f80, f72, ffr, frd, fwr⟩ :=
    t1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  have pay2 : ∀ q, ptr ≤ q → q < ptr + 148 → μ2.read q = μ.read q := fun q h1 h2 => ffr q (by omega) (by omega)
  have rd2 : ∀ q, rd ≤ q → q < rd + 16 → μ2.read q = μ.read q := fun q h1 h2 => ffr q (by omega) (by omega)
  -- the u32, into S + 24
  obtain ⟨ω3, μ3, run3, m0, m1, m2, m3, m4, m5, m6, m12, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1072 22997 (A - 176) rd (A - 152) ptr len 4 f0 f1 f7 f8 f9
      (by decide) jte_535 bs_22997 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => rd2 _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => rd2 _ (by omega) (by omega))]; exact hR8)
  have pay3 : ∀ q, ptr ≤ q → q < ptr + 148 → μ3.read q = μ.read q := fun q h1 h2 =>
    (mfr q (by omega) (by omega) (by omega) (by omega)).trans (pay2 q h1 h2)
  -- parked at S + 16; the first u64's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, ku32, kfr, krd, kwr⟩ :=
    t2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 176) (Num.decodeLE (μ.readN ptr 4)) (by omega) (m1.trans f1) m7
      (dl4 _)
      (by rw [show A - 176 + 24 = A - 152 by omega, mbuf, el4]
          exact Memory.readN_congr (fun j hj => pay2 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [mwr, fwr]; exact hws a (by omega) (by omega))
  have pay4 : ∀ q, ptr ≤ q → q < ptr + 148 → μ4.read q = μ.read q := fun q h1 h2 =>
    (kfr q (by omega) (by omega)).trans (pay3 q h1 h2)
  -- the first u64, into S + 24
  obtain ⟨ω5, μ5, run5, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1074 23025 (A - 176) rd (A - 176 + 24) (ptr + 4) (len - 4) 8 k0
      (k1.trans (m1.trans f1)) (k7.trans (m6.trans f6)) k8 k9
      (by decide) jte_536 bs_23025 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, mwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, mrd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact mR8)
  have pay5 : ∀ q, ptr ≤ q → q < ptr + 148 → μ5.read q = μ.read q := fun q h1 h2 =>
    (nfr q (by omega) (by omega) (by omega) (by omega)).trans (pay4 q h1 h2)
  -- parked at S + 8; the second u64's call
  obtain ⟨ω6, μ6, run6, q0, q1, q5, q6, q7, q8, q9, qa, qfr, qrd, qwr⟩ :=
    t3 (p := p) (P := P) (R := R) x ω5 μ5 (A - 176) (Num.decodeLE (μ.readN (ptr + 4) 8)) (by omega)
      (n1.trans (k1.trans (m1.trans f1))) n7 (dl _)
      (by rw [nbuf, el]; exact Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
  have pay6 : ∀ q, ptr ≤ q → q < ptr + 148 → μ6.read q = μ.read q := fun q h1 h2 =>
    (qfr q (by omega) (by omega) (by omega)).trans (pay5 q h1 h2)
  -- the second u64, into S + 24
  obtain ⟨ω7, μ7, run7, u0, u1, u2, u3, u4, u5, u6, u12, u7, uR0, uR8, ubuf, ufr, urd, uwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω6 μ6 1076 23053 (A - 176) rd (A - 176 + 24) (ptr + 12) (len - 12) 8
      q0 (q1.trans (n1.trans (k1.trans (m1.trans f1)))) (q7.trans (n6.trans (k6.trans (m6.trans f6)))) q8 q9
      (by decide) jte_537 bs_23053 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [qwr, nwr, kwr, mwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [qrd, nrd, krd, mrd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => qfr _ (by omega) (by omega) (by omega))]
          exact nR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => qfr _ (by omega) (by omega) (by omega))]
          exact nR8.trans (congrArg (Num.encodeLE 8) (by omega)))
  have pay7 : ∀ q, ptr ≤ q → q < ptr + 148 → μ7.read q = μ.read q := fun q h1 h2 =>
    (ufr q (by omega) (by omega) (by omega) (by omega)).trans (pay6 q h1 h2)
  -- parked at S; memzero's call
  obtain ⟨ω8, μ8, run8, w0, w1, w5, w6, w7, w8, w9, wg, wfr, wrd, wwr⟩ :=
    t4 (p := p) (P := P) (R := R) x ω7 μ7 (A - 176) (Num.decodeLE (μ.readN (ptr + 12) 8)) (by omega)
      (u1.trans (q1.trans (n1.trans (k1.trans (m1.trans f1))))) u7 (dl _)
      (by rw [ubuf, el]; exact Memory.readN_congr (fun j hj => pay6 _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [uwr, qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [urd, qrd, nrd, krd, mrd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- the memo's buffer zeroed
  obtain ⟨ω9, μ9, run9, z0, z1, z5, z6, zz, zfr, zrd, zwr⟩ :=
    Memzero.memzero (p := p) (P := P) (R := R) x ω8 μ8 (A - 176 + 24) 128 1078 23078 (by omega) ⟨by decide, by decide⟩
      (by omega) w0 w7 w8 w9 (by decide) jte_538 bs_23078
      (fun a h1 h2 => by rw [wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
  have pay9 : ∀ q, ptr ≤ q → q < ptr + 148 → μ9.read q = μ.read q := fun q h1 h2 =>
    (zfr q (by omega) (by omega)).trans ((wfr q (by omega) (by omega)).trans (pay7 q h1 h2))
  -- the memo, into S + 24
  obtain ⟨ω10, run10, y0, y1, y5, y6, y7, y8, y9⟩ :=
    t5 (p := p) (P := P) (R := R) x ω9 μ9 (A - 176) (by omega)
      (z1.trans (w1.trans (u1.trans (q1.trans (n1.trans (k1.trans (m1.trans f1)))))))
  obtain ⟨ω11, μ11, run11, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω10 μ9 1080 23094 (A - 176) rd (A - 176 + 24) (ptr + 20) (len - 20)
      128 y0 (y1.trans (z1.trans (w1.trans (u1.trans (q1.trans (n1.trans (k1.trans (m1.trans f1))))))))
      (y7.trans (z6.trans (w6.trans (u6.trans (q6.trans (n6.trans (k6.trans (m6.trans f6)))))))) y8 y9
      (by decide) jte_539 bs_23094 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)
      (fun a h1 h2 => by rw [zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [zrd, wrd, urd, qrd, nrd, krd, mrd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => (zfr _ (by omega) (by omega)).trans (wfr _ (by omega) (by omega)))]
          exact uR0.trans (congrArg (Num.encodeLE 8) (by omega)))
      (by rw [Memory.readN_congr (fun j hj => (zfr _ (by omega) (by omega)).trans (wfr _ (by omega) (by omega)))]
          exact uR8.trans (congrArg (Num.encodeLE 8) (by omega)))
  -- the memo, copied to O + 8
  obtain ⟨ω12, run12, c0, c1, c5, c6, c7, c8, c9⟩ :=
    t6 (p := p) (P := P) (R := R) x ω11 μ11 (A - 176) O (by omega) (by omega)
      (g1.trans (y1.trans (z1.trans (w1.trans (u1.trans (q1.trans (n1.trans (k1.trans (m1.trans f1)))))))))
      (g5.trans (y5.trans (z5.trans (w5.trans (u5.trans (q5.trans (n5.trans (k5.trans (m5.trans f5))))))))) g7
  obtain ⟨ω13, μ13, run13, d0, d1, d5, d6, dcp, dfr, drd, dwr⟩ :=
    memcpy_big_aligned (p := p) (P := P) (R := R) x ω12 μ11 1082 23138 (A - 176) (O + 8) (A - 176 + 24) 128 c0
      (c1.trans (g1.trans (y1.trans (z1.trans (w1.trans (u1.trans (q1.trans (n1.trans (k1.trans
        (m1.trans f1)))))))))) c7 c8 c9
      (by decide) jte_540 bs_23138 ⟨by omega, by omega, by omega⟩ (by decide) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by
        rw [grd, zrd, wrd, urd, qrd, nrd, krd, mrd, frd]
        exact Memory.readable_of_writable (hws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hwO a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hws a (by omega) (by omega))
  -- what survives to μ13
  have b13 : ∀ a, a < 4294967296 → (a < A - 264 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 156 ≤ a) →
      μ13.read a = μ.read a := fun a h0 h1 h2 h3 =>
    (dfr a h0 (by omega) (by omega)).trans ((gfr a h0 (by omega) h2 (by omega)).trans
      ((zfr a h0 (by omega)).trans ((wfr a h0 (by omega)).trans ((ufr a h0 (by omega) h2 (by omega)).trans
      ((qfr a h0 (by omega) (by omega)).trans ((nfr a h0 (by omega) h2 (by omega)).trans
      ((kfr a h0 (by omega)).trans ((mfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))))))))
  have b13s : ∀ a, A - 24 ≤ a → a < A → μ13.read a = μ2.read a := fun a h1 h2 =>
    (dfr a (by omega) (by omega) (by omega)).trans ((gfr a (by omega) (by omega) (by omega) (by omega)).trans
      ((zfr a (by omega) (by omega)).trans ((wfr a (by omega) (by omega)).trans
      ((ufr a (by omega) (by omega) (by omega) (by omega)).trans ((qfr a (by omega) (by omega) (by omega)).trans
      ((nfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega)).trans
      (mfr a (by omega) (by omega) (by omega) (by omega)))))))))
  have b13u : ∀ a, A - 160 ≤ a → a < A - 152 → μ13.read a = μ4.read a := fun a h1 h2 =>
    (dfr a (by omega) (by omega) (by omega)).trans ((gfr a (by omega) (by omega) (by omega) (by omega)).trans
      ((zfr a (by omega) (by omega)).trans ((wfr a (by omega) (by omega)).trans
      ((ufr a (by omega) (by omega) (by omega) (by omega)).trans ((qfr a (by omega) (by omega) (by omega)).trans
      (nfr a (by omega) (by omega) (by omega) (by omega)))))))
  have b13a : ∀ a, A - 168 ≤ a → a < A - 160 → μ13.read a = μ6.read a := fun a h1 h2 =>
    (dfr a (by omega) (by omega) (by omega)).trans ((gfr a (by omega) (by omega) (by omega) (by omega)).trans
      ((zfr a (by omega) (by omega)).trans ((wfr a (by omega) (by omega)).trans
      (ufr a (by omega) (by omega) (by omega) (by omega)))))
  have b13g : ∀ a, A - 176 ≤ a → a < A - 168 → μ13.read a = μ8.read a := fun a h1 h2 =>
    (dfr a (by omega) (by omega) (by omega)).trans ((gfr a (by omega) (by omega) (by omega) (by omega)).trans
      (zfr a (by omega) (by omega)))
  -- the stores and the return
  obtain ⟨ω14, μ14, run14, o0, o1, o5, o6, oO, oA, oG, oW, ofr, ord, owr⟩ := t7 (p := p) (P := P) (R := R)
    x ω13 μ13 (A - 176) O ret t v5 v6 (Num.decodeLE (μ.readN (ptr + 4) 8)) (Num.decodeLE (μ.readN (ptr + 12) 8))
    (Num.decodeLE (μ13.readN (A - 176 + 16) 8)) rd (by omega) (by omega) (by omega) d1
    (d5.trans (c5.trans (g5.trans (y5.trans (z5.trans (w5.trans (u5.trans (q5.trans (n5.trans (k5.trans
      (m5.trans f5)))))))))))
    (dl _) (dl _) (by have := decodeLE_lt (μ13.readN (A - 176 + 16) 8); simpa [Memory.length_readN] using this)
    F.hv5 F.hv6 hrd64 hO64
    (by rw [Memory.readN_congr (fun j hj => b13a _ (by omega) (by omega))]; exact qa)
    (by rw [Memory.readN_congr (fun j hj => b13g _ (by omega) (by omega))]; exact wg)
    (el _ _).symm
    (by rw [show A - 176 + 168 = A - 8 by omega, Memory.readN_congr (fun j hj => b13s _ (by omega) (by omega))]
        exact f88)
    (by rw [show A - 176 + 160 = A - 16 by omega, Memory.readN_congr (fun j hj => b13s _ (by omega) (by omega))]
        exact f80)
    (by rw [show A - 176 + 152 = A - 24 by omega, Memory.readN_congr (fun j hj => b13s _ (by omega) (by omega))]
        exact f72)
    (by rw [show A - 176 + 224 = A + 48 by omega,
          Memory.readN_congr (fun j hj => b13 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [show A - 176 + 216 = A + 40 by omega,
          Memory.readN_congr (fun j hj => b13 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [show A - 176 + 208 = A + 32 by omega,
          Memory.readN_congr (fun j hj => b13 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt
    (fun a h1 h2 => by rw [dwr, gwr, zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by
      rw [drd, grd, zrd, wrd, urd, qrd, nrd, krd, mrd, frd]
      rcases Nat.lt_or_ge a A with h | h
      · exact Memory.readable_of_writable (hws a (by omega) h)
      · exact F.hr a h (by omega))
  refine ⟨ω14, μ14, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans
    run14))))))))))))).mono (by omega), o0, by rw [o1]; congr 1; omega, o5, o6, oO, ?_, oA.trans (el _ _),
    oG.trans (el _ _), ?_, ?_, ?_, ?_,
    fun a => by rw [ord, drd, grd, zrd, wrd, urd, qrd, nrd, krd, mrd, frd],
    fun a => by rw [owr, dwr, gwr, zwr, wwr, uwr, qwr, nwr, kwr, mwr, fwr]⟩
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (by omega) (by omega)), dcp, gbuf]
    exact Memory.readN_congr (fun j hj => pay9 _ (by omega) (by omega))
  · rw [oW, ← take_encodeLE, el, Memory.readN_congr (fun j hj => b13u _ (by omega) (by omega)), ku32, el4]
  · rw [Memory.readN_congr (fun j hj => (ofr _ (by omega) (by omega) (by omega)).trans
      (dfr _ (by omega) (by omega) (by omega)))]
    exact gR0.trans (congrArg (Num.encodeLE 8) (by omega))
  · rw [Memory.readN_congr (fun j hj => (ofr _ (by omega) (by omega) (by omega)).trans
      (dfr _ (by omega) (by omega) (by omega)))]
    exact gR8.trans (congrArg (Num.encodeLE 8) (by omega))
  · intro a h0 h1 h2 h3
    rw [ofr a h0 (by omega) (by omega)]; exact b13 a h0 h1 h2 h3

end Services.Bootstrap.Decode.Transfer
