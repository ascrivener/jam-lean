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

end Services.Bootstrap.Decode.Transfer
