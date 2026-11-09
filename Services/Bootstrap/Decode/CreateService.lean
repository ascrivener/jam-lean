import Services.Bootstrap.Decode.LookedUp
import Services.Bootstrap.Decode.Fixed
import Services.Bootstrap.Decode.Transfer

/-!
# `Instruction::decode`: `CreateService` (tag 0)

`CreateService` (GP v0.8.0 B.7, the bootstrap service's instruction list; tag 0, the enum's dataful
variant, so no discriminant word: its `Option<Vec<u8>>`'s capacity word at O is the niche) is encoded as
`[0] ++ h ++ u₁ ++ u₂ ++ u₃ ++ u₄ ++ arr ++ ov ++ u₅ ++ ou`: a 32-octet code hash h, four `u64`s, a
128-octet array, an `Option<Vec<u8>>` ov, a `u64` u₅ and an `Option<u32>` ou.

Its decoder (20677) opens a 384-octet frame at S = A − 384 (the return address 934, O and the reader at
S + 376, S + 368, S + 360), and:
1. reads h into S + 232 (`read_big_sp`) and copies it to S + 72 … S + 104;
2. reads each `u64` into S + 232 and parks it at S + 64, S + 56, S + 48, S + 40;
3. zeroes S + 232 … S + 360 (`memzero`), reads the array into it (`read_big_sp`) and copies it to
   S + 104 … S + 232 (`memcpy_big_aligned`);
4. decodes the `Option<Vec<u8>>` (35937, `LookedUp`) into the 24-octet slot S + 232, its three words
   parked at S + 32, S + 24, S + 16 (the first word 2^64 − 2 is the error);
5. reads u₅ (3791, `read_u64`) and parks it at S + 8;
6. decodes the `Option<u32>` inline, in a 32-octet frame at S − 32 (return 1134 → 24372): the tag octet
   at S − 29; 0 gives ω₇ = 0 (`None`), 1 reads 4 octets at S − 28 and gives ω₇ = 1, ω₈ the `u32`
   sign-extended (`Some`);
7. stores into O: the option's words at O, O + 8, O + 16, the `Option<u32>`'s tag (`u32`) at O + 24, its
   value (`u32`) at O + 28, h at O + 32, the `u64`s at O + 64 … O + 96, the array at O + 96 … O + 224,
   u₅ at O + 224, and returns through 934 (20738) and its frame at A.

This file proves the steps `c1` … `c13`, generic in the host relation. The runs built from them are in
`Services.Bootstrap.Decode.CreateServiceRun` (`cs_head`, `cs_tail`, `create_service_none`) and
`Services.Bootstrap.Decode.CreateServiceHeap` (`create_service_heap`, the `Some` case through the heap).
-/

namespace Services.Bootstrap.Decode.CreateService

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

macro "cs_simp" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try (congr 1; omega)
  all_goals try rfl))

/-- A word read back as the octets it was read from. -/
theorem enc_rdN (μ : Memory) (a : Nat) : Num.encodeLE 8 (rdN μ a 8 % 18446744073709551616) = μ.readN a 8 := by
  rw [Nat.mod_eq_of_lt (rdN_lt64 μ a), encodeLE_rdN]

/-- The low four octets of a word read back as the octets they were read from. -/
theorem enc4_rdN (μ : Memory) (a : Nat) :
    Num.encodeLE 4 (rdN μ a 8 % 18446744073709551616 % 4294967296) = μ.readN a 4 := by
  rw [encodeLE_mod 4, ← take_encodeLE, enc_rdN, readN_take _ _ 8 4 (by decide)]

/-- `cs_simp` without its closing `rfl`, for goals with many stores. -/
macro "cs_simp2" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.getD_some', enc_rdN, enc4_rdN]))

/-- 20677 … 20734: `CreateService`'s decoder opens a 384-octet frame at S = A − 384 saving the return
    address 934, O and the reader at S + 376, S + 368, S + 360, zeroes S + 232 … S + 264 and calls the
    reader for 32 octets into S + 232 (return address 1114). -/
theorem c1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O rd : Nat)
    (hS : 65536 ≤ S ∧ S + 384 < 4294967296) (h1 : ω[1] = UInt64.ofNat (S + 384)) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 384 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20677 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1114 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 232) ∧
      ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (S + 376) 8 = Num.encodeLE 8 934 ∧ μ'.readN (S + 368) 8 = Num.encodeLE 8 O ∧
      μ'.readN (S + 360) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 384 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 24015 … 24061: the hash read succeeded (ω₇ = 0): its four words go from S + 232 to S + 72 … S + 104,
    S + 232 … S + 240 is zeroed and the reader called for 8 octets into S + 232 (return address 1116). -/
theorem c2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 264 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, S + 72 ≤ a → a < S + 104 → μ.writable a = true)
    (hw' : ∀ a, S + 232 ≤ a → a < S + 240 → μ.writable a = true)
    (hr : ∀ a, S + 232 ≤ a → a < S + 264 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24015 ω μ x 58434 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 1116 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 232) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (S + 72) 32 = μ.readN (S + 232) 32 ∧
      (∀ a, a < 4294967296 → (a < S + 72 ∨ S + 104 ≤ a) → (a < S + 232 ∨ S + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hw', hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (have := copy4g μ μ (S + 232) (S + 72) (by omega); simp only [Nat.add_assoc, Nat.reduceAdd] at this; exact this)

/-- 24068 … 24093, 24100 … 24124, 24131 … 24155: a `u64` read succeeded (ω₇ = 0): it is parked at
    S + k (k = 64, 56, 48), S + 232 … S + 240 is zeroed and the reader called for 8 octets into S + 232
    (return address r = 1118, 1120, 1122). -/
theorem c3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (e k r S v : Nat)
    (he : (e = 24068 ∧ k = 64 ∧ r = 1118) ∨ (e = 24100 ∧ k = 56 ∧ r = 1120) ∨ (e = 24131 ∧ k = 48 ∧ r = 1122))
    (hS : S + 240 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (sv : μ.readN (S + 232) 8 = Num.encodeLE 8 v)
    (hw0 : ∀ a, S + k ≤ a → a < S + k + 8 → μ.writable a = true)
    (hw : ∀ a, S + 232 ≤ a → a < S + 240 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R e ω μ x 58434 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 232) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (S + k) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S + k ∨ S + k + 8 ≤ a) → (a < S + 232 ∨ S + 240 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 232) 8 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  have hr : ∀ a, S + 232 ≤ a → a < S + 240 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hS, hw, hw0, hr, rv, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      cs_simp
      all_goals try exact UInt64.ofNat_toNat
      all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 24162 … 24183: the fourth `u64` read succeeded (ω₇ = 0): it is parked at S + 40, and `memzero` is
    called for the 128 octets at S + 232 (return address 1124). -/
theorem c4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 240 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (sv : μ.readN (S + 232) 8 = Num.encodeLE 8 v)
    (hw0 : ∀ a, S + 40 ≤ a → a < S + 48 → μ.writable a = true)
    (hr : ∀ a, S + 232 ≤ a → a < S + 240 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24162 ω μ x 70133 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1124 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 232) ∧ ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat 128 ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S + 40 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 232) 8 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw0, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 24190 … 24200: after `memzero`, the reader is called for the 128-octet array into S + 232 (return
    address 1126). -/
theorem c5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 360 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 24190 ω μ x 58434 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat 1126 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 232) ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 24207 then 24235 … 24246: the array read succeeded (ω₇ = 0): `memcpy` is called to copy the 128
    octets at S + 232 to S + 104 (return address 1128). -/
theorem c6 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 360 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0) :
    ∃ ω', FreeStepsH p R 24207 ω μ x 68729 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1128 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 104) ∧ ω'[8] = UInt64.ofNat (S + 232) ∧ ω'[9] = UInt64.ofNat 128 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 24253 … 24259: `Option<Vec<u8>>::decode` (35937) is called with its slot S + 232 (ω₇) and the reader
    (ω₈ = ω₆), return address 1130. -/
theorem c7 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 360 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) :
    ∃ ω', FreeStepsH p R 24253 ω μ x 35937 ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat 1130 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 232) ∧ ω'[8] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 24265 … 24316: `Option<Vec<u8>>::decode` returned without error (the word W at S + 232 is not
    2^64 − 2): its three words W, w₁, w₂ are parked at S + 32, S + 24, S + 16, and the `u64` reader (3791)
    is called on the reader (ω₇ = ω₆), return address 1132. -/
theorem c8 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S W w1 w2 : Nat)
    (hS : S + 256 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hW : W < 18446744073709551616) (hW' : W ≠ 18446744073709551614) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616)
    (sW : μ.readN (S + 232) 8 = Num.encodeLE 8 W) (s1 : μ.readN (S + 240) 8 = Num.encodeLE 8 w1)
    (s2 : μ.readN (S + 248) 8 = Num.encodeLE 8 w2)
    (hw : ∀ a, S + 16 ≤ a → a < S + 40 → μ.writable a = true)
    (hr : ∀ a, S + 232 ≤ a → a < S + 256 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24265 ω μ x 3791 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1132 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 W ∧ μ'.readN (S + 24) 8 = Num.encodeLE 8 w1 ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 w2 ∧
      (∀ a, a < 4294967296 → (a < S + 16 ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rW := LookedUp.rd8 hW sW
  have r1 := LookedUp.rd8 hw1 s1
  have r2 := LookedUp.rd8 hw2 s2
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, hw, hr, rW, r1, r2, hW', rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 24322 … 24368: the `u64` read succeeded (ω₇ = 0, the value v in ω₈): v is parked at S + 8; the
    `Option<u32>` decoder opens a 32-octet frame at S − 32 (the return address 1134, O and the reader at
    S − 8, S − 16, S − 24), keeps the reader in ω₅, zeroes the octet at S − 29 and calls the reader for
    1 octet into S − 29 (return address 1688). -/
theorem c9 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O rd v : Nat)
    (hS : 65536 + 32 ≤ S ∧ S + 16 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat v)
    (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616) (hv : v < 18446744073709551616)
    (hw : ∀ a, S - 32 ≤ a → a < S → μ.writable a = true)
    (hw8 : ∀ a, S + 8 ≤ a → a < S + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 24322 ω μ x 58434 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 1688 ∧ ω'[1] = UInt64.ofNat (S - 32) ∧ ω'[5] = UInt64.ofNat rd ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S - 29) ∧
      ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (S + 8) 8 = Num.encodeLE 8 v ∧ μ'.readN (S - 8) 8 = Num.encodeLE 8 1134 ∧
      μ'.readN (S - 16) 8 = Num.encodeLE 8 O ∧ μ'.readN (S - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < S - 32 ∨ S ≤ a) → (a < S + 8 ∨ S + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, h8, hS, hw, hw8]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp
    all_goals (try simp only [show S - 32 + 24 = S - 8 by omega, show S - 32 + 16 = S - 16 by omega,
      show S - 32 + 8 = S - 24 by omega]); cs_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
    all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))

/-- 36095 … 36147: the tag octet was read (ω₇ = 0) and is 0 (`None`): the `Option<u32>` decoder
    returns ω₇ = 0, restoring ω₀, ω₅, ω₆ from its frame at F and returning (to 24372). -/
theorem c10n {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F O rd : Nat)
    (hF : 65536 ≤ F ∧ F + 32 < 4294967296) (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat 1)
    (h7 : ω[7] = UInt64.ofNat 0) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (tag : μ.read (F + 3) = 0)
    (s0 : μ.readN (F + 24) 8 = Num.encodeLE 8 1134) (s5 : μ.readN (F + 16) 8 = Num.encodeLE 8 O)
    (s6 : μ.readN (F + 8) 8 = Num.encodeLE 8 rd)
    (hr : ∀ a, F ≤ a → a < F + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 36095 ω μ x 24372 ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat 1134 ∧ ω'[1] = UInt64.ofNat (F + 32) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = ω[8] := by
  have rb : rdN μ (F + 3) 1 = 0 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  have r0 := LookedUp.rd8 (by decide) s0
  have r5 := LookedUp.rd8 hO s5
  have r6 := LookedUp.rd8 hrd s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, h7, hF, hr, rb, r0, r5, r6, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    cs_simp

/-- 36095 … 36121: the tag octet was read (ω₇ = 0) and is 1 (`Some`): the `Option<u32>` decoder zeroes
    F + 4 … F + 8 and calls the reader (ω₇ = ω₅) for 4 octets into F + 4 (return address 1690). -/
theorem c10s {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F : Nat)
    (hF : 65536 ≤ F ∧ F + 32 < 4294967296) (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat 1)
    (h7 : ω[7] = UInt64.ofNat 0) (tag : μ.read (F + 3) = 1)
    (hr : μ.readable (F + 3) = true) (hw : ∀ a, F + 4 ≤ a → a < F + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36095 ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1690 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[5] ∧
      ω'[8] = UInt64.ofNat (F + 4) ∧ ω'[9] = UInt64.ofNat 4 ∧
      (∀ a, a < 4294967296 → (a < F + 4 ∨ F + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rb : rdN μ (F + 3) 1 = 1 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, h7, hF, hr, hw, rb, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 36127 … 36168: the 4 octets were read (ω₇ = 0) into F + 4, the `u32` v: the `Option<u32>` decoder
    returns ω₇ = 1 and ω₈ = v sign-extended, restoring ω₀, ω₅, ω₆ from its frame at F and returning (to
    24372). -/
theorem c11 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (F O rd v : Nat)
    (hF : 65536 ≤ F ∧ F + 32 < 4294967296) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat 0)
    (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616) (hv : v < 4294967296)
    (sv : μ.readN (F + 4) 4 = Num.encodeLE 4 v)
    (s0 : μ.readN (F + 24) 8 = Num.encodeLE 8 1134) (s5 : μ.readN (F + 16) 8 = Num.encodeLE 8 O)
    (s6 : μ.readN (F + 8) 8 = Num.encodeLE 8 rd)
    (hr : ∀ a, F ≤ a → a < F + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 36127 ω μ x 24372 ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat 1134 ∧ ω'[1] = UInt64.ofNat (F + 32) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat 1 ∧ ω'[8] = UInt64.ofNat (sxw 4 v) := by
  have rv : rdN μ (F + 4) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have r0 := LookedUp.rd8 (by decide) s0
  have r5 := LookedUp.rd8 hO s5
  have r6 := LookedUp.rd8 hrd s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, hF, hr, rv, r0, r5, r6, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    cs_simp

/-- 24372 … 24419: the `Option<u32>` decoder returned its tag τ ∈ {0, 1} (ω₇) and value v (ω₈): τ is
    kept in ω₆, v parked at S, the hash's four words copied from S + 72 … S + 104 to O + 32 … O + 64, and
    `memcpy` called to copy the 128 octets at S + 104 to O + 96 (return address 1136). -/
theorem c12 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O τ v : Nat)
    (hS : S + 104 ≤ 4294967296) (hO : O + 96 < 4294967296) (hOS : O + 64 ≤ S ∨ S + 104 ≤ O + 32)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (h7 : ω[7] = UInt64.ofNat τ) (hτ : τ = 0 ∨ τ = 1) (h8 : ω[8] = UInt64.ofNat v)
    (hv : v < 18446744073709551616)
    (hw : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hwO : ∀ a, O + 32 ≤ a → a < O + 64 → μ.writable a = true)
    (hr : ∀ a, S + 72 ≤ a → a < S + 104 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24372 ω μ x 68729 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 1136 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat τ ∧
      ω'[7] = UInt64.ofNat (O + 96) ∧ ω'[8] = UInt64.ofNat (S + 104) ∧ ω'[9] = UInt64.ofNat 128 ∧
      μ'.readN S 8 = Num.encodeLE 8 v ∧ μ'.readN (O + 32) 32 = μ.readN (S + 72) 32 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < O + 32 ∨ O + 64 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hτ with rfl | rfl <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, h7, h8, hS, hO, hOS, hw, hwO, hr, rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?hash, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      case hash =>
        have := copy4g μ (μ.writeN S (Num.encodeLE 8 v)) (S + 72) (O + 32) (by omega)
        rw [show S + 72 + 8 = S + 80 from rfl, show S + 72 + 16 = S + 88 from rfl,
          show S + 72 + 24 = S + 96 from rfl] at this
        exact this
      cs_simp2
      all_goals try exact UInt64.ofNat_toNat
      all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 24426 … 24443: the option's words (S + 32, S + 24, S + 16) go to O, O + 8, O + 16 and the
    `Option<u32>`'s tag τ (ω₆) as a `u32` to O + 24. -/
theorem c13a {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O τ : Nat) (hS : S + 40 ≤ 4294967296) (hO : O + 28 ≤ 4294967296)
    (hOS : O + 28 ≤ S + 16 ∨ S + 40 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat τ) (hτ : τ < 2)
    (hw : ∀ a, O ≤ a → a < O + 28 → μ.writable a = true)
    (hr : ∀ a, S + 16 ≤ a → a < S + 40 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24426 ω μ x 24446 ω' μ' x 8 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN O 8 = μ.readN (S + 32) 8 ∧ μ'.readN (O + 8) 8 = μ.readN (S + 24) 8 ∧
      μ'.readN (O + 16) 8 = μ.readN (S + 16) 8 ∧ μ'.readN (O + 24) 4 = Num.encodeLE 4 τ ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 28 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hO, hOS, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp2

/-- 24446 … 24478: the low four octets of the word at S go to O + 28, the `u64`s (S + 64, S + 56,
    S + 48, S + 40) to O + 64 … O + 96 and the `u64` at S + 8 to O + 224. -/
theorem c13b {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O : Nat) (hS : S + 72 ≤ 4294967296) (hO : O + 232 ≤ 4294967296)
    (hOS : O + 232 ≤ S ∨ S + 72 ≤ O + 28)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (hw : ∀ a, O + 28 ≤ a → a < O + 232 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 72 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24446 ω μ x 24482 ω' μ' x 14 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (O + 28) 4 = μ.readN S 4 ∧
      μ'.readN (O + 64) 8 = μ.readN (S + 64) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (S + 56) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (S + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (S + 40) 8 ∧
      μ'.readN (O + 224) 8 = μ.readN (S + 8) 8 ∧
      (∀ a, a < 4294967296 → (a < O + 28 ∨ O + 32 ≤ a) → (a < O + 64 ∨ O + 96 ≤ a) → (a < O + 224 ∨ O + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hS, hO, hOS, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
    cs_simp2

/-- 24482 … 24498 then 20738 … 20750: the decoder pops its frame through 934 to 20738 and returns
    through its frame at A = S + 384. -/
theorem c13c {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S ret t v5 v6 : Nat) (hA : S + 384 + 56 < 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sr : μ.readN (S + 376) 8 = Num.encodeLE 8 934)
    (s0 : μ.readN (S + 432) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 424) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 416) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, S + 360 ≤ a → a < S + 440 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 24482 ω μ x t ω' μ x 12 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have rr := LookedUp.rd8 (by decide) sr
  have r0 : rdN μ (S + 384 + 48) 8 = ret := by
    rw [show S + 384 + 48 = S + 432 by omega]; exact LookedUp.rd8 (by omega) s0
  have r5 : rdN μ (S + 384 + 40) 8 = v5 := by
    rw [show S + 384 + 40 = S + 424 by omega]; exact LookedUp.rd8 hv5 s5
  have r6 : rdN μ (S + 384 + 32) 8 = v6 := by
    rw [show S + 384 + 32 = S + 416 by omega]; exact LookedUp.rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hA, hr, rr, r0, r5, r6, hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    cs_simp

/-- 24426 … 24498 then 20738 … 20750: `c13a`, `c13b`, `c13c`: the stores into O and the return through
    934 (20738) and the frame at A = S + 384. -/
theorem c13 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O τ ret t v5 v6 : Nat) (hA : S + 384 + 56 < 4294967296) (hO : O + 232 ≤ 4294967296)
    (hOS : O + 232 ≤ S ∨ S + 440 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat τ) (hτ : τ < 2)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sr : μ.readN (S + 376) 8 = Num.encodeLE 8 934)
    (s0 : μ.readN (S + 432) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 424) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 416) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 232 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 440 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24426 ω μ x t ω' μ' x 34 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = μ.readN (S + 32) 8 ∧ μ'.readN (O + 8) 8 = μ.readN (S + 24) 8 ∧
      μ'.readN (O + 16) 8 = μ.readN (S + 16) 8 ∧ μ'.readN (O + 24) 4 = Num.encodeLE 4 τ ∧
      μ'.readN (O + 28) 4 = μ.readN S 4 ∧
      μ'.readN (O + 64) 8 = μ.readN (S + 64) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (S + 56) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (S + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (S + 40) 8 ∧
      μ'.readN (O + 224) 8 = μ.readN (S + 8) 8 ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 32 ≤ a) → (a < O + 64 ∨ O + 96 ≤ a) → (a < O + 224 ∨ O + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, aO, aO8, aO16, aO24, afr, ard, awr⟩ :=
    c13a (p := p) (P := P) (R := R) x ω μ S O τ (by omega) (by omega) (by omega) h1 h5 h6 hτ
      (fun a h1 h2 => hw a h1 (by omega)) (fun a h1 h2 => hr a (by omega) (by omega))
  have b1 : ∀ a, S ≤ a → a < S + 440 → μ1.read a = μ.read a := fun a h1 h2 => afr a (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, b0, b1', b5, b6, bO28, bO64, bO72, bO80, bO88, bO224, bfr, brd, bwr⟩ :=
    c13b (p := p) (P := P) (R := R) x ω1 μ1 S O (by omega) hO (by omega) (a1.trans h1) (a5.trans h5)
      (fun a h1 h2 => by rw [awr]; exact hw a (by omega) h2)
      (fun a h1 h2 => by rw [ard]; exact hr a h1 (by omega))
  have b2 : ∀ a, S ≤ a → a < S + 440 → μ2.read a = μ.read a := fun a h1 h2 =>
    (bfr a (by omega) (by omega) (by omega) (by omega)).trans (b1 a h1 h2)
  obtain ⟨ω3, run3, c0, c1, c5, c6⟩ :=
    c13c (p := p) (P := P) (R := R) x ω2 μ2 S ret t v5 v6 hA (b1'.trans (a1.trans h1)) hv5 hv6
      (by rw [Memory.readN_congr (fun j hj => b2 _ (by omega) (by omega))]; exact sr)
      (by rw [Memory.readN_congr (fun j hj => b2 _ (by omega) (by omega))]; exact s0)
      (by rw [Memory.readN_congr (fun j hj => b2 _ (by omega) (by omega))]; exact s5)
      (by rw [Memory.readN_congr (fun j hj => b2 _ (by omega) (by omega))]; exact s6)
      hret hjt hbt (fun a h1 h2 => by rw [brd, ard]; exact hr a (by omega) h2)
  refine ⟨ω3, μ2, (run1.trans (run2.trans run3)).mono (by omega), c0, c1, c5, c6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, fun a h0 h1 h2 h3 => ?_, fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega)), aO]
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega)), aO8]
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega)), aO16]
  · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega)), aO24]
  · rw [bO28]; exact Memory.readN_congr (fun j hj => b1 _ (by omega) (by omega))
  · rw [bO64]; exact Memory.readN_congr (fun j hj => b1 _ (by omega) (by omega))
  · rw [bO72]; exact Memory.readN_congr (fun j hj => b1 _ (by omega) (by omega))
  · rw [bO80]; exact Memory.readN_congr (fun j hj => b1 _ (by omega) (by omega))
  · rw [bO88]; exact Memory.readN_congr (fun j hj => b1 _ (by omega) (by omega))
  · rw [bO224]; exact Memory.readN_congr (fun j hj => b1 _ (by omega) (by omega))
  · rw [bfr a h0 (by omega) h2 h3]; exact afr a h0 (by omega)

end Services.Bootstrap.Decode.CreateService
