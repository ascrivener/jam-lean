import Services.Bootstrap.Decode.U32Hash
import Services.Bootstrap.DecodeU32

/-!
# `Instruction::decode` of `Bless` with no always-accumulate entries

`Bless { manager, assigner, designator, registrar: u32, always_acc: Vec<(u32, u64)> }` (tag 11) is
decoded by a helper with an 80-octet frame at H = A − 80. It reads the four `u32`s into H + 32 in turn
(`read_ok`), parking each, sign-extended, at H + 24, H + 16, H + 8 and H. It decodes the length n
(`decodeU32`) and reads the n pairs into a `Vec` at H + 32 (the element reader at 2727). It then stores
the variant into the slot O: the discriminant word 2^63 + 10 at O, the `Vec` at O + 8 and the four
`u32`s at O + 32, O + 36, O + 40, O + 44.

This file proves the case n = 0, which allocates nothing: `bless_empty`.
-/

namespace Services.Bootstrap.Decode.Bless

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.U32Hash

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

theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

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

/-- 20857 … 20896: `Bless`'s decoder enters the helper: an 80-octet frame at H = A − 80 saving the
    return address 944, O and the reader at H + 72, H + 64, H + 56, a zeroed `u32` at H + 32, and the
    call of the reader for 4 octets into H + 32 (return address 1140). -/
theorem b1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 80 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 80 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20857 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1140 ∧ ω'[1] = UInt64.ofNat (A - 80) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 48) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 944 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 80 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show A - 80 + 72 = A - 8 by omega, show A - 80 + 64 = A - 16 by omega,
      show A - 80 + 56 = A - 24 by omega, show A - 80 + 32 = A - 48 by omega])
    post_simp
    all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
    all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))

/-- The three parks between the `u32` reads: at `pc` (24543, 24572, 24601), the read succeeded
    (ω₇ = 0): the helper parks the `u32` at H + 32, sign-extended, as a word at H + off (24, 16, 8),
    zeroes H + 32 … H + 36 and calls the reader for the next 4 octets into H + 32 (return address r). -/
theorem bk {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (pc off r H v : Nat)
    (hk : (pc = 24543 ∧ off = 24 ∧ r = 1142) ∨ (pc = 24572 ∧ off = 16 ∧ r = 1144) ∨
      (pc = 24601 ∧ off = 8 ∧ r = 1146))
    (hH : H + 80 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (H + 32) 4 = Num.encodeLE 4 v)
    (hw0 : ∀ a, H + off ≤ a → a < H + off + 8 → μ.writable a = true)
    (hw : ∀ a, H + 32 ≤ a → a < H + 36 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R pc ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (H + 32) ∧ ω'[9] = UInt64.ofNat 4 ∧
      (μ'.readN (H + off) 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < H + off ∨ H + off + 8 ≤ a) → (a < H + 32 ∨ H + 36 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (H + 32) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, H + 32 ≤ a → a < H + 36 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  rcases hk with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h7, hH, hw, hw0, hr, rv, ↓rdN_fold, ↓loadI_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      post_simp
      all_goals try exact UInt64.ofNat_toNat
      all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 24630 … 24641: the fourth read succeeded (ω₇ = 0): the helper parks the `u32` at H + 32,
    sign-extended, as a word at H and calls the length decoder (31894) on the reader (return address
    1148). -/
theorem b5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H v : Nat)
    (hH : H + 80 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (H + 32) 4 = Num.encodeLE 4 v)
    (hw0 : ∀ a, H ≤ a → a < H + 8 → μ.writable a = true)
    (hr : ∀ a, H + 32 ≤ a → a < H + 36 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24630 ω μ x 31894 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1148 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = ω[6] ∧
      (μ'.readN H 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < H ∨ H + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (H + 32) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hH, hw0, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 24647 … 24664: the length n < 2^32 was decoded (ω₇ = 0, ω₈ = n): the pair reader (2727) is called for
    n pairs into a `Vec` at H + 32 (ω₇ = H + 32, ω₈ = the reader ω₆, ω₉ = n), return address 1150. -/
theorem b6 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (H n : Nat) (hH : H + 32 < 4294967296) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R 24647 ω μ x 2727 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 1150 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (H + 32) ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h7, h8, hH, hn]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- **The `(u32, u64)` reader with no elements** (2727, n = 0): it opens a 120-octet frame, finds
    nothing to read, stores the empty `Vec` `{cap 0, ptr 8, len 0}` at O (ω₇), restores ω₀, ω₅, ω₆ and
    returns. -/
theorem pairs_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp O rd ret t v5 v6 : Nat) (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat 0) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ sp - 128 ∨ sp ≤ O)
    (hw : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 2727 ω μ x t ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 8 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 128 ∨ sp ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 128 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hwO, hO, hOS, hret, hjt, hbt,
      rdN_writeN_disjoint, rdN_writeN_same8, rdN_writeN_lit, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show sp - 120 + 120 = sp by omega])
    post_simp
    all_goals try decide

/-- 24670 … 24743: the pair reader stored a `Vec` `{cap, ptr, len}` at H + 32 (cap ≠ 2^64 − 1): the
    helper stores the discriminant word 2^63 + 10 at O, the three words at O + 8, O + 16, O + 24 and the
    low four octets of the parked words w₀ … w₃ (at H + 24, H + 16, H + 8, H) at O + 32, O + 36, O + 40,
    O + 44; it restores ω₀, ω₅, ω₆ from H + 72, H + 64, H + 56 and returns to 944's entry, 20900. -/
theorem b7 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (H O cap ptr len w0 w1 w2 w3 o6 : Nat) (hH : H + 80 < 4294967296) (hO : O + 48 ≤ 4294967296)
    (hOH : O + 48 ≤ H ∨ H + 80 ≤ O)
    (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat O)
    (hcap : cap < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616)
    (hw2 : w2 < 18446744073709551616) (hw3 : w3 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sc : μ.readN (H + 32) 8 = Num.encodeLE 8 cap) (sp : μ.readN (H + 40) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (H + 48) 8 = Num.encodeLE 8 len)
    (s0 : μ.readN (H + 24) 8 = Num.encodeLE 8 w0) (s1 : μ.readN (H + 16) 8 = Num.encodeLE 8 w1)
    (s2 : μ.readN (H + 8) 8 = Num.encodeLE 8 w2) (s3 : μ.readN H 8 = Num.encodeLE 8 w3)
    (sr : μ.readN (H + 72) 8 = Num.encodeLE 8 944) (sO : μ.readN (H + 64) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (H + 56) 8 = Num.encodeLE 8 o6)
    (hw : ∀ x, O ≤ x → x < O + 48 → μ.writable x = true)
    (hr : ∀ x, H ≤ x → x < H + 80 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 24670 ω μ x 20900 ω' μ' x 30 ∧
      ω'[0] = UInt64.ofNat 944 ∧ ω'[1] = UInt64.ofNat (H + 80) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat o6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775818 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 len ∧
      μ'.readN (O + 32) 4 = Num.encodeLE 4 w0 ∧ μ'.readN (O + 36) 4 = Num.encodeLE 4 w1 ∧
      μ'.readN (O + 40) 4 = Num.encodeLE 4 w2 ∧ μ'.readN (O + 44) 4 = Num.encodeLE 4 w3 ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 48 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rc := rd8 (by omega) sc
  have rp := rd8 hptr sp
  have rl := rd8 hlen sl
  have r0 := rd8 hw0 s0
  have r1 := rd8 hw1 s1
  have r2 := rd8 hw2 s2
  have r3 := rd8 hw3 s3
  have rr := rd8 (by decide) sr
  have rO := rd8 hOv sO
  have ro6 := rd8 ho6 so6
  have hc : ¬ cap = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hH, hO, hOH, hw, hr, rc, rp, rl, r0, r1, r2, r3, rr, rO, ro6, hc, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try exact encodeLE_mod 4 _

/-- 20900 … 20912: `Instruction::decode`'s end for `Bless`: restore ω₀, ω₅, ω₆ from the frame at A and
    return. -/
theorem b8 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A ret t v5 v6 : Nat) (hA : 65536 ≤ A ∧ A + 56 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat A)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, A + 32 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 20900 ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hA, hr, r0, r5, r6, hret, hjt, hbt, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    post_simp

/-- The four octets of a `u32` field, read back from where `read_ok` put them. -/
theorem u32_of {μ : Memory} {a : Nat} :
    Num.decodeLE (μ.readN a 4) < 4294967296 ∧ Num.encodeLE 4 (Num.decodeLE (μ.readN a 4)) = μ.readN a 4 := by
  refine ⟨?_, ?_⟩
  · have := decodeLE_lt (μ.readN a 4); simpa [Memory.length_readN] using this
  · have := encodeLE_decodeLE (μ.readN a 4); simpa [Memory.length_readN] using this

/-- **`Bless` with no always-accumulate entries**: from 20626, with tag 11 read without error and the
    reader `{ptr, len}` at rd (ω₆) holding the four `u32`s (16 octets) and then ℰ(0) (the octet 0),
    `Instruction::decode` returns `Bless { manager, assigner, designator, registrar, always_acc: [] }`
    in its slot O: the discriminant word 2^63 + 10 at O, the empty `Vec` `{cap 0, ptr 8, len 0}` at O + 8,
    and the four `u32`s (from ptr, ptr + 4, ptr + 8, ptr + 12) at O + 32, O + 36, O + 40, O + 44. Nothing
    is allocated. The reader is advanced by 17. Memory changes only in A − 208 … A (the helper's and the
    callees' frames), the reader and O … O + 48. -/
theorem bless_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 208 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 11) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 48 < 4294967296)
    (hlen : 17 ≤ len ∧ len < 4294967296) (hzero : μ.read (ptr + 16) = 0)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 208 ∨ A + 56 ≤ rd) (hpA : ptr + 48 ≤ A - 208 ∨ A + 56 ≤ ptr)
    (hOA : O + 48 ≤ A - 208 ∨ A + 56 ≤ O) (hOr : O + 48 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 48 ≤ rd ∨ rd + 16 ≤ ptr) (hO48 : O + 48 ≤ 4294967296)
    (hws : ∀ a, A - 208 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 48 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 17 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 1000 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775818 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 8 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (O + 32) 4 = μ.readN ptr 4 ∧ μ'.readN (O + 36) 4 = μ.readN (ptr + 4) 4 ∧
      μ'.readN (O + 40) 4 = μ.readN (ptr + 8) 4 ∧ μ'.readN (O + 44) 4 = μ.readN (ptr + 12) 4 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 17) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 17) ∧
      (∀ a, a < 4294967296 → (a < A - 208 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 48 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  obtain ⟨hv0, ev0⟩ := u32_of (μ := μ) (a := ptr)
  obtain ⟨hv1, ev1⟩ := u32_of (μ := μ) (a := ptr + 4)
  obtain ⟨hv2, ev2⟩ := u32_of (μ := μ) (a := ptr + 8)
  obtain ⟨hv3, ev3⟩ := u32_of (μ := μ) (a := ptr + 12)
  -- abbreviations: H the helper's frame, B the buffer at H + 32
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 11 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f72, f64, f56, ffr, frd, fwr⟩ :=
    b1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- manager
  obtain ⟨ω3, μ3, run3, g0, g1, -, -, -, g5, g6, -, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1140 24543 (A - 80) rd (A - 48) ptr len 4 f0 f1 f7 f8 f9
      (by decide) jte_569 bs_24543 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  have pay3 : ∀ q, ptr ≤ q → q < ptr + 17 → μ3.read q = μ.read q := fun q h1 h2 =>
    (gfr q (by omega) (by omega) (by omega) (by omega)).trans (ffr q (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    bk (p := p) (P := P) (R := R) x ω3 μ3 24543 24 1142 (A - 80) (Num.decodeLE (μ.readN ptr 4))
      (Or.inl ⟨rfl, rfl, rfl⟩) (by omega) (g1.trans f1) g7 hv0
      (by rw [show A - 80 + 32 = A - 48 by omega, gbuf, ev0]
          exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  -- assigner
  obtain ⟨ω5, μ5, run5, m0, m1, -, -, -, m5, m6, -, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1142 24572 (A - 80) rd (A - 48) (ptr + 4) (len - 4) 4 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) (by rw [k8, show A - 80 + 32 = A - 48 by omega]) k9
      (by decide) jte_570 bs_24572 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have pay5 : ∀ q, ptr ≤ q → q < ptr + 17 → μ5.read q = μ.read q := fun q h1 h2 =>
    (mfr q (by omega) (by omega) (by omega) (by omega)).trans ((kfr q (by omega) (by omega) (by omega)).trans
      (pay3 q h1 h2))
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, n7, n8, n9, npark, nfr, nrd, nwr⟩ :=
    bk (p := p) (P := P) (R := R) x ω5 μ5 24572 16 1144 (A - 80) (Num.decodeLE (μ.readN (ptr + 4) 4))
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (by omega) (m1.trans (k1.trans (g1.trans f1))) m7 hv1
      (by rw [show A - 80 + 32 = A - 48 by omega, mbuf, ev1]
          exact Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega) (by omega)).trans (pay3 _ (by omega) (by omega))))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- designator
  obtain ⟨ω7, μ7, run7, q0, q1, -, -, -, q5, q6, -, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω6 μ6 1144 24601 (A - 80) rd (A - 48) (ptr + 4 + 4) (len - 4 - 4) 4 n0
      (n1.trans (m1.trans (k1.trans (g1.trans f1)))) (n7.trans (m6.trans (k6.trans (g6.trans f6))))
      (by rw [n8, show A - 80 + 32 = A - 48 by omega]) n9
      (by decide) jte_571 bs_24601 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR8)
  have pay7 : ∀ q, ptr ≤ q → q < ptr + 17 → μ7.read q = μ.read q := fun q h1 h2 =>
    (qfr q (by omega) (by omega) (by omega) (by omega)).trans ((nfr q (by omega) (by omega) (by omega)).trans
      (pay5 q h1 h2))
  obtain ⟨ω8, μ8, run8, r0, r1, r5, r6, r7, r8, r9, rpark, rfr, rrd, rwr⟩ :=
    bk (p := p) (P := P) (R := R) x ω7 μ7 24601 8 1146 (A - 80) (Num.decodeLE (μ.readN (ptr + 8) 4))
      (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) (by omega) (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))) q7 hv2
      (by rw [show A - 80 + 32 = A - 48 by omega, qbuf, ev2, show ptr + 4 + 4 = ptr + 8 by omega]
          exact Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega)).trans (pay5 _ (by omega) (by omega))))
      (fun a h1 h2 => by rw [qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- registrar
  obtain ⟨ω9, μ9, run9, s0, s1, -, -, -, s5, s6, -, s7, sR0, sR8, sbuf, sfr, srd, swr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω8 μ8 1146 24630 (A - 80) rd (A - 48) (ptr + 4 + 4 + 4) (len - 4 - 4 - 4) 4 r0
      (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))))
      (r7.trans (q6.trans (n6.trans (m6.trans (k6.trans (g6.trans f6))))))
      (by rw [r8, show A - 80 + 32 = A - 48 by omega]) r9
      (by decide) jte_572 bs_24630 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rrd, qrd, nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega) (by omega))]; exact qR0)
      (by rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega) (by omega))]; exact qR8)
  have pay9 : ∀ q, ptr ≤ q → q < ptr + 17 → μ9.read q = μ.read q := fun q h1 h2 =>
    (sfr q (by omega) (by omega) (by omega) (by omega)).trans ((rfr q (by omega) (by omega) (by omega)).trans
      (pay7 q h1 h2))
  obtain ⟨ω10, μ10, run10, u0, u1, u5, u6, u7, upark, ufr, urd, uwr⟩ :=
    b5 (p := p) (P := P) (R := R) x ω9 μ9 (A - 80) (Num.decodeLE (μ.readN (ptr + 12) 4)) (by omega)
      (s1.trans (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))))) s7 hv3
      (by rw [show A - 80 + 32 = A - 48 by omega, sbuf, ev3, show ptr + 4 + 4 + 4 = ptr + 12 by omega]
          exact Memory.readN_congr (fun j hj => (rfr _ (by omega) (by omega) (by omega)).trans (pay7 _ (by omega) (by omega))))
      (fun a h1 h2 => by rw [swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [srd, rrd, qrd, nrd, mrd, krd, grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have h1_10 : ω10[1] = UInt64.ofNat (A - 80) := u1.trans (s1.trans (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1)))))))
  have h6_10 : ω10[6] = UInt64.ofNat rd := u6.trans (s6.trans (r6.trans (q6.trans (n6.trans (m6.trans (k6.trans (g6.trans f6)))))))
  have h5_10 : ω10[5] = UInt64.ofNat O := u5.trans (s5.trans (r5.trans (q5.trans (n5.trans (m5.trans (k5.trans (g5.trans f5)))))))
  -- the length ℰ(0)
  have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := by simp [Blob.encodeNat]
  have hz10 : μ10.read (ptr + 16) = 0 := by
    rw [ufr _ (by omega) (by omega), pay9 _ (by omega) (by omega)]; exact hzero
  obtain ⟨ω11, μ11, run11, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω10 μ10 1148 24647 (A - 80) rd (ptr + 4 + 4 + 4 + 4)
      (len - 4 - 4 - 4 - 4) u0 h1_10 (u7.trans (u6.symm.trans h6_10)) (by decide) jte_573 bs_24647 ⟨by omega, by omega⟩ hrd
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => ufr _ (by omega) (by omega))]; exact sR0)
      (by rw [Memory.readN_congr (fun j hj => ufr _ (by omega) (by omega))]; exact sR8) 0 (by decide)
      (by rw [he]; simp; omega)
      (fun a h1 h2 => by
        rw [he] at h2; simp at h2
        rw [urd, srd, rrd, qrd, nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [he]; simp [Memory.readN, show ptr + 4 + 4 + 4 + 4 = ptr + 16 by omega, hz10])
  rw [he] at dR0 dR8
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at dR0 dR8
  obtain ⟨ω12, run12, c0, c1, c5, c6, c7, c8, c9⟩ := b6 (p := p) (P := P) (R := R) x ω11 μ11 (A - 80) 0
    (by omega) (by decide) (d1.trans h1_10) d7 d8
  obtain ⟨ω13, μ13, run13, v0, v1, v5', v6', vc, vp, vl, vfr, vrd, vwr⟩ :=
    pairs_empty (p := p) (P := P) (R := R) x ω12 μ11 (A - 80) (A - 80 + 32) rd 1150 24670 O rd
      ⟨by omega, by omega⟩ c0 (by rw [c1, d1, h1_10]) (by rw [c5, d5, h5_10]) (by rw [c6, d6, h6_10]) c7
      (by rw [c8, d6, h6_10]) c9 hO64 hrd64 hrd64 (by decide) jte_574 bs_24670 (by omega) (Or.inr (by omega))
      (fun a h1 h2 => by rw [dwr, uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [dwr, uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- the frame's words in μ13
  have kH : ∀ a, A - 80 ≤ a → a < A + 56 → (a < A - 48 ∨ A - 24 ≤ a) → μ13.read a = μ10.read a :=
    fun a h1 h2 h3 => (vfr a (by omega) (by omega) (by omega)).trans (dfr a (by omega) (by omega) (by omega))
  have park0 : (μ13.readN (A - 80 + 24) 8).take 4 = μ.readN ptr 4 := by
    rw [Memory.readN_congr (fun j hj => (kH _ (by omega) (by omega) (by omega)).trans ((ufr _ (by omega) (by omega)).trans
      ((sfr _ (by omega) (by omega) (by omega) (by omega)).trans ((rfr _ (by omega) (by omega) (by omega)).trans
      ((qfr _ (by omega) (by omega) (by omega) (by omega)).trans ((nfr _ (by omega) (by omega) (by omega)).trans
      (mfr _ (by omega) (by omega) (by omega) (by omega)))))))), kpark, ev0]
  have park1 : (μ13.readN (A - 80 + 16) 8).take 4 = μ.readN (ptr + 4) 4 := by
    rw [Memory.readN_congr (fun j hj => (kH _ (by omega) (by omega) (by omega)).trans ((ufr _ (by omega) (by omega)).trans
      ((sfr _ (by omega) (by omega) (by omega) (by omega)).trans ((rfr _ (by omega) (by omega) (by omega)).trans
      (qfr _ (by omega) (by omega) (by omega) (by omega)))))), npark, ev1]
  have park2 : (μ13.readN (A - 80 + 8) 8).take 4 = μ.readN (ptr + 8) 4 := by
    rw [Memory.readN_congr (fun j hj => (kH _ (by omega) (by omega) (by omega)).trans ((ufr _ (by omega) (by omega)).trans
      (sfr _ (by omega) (by omega) (by omega) (by omega)))), rpark, ev2]
  have park3 : (μ13.readN (A - 80) 8).take 4 = μ.readN (ptr + 12) 4 := by
    rw [Memory.readN_congr (fun j hj => kH _ (by omega) (by omega) (by omega)), upark, ev3]
  have hsv : ∀ a, A - 24 ≤ a → a < A → μ13.read a = μ2.read a := fun a h1 h2 =>
    (kH a (by omega) (by omega) (by omega)).trans ((ufr a (by omega) (by omega)).trans
      ((sfr a (by omega) (by omega) (by omega) (by omega)).trans ((rfr a (by omega) (by omega) (by omega)).trans
      ((qfr a (by omega) (by omega) (by omega) (by omega)).trans ((nfr a (by omega) (by omega) (by omega)).trans
      ((mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))))))))
  have b13 : ∀ a, a < 4294967296 → (a < A - 208 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ13.read a = μ.read a :=
    fun a h0 h1 h2 => (vfr a h0 (by omega) (by omega)).trans ((dfr a h0 (by omega) h2).trans
      ((ufr a h0 (by omega)).trans ((sfr a h0 (by omega) h2 (by omega)).trans ((rfr a h0 (by omega) (by omega)).trans
      ((qfr a h0 (by omega) h2 (by omega)).trans ((nfr a h0 (by omega) (by omega)).trans
      ((mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega) (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega)))))))))))
  have rd13 : ∀ a, μ13.readable a = μ.readable a := fun a => by
    rw [vrd, drd, urd, srd, rrd, qrd, nrd, mrd, krd, grd, frd]
  have wr13 : ∀ a, μ13.writable a = μ.writable a := fun a => by
    rw [vwr, dwr, uwr, swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]
  obtain ⟨ω14, μ14, run14, z0, z1, z5, z6, zO, zO8, zO16, zO24, zO32, zO36, zO40, zO44, zfr, zrd, zwr⟩ :=
    b7 (p := p) (P := P) (R := R) x ω13 μ13 (A - 80) O 0 8 0 (rdN μ13 (A - 80 + 24) 8) (rdN μ13 (A - 80 + 16) 8)
      (rdN μ13 (A - 80 + 8) 8) (rdN μ13 (A - 80) 8) rd (by omega) hO48 (by omega) (by rw [v1])
      (by rw [v5']) (by decide) (by decide) (by decide) (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
      (rdN_lt64 _ _) hrd64 hO64 vc vp vl (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (encodeLE_rdN _ _ _).symm (encodeLE_rdN _ _ _).symm
      (by rw [show A - 80 + 72 = A - 8 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact f72)
      (by rw [show A - 80 + 64 = A - 16 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact f64)
      (by rw [show A - 80 + 56 = A - 24 by omega, Memory.readN_congr (fun j hj => hsv _ (by omega) (by omega))]; exact f56)
      (fun a h1 h2 => by rw [wr13]; exact hwO a h1 h2)
      (fun a h1 h2 => by rw [rd13]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have b14 : ∀ a, a < 4294967296 → (a < A - 208 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 48 ≤ a) →
      μ14.read a = μ.read a := fun a h0 h1 h2 h3 => (zfr a h0 h3).trans (b13 a h0 h1 h2)
  obtain ⟨ω15, run15, y0, y1, y5, y6⟩ := b8 (p := p) (P := P) (R := R) x ω14 μ14 A ret t v5 v6
    ⟨by omega, by omega⟩ (by rw [z1]; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => b14 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => b14 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => b14 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => by rw [zrd, rd13]; exact F.hr a (by omega) h2)
  have hrdf : ∀ j, j < 16 → μ14.read (rd + j) = μ11.read (rd + j) := fun j hj =>
    (zfr _ (by omega) (by omega)).trans (vfr _ (by omega) (by omega) (by omega))
  refine ⟨ω15, μ14, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans (run10.trans (run11.trans (run12.trans (run13.trans (run14.trans
    run15)))))))))))))).mono (by omega), y0, y1, y5, y6, zO, zO8, zO16, zO24, ?_, ?_, ?_, ?_, ?_, ?_, b14,
    fun a => by rw [zrd, rd13], fun a => by rw [zwr, wr13]⟩
  · rw [zO32, ← take_encodeLE, encodeLE_rdN]; exact park0
  · rw [zO36, ← take_encodeLE, encodeLE_rdN]; exact park1
  · rw [zO40, ← take_encodeLE, encodeLE_rdN]; exact park2
  · rw [zO44, ← take_encodeLE, encodeLE_rdN]; exact park3
  · rw [show ptr + 17 = ptr + 4 + 4 + 4 + 4 + 1 by omega,
      Memory.readN_congr (a := rd) (n := 8) (fun j hj => hrdf j (by omega))]; exact dR0
  · have e8 : μ14.readN (rd + 8) 8 = μ11.readN (rd + 8) 8 :=
      Memory.readN_congr (fun j hj => by rw [Nat.add_assoc]; exact hrdf (8 + j) (by omega))
    rw [show len - 17 = len - 4 - 4 - 4 - 4 - 1 by omega, e8]; exact dR8

end Services.Bootstrap.Decode.Bless
