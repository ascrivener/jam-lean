import Services.Bootstrap.Decode.VecU8
import Services.Bootstrap.DecodeU32

/-!
# `Instruction::decode` of the single-`Vec` variants with no elements

`DeleteItems { keys }` (tag 5), `Export { data }` (tag 10) and `Imported { data }` (tag 19) each hold a
`Vec<Vec<u8>>`, and `Import { items }` (tag 9) a `Vec<(u64, u64)>`. Their decoders share one shape
(`Shape`): a 48-octet helper frame at H = A − 48, the length n decoded with `decodeU32` (31894), then
the element reader (8 for `Vec<u8>` elements, 3100 for pairs) into a `Vec` at H, whose three words
are copied to O + 8 after the discriminant word at O.

This file proves the case n = 0: nothing is allocated, and the variant's `Vec` is
`{cap 0, ptr 8, len 0}` (the dangling pointer for an alignment of 8): `vec_empty`.
-/

namespace Services.Bootstrap.Decode.VecEmpty

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.VecU8

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

/-- The four variants: the decoder's address, its return address into `Instruction::decode`'s end,
    the return address from `decodeU32`, the return address from the element reader, and the element
    reader (8 for `Vec<u8>` elements, 3100 for `(u64, u64)` pairs). -/
def Shape (h r1 r2 r3 B : Nat) : Prop :=
  (h = 21522 ∧ r1 = 990 ∧ r2 = 1088 ∧ r3 = 1090 ∧ B = 8) ∨
    (h = 21871 ∧ r1 = 1010 ∧ r2 = 1110 ∧ r3 = 1112 ∧ B = 8) ∨
    (h = 22072 ∧ r1 = 1022 ∧ r2 = 1170 ∧ r3 = 1172 ∧ B = 8) ∨
    (h = 21028 ∧ r1 = 956 ∧ r2 = 1106 ∧ r3 = 1108 ∧ B = 3100)

/-- 21522 … 21552, 21871 … 21901, 22072 … 22102: the decoder opens its helper frame at H = A − 48
    (the return address r1, O and the reader at H + 40, H + 32, H + 24) and calls `decodeU32` on the
    reader (return address r2). -/
theorem e1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h r1 r2 r3 B A O rd : Nat) (hs : Shape h r1 r2 r3 B) (hA : 65536 + 48 ≤ A ∧ A < 4294967296)
    (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat rd)
    (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 48 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R h ω μ x 31894 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat r2 ∧ ω'[1] = UInt64.ofNat (A - 48) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 r1 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 48 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hs with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, h6, hA, hw]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
      all_goals (try simp only [show A - 48 + 40 = A - 8 by omega, show A - 48 + 32 = A - 16 by omega,
        show A - 48 + 24 = A - 24 by omega])
      post_simp
      all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
      all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))

/-- The continuation after `decodeU32` (23303, 23923, 25298 for the three shapes), the length n
    decoded (ω₇ = 0, ω₈ = n < 2^32): the element reader (8) is called for n elements into a `Vec` at H
    (ω₇ = H = ω₁, ω₈ = the reader ω₆, ω₉ = n), return address r3. -/
theorem e2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h r1 r2 r3 B H n : Nat) (hs : Shape h r1 r2 r3 B) (hH : H < 4294967296) (hn : n < 4294967296)
    (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) :
    ∃ ω', FreeStepsH p R (P.jumpTable.getD (r2 / 2 - 1) 0) ω μ x B ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat r3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat H ∧ ω'[8] = ω[6] ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hs with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  · simp only [Nat.reduceDiv, Nat.reduceSub, jte_543, jte_554, jte_584, jte_552]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h7, h8, hH, hn]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      post_simp
      all_goals try exact UInt64.ofNat_toNat

/-- **The element reader with no elements** (8, n = 0): it opens a 128-octet frame, finds nothing
    to read, stores the empty `Vec` `{cap 0, ptr 8, len 0}` at O (ω₇), restores ω₀, ω₅, ω₆ and
    returns. -/
theorem vec_elems_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
    ∃ ω' μ', FreeStepsH p R 8 ω μ x t ω' μ' x 40 ∧
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
    all_goals (try simp only [show sp - 128 + 128 = sp by omega])
    post_simp
    all_goals try decide

/-- **The `(u64, u64)` reader with no elements** (3100, n = 0): it opens a 120-octet frame, finds
    nothing to read, stores the empty `Vec` `{cap 0, ptr 8, len 0}` at O (ω₇), restores ω₀, ω₅, ω₆ and
    returns. -/
theorem vec_pairs_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
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
    ∃ ω' μ', FreeStepsH p R 3100 ω μ x t ω' μ' x 40 ∧
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

/-- The element reader B of a shape with no elements: `vec_elems_empty` or `vec_pairs_empty`. -/
theorem body_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h r1 r2 r3 B sp O rd ret t v5 v6 : Nat) (hs : Shape h r1 r2 r3 B)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat 0) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hO : O + 24 ≤ 4294967296) (hOS : O + 24 ≤ sp - 128 ∨ sp ≤ O)
    (hw : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R B ω μ x t ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 8 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 128 ∨ sp ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hB : B = 8 ∨ B = 3100 := by unfold Shape at hs; omega
  rcases hB with rfl | rfl
  · exact vec_elems_empty x ω μ sp O rd ret t v5 v6 hsp h0 h1 h5 h6 h7 h8 h9 hv5 hv6 hrd hret hjt hbt hO hOS hw hwO
  · exact vec_pairs_empty x ω μ sp O rd ret t v5 v6 hsp h0 h1 h5 h6 h7 h8 h9 hv5 hv6 hrd hret hjt hbt hO hOS hw hwO

/-- The copy after the element reader (23325, 23945, 25320 for the three shapes): the reader stored
    a `Vec` `{cap, ptr, len}` at H (cap ≠ 2^64 − 1, not its error): the variant's discriminant word W
    goes to O, the three words to O + 8, O + 16, O + 24, and the helper returns through its frame at
    H to the address r1 saved at H + 40. -/
theorem e3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h r1 r2 r3 B W H O cap ptr len v5 v6 : Nat) (hs : Shape h r1 r2 r3 B)
    (hW : (h = 21522 ∧ W = 9223372036854775812) ∨ (h = 21871 ∧ W = 9223372036854775817) ∨
      (h = 22072 ∧ W = 9223372036854775826) ∨ (h = 21028 ∧ W = 9223372036854775816))
    (hH : 65536 ≤ H ∧ H + 48 < 4294967296)
    (hO : O + 32 ≤ 4294967296) (hOH : O + 32 ≤ H ∨ H + 48 ≤ O)
    (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat O)
    (hcap : cap < 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (sc : μ.readN H 8 = Num.encodeLE 8 cap) (sp : μ.readN (H + 8) 8 = Num.encodeLE 8 ptr)
    (sl : μ.readN (H + 16) 8 = Num.encodeLE 8 len)
    (s0 : μ.readN (H + 40) 8 = Num.encodeLE 8 r1) (s5 : μ.readN (H + 32) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (H + 24) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, H ≤ a → a < H + 48 → μ.readable a = true)
    (hw : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R (P.jumpTable.getD (r3 / 2 - 1) 0) ω μ x (P.jumpTable.getD (r1 / 2 - 1) 0)
        ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r1 ∧ ω'[1] = UInt64.ofNat (H + 48) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 W ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 ptr ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) sc
  have rp := rd8 hptr sp
  have rl := rd8 hlen sl
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  have hc : ¬ cap = 18446744073709551615 := by omega
  rw [show ω = regsNF ω [] from rfl]
  rcases hs with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  · rcases hW with ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ | ⟨h', rfl⟩ <;> (try (exfalso; omega)) <;>
    · have r0 := rd8 (by decide) s0
      simp only [Nat.reduceDiv, Nat.reduceSub, jte_544, jte_555, jte_585, jte_553, jte_494, jte_504, jte_510, jte_477]
      refine ⟨?_, ?_, ?_, ?_⟩
      rotate_left 2
      · pvm_go [h1, h5, hH, hO, hOH, hw, hr, rc, rp, rl, r0, r5, r6, hc, rdN_writeN_disjoint, ↓rdN_fold]
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
        post_simp

/-- `Instruction::decode`'s end at the variant's return address (21555, 21904, 22105): restore ω₀,
    ω₅, ω₆ from the frame at A and return. -/
theorem e4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h r1 r2 r3 B A ret t v5 v6 : Nat) (hs : Shape h r1 r2 r3 B) (hA : 65536 ≤ A ∧ A + 56 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat A)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, A + 32 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R (P.jumpTable.getD (r1 / 2 - 1) 0) ω μ x t ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 := by
  have r0 := rd8 (by omega) s0
  have r5 := rd8 hv5 s5
  have r6 := rd8 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  rcases hs with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  · simp only [Nat.reduceDiv, Nat.reduceSub, jte_494, jte_504, jte_510, jte_477]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, hA, hr, r0, r5, r6, hret, hjt, hbt, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_⟩
      post_simp

/-- The block starts the three shapes return to. -/
theorem shape_bs {p : ByteArray} {P : Program} [HasCode p P] {h r1 r2 r3 B : Nat} (hs : Shape h r1 r2 r3 B) :
    P.isBlockStart (P.jumpTable.getD (r1 / 2 - 1) 0) = true ∧
      P.isBlockStart (P.jumpTable.getD (r2 / 2 - 1) 0) = true ∧
      P.isBlockStart (P.jumpTable.getD (r3 / 2 - 1) 0) = true := by
  rcases hs with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
  · simp only [Nat.reduceDiv, Nat.reduceSub, jte_494, jte_504, jte_510, jte_543, jte_554, jte_584, jte_544,
      jte_555, jte_585, jte_477, jte_552, jte_553]
    refine ⟨?_, ?_, ?_⟩ <;>
    simp only [bs_21555, bs_21904, bs_22105, bs_23303, bs_23923, bs_25298, bs_23325, bs_23945, bs_25320,
      bs_21061, bs_23831, bs_23853]

/-- **The `Vec` variants with no elements**: from 20626, with tag 5 (`DeleteItems`), 10 (`Export`),
    19 (`Imported`) or 9 (`Import`) read without error, and the reader `{ptr, len}` at rd (ω₆) holding ℰ(0)
    next (the octet 0, length 0), `Instruction::decode` returns the variant with an empty `Vec` in its
    slot O: the discriminant word W (2^63 + 4, 2^63 + 9, 2^63 + 18, 2^63 + 8) at O and `{cap 0, ptr 8, len 0}` at
    O + 8. Nothing is allocated. The reader is advanced by 1. Memory changes only in A − 176 … A (the
    helper's and the callees' frames), the reader and O … O + 32. -/
theorem vec_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (tag h r1 r2 r3 B W A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hs : Shape h r1 r2 r3 B)
    (htag : (tag = 5 ∧ h = 21522 ∧ W = 9223372036854775812) ∨ (tag = 10 ∧ h = 21871 ∧ W = 9223372036854775817) ∨
      (tag = 19 ∧ h = 22072 ∧ W = 9223372036854775826) ∨ (tag = 9 ∧ h = 21028 ∧ W = 9223372036854775816))
    (hA : 65536 + 176 ≤ A) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (htg : μ.read A = UInt8.ofNat tag) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 32 < 4294967296)
    (hlen : 1 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hzero : μ.read ptr = 0)
    (hrdA : rd + 16 ≤ A - 176 ∨ A + 56 ≤ rd) (hpA : ptr + 32 ≤ A - 176 ∨ A + 56 ≤ ptr)
    (hpr : ptr + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hOA : O + 32 ≤ A - 176 ∨ A + 56 ≤ O) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O) (hO32 : O + 32 ≤ 4294967296)
    (hws : ∀ a, A - 176 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 32 → μ.writable a = true)
    (hrp : μ.readable ptr = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 600 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 W ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 8 ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 0 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1) ∧
      (∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by have := F.hO; omega
  have hsh := hs
  unfold Shape at hsh
  obtain ⟨bs1, bs2, bs3⟩ := shape_bs (p := p) (P := P) hs
  have hh : handler tag = h := by
    rcases htag with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ <;> rfl
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A tag (by omega)
    (by omega) F.h1 h7 htg tab (F.hr A (by omega) (by omega)) hrt
  rw [hh] at run1
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bs0, bs5, bs6, bfr, brd, bwr⟩ :=
    e1 (p := p) (P := P) (R := R) x ω1 μ h r1 r2 r3 B A O rd hs ⟨by omega, by omega⟩ (e1'.trans F.h1)
      (e5'.trans F.h5) (e6'.trans h6) hO64 (by omega) (fun a h1 h2 => hws a (by omega) h2)
  have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := by simp [Blob.encodeNat]
  obtain ⟨ω3, μ3, run3, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω2 μ2 r2 _ (A - 48) rd ptr len b0 b1 b7 (by omega) rfl bs2
      ⟨by omega, by omega⟩ hrd hptr (by omega) (by omega) hpr
      (fun a h1 h2 => by rw [bwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [bwr]; exact hwr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hR8) 0 (by decide)
      (by rw [he]; simp; omega)
      (fun a h1 h2 => by rw [he] at h2; simp at h2; rw [brd, show a = ptr by omega]; exact hrp)
      (by rw [he]; simp [Memory.readN, bfr ptr (by omega) (by omega), hzero])
  rw [he] at dR0 dR8
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at dR0 dR8
  obtain ⟨ω4, run4, c0, c1, c5, c6, c7, c8, c9⟩ := e2 (p := p) (P := P) (R := R) x ω3 μ3 h r1 r2 r3 B (A - 48) 0
    hs (by omega) (by decide) (by rw [d1, b1]) d7 d8
  have hv6 : ω4[6] = UInt64.ofNat rd := by rw [c6, d6, b6]
  obtain ⟨ω5, μ5, run5, v0, v1, v5', v6', vc, vp, vl, vfr, vrd, vwr⟩ :=
    body_empty (p := p) (P := P) (R := R) x ω4 μ3 h r1 r2 r3 B (A - 48) (A - 48) rd r3 _ O rd hs ⟨by omega, by omega⟩
      c0 (by rw [c1, d1, b1]) (by rw [c5, d5, b5]) hv6 c7 (by rw [c8, d6, b6]) c9 hO64 (by omega) (by omega)
      (by omega) rfl bs3 (by omega) (Or.inr (Nat.le_refl _))
      (fun a h1 h2 => by rw [dwr, bwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [dwr, bwr]; exact hws a (by omega) (by omega))
  have hfrH : ∀ a, A - 24 ≤ a → a < A + 56 → μ5.read a = μ2.read a := fun a h1 h2 =>
    (vfr a (by omega) (by omega) (by omega)).trans (dfr a (by omega) (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fO, fO8, fO16, fO24, ffr, frd, fwr⟩ :=
    e3 (p := p) (P := P) (R := R) x ω5 μ5 h r1 r2 r3 B W (A - 48) O 0 8 0 O rd hs
      (by rcases htag with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> simp [h1, h2]) ⟨by omega, by omega⟩
      hO32 (by omega) v1 v5' (by decide) (by decide) (by decide) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 40 = A - 8 by omega]; exact bs0)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 32 = A - 16 by omega]; exact bs5)
      (by rw [Memory.readN_congr (fun j hj => hfrH _ (by omega) (by omega)), show A - 48 + 24 = A - 24 by omega]; exact bs6)
      (fun a h1 h2 => by rw [vrd, drd, brd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [vwr, dwr, bwr]; exact hwO a h1 h2)
  have hfar : ∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
      μ6.read a = μ.read a :=
    fun a h0 h1 h2 h3 => (ffr a h0 h3).trans ((vfr a h0 (by omega) (by omega)).trans
      ((dfr a h0 (by omega) h2).trans (bfr a h0 (by omega))))
  have rd6 : ∀ a, μ6.readable a = μ.readable a := fun a => by rw [frd, vrd, drd, brd]
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [fwr, vwr, dwr, bwr]
  obtain ⟨ω7, run7, g0, g1, g5, g6⟩ := e4 (p := p) (P := P) (R := R) x ω6 μ6 h r1 r2 r3 B A ret t v5 v6 hs
    ⟨by omega, by omega⟩ (by rw [f1]; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => by rw [rd6]; exact F.hr a (by omega) h2)
  have hrd6 : ∀ j, j < 16 → μ6.read (rd + j) = μ3.read (rd + j) := fun j hj =>
    (ffr _ (by omega) (by omega)).trans (vfr _ (by omega) (by omega) (by omega))
  refine ⟨ω7, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))).mono
    (by omega), g0, g1, g5, g6, fO, fO8, fO16, fO24, ?_, ?_, hfar, rd6, wr6⟩
  · rw [Memory.readN_congr (a := rd) (n := 8) (fun j hj => hrd6 j (by omega))]; exact dR0
  · have e8 : μ6.readN (rd + 8) 8 = μ3.readN (rd + 8) 8 :=
      Memory.readN_congr (fun j hj => by rw [Nat.add_assoc]; exact hrd6 (8 + j) (by omega))
    rw [e8]; exact dR8

end Services.Bootstrap.Decode.VecEmpty
