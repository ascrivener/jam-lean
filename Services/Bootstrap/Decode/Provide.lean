import Services.Bootstrap.Decode.U32Hash
import Services.Bootstrap.Decode.HashU64

/-!
# `Instruction::decode`: `Provide { service: u32, preimage: Hash(hash) }`

`Provide` (tag 17) is decoded by a helper with a 152-octet frame at H = A − 152: it reads the `u32`
into H + 48 (`read_ok`) and parks it, sign-extended, at H + 8; reads the preimage's tag octet into
H + 48 (`read_ok`); for tag 0 (`Hash`) it keeps the tag at H, reads the hash into H + 48
(`read_big_sp`) and moves it to H + 16; then it stores the variant into the slot O: the discriminant
word 2^63 + 16 at O, the preimage's tag octet at O + 8, the hash at O + 9 and the `u32` at O + 48.
Tag 1 (`Inline(bytes)`) reads a `Vec<u8>`, which allocates, and is not covered here.
-/

namespace Services.Bootstrap.Decode.Provide

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

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

/-- 21416 … 21459: `Provide`'s decoder enters the helper: a 152-octet frame at H = A − 152 saving the
    return address 982, O and the reader at H + 144, H + 136, H + 128, a zeroed `u32` at H + 48, and the
    call of the reader for 4 octets into H + 48 (return address 1160). -/
theorem p1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 152 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 152 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21416 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1160 ∧ ω'[1] = UInt64.ofNat (A - 152) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 104) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 982 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 152 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals (try simp only [show A - 152 + 144 = A - 8 by omega, show A - 152 + 136 = A - 16 by omega,
      show A - 152 + 128 = A - 24 by omega, show A - 152 + 48 = A - 104 by omega])
    post_simp
    all_goals try (rw [Nat.mod_eq_of_lt (by omega)])
    all_goals try (congr 1; exact Nat.mod_eq_of_lt (by omega))

/-- 25012 … 25034: the `u32` read succeeded (ω₇ = 0): the helper parks it, sign-extended, as a word at
    H + 8, zeroes the octet at H + 48 and calls the reader for 1 octet into H + 48 (return address
    1162). -/
theorem p2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H v : Nat)
    (hH : H + 152 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (H + 48) 4 = Num.encodeLE 4 v)
    (hw0 : ∀ a, H + 8 ≤ a → a < H + 16 → μ.writable a = true)
    (hw : ∀ a, H + 48 ≤ a → a < H + 52 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 25012 ω μ x 58434 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1162 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (H + 48) ∧ ω'[9] = UInt64.ofNat 1 ∧
      (μ'.readN (H + 8) 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < H + 8 ∨ H + 16 ≤ a) → a ≠ H + 48 → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (H + 48) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, H + 48 ≤ a → a < H + 52 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hH, hw, hw0, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])
    all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_ne'])

/-- 25041 … 25082: the tag read succeeded (ω₇ = 0) and is 0 (`Hash`): the helper keeps the tag word 0
    at H, zeroes H + 48 … H + 80 and calls the reader for 32 octets into H + 48 (return address 1164). -/
theorem p3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H : Nat)
    (hH : H + 152 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (H + 48) = 0)
    (hw0 : ∀ a, H ≤ a → a < H + 8 → μ.writable a = true)
    (hw : ∀ a, H + 48 ≤ a → a < H + 80 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 25041 ω μ x 58434 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat 1164 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (H + 48) ∧ ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN H 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < H ∨ H + 8 ≤ a) → (a < H + 48 ∨ H + 80 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rb : rdN μ (H + 48) 1 = 0 := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, tag,
      Num.decodeLE]
    simp
  have hr : μ.readable (H + 48) = true := Memory.readable_of_writable (hw _ (by omega) (by omega))
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hH, hw, hw0, hr, rb, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat

/-- 25089 … 25117: the hash read succeeded (ω₇ = 0): the helper moves it from H + 48 to H + 16. -/
theorem p4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H : Nat)
    (hH : H + 152 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, H + 16 ≤ a → a < H + 48 → μ.writable a = true)
    (hr : ∀ a, H + 48 ≤ a → a < H + 80 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 25089 ω μ x 25209 ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (H + 16) 32 = μ.readN (H + 48) 32 ∧
      (∀ a, a < 4294967296 → (a < H + 16 ∨ H + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h7' : (ω[7]).toNat = 0 := by rw [h7]; rfl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7', hH, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try (rw [show H + 24 = H + 16 + 8 by omega, show H + 32 = H + 16 + 16 by omega,
      show H + 40 = H + 16 + 24 by omega, show H + 56 = H + 48 + 8 by omega, show H + 64 = H + 48 + 16 by omega,
      show H + 72 = H + 48 + 24 by omega]; exact copy4g μ μ (H + 48) (H + 16) (by omega))

/-- 25209 … 25272: the helper stores the variant into O: the discriminant word 2^63 + 16, the low
    octet of the tag word at H (0) at O + 8, the hash (H + 16) at O + 9 and the low four octets of the
    word w at H + 8 at O + 48; it restores ω₀, ω₅, ω₆ from H + 144, H + 136, H + 128 and returns to
    982's entry, 21463. -/
theorem p5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (H O w o6 : Nat) (hH : H + 152 < 4294967296) (hO : O + 52 ≤ 4294967296)
    (hOH : O + 52 ≤ H ∨ H + 152 ≤ O)
    (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat O)
    (hw64 : w < 18446744073709551616) (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (st : μ.readN H 8 = Num.encodeLE 8 0) (sw : μ.readN (H + 8) 8 = Num.encodeLE 8 w)
    (sr : μ.readN (H + 144) 8 = Num.encodeLE 8 982) (sO : μ.readN (H + 136) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (H + 128) 8 = Num.encodeLE 8 o6)
    (hw : ∀ x, O ≤ x → x < O + 52 → μ.writable x = true)
    (hr : ∀ x, H ≤ x → x < H + 152 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 25209 ω μ x 21463 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 982 ∧ ω'[1] = UInt64.ofNat (H + 152) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat o6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 0 ∧
      μ'.readN (O + 9) 32 = μ.readN (H + 16) 32 ∧ μ'.readN (O + 48) 4 = Num.encodeLE 4 w ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 52 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rt := rd8 (by decide) st
  have rw0 := rd8 hw64 sw
  have rr := rd8 (by decide) sr
  have rO := rd8 hOv sO
  have ro6 := rd8 ho6 so6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, hH, hO, hOH, hw, hr, rt, rw0, rr, rO, ro6, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try exact encodeLE_mod 4 w
    all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_eq'])
    all_goals try (rw [show O + 17 = O + 9 + 8 by omega, show O + 25 = O + 9 + 16 by omega,
      show O + 33 = O + 9 + 24 by omega, show H + 24 = H + 16 + 8 by omega, show H + 32 = H + 16 + 16 by omega,
      show H + 40 = H + 16 + 24 by omega]; exact copy4g μ _ (H + 16) (O + 9) (by omega))
    all_goals try decide

/-- 21463 … 21475: `Instruction::decode`'s end for `Provide`: restore ω₀, ω₅, ω₆ from the frame at A
    and return. -/
theorem p6 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A ret t v5 v6 : Nat) (hA : 65536 ≤ A ∧ A + 56 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat A)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (s0 : μ.readN (A + 48) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (A + 40) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (A + 32) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, A + 32 ≤ a → a < A + 56 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 21463 ω μ x t ω' μ x 6 ∧
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

/-- **`Provide { service, preimage: Hash(hash) }`**: from 20626, with tag 17 read without error and the
    reader `{ptr, len}` at rd (ω₆) holding at least 37 more octets, of which the fifth (at ptr + 4) is 0
    (`Hash`), `Instruction::decode` returns `Provide { service, preimage: Hash(hash) }` in its slot O:
    the discriminant word 2^63 + 16 at O, the preimage's tag 0 at O + 8, the 32 octets of `hash` (from
    ptr + 5) at O + 9 and the 4 of `service` (from ptr) at O + 48. Nothing is allocated. The reader is
    advanced by 37. Memory changes only in A − 240 … A (the helper's and the reader's frames), the
    reader and O … O + 52. -/
theorem provide_hash {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 240 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 17) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 72 < 4294967296)
    (hlen : 37 ≤ len ∧ len < 4294967296) (hhash : μ.read (ptr + 4) = 0)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 240 ∨ A + 56 ≤ rd) (hpA : ptr + 72 ≤ A - 240 ∨ A + 56 ≤ ptr)
    (hOA' : O + 52 ≤ A - 240 ∨ A + 56 ≤ O) (hOr : O + 52 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 37 ≤ rd ∨ rd + 16 ≤ ptr) (hO52 : O + 52 ≤ 4294967296)
    (hws : ∀ a, A - 240 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 52 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 37 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 800 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775824 ∧ μ'.read (O + 8) = 0 ∧
      μ'.readN (O + 9) 32 = μ.readN (ptr + 5) 32 ∧ μ'.readN (O + 48) 4 = μ.readN ptr 4 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 37) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 37) ∧
      (∀ a, a < 4294967296 → (a < A - 240 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 52 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hv : Num.decodeLE (μ.readN ptr 4) < 4294967296 := by
    have := decodeLE_lt (μ.readN ptr 4); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 4 (Num.decodeLE (μ.readN ptr 4)) = μ.readN ptr 4 := by
    have := encodeLE_decodeLE (μ.readN ptr 4); simpa [Memory.length_readN] using this
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 17 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f88, f80, f72, ffr, frd, fwr⟩ :=
    p1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- the u32, into H + 48
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1160 25012 (A - 152) rd (A - 104) ptr len 4 f0 f1 f7 f8 f9
      (by decide) jte_579 bs_25012 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- parked at H + 8, and the tag's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    p2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 152) (Num.decodeLE (μ.readN ptr 4)) (by omega) (g1.trans f1) g7 hv
      (by rw [show A - 152 + 48 = A - 104 by omega, gbuf, ev]
          exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  -- the tag, into H + 48
  obtain ⟨ω5, μ5, run5, m0, m1, -, -, -, m5, m6, -, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1162 25041 (A - 152) rd (A - 104) (ptr + 4) (len - 4) 1 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) (by rw [k8, show A - 152 + 48 = A - 104 by omega]) k9
      (by decide) jte_580 bs_25041 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  have pay4 : ∀ q, ptr ≤ q → q < ptr + 37 → μ4.read q = μ.read q := fun q h1 h2 =>
    (kfr q (by omega) (by omega) (by omega)).trans ((gfr q (by omega) (by omega) (by omega) (by omega)).trans
      (ffr q (by omega) (by omega)))
  have htag5 : μ5.read (A - 152 + 48) = 0 := by
    have := congrArg List.head? mbuf
    simp only [Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.head?_cons,
      Option.some.injEq] at this
    rw [show A - 152 + 48 = A - 104 by omega, this, pay4 _ (by omega) (by omega)]; exact hhash
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, n7, n8, n9, ntag, nfr, nrd, nwr⟩ :=
    p3 (p := p) (P := P) (R := R) x ω5 μ5 (A - 152) (by omega) (m1.trans (k1.trans (g1.trans f1))) m7 htag5
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- the hash, into H + 48
  obtain ⟨ω7, μ7, run7, q0, q1, q5, q6, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω6 μ6 1164 25089 (A - 152) rd (A - 104) (ptr + 5) (len - 4 - 1) 32 n0
      (n1.trans (m1.trans (k1.trans (g1.trans f1)))) (n7.trans (m6.trans (k6.trans (g6.trans f6))))
      (by rw [n8, show A - 152 + 48 = A - 104 by omega]) n9
      (by decide) jte_581 bs_25089 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR8)
  -- moved to H + 16
  obtain ⟨ω8, μ8, run8, r1, r5, r6, rmv, rfr, rrd, rwr⟩ :=
    p4 (p := p) (P := P) (R := R) x ω7 μ7 (A - 152) (by omega)
      (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))) q7
      (fun a h1 h2 => by rw [qwr, nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [qrd, nrd, mrd, krd, grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- back to μ
  have b8 : ∀ a, a < 4294967296 → (a < A - 240 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ8.read a = μ.read a :=
    fun a h0 h1 h2 => (rfr a h0 (by omega)).trans ((qfr a h0 (by omega) h2 (by omega)).trans
      ((nfr a h0 (by omega) (by omega)).trans ((mfr a h0 (by omega) h2 (by omega)).trans
      ((kfr a h0 (by omega) (by omega)).trans ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega)))))))
  have b8s : ∀ a, A - 24 ≤ a → a < A → μ8.read a = μ2.read a :=
    fun a h1 h2 => (rfr a (by omega) (by omega)).trans ((qfr a (by omega) (by omega) (by omega) (by omega)).trans
      ((nfr a (by omega) (by omega) (by omega)).trans ((mfr a (by omega) (by omega) (by omega) (by omega)).trans
      ((kfr a (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega) (by omega) (by omega))))))
  have hpark : (μ8.readN (A - 152 + 8) 8).take 4 = μ.readN ptr 4 := by
    rw [Memory.readN_congr (fun j hj => (rfr _ (by omega) (by omega)).trans ((qfr _ (by omega) (by omega) (by omega) (by omega)).trans
      ((nfr _ (by omega) (by omega) (by omega)).trans (mfr _ (by omega) (by omega) (by omega) (by omega))))), kpark, ev]
  have htag8 : μ8.readN (A - 152) 8 = Num.encodeLE 8 0 := by
    rw [Memory.readN_congr (fun j hj => (rfr _ (by omega) (by omega)).trans (qfr _ (by omega) (by omega) (by omega) (by omega)))]
    exact ntag
  have hH16 : μ8.readN (A - 152 + 16) 32 = μ.readN (ptr + 5) 32 := by
    rw [rmv, show A - 152 + 48 = A - 104 by omega, qbuf]
    exact Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega)).trans
      ((mfr _ (by omega) (by omega) (by omega) (by omega)).trans (pay4 _ (by omega) (by omega))))
  obtain ⟨ω9, μ9, run9, s0', s1', s5', s6', sO, sO8, sO9, sO48, sfr, srd, swr⟩ := p5 (p := p) (P := P) (R := R) x ω8 μ8
    (A - 152) O (rdN μ8 (A - 152 + 8) 8) rd (by omega) hO52 (by omega)
    (r1.trans (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))))
    (r5.trans (q5.trans (n5.trans (m5.trans (k5.trans (g5.trans f5)))))) (rdN_lt64 _ _) hrd64 hO64 htag8
    (encodeLE_rdN _ _ _).symm
    (by rw [show A - 152 + 144 = A - 8 by omega, Memory.readN_congr (fun j hj => b8s _ (by omega) (by omega))]; exact f88)
    (by rw [show A - 152 + 136 = A - 16 by omega, Memory.readN_congr (fun j hj => b8s _ (by omega) (by omega))]; exact f80)
    (by rw [show A - 152 + 128 = A - 24 by omega, Memory.readN_congr (fun j hj => b8s _ (by omega) (by omega))]; exact f72)
    (fun a h1 h2 => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by rw [rrd, qrd, nrd, mrd, krd, grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  have b9 : ∀ a, a < 4294967296 → (a < A - 240 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 52 ≤ a) →
      μ9.read a = μ.read a := fun a h0 h1 h2 h3 => (sfr a h0 h3).trans (b8 a h0 h1 h2)
  have rd9 : ∀ a, μ9.readable a = μ.readable a := fun a => by rw [srd, rrd, qrd, nrd, mrd, krd, grd, frd]
  have wr9 : ∀ a, μ9.writable a = μ.writable a := fun a => by rw [swr, rwr, qwr, nwr, mwr, kwr, gwr, fwr]
  obtain ⟨ω10, run10, u0, u1, u5, u6⟩ := p6 (p := p) (P := P) (R := R) x ω9 μ9 A ret t v5 v6
    ⟨by omega, by omega⟩ (by rw [s1']; congr 1; omega) F.hv5 F.hv6
    (by rw [Memory.readN_congr (fun j hj => b9 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [Memory.readN_congr (fun j hj => b9 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [Memory.readN_congr (fun j hj => b9 _ (by omega) (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt (fun a h1 h2 => by rw [rd9]; exact F.hr a (by omega) h2)
  refine ⟨ω10, μ9, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans (run9.trans run10))))))))).mono (by omega), u0, u1, u5, u6, sO, sO8, sO9.trans hH16, ?_, ?_, ?_,
    b9, rd9, wr9⟩
  · rw [sO48, ← take_encodeLE, encodeLE_rdN]; exact hpark
  · rw [show ptr + 37 = ptr + 5 + 32 by omega, Memory.readN_congr (a := rd) (n := 8) (fun j hj =>
      (sfr _ (by omega) (by omega)).trans (rfr _ (by omega) (by omega)))]; exact qR0
  · rw [show len - 37 = len - 4 - 1 - 32 by omega, Memory.readN_congr (a := rd + 8) (n := 8) (fun j hj =>
      (sfr _ (by omega) (by omega)).trans (rfr _ (by omega) (by omega)))]; exact qR8

end Services.Bootstrap.Decode.Provide
