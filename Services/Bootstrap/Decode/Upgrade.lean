import Services.Bootstrap.Decode.HashU64

/-!
# `Instruction::decode`: `Upgrade { code_hash, min_item_gas: u64, min_memo_gas: u64 }`

`Upgrade` (tag 1) is decoded by a helper with a 96-octet frame at S = A − 96: it reads the hash into
S + 40 (`read_big_sp`) and moves it to S + 8, reads the first `u64` into S + 40 (`read_ok`) and parks it
at S, reads the second into S + 40, and stores the variant into the slot O: the discriminant word 2^63
at O, the hash at O + 8 and the two `u64`s at O + 40 and O + 48.
-/

namespace Services.Bootstrap.Decode.Upgrade

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21350 … 21398: `Upgrade`'s decoder enters the helper: a 96-octet frame at S = A − 96 saving the
    return address 978, O and the reader at S + 88, S + 80, S + 72, a zeroed buffer at S + 40, and the
    call of the reader for 32 octets into S + 40 (return address 1066). -/
theorem u1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 96 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 96 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21350 ω μ x 58434 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 1066 ∧ ω'[1] = UInt64.ofNat (A - 96) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 978 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 96 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 96 + 88 = A - 8 by omega, show A - 96 + 80 = A - 16 by omega,
      show A - 96 + 72 = A - 24 by omega, show A - 96 + 40 = A - 56 by omega]; post_simp)

/-- 22839 … 22878: the hash read succeeded (ω₇ = 0): the helper moves it from S + 40 to S + 8, zeroes
    S + 40 … S + 48 and calls the reader for 8 octets into S + 40 (return address 1068). -/
theorem u2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 72 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, S + 8 ≤ a → a < S + 48 → μ.writable a = true)
    (hr : ∀ a, S + 40 ≤ a → a < S + 72 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 22839 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1068 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 40) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN (S + 8) 32 = μ.readN (S + 40) 32 ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
      show S + 32 = S + 8 + 24 by omega, show S + 48 = S + 40 + 8 by omega, show S + 56 = S + 40 + 16 by omega,
      show S + 64 = S + 40 + 24 by omega]; exact copy4g μ μ (S + 40) (S + 8) (by omega))

/-- 22885 … 22905: the first `u64` read succeeded (ω₇ = 0): the helper parks it at S, zeroes S + 40 …
    S + 48 and calls the reader for 8 more octets into S + 40 (return address 1070). -/
theorem u3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 48 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (sv : μ.readN (S + 40) 8 = Num.encodeLE 8 v)
    (hw0 : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hw : ∀ a, S + 40 ≤ a → a < S + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 22885 ω μ x 58434 ω' μ' x 9 ∧
      ω'[0] = UInt64.ofNat 1070 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 40) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN S 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 40) 8 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]
  have hr : ∀ a, S + 40 ≤ a → a < S + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hw0, hr, rv, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [Nat.mod_eq_of_lt hv])

/-- 22912 … 22995 then 21402 … 21414: the second `u64` read succeeded (ω₇ = 0): the helper stores
    `Upgrade`'s discriminant word 2^63 at O, the hash (S + 8 … S + 40) at O + 8, the first `u64` (S) at
    O + 40 and the second (S + 40) at O + 48, pops its frame and returns to 21402, and the decoder
    returns through its frame at A = S + 96. -/
theorem u4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 a b o6 : Nat) (hA : S + 96 + 56 < 4294967296) (hO : O + 56 ≤ 4294967296)
    (hOS : O + 56 ≤ S ∨ S + 152 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sa : μ.readN S 8 = Num.encodeLE 8 a) (sb : μ.readN (S + 40) 8 = Num.encodeLE 8 b)
    (sr : μ.readN (S + 88) 8 = Num.encodeLE 8 978) (sO : μ.readN (S + 80) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 72) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 144) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ x, O ≤ x → x < O + 56 → μ.writable x = true)
    (hr : ∀ x, S ≤ x → x < S + 152 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 22912 ω μ x t ω' μ' x 26 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775808 ∧ μ'.readN (O + 8) 32 = μ.readN (S + 8) 32 ∧
      μ'.readN (O + 40) 8 = Num.encodeLE 8 a ∧ μ'.readN (O + 48) 8 = Num.encodeLE 8 b ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 56 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have ra := rd _ a ha sa
  have rb := rd _ b hb sb
  have rr := rd _ 978 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 96 + 48) 8 = ret := by rw [show S + 96 + 48 = S + 144 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 96 + 40) 8 = v5 := by rw [show S + 96 + 40 = S + 136 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 96 + 32) 8 = v6 := by rw [show S + 96 + 32 = S + 128 by omega]; exact rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, ra, rb, rr, rO, ro6, r0, r5, r6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
    post_simp
    all_goals try (rw [show O + 16 = O + 8 + 8 by omega, show O + 24 = O + 8 + 16 by omega,
      show O + 32 = O + 8 + 24 by omega, show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
      show S + 32 = S + 8 + 24 by omega]; exact copy4g μ _ (S + 8) (O + 8) (by omega))

end Services.Bootstrap.Decode.Upgrade
