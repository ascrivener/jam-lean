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

/-- **`Upgrade`**: from 20626, with tag 1 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding at least 48 more octets, `Instruction::decode` returns
    `Upgrade { code_hash, min_item_gas, min_memo_gas }` in its slot O: the discriminant word 2^63 at O,
    the 32 octets of `code_hash` (from ptr) at O + 8, and the 8 octets of each `u64` (from ptr + 32 and
    ptr + 40) at O + 40 and O + 48. The reader is advanced by 48. Memory changes only in A − 184 … A
    (the helper's and the reader's frames), the reader and O … O + 56. -/
theorem upgrade {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 184 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 1) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 72 < 4294967296)
    (hlen : 48 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 184 ∨ A + 56 ≤ rd) (hpA : ptr + 72 ≤ A - 184 ∨ A + 56 ≤ ptr)
    (hOA' : O + 56 ≤ A - 184 ∨ A + 56 ≤ O) (hOr : O + 56 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 48 ≤ rd ∨ rd + 16 ≤ ptr) (hO56 : O + 56 ≤ 4294967296)
    (hws : ∀ a, A - 184 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 56 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 48 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 760 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775808 ∧ μ'.readN (O + 8) 32 = μ.readN ptr 32 ∧
      μ'.readN (O + 40) 8 = μ.readN (ptr + 32) 8 ∧ μ'.readN (O + 48) 8 = μ.readN (ptr + 40) 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 48) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 48) ∧
      (∀ a, a < 4294967296 → (a < A - 184 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 56 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have dl : ∀ q, Num.decodeLE (μ.readN q 8) < 18446744073709551616 := fun q => by
    have := decodeLE_lt (μ.readN q 8); simpa [Memory.length_readN] using this
  have el : ∀ q, Num.encodeLE 8 (Num.decodeLE (μ.readN q 8)) = μ.readN q 8 := fun q => by
    have := encodeLE_decodeLE (μ.readN q 8); simpa [Memory.length_readN] using this
  -- the dispatch and the helper's entry
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 1 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f88, f80, f72, ffr, frd, fwr⟩ :=
    u1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- the hash, into S + 40
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω2 μ2 1066 22839 (A - 96) rd (A - 56) ptr len 32 f0 f1 f7 f8 f9
      (by decide) jte_532 bs_22839 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- moved to S + 8, and the first u64's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kmv, kfr, krd, kwr⟩ :=
    u2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 96) (by omega) (g1.trans f1) g7
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- the first u64, into S + 40
  obtain ⟨ω5, μ5, run5, m0, m1, m2, m3, m4, m5, m6, m12, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1068 22885 (A - 96) rd (A - 56) (ptr + 32) (len - 32) 8 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) (by rw [k8, show A - 96 + 40 = A - 56 by omega]) k9
      (by decide) jte_533 bs_22885 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR8)
  -- μ5 at the payload is μ
  have pay5 : ∀ q, ptr ≤ q → q < ptr + 48 → μ5.read q = μ.read q := fun q h1 h2 =>
    (mfr q (by omega) (by omega) (by omega) (by omega)).trans ((kfr q (by omega) (by omega)).trans
      ((gfr q (by omega) (by omega) (by omega) (by omega)).trans (ffr q (by omega) (by omega))))
  -- parked at S, and the second u64's call
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, n7, n8, n9, npark, nfr, nrd, nwr⟩ :=
    u3 (p := p) (P := P) (R := R) x ω5 μ5 (A - 96) (Num.decodeLE (μ.readN (ptr + 32) 8)) (by omega)
      (m1.trans (k1.trans (g1.trans f1))) m7 (dl _)
      (by rw [show A - 96 + 40 = A - 56 by omega, mbuf, el]
          exact Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega)).trans
            ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans (ffr _ (by omega) (by omega)))))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
  -- the second u64, into S + 40
  obtain ⟨ω7, μ7, run7, q0, q1, q2, q3, q4, q5, q6, q12, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω6 μ6 1070 22912 (A - 96) rd (A - 56) (ptr + 40) (len - 40) 8 n0
      (n1.trans (m1.trans (k1.trans (g1.trans f1)))) (n7.trans (m6.trans (k6.trans (g6.trans f6))))
      (by rw [n8, show A - 96 + 40 = A - 56 by omega]) n9
      (by decide) jte_534 bs_22912 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega) (by omega)), mR8]; congr 1)
  -- back to μ
  have b7 : ∀ a, a < 4294967296 → (a < A - 184 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (qfr a h0 (by omega) h2 (by omega)).trans ((nfr a h0 (by omega) (by omega)).trans
      ((mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))))
  have b7s : ∀ a, A - 24 ≤ a → a < A → μ7.read a = μ2.read a :=
    fun a h1 h2 => (qfr a (by omega) (by omega) (by omega) (by omega)).trans ((nfr a (by omega) (by omega) (by omega)).trans
      ((mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))))
  have hS8 : μ7.readN (A - 96 + 8) 32 = μ.readN ptr 32 := by
    rw [Memory.readN_congr (fun j hj => (qfr _ (by omega) (by omega) (by omega) (by omega)).trans
      ((nfr _ (by omega) (by omega) (by omega)).trans (mfr _ (by omega) (by omega) (by omega) (by omega)))), kmv,
      show A - 96 + 40 = A - 56 by omega, gbuf]
    exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))
  obtain ⟨ω8, μ8, run8, r0, r1, r5, r6, rO, rO8, rO40, rO48, rfr, rrd, rwr⟩ := u4 (p := p) (P := P) (R := R) x ω7 μ7
    (A - 96) O ret t v5 v6 (Num.decodeLE (μ.readN (ptr + 32) 8)) (Num.decodeLE (μ.readN (ptr + 40) 8)) rd
    (by omega) hO56 (by omega) (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1)))))
    (q5.trans (n5.trans (m5.trans (k5.trans (g5.trans f5))))) q7 (dl _) (dl _) F.hv5 F.hv6 hrd64 hO64
    (by rw [Memory.readN_congr (fun j hj => qfr _ (by omega) (by omega) (by omega) (by omega))]; exact npark)
    (by rw [show A - 96 + 40 = A - 56 by omega, qbuf, el]
        exact Memory.readN_congr (fun j hj => (nfr _ (by omega) (by omega) (by omega)).trans (pay5 _ (by omega) (by omega))))
    (by rw [show A - 96 + 88 = A - 8 by omega, Memory.readN_congr (fun j hj => b7s _ (by omega) (by omega))]; exact f88)
    (by rw [show A - 96 + 80 = A - 16 by omega, Memory.readN_congr (fun j hj => b7s _ (by omega) (by omega))]; exact f80)
    (by rw [show A - 96 + 72 = A - 24 by omega, Memory.readN_congr (fun j hj => b7s _ (by omega) (by omega))]; exact f72)
    (by rw [show A - 96 + 144 = A + 48 by omega, Memory.readN_congr (fun j hj => b7 _ (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [show A - 96 + 136 = A + 40 by omega, Memory.readN_congr (fun j hj => b7 _ (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [show A - 96 + 128 = A + 32 by omega, Memory.readN_congr (fun j hj => b7 _ (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt
    (fun a h1 h2 => by rw [qwr, nwr, mwr, kwr, gwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by
      rw [qrd, nrd, mrd, krd, grd, frd]
      rcases Nat.lt_or_ge a A with h | h
      · exact Memory.readable_of_writable (hws a (by omega) h)
      · exact F.hr a h (by omega))
  refine ⟨ω8, μ8, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    run8))))))).mono (by omega), r0, by rw [r1]; congr 1; omega, r5, r6, rO, rO8.trans hS8,
    rO40.trans (el _), rO48.trans (el _), ?_, ?_, ?_,
    fun a => by rw [rrd, qrd, nrd, mrd, krd, grd, frd], fun a => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]⟩
  · rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega)), qR0]
  · rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega)), qR8]; congr 1
  · intro a h0 h1 h2 h3
    rw [rfr a h0 h3]; exact b7 a h0 h1 h2

end Services.Bootstrap.Decode.Upgrade
