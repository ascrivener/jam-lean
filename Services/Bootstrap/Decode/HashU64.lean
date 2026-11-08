import Services.Bootstrap.Decode.Hash
import Services.Bootstrap.Decode.Fixed

/-!
# `Instruction::decode`: variants with a hash and a `u64`

`Solicit { hash, len: u64 }` (tag 6) is decoded by a helper at 21749 with its own 88-octet frame at
S = A − 88: it reads the hash into S + 32 (`read_big_sp`), moves it to S, reads the `u64` into S + 32
(`read_ok`), and stores the variant into the slot O. Then `Instruction::decode` returns as usual.
-/

namespace Services.Bootstrap.Decode.HashU64

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21741 … 21789: `Solicit`'s decoder enters the helper: an 88-octet frame at S = A − 88 saving the
    return address 1002, O and the reader at S + 80, S + 72, S + 64, a zeroed buffer at S + 32, and
    the call of the reader for 32 octets into S + 32 (return address 1092). -/
theorem s1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 88 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 88 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21741 ω μ x 58434 ω' μ' x 18 ∧
      ω'[0] = UInt64.ofNat 1092 ∧ ω'[1] = UInt64.ofNat (A - 88) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 1002 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 88 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 88 + 80 = A - 8 by omega, show A - 88 + 72 = A - 16 by omega,
      show A - 88 + 64 = A - 24 by omega]; post_simp)

/-- Four words copied from A … A + 32 to D … D + 32, as the stores leave them. -/
theorem copy4g (μ ν : Memory) (A D : Nat) (hD : D + 32 ≤ 4294967296) :
    ((((ν.writeN D (Num.encodeLE 8 (rdN μ A 8 % 18446744073709551616))).writeN (D + 8)
      (Num.encodeLE 8 (rdN μ (A + 8) 8 % 18446744073709551616))).writeN (D + 16)
      (Num.encodeLE 8 (rdN μ (A + 16) 8 % 18446744073709551616))).writeN (D + 24)
      (Num.encodeLE 8 (rdN μ (A + 24) 8 % 18446744073709551616))).readN D 32 = μ.readN A 32 := by
  have hm : ∀ a, rdN μ a 8 % 18446744073709551616 = rdN μ a 8 := fun a => Nat.mod_eq_of_lt (rdN_lt64 μ a)
  rw [hm A, hm (A + 8), hm (A + 16), hm (A + 24), encodeLE_rdN, encodeLE_rdN, encodeLE_rdN, encodeLE_rdN]
  rw [readN_32, readN_32]
  simp (disch := (simp [two32] <;> omega)) only [Memory.readN_writeN_same, Memory.readN_writeN_disjoint]

/-- 23395 … 23433: the hash read succeeded (ω₇ = 0): the helper moves it from S + 32 to S, zeroes
    S + 32 … S + 40 and calls the reader for 8 octets into S + 32 (return address 1094). -/
theorem s2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 64 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, S ≤ a → a < S + 40 → μ.writable a = true)
    (hr : ∀ a, S + 32 ≤ a → a < S + 64 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23395 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1094 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 32) ∧ ω'[9] = UInt64.ofNat 8 ∧
      μ'.readN S 32 = μ.readN (S + 32) 32 ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (have := copy4g μ μ (S + 32) S (by omega); simp only [Nat.add_assoc, Nat.reduceAdd] at this; exact this)

/-- 23440 … 23517 then 21793 … 21805: the `u64` read succeeded (ω₇ = 0): the helper stores
    `Solicit`'s discriminant word 2^63 + 5 at O, the hash (S … S + 32) at O + 8 and the `u64`
    (S + 32) at O + 40, pops its frame and returns to 21793, and the decoder returns through its frame
    at A = S + 88. -/
theorem s3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 v o6 : Nat) (hA : S + 88 + 56 < 4294967296) (hO : O + 48 ≤ 4294967296)
    (hOS : O + 48 ≤ S ∨ S + 144 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sv : μ.readN (S + 32) 8 = Num.encodeLE 8 v)
    (sr : μ.readN (S + 80) 8 = Num.encodeLE 8 1002) (sO : μ.readN (S + 72) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 64) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 136) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 128) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 120) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 48 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 144 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23440 ω μ x t ω' μ' x 24 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 144) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775813 ∧ μ'.readN (O + 8) 32 = μ.readN S 32 ∧
      μ'.readN (O + 40) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rv := rd _ v hv sv
  have rr := rd _ 1002 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 88 + 48) 8 = ret := by rw [show S + 88 + 48 = S + 136 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 88 + 40) 8 = v5 := by rw [show S + 88 + 40 = S + 128 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 88 + 32) 8 = v6 := by rw [show S + 88 + 32 = S + 120 by omega]; exact rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rv, rr, rO, ro6, r0, r5, r6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try (rw [show O + 16 = O + 8 + 8 by omega, show O + 24 = O + 8 + 16 by omega,
      show O + 32 = O + 8 + 24 by omega]; exact copy4g μ _ S (O + 8) (by omega))

/-- **`Solicit`**: from 20626, with tag 6 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding at least 40 more octets, `Instruction::decode` returns `Solicit { hash, len }` in its slot
    O: the discriminant word 2^63 + 5 at O, the 32 octets of `hash` (from ptr) at O + 8 and the 8 of
    `len` (from ptr + 32) at O + 40. The reader is advanced by 40. Memory changes only in
    A − 176 … A (the helper's and the reader's frames), the reader and O … O + 48. -/
theorem solicit {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 176 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 6) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 56 < 4294967296)
    (hlen : 40 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 176 ∨ A + 56 ≤ rd) (hpA : ptr + 56 ≤ A - 176 ∨ A + 56 ≤ ptr)
    (hOA' : O + 48 ≤ A - 176 ∨ A + 56 ≤ O) (hOr : O + 48 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 40 ≤ rd ∨ rd + 16 ≤ ptr) (hO48 : O + 48 ≤ 4294967296)
    (hws : ∀ a, A - 176 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 48 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 40 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 650 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775813 ∧ μ'.readN (O + 8) 32 = μ.readN ptr 32 ∧
      μ'.readN (O + 40) 8 = μ.readN (ptr + 32) 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 40) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 40) ∧
      (∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 48 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  -- the dispatch and the helper's entry
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 6 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f80, f72, f64, ffr, frd, fwr⟩ :=
    s1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1.trans F.h1) (e5.trans F.h5)
      (e6.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- the hash, into S + 32
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω2 μ2 1092 23395 (A - 88) rd (A - 56) ptr len 32 f0 f1 f7
      (by rw [f8]) f9 (by decide) jte_545 bs_23395 ⟨by omega, by omega, by omega⟩ hrd
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega)
      (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- moved to S, and the u64's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kmv, kfr, krd, kwr⟩ :=
    s2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 88) (by omega) (g1.trans f1) g7
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- the u64, into S + 32
  obtain ⟨ω5, μ5, run5, m0, m1, m2, m3, m4, m5, m6, m12, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω4 μ4 1094 23440 (A - 88) rd (A - 56) (ptr + 32) (len - 32) 8 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans (f6))) (by rw [k8, show A - 88 + 32 = A - 56 by omega]) k9 (by decide) jte_546 bs_23440
      ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR8)
  -- what the stores need, back to μ
  have hv : Num.decodeLE (μ.readN (ptr + 32) 8) < 18446744073709551616 := by
    have := decodeLE_lt (μ.readN (ptr + 32) 8); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 8 (Num.decodeLE (μ.readN (ptr + 32) 8)) = μ.readN (ptr + 32) 8 := by
    have := encodeLE_decodeLE (μ.readN (ptr + 32) 8); simpa [Memory.length_readN] using this
  have b5 : ∀ a, a < 4294967296 → (a < A - 176 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h1 h2 => (mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))
  have b5s : ∀ a, A - 24 ≤ a → a < A → μ5.read a = μ2.read a :=
    fun a h1 h2 => (mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))
  have hS32 : μ5.readN (A - 88) 32 = μ.readN ptr 32 := by
    rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (by omega) (by omega) (by omega)), kmv,
      show A - 88 + 32 = A - 56 by omega, gbuf]
    exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, nO, nO8, nO40, nfr, nrd, nwr⟩ := s3 (p := p) (P := P) (R := R) x ω5 μ5
    (A - 88) O ret t v5 v6 (Num.decodeLE (μ.readN (ptr + 32) 8)) rd (by omega) hO48 (by omega)
    (m1.trans (k1.trans (g1.trans f1))) (m5.trans (k5.trans (g5.trans f5))) m7 hv F.hv5 F.hv6 hrd64 hO64
    (by rw [show A - 88 + 32 = A - 56 by omega, mbuf, ev]
        exact Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega)).trans
          ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans (ffr _ (by omega) (by omega)))))
    (by rw [show A - 88 + 80 = A - 8 by omega, Memory.readN_congr (fun j hj => b5s _ (by omega) (by omega))]; exact f80)
    (by rw [show A - 88 + 72 = A - 16 by omega, Memory.readN_congr (fun j hj => b5s _ (by omega) (by omega))]; exact f72)
    (by rw [show A - 88 + 64 = A - 24 by omega, Memory.readN_congr (fun j hj => b5s _ (by omega) (by omega))]; exact f64)
    (by rw [show A - 88 + 136 = A + 48 by omega, Memory.readN_congr (fun j hj => b5 _ (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [show A - 88 + 128 = A + 40 by omega, Memory.readN_congr (fun j hj => b5 _ (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [show A - 88 + 120 = A + 32 by omega, Memory.readN_congr (fun j hj => b5 _ (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt
    (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by
      rw [mrd, krd, grd, frd]
      rcases Nat.lt_or_ge a A with h | h
      · exact Memory.readable_of_writable (hws a (by omega) h)
      · exact F.hr a h (by omega))
  refine ⟨ω6, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    n0, by rw [n1]; congr 1; omega, n5, n6, nO, nO8.trans hS32, nO40.trans ev, ?_, ?_, ?_,
    fun a => by rw [nrd, mrd, krd, grd, frd], fun a => by rw [nwr, mwr, kwr, gwr, fwr]⟩
  · rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega)), mR0]
  · rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega)), mR8]; congr 1
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact b5 a h0 h1 h2

end Services.Bootstrap.Decode.HashU64
