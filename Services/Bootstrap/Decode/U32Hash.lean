import Services.Bootstrap.Decode.HashU64

/-!
# `Instruction::decode`: `Eject { target: u32, code_hash }`

`Eject` (tag 4) is decoded by a helper with a 64-octet frame at S = A − 64: it reads the `u32` into
S + 8 (`read_ok`), parks it (sign-extended) at S, reads the hash into S + 8 (`read_big_sp`), and stores
the variant into the slot O: the discriminant word 2^63 + 3 at O, the hash at O + 8 and the `u32` at
O + 40.
-/

namespace Services.Bootstrap.Decode.U32Hash

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 20914 … 20953: `Eject`'s decoder enters the helper: a 64-octet frame at S = A − 64 saving the
    return address 948, O and the reader at S + 56, S + 48, S + 40, a zeroed `u32` at S + 8, and the
    call of the reader for 4 octets into S + 8 (return address 1084). -/
theorem e1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 64 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 64 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20914 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1084 ∧ ω'[1] = UInt64.ofNat (A - 64) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 948 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 64 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 64 + 56 = A - 8 by omega, show A - 64 + 48 = A - 16 by omega,
      show A - 64 + 40 = A - 24 by omega, show A - 64 + 8 = A - 56 by omega]; post_simp)

/-- The low four octets of a word. -/
theorem take_encodeLE (x : Nat) : (Num.encodeLE 8 x).take 4 = Num.encodeLE 4 x := by
  simp [Num.encodeLE]

/-- A sign-extended `u32`, reduced to 64 bits, has the `u32`'s four octets. -/
theorem encodeLE4_sxw (v : Nat) (hv : v < 4294967296) :
    Num.encodeLE 4 (sxw 4 v % 18446744073709551616) = Num.encodeLE 4 v := by
  rw [← encodeLE_mod 4 (sxw 4 v % 18446744073709551616), Nat.mod_mod_of_dvd _ (by decide), encodeLE_mod,
    encodeLE_sxw 4 v (Or.inr rfl) hv]

/-- 23188 … 23217: the `u32` read succeeded (ω₇ = 0): the helper parks it, sign-extended, as a word at
    S, zeroes S + 8 … S + 40 and calls the reader for 32 octets into S + 8 (return address 1086). -/
theorem e2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 40 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (S + 8) 4 = Num.encodeLE 4 v)
    (hw : ∀ a, S ≤ a → a < S + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 23188 ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1086 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 8) ∧ ω'[9] = UInt64.ofNat 32 ∧
      (μ'.readN S 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 8) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, S ≤ a → a < S + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 23224 … 23301 then 20957 … 20969: the hash read succeeded (ω₇ = 0): the helper stores `Eject`'s
    discriminant word 2^63 + 3 at O, the hash (S + 8 … S + 40) at O + 8 and the `u32` (the low four
    octets of the word at S) at O + 40, pops its frame and returns to 20957, and the decoder returns
    through its frame at A = S + 64. -/
theorem e3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 w o6 : Nat) (hA : S + 64 + 56 < 4294967296) (hO : O + 44 ≤ 4294967296)
    (hOS : O + 44 ≤ S ∨ S + 120 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hw64 : w < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sw : μ.readN S 8 = Num.encodeLE 8 w)
    (sr : μ.readN (S + 56) 8 = Num.encodeLE 8 948) (sO : μ.readN (S + 48) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 40) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 112) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 104) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 96) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 44 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23224 ω μ x t ω' μ' x 24 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 120) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775811 ∧ μ'.readN (O + 8) 32 = μ.readN (S + 8) 32 ∧
      μ'.readN (O + 40) 4 = Num.encodeLE 4 w ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 44 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rw0 := rd _ w hw64 sw
  have rr := rd _ 948 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 64 + 48) 8 = ret := by rw [show S + 64 + 48 = S + 112 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 64 + 40) 8 = v5 := by rw [show S + 64 + 40 = S + 104 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 64 + 32) 8 = v6 := by rw [show S + 64 + 32 = S + 96 by omega]; exact rd _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rw0, rr, rO, ro6, r0, r5, r6, hret, hjt, hbt,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try (rw [show O + 16 = O + 8 + 8 by omega, show O + 24 = O + 8 + 16 by omega,
      show O + 32 = O + 8 + 24 by omega, show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
      show S + 32 = S + 8 + 24 by omega]; exact copy4g μ _ (S + 8) (O + 8) (by omega))
    all_goals try exact encodeLE_mod 4 w

/-- **`Eject`**: from 20626, with tag 4 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding at least 36 more octets, `Instruction::decode` returns `Eject { target, code_hash }` in its
    slot O: the discriminant word 2^63 + 3 at O, the 32 octets of `code_hash` (from ptr + 4) at O + 8
    and the 4 of `target` (from ptr) at O + 40. The reader is advanced by 36. Memory changes only in
    A − 152 … A (the helper's and the reader's frames), the reader and O … O + 44. -/
theorem eject {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 152 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 4) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 64 < 4294967296)
    (hlen : 36 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 152 ∨ A + 56 ≤ rd) (hpA : ptr + 64 ≤ A - 152 ∨ A + 56 ≤ ptr)
    (hOA' : O + 44 ≤ A - 152 ∨ A + 56 ≤ O) (hOr : O + 44 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 36 ≤ rd ∨ rd + 16 ≤ ptr) (hO44 : O + 44 ≤ 4294967296)
    (hws : ∀ a, A - 152 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 44 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 36 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 650 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775811 ∧ μ'.readN (O + 8) 32 = μ.readN (ptr + 4) 32 ∧
      μ'.readN (O + 40) 4 = μ.readN ptr 4 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 36) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 36) ∧
      (∀ a, a < 4294967296 → (a < A - 152 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 44 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  -- the dispatch and the helper's entry
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 4 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f56, f48, f40, ffr, frd, fwr⟩ :=
    e1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- the u32, into S + 8
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1084 23188 (A - 64) rd (A - 56) ptr len 4 f0 f1 f7 f8 f9
      (by decide) jte_541 bs_23188 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  have hv : Num.decodeLE (μ.readN ptr 4) < 4294967296 := by
    have := decodeLE_lt (μ.readN ptr 4); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 4 (Num.decodeLE (μ.readN ptr 4)) = μ.readN ptr 4 := by
    have := encodeLE_decodeLE (μ.readN ptr 4); simpa [Memory.length_readN] using this
  -- parked at S, and the hash's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    e2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 64) (Num.decodeLE (μ.readN ptr 4)) (by omega) (g1.trans f1) g7 hv
      (by rw [show A - 64 + 8 = A - 56 by omega, gbuf, ev]
          exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  -- the hash, into S + 8
  obtain ⟨ω5, μ5, run5, m0, m1, m5, m6, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω4 μ4 1086 23224 (A - 64) rd (A - 56) (ptr + 4) (len - 4) 32 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) (by rw [k8, show A - 64 + 8 = A - 56 by omega]) k9
      (by decide) jte_542 bs_23224 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega))]; exact gR8)
  have b5 : ∀ a, a < 4294967296 → (a < A - 152 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h1 h2 => (mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))
  have b5s : ∀ a, A - 24 ≤ a → a < A → μ5.read a = μ2.read a :=
    fun a h1 h2 => (mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))
  have hpark : (μ5.readN (A - 64) 8).take 4 = μ.readN ptr 4 := by
    rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (by omega) (by omega) (by omega)), kpark, ev]
  have hS8 : μ5.readN (A - 56) 32 = μ.readN (ptr + 4) 32 := by
    rw [mbuf]
    exact Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega)).trans
      ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans (ffr _ (by omega) (by omega))))
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, nO, nO8, nO40, nfr, nrd, nwr⟩ := e3 (p := p) (P := P) (R := R) x ω5 μ5
    (A - 64) O ret t v5 v6 (rdN μ5 (A - 64) 8) rd (by omega) hO44 (by omega)
    (m1.trans (k1.trans (g1.trans f1))) (m5.trans (k5.trans (g5.trans f5))) m7 (rdN_lt64 _ _) F.hv5 F.hv6 hrd64 hO64
    (encodeLE_rdN _ _ _).symm
    (by rw [show A - 64 + 56 = A - 8 by omega, Memory.readN_congr (fun j hj => b5s _ (by omega) (by omega))]; exact f56)
    (by rw [show A - 64 + 48 = A - 16 by omega, Memory.readN_congr (fun j hj => b5s _ (by omega) (by omega))]; exact f48)
    (by rw [show A - 64 + 40 = A - 24 by omega, Memory.readN_congr (fun j hj => b5s _ (by omega) (by omega))]; exact f40)
    (by rw [show A - 64 + 112 = A + 48 by omega, Memory.readN_congr (fun j hj => b5 _ (by omega) (by omega) (by omega))]; exact F.s0)
    (by rw [show A - 64 + 104 = A + 40 by omega, Memory.readN_congr (fun j hj => b5 _ (by omega) (by omega) (by omega))]; exact F.s5)
    (by rw [show A - 64 + 96 = A + 32 by omega, Memory.readN_congr (fun j hj => b5 _ (by omega) (by omega) (by omega))]; exact F.s6)
    F.hret F.hjt F.hbt
    (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hwO a h1 h2)
    (fun a h1 h2 => by
      rw [mrd, krd, grd, frd]
      rcases Nat.lt_or_ge a A with h | h
      · exact Memory.readable_of_writable (hws a (by omega) h)
      · exact F.hr a h (by omega))
  refine ⟨ω6, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    n0, by rw [n1]; congr 1; omega, n5, n6, nO, ?_, ?_, ?_, ?_, ?_,
    fun a => by rw [nrd, mrd, krd, grd, frd], fun a => by rw [nwr, mwr, kwr, gwr, fwr]⟩
  · rw [nO8, show A - 64 + 8 = A - 56 by omega]; exact hS8
  · rw [nO40, ← take_encodeLE, encodeLE_rdN]; exact hpark
  · rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega)), mR0]
  · rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega)), mR8]; congr 1
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact b5 a h0 h1 h2

end Services.Bootstrap.Decode.U32Hash
