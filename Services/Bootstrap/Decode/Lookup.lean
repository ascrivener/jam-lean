import Services.Bootstrap.Decode.U32Hash

/-!
# `Instruction::decode`: `Lookup { service: u32, hash, eager: bool }`

`Lookup` (tag 8) is decoded by a helper with a 96-octet frame at S = A − 96: it reads the `u32` into
S + 40 (`read_ok`) and parks it at S, reads the hash into S + 40 (`read_big_sp`) and moves it to S + 8,
reads one octet into S + 40 (`read_ok`), checks that it is 0 or 1 (`bool`), and stores the variant into
the slot O: the discriminant word 2^63 + 7 at O, the `u32` at O + 8, the hash at O + 12 and the bool
at O + 44.
-/

namespace Services.Bootstrap.Decode.Lookup

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21918 … 21957: `Lookup`'s decoder enters the helper: a 96-octet frame at S = A − 96 saving the
    return address 1014, O and the reader at S + 88, S + 80, S + 72, a zeroed `u32` at S + 40, and the
    call of the reader for 4 octets into S + 40 (return address 1100). -/
theorem l1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 96 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 96 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21918 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1100 ∧ ω'[1] = UInt64.ofNat (A - 96) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 56) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 1014 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
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

/-- 23643 … 23672: the `u32` read succeeded (ω₇ = 0): the helper parks it, sign-extended, as a word at
    S, zeroes S + 40 … S + 72 and calls the reader for 32 octets into S + 40 (return address 1102). -/
theorem l2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S v : Nat)
    (hS : S + 72 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hv : v < 4294967296) (sv : μ.readN (S + 40) 4 = Num.encodeLE 4 v)
    (hw0 : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hw : ∀ a, S + 40 ≤ a → a < S + 72 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 23643 ω μ x 58434 ω' μ' x 12 ∧
      ω'[0] = UInt64.ofNat 1102 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 40) ∧ ω'[9] = UInt64.ofNat 32 ∧
      (μ'.readN S 8).take 4 = Num.encodeLE 4 v ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → (a < S + 40 ∨ S + 72 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rv : rdN μ (S + 40) 4 = v := by
    show Num.decodeLE _ = _
    rw [sv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hv)]
  have hr : ∀ a, S + 40 ≤ a → a < S + 72 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hw0, hr, rv, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try exact UInt64.ofNat_toNat
    all_goals try (rw [take_encodeLE, encodeLE4_sxw v hv])

/-- 23679 … 23738: the hash read succeeded (ω₇ = 0): the helper moves it from S + 40 to S + 8, zeroes
    the octet at S + 40 and calls the reader for 1 octet into S + 40 (return address 1104). -/
theorem l3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S : Nat)
    (hS : S + 72 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat 0)
    (hw : ∀ a, S + 8 ≤ a → a < S + 41 → μ.writable a = true)
    (hr : ∀ a, S + 40 ≤ a → a < S + 72 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 23679 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1104 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[6] ∧ ω'[8] = UInt64.ofNat (S + 40) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (S + 8) 32 = μ.readN (S + 40) 32 ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 41 ≤ a) → μ'.read a = μ.read a) ∧
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

set_option maxHeartbeats 32000000 in
/-- 23745 … 23829 then 21961 … 21973: the octet read succeeded (ω₇ = 0) and is a bool b ∈ {0, 1}: the
    helper stores `Lookup`'s discriminant word 2^63 + 7 at O, the `u32` (the low four octets of the word
    at S) at O + 8, the hash (S + 8 … S + 40) at O + 12 and b at O + 44, pops its frame and returns to
    21961, and the decoder returns through its frame at A = S + 96. -/
theorem l4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 w b o6 : Nat) (hA : S + 96 + 56 < 4294967296) (hO : O + 45 ≤ 4294967296)
    (hOS : O + 45 ≤ S ∨ S + 152 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hw64 : w < 18446744073709551616) (hb : b < 2)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (ho6 : o6 < 18446744073709551616) (hOv : O < 18446744073709551616)
    (sw : μ.readN S 8 = Num.encodeLE 8 w) (sb : μ.read (S + 40) = UInt8.ofNat b)
    (sr : μ.readN (S + 88) 8 = Num.encodeLE 8 1014) (sO : μ.readN (S + 80) 8 = Num.encodeLE 8 O)
    (so6 : μ.readN (S + 72) 8 = Num.encodeLE 8 o6)
    (s0 : μ.readN (S + 144) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 136) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 128) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ x, O ≤ x → x < O + 45 → μ.writable x = true)
    (hr : ∀ x, S ≤ x → x < S + 152 → μ.readable x = true) :
    ∃ ω' μ', FreeStepsH p R 23745 ω μ x t ω' μ' x 34 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 152) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775815 ∧ μ'.readN (O + 8) 4 = Num.encodeLE 4 w ∧
      μ'.readN (O + 12) 32 = μ.readN (S + 8) 32 ∧ μ'.read (O + 44) = UInt8.ofNat b ∧
      (∀ x, x < 4294967296 → (x < O ∨ O + 45 ≤ x) → μ'.read x = μ.read x) ∧
      (∀ x, μ'.readable x = μ.readable x) ∧ (∀ x, μ'.writable x = μ.writable x) := by
  have rd : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rw0 := rd _ w hw64 sw
  have rr := rd _ 1014 (by decide) sr
  have rO := rd _ O hOv sO
  have ro6 := rd _ o6 ho6 so6
  have r0 : rdN μ (S + 96 + 48) 8 = ret := by rw [show S + 96 + 48 = S + 144 by omega]; exact rd _ ret (by omega) s0
  have r5 : rdN μ (S + 96 + 40) 8 = v5 := by rw [show S + 96 + 40 = S + 136 by omega]; exact rd _ v5 hv5 s5
  have r6 : rdN μ (S + 96 + 32) 8 = v6 := by rw [show S + 96 + 32 = S + 128 by omega]; exact rd _ v6 hv6 s6
  have rbb : rdN μ (S + 40) 1 = b := by
    simp only [rdN, Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, sb, Num.decodeLE]
    simp; omega
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
  · rw [show ω = regsNF ω [] from rfl]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rw0, rr, rO, ro6, r0, r5, r6, rbb, hret, hjt, hbt,
        rdN_writeN_disjoint, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x ha0 ha1 => ?_, fun x => ?_, fun x => ?_⟩
      post_simp
      all_goals try exact encodeLE_mod 4 w
      all_goals try (simp (disch := omega) only [Memory.writeN_cons, Memory.writeN_nil, PVM.read_write_eq'])
      all_goals try (rw [show O + 20 = O + 12 + 8 by omega, show O + 28 = O + 12 + 16 by omega,
        show O + 36 = O + 12 + 24 by omega, show S + 16 = S + 8 + 8 by omega, show S + 24 = S + 8 + 16 by omega,
        show S + 32 = S + 8 + 24 by omega]; exact copy4g μ _ (S + 8) (O + 12) (by omega))

/-- **`Lookup`**: from 20626, with tag 8 read without error and the reader `{ptr, len}` at rd (ω₆)
    holding at least 37 more octets of which the last, at ptr + 36, is a bool b ∈ {0, 1},
    `Instruction::decode` returns `Lookup { service, hash, eager }` in its slot O: the discriminant
    word 2^63 + 7 at O, the 4 octets of `service` (from ptr) at O + 8, the 32 of `hash` (from ptr + 4) at
    O + 12 and b at O + 44. The reader is advanced by 37. Memory changes only in A − 184 … A (the
    helper's and the reader's frames), the reader and O … O + 45. -/
theorem lookup {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A O ret t v5 v6 rd ptr len b : Nat) (F : Frame P A O ret t v5 v6 ω μ)
    (hA : 65536 + 184 ≤ A ∧ A % 8 = 0) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 8) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 72 < 4294967296)
    (hlen : 37 ≤ len ∧ len < 4294967296) (hb : b < 2) (sb : μ.read (ptr + 36) = UInt8.ofNat b)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hrdA : rd + 16 ≤ A - 184 ∨ A + 56 ≤ rd) (hpA : ptr + 72 ≤ A - 184 ∨ A + 56 ≤ ptr)
    (hOA' : O + 45 ≤ A - 184 ∨ A + 56 ≤ O) (hOr : O + 45 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 37 ≤ rd ∨ rd + 16 ≤ ptr) (hO45 : O + 45 ≤ 4294967296)
    (hws : ∀ a, A - 184 ≤ a → a < A → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 45 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 37 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 760 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775815 ∧ μ'.readN (O + 8) 4 = μ.readN ptr 4 ∧
      μ'.readN (O + 12) 32 = μ.readN (ptr + 4) 32 ∧ μ'.read (O + 44) = UInt8.ofNat b ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 37) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 37) ∧
      (∀ a, a < 4294967296 → (a < A - 184 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 45 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hv : Num.decodeLE (μ.readN ptr 4) < 4294967296 := by
    have := decodeLE_lt (μ.readN ptr 4); simpa [Memory.length_readN] using this
  have ev : Num.encodeLE 4 (Num.decodeLE (μ.readN ptr 4)) = μ.readN ptr 4 := by
    have := encodeLE_decodeLE (μ.readN ptr 4); simpa [Memory.length_readN] using this
  -- the dispatch and the helper's entry
  obtain ⟨ω1, run1, e0', e1', e5', e6'⟩ := dispatch (p := p) (P := P) (R := R) x ω μ A 8 (by decide) (by omega)
    F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f88, f80, f72, ffr, frd, fwr⟩ :=
    l1 (p := p) (P := P) (R := R) x ω1 μ A O rd ⟨by omega, by omega⟩ (e1'.trans F.h1) (e5'.trans F.h5)
      (e6'.trans h6) hO64 hrd64 (fun a h1 h2 => hws a (by omega) h2)
  -- the u32, into S + 40
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω2 μ2 1100 23643 (A - 96) rd (A - 56) ptr len 4 f0 f1 f7 f8 f9
      (by decide) jte_549 bs_23643 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact hR8)
  -- parked at S, and the hash's call
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, kpark, kfr, krd, kwr⟩ :=
    l2 (p := p) (P := P) (R := R) x ω3 μ3 (A - 96) (Num.decodeLE (μ.readN ptr 4)) (by omega) (g1.trans f1) g7 hv
      (by rw [show A - 96 + 40 = A - 56 by omega, gbuf, ev]
          exact Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hws a (by omega) (by omega))
  -- the hash, into S + 40
  obtain ⟨ω5, μ5, run5, m0, m1, m5, m6, m7, mR0, mR8, mbuf, mfr, mrd, mwr⟩ :=
    read_big_sp (p := p) (P := P) (R := R) x ω4 μ4 1102 23679 (A - 96) rd (A - 56) (ptr + 4) (len - 4) 32 k0
      (k1.trans (g1.trans f1)) (k7.trans (g6.trans f6)) (by rw [k8, show A - 96 + 40 = A - 56 by omega]) k9
      (by decide) jte_550 bs_23679 ⟨by omega, by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (by omega) (by omega))]; exact gR8)
  -- moved to S + 8, and the bool's call
  obtain ⟨ω6, μ6, run6, n0, n1, n5, n6, n7, n8, n9, nmv, nfr, nrd, nwr⟩ :=
    l3 (p := p) (P := P) (R := R) x ω5 μ5 (A - 96) (by omega) (m1.trans (k1.trans (g1.trans f1))) m7
      (fun a h1 h2 => by rw [mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [mrd, krd, grd, frd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
  -- the bool, into S + 40
  obtain ⟨ω7, μ7, run7, q0, q1, q2, q3, q4, q5, q6, q12, q7, qR0, qR8, qbuf, qfr, qrd, qwr⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω6 μ6 1104 23745 (A - 96) rd (A - 56) (ptr + 36) (len - 36) 1 n0
      (n1.trans (m1.trans (k1.trans (g1.trans f1)))) (n7.trans (m6.trans (k6.trans (g6.trans f6))))
      (by rw [n8, show A - 96 + 40 = A - 56 by omega]) n9
      (by decide) jte_551 bs_23745 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [nwr, mwr, kwr, gwr, fwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [nrd, mrd, krd, grd, frd]; exact hrp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega))]; exact mR0)
      (by rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (by omega)), mR8]; congr 1)
  -- back to μ
  have b7 : ∀ a, a < 4294967296 → (a < A - 184 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (qfr a h0 (by omega) h2 (by omega)).trans ((nfr a h0 (by omega)).trans
      ((mfr a h0 (by omega) h2 (by omega)).trans ((kfr a h0 (by omega) (by omega)).trans
      ((gfr a h0 (by omega) h2 (by omega)).trans (ffr a h0 (by omega))))))
  have b7s : ∀ a, A - 24 ≤ a → a < A → μ7.read a = μ2.read a :=
    fun a h1 h2 => (qfr a (by omega) (by omega) (by omega) (by omega)).trans ((nfr a (by omega) (by omega)).trans
      ((mfr a (by omega) (by omega) (by omega) (by omega)).trans ((kfr a (by omega) (by omega) (by omega)).trans
      (gfr a (by omega) (by omega) (by omega) (by omega)))))
  have pay6 : ∀ q, ptr ≤ q → q < ptr + 37 → μ6.read q = μ.read q := fun q h1 h2 =>
    (nfr q (by omega) (by omega)).trans ((mfr q (by omega) (by omega) (by omega) (by omega)).trans
      ((kfr q (by omega) (by omega) (by omega)).trans ((gfr q (by omega) (by omega) (by omega) (by omega)).trans
      (ffr q (by omega) (by omega)))))
  have hpark : (μ7.readN (A - 96) 8).take 4 = μ.readN ptr 4 := by
    rw [Memory.readN_congr (fun j hj => (qfr _ (by omega) (by omega) (by omega) (by omega)).trans
      ((nfr _ (by omega) (by omega)).trans (mfr _ (by omega) (by omega) (by omega) (by omega)))), kpark, ev]
  have hS8 : μ7.readN (A - 96 + 8) 32 = μ.readN (ptr + 4) 32 := by
    rw [Memory.readN_congr (fun j hj => qfr _ (by omega) (by omega) (by omega) (by omega)), nmv,
      show A - 96 + 40 = A - 56 by omega, mbuf]
    exact Memory.readN_congr (fun j hj => (kfr _ (by omega) (by omega) (by omega)).trans
      ((gfr _ (by omega) (by omega) (by omega) (by omega)).trans (ffr _ (by omega) (by omega))))
  have hb7 : μ7.read (A - 96 + 40) = UInt8.ofNat b := by
    have := congrArg List.head? qbuf
    simp only [Memory.readN, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, List.head?_cons,
      Option.some.injEq] at this
    rw [show A - 96 + 40 = A - 56 by omega, this, pay6 _ (by omega) (by omega)]; exact sb
  obtain ⟨ω8, μ8, run8, r0, r1, r5, r6, rO, rO8, rO12, rO44, rfr, rrd, rwr⟩ := l4 (p := p) (P := P) (R := R) x ω7 μ7
    (A - 96) O ret t v5 v6 (rdN μ7 (A - 96) 8) b rd (by omega) hO45 (by omega)
    (q1.trans (n1.trans (m1.trans (k1.trans (g1.trans f1))))) (q5.trans (n5.trans (m5.trans (k5.trans (g5.trans f5)))))
    q7 (rdN_lt64 _ _) hb F.hv5 F.hv6 hrd64 hO64 (encodeLE_rdN _ _ _).symm hb7
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
    run8))))))).mono (by omega), r0, by rw [r1]; congr 1; omega, r5, r6, rO, ?_, rO12.trans hS8, rO44, ?_, ?_, ?_,
    fun a => by rw [rrd, qrd, nrd, mrd, krd, grd, frd], fun a => by rw [rwr, qwr, nwr, mwr, kwr, gwr, fwr]⟩
  · rw [rO8, ← take_encodeLE, encodeLE_rdN]; exact hpark
  · rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega)), qR0]
  · rw [Memory.readN_congr (fun j hj => rfr _ (by omega) (by omega)), qR8]; congr 1
  · intro a h0 h1 h2 h3
    rw [rfr a h0 h3]; exact b7 a h0 h1 h2

end Services.Bootstrap.Decode.Lookup
