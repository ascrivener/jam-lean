import Services.Bootstrap.Decode.CreateServiceRun

/-!
# `Instruction::decode` of `CreateService` with `Option<Vec<u8>>` = `Some([])`

`opt_vec_empty`: `Option<Vec<u8>>::decode` (35937) called with its slot at sp + 232 (as
`CreateService`'s decoder calls it, return address 1130) on `Some([])`, the octets 1, 0: the empty
`Vec` `{cap 0, ptr 1, len 0}`, nothing allocated (as `LookedUp.looked_up_empty`).
`create_service_empty`: `CreateService` (tag 0; GP v0.8.0 B.7) with that option, from `cs_head`,
`opt_vec_empty` and `cs_tail`; generic in the host relation.
-/

namespace Services.Bootstrap.Decode.CreateService

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.LookedUp

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Option<Vec<u8>>::decode` of `Some([])`**: from 35937 with sp = ω₁, the slot sp + 232 (ω₇), the
    reader rd (ω₈) holding the octets 1 (`Some`) and 0 (ℰ(0)), and return address 1130, the decoder
    returns to 24265 with the empty `Vec` `{cap 0, ptr 1, len 0}` in the slot and the reader advanced by
    2. Memory changes only in sp − 184 … sp, the reader and the slot. -/
theorem opt_vec_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v5 v6 rd ptr len : Nat)
    (h0 : ω[0] = UInt64.ofNat 1130) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat (sp + 232)) (h8 : ω[8] = UInt64.ofNat rd)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hsp : 65536 + 184 ≤ sp ∧ sp + 256 < 4294967296)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 33 < 4294967296)
    (hlen : 2 ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (hzero : μ.read (ptr + 1) = 0)
    (hrdA : rd + 16 ≤ sp - 184 ∨ sp + 256 ≤ rd) (hpA : ptr + 33 ≤ sp - 184 ∨ sp + 256 ≤ ptr)
    (hpr : ptr + 33 ≤ rd ∨ rd + 16 ≤ ptr)
    (hws : ∀ a, sp - 184 ≤ a → a < sp + 256 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 2 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 35937 ω μ x 24265 ω' μ' x 700 ∧
      ω'[0] = UInt64.ofNat 1130 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN (sp + 232) 8 = Num.encodeLE 8 0 ∧ μ'.readN (sp + 240) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (sp + 248) 8 = Num.encodeLE 8 0 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 2) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 2) ∧
      (∀ a, a < 4294967296 → (a < sp - 184 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        (a < sp + 232 ∨ sp + 256 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hO64 : sp + 232 < 18446744073709551616 := by omega
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    o1 (p := p) (P := P) (R := R) x ω μ sp (sp + 232) rd 1130 v5 v6 ⟨by omega, by omega⟩ hO64 (by omega)
      (by omega) hv5 hv6 h0 h1 h5 h6 h7 h8 (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 1682 35970 (sp - 56) rd (sp - 25) ptr len 1 g0 g1 g7 g8 g9
      (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨hptr.1, by omega⟩
      (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact hrp a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (sp - 56 + 31) = 1 := by
    rw [show sp - 56 + 31 = sp - 25 by omega, read_of_readN1 kbuf, ← hsome]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := o_some (p := p) (P := P) (R := R) x ω4 μ4 (sp - 56)
    ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have he : Blob.encodeNat 0 = [UInt8.ofNat 0] := by simp [Blob.encodeNat]
  have hz4 : μ4.read (ptr + 1) = 0 := by
    rw [kfr _ (by omega) (by omega) (by omega) (by omega), gfr _ (by omega) (by omega)]; exact hzero
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := R) x ω5 μ4 1684 35994 (sp - 56) rd (ptr + 1) (len - 1) m0
      (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_841 bs_35994 ⟨by omega, by omega⟩ hrd
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact hwr a h1 h2) kR0 kR8 0 (by decide)
      (by rw [he]; simp; omega)
      (fun a h1 h2 => by rw [he] at h2; simp at h2; rw [krd, grd]; exact hrp a (by omega) (by omega))
      (by rw [he]; simp [Memory.readN, hz4])
  rw [he] at dR0 dR8
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := o_len (p := p) (P := P) (R := R) x ω6 μ6 (sp - 56) 0
    (by omega) (by decide) (by rw [d1, m1, k1', g1]) d7 d8
  have hv6' : ω7[6] = UInt64.ofNat rd := by rw [o6, d6, m6, k6, g6]
  obtain ⟨ω8, μ8, run8, v0, v1, v5', v6', vc, vp, vl, vfr, vrd, vwr⟩ :=
    Services.Bootstrap.Decode.VecU8.vec_u8_empty (p := p) (P := P) (R := R) x ω7 μ6 (sp - 56) (sp - 56) rd
      (len - 1 - 1) 1686 36016 (sp + 232) rd ⟨by omega, by omega⟩ o0 (by rw [o1', d1, m1, k1', g1])
      (by rw [o5, d5, m5, k5, g5]) hv6' o7 (by rw [o8, d6, m6, k6, g6]) o9 (by omega) (by omega) (by decide)
      jte_842 bs_36016 (by omega) (Or.inr (Nat.le_refl _)) hrd.2 (by omega) (rd8 (by omega) dR8)
      (fun a h1 h2 => by rw [drd, krd, grd]; exact Memory.readable_of_writable (hwr a (by omega) h2))
      (fun a h1 h2 => by rw [dwr, kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [dwr, kwr, gwr]; exact hws a (by omega) (by omega))
  have hfrA : ∀ a, sp - 32 ≤ a → a < sp → a ≠ sp - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    o_copy (p := p) (P := P) (R := R) x ω8 μ8 (sp - 56) (sp + 232) 0 1 0 1130 24265 v5 v6 ⟨by omega, by omega⟩
      (by omega) (by omega) v1 v5' (by decide) (by decide) (by decide) hv5 hv6
      vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfrA _ (by omega) (by omega) (by omega)), show sp - 56 + 48 = sp - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfrA _ (by omega) (by omega) (by omega)), show sp - 56 + 40 = sp - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfrA _ (by omega) (by omega) (by omega)), show sp - 56 + 32 = sp - 24 by omega]; exact gs6)
      (by decide) jte_564 bs_24265
      (fun a h1 h2 => by rw [vrd, drd, krd, grd]; exact Memory.readable_of_writable (hws a (by omega) (by omega)))
      (fun a h1 h2 => by rw [vwr, dwr, kwr, gwr]; exact hws a (by omega) (by omega))
  have hrd9 : ∀ j, j < 16 → μ9.read (rd + j) = μ6.read (rd + j) := fun j hj =>
    (cfr _ (by omega) (by omega)).trans (vfr _ (by omega) (by omega) (by omega))
  refine ⟨ω9, μ9, (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9)))))).mono
    (by omega), c0, by rw [c1]; congr 1; omega, c5, c6, cO, cO8, cO16, ?_, ?_, ?_,
    fun a => by rw [crd, vrd, drd, krd, grd], fun a => by rw [cwr, vwr, dwr, kwr, gwr]⟩
  · rw [show ptr + 2 = ptr + 1 + 1 by omega, Memory.readN_congr (a := rd) (n := 8) (fun j hj => hrd9 j (by omega))]; exact dR0
  · have e8 : μ9.readN (rd + 8) 8 = μ6.readN (rd + 8) 8 :=
      Memory.readN_congr (fun j hj => by rw [Nat.add_assoc]; exact hrd9 (8 + j) (by omega))
    rw [show len - 2 = len - 1 - 1 by omega, e8]; exact dR8
  · intro a h0 h1 h2 h3
    rw [cfr a h0 h3]
    exact (vfr a h0 (by omega) (by omega)).trans ((dfr a h0 (by omega) h2).trans
      ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega))))

/-- **`CreateService` with `Option<Vec<u8>>` = `Some([])`**: as `create_service_none`, with the octets
    1, 0 for the option: the empty `Vec` `{cap 0, ptr 1, len 0}` at O, O + 8, O + 16; nothing is
    allocated. Memory changes only in S − 184 … A (A = S + 384), the reader and O … O + 232. -/
theorem create_service_empty {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 rd ptr len : Nat) (ou : List UInt8) (F : Frame P (S + 384) O ret t v5 v6 ω μ)
    (hS : 65536 + 184 ≤ S ∧ S % 8 = 0) (hO8 : O % 8 = 0 ∧ O + 256 ≤ 4294967296) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read (S + 384) = 0) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296) (hptr : 65536 ≤ ptr ∧ ptr + 240 < 4294967296)
    (hou : ou = [0] ∨ ∃ u : List UInt8, u.length = 4 ∧ ou = 1 :: u)
    (hlen : 202 + ou.length ≤ len ∧ len < 4294967296)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read (ptr + 192) = 1) (hzero : μ.read (ptr + 193) = 0)
    (pay : μ.readN (ptr + 202) ou.length = ou)
    (hrdS : rd + 16 ≤ S - 184 ∨ S + 440 ≤ rd) (hpS : ptr + 240 ≤ S - 184 ∨ S + 440 ≤ ptr)
    (hOS : O + 232 ≤ S - 184 ∨ S + 440 ≤ O) (hOr : O + 232 ≤ rd ∨ rd + 16 ≤ O)
    (hpr : ptr + 240 ≤ rd ∨ rd + 16 ≤ ptr)
    (hws : ∀ a, S - 184 ≤ a → a < S + 384 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwO : ∀ a, O ≤ a → a < O + 232 → μ.writable a = true)
    (hrp : ∀ a, ptr ≤ a → a < ptr + 202 + ou.length → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20626 ω μ x t ω' μ' x 4400 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 440) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 0 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 0 ∧
      μ'.readN (O + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat ∧
      (ou.headD 0 = 1 → μ'.readN (O + 28) 4 = ou.tail) ∧
      μ'.readN (O + 32) 32 = μ.readN ptr 32 ∧
      μ'.readN (O + 64) 8 = μ.readN (ptr + 32) 8 ∧ μ'.readN (O + 72) 8 = μ.readN (ptr + 40) 8 ∧
      μ'.readN (O + 80) 8 = μ.readN (ptr + 48) 8 ∧ μ'.readN (O + 88) 8 = μ.readN (ptr + 56) 8 ∧
      μ'.readN (O + 96) 128 = μ.readN (ptr + 64) 128 ∧ μ'.readN (O + 224) 8 = μ.readN (ptr + 194) 8 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 202 + ou.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 202 - ou.length) ∧
      (∀ a, a < 4294967296 → (a < S - 184 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 232 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hrd64 : rd < 18446744073709551616 := by omega
  have hol : 1 ≤ ou.length ∧ ou.length ≤ 5 := by rcases hou with rfl | ⟨u, hu, rfl⟩ <;> simp [*]
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a376, a368, a360, ahash, a64, a56, a48, a40, aarr, aR0, aR8,
      afr, ard, awr⟩ :=
    cs_head (p := p) (P := P) (R := R) x ω μ S O ret t v5 v6 rd ptr len F ⟨by omega, hS.2⟩ h6 h7 tag tab hrt hrd
      ⟨hptr.1, by omega⟩ ⟨by omega, hlen.2⟩ hR0 hR8 (by omega) (by omega) (by omega)
      (fun a h1 h2 => hws a (by omega) h2) hwr (fun a h1 h2 => hrp a h1 (by omega))
  have hp1 : ∀ q, ptr ≤ q → q < ptr + 202 + ou.length → μ1.read q = μ.read q := fun q h1 h2 =>
    afr q (by omega) (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, gW, g1', g2', gR0, gR8, gfr, grd, gwr⟩ :=
    opt_vec_empty (p := p) (P := P) (R := R) x ω1 μ1 S O rd rd (ptr + 192) (len - 192) a0 a1 a5 a6 a7 a8 hO64
      hrd64 ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ aR0 aR8
      (by rw [hp1 _ (by omega) (by omega)]; exact hsome)
      (by rw [show ptr + 192 + 1 = ptr + 193 by omega, hp1 _ (by omega) (by omega)]; exact hzero)
      (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [awr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [awr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [ard]; exact hrp a (by omega) (by omega))
  have bS : ∀ a, S + 40 ≤ a → a < S + 440 → (a < S + 232 ∨ S + 360 ≤ a) → μ2.read a = μ1.read a :=
    fun a h1 h2 h3 => gfr a (by omega) (by omega) (by omega) (by omega)
  have b0 : ∀ a, a < 4294967296 → (a < S - 184 ∨ S + 384 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 => (gfr a h0 (by omega) h2 (by omega)).trans (afr a h0 (by omega) h2)
  have rd2 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [grd, ard]
  have wr2 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [gwr, awr]
  obtain ⟨ω5, μ5, run5, n0, n1, n5, n6, nO, nO8, nO16, nO24, nO28, nO32, nO64, nO72, nO80, nO88, nO96, nO224,
      nR0, nR8, nfr, nrd, nwr⟩ :=
    cs_tail (p := p) (P := P) (R := R) x ω2 μ2 S O ret t v5 v6 rd (ptr + 194) (len - 194) 0 1 0 ou
      ⟨by omega, hS.2, by omega⟩ hO8 (by omega) g1 g5 g6 (by decide) (by decide) (by decide) (by decide) gW g1' g2'
      (by rw [Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a376)
      (by rw [Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hv5 F.hv6 F.hret F.hjt F.hbt hrd ⟨by omega, by omega⟩ hou ⟨by omega, by omega⟩
      (gR0.trans (congrArg _ (by omega))) (gR8.trans (congrArg _ (by omega)))
      (by rw [Memory.readN_congr (fun j hj => (b0 _ (by omega) (by omega) (by omega)))]
          rw [show ptr + 194 + 8 = ptr + 202 by omega]; exact pay)
      (by omega) (by omega) hOr (by omega)
      (fun a h1 h2 => by rw [wr2]; exact hws a (by omega) h2)
      (fun a h1 h2 => by rw [wr2]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr2]; exact hwO a h1 h2)
      (fun a h1 h2 => by rw [rd2]; exact hrp a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd2]; exact F.hr a (by omega) (by omega))
  refine ⟨ω5, μ5, (run1.trans (run2.trans run5)).mono (by omega), n0, n1, n5, n6, nO, nO8, nO16,
    nO24, nO28, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 h3 => ?_,
    fun a => by rw [nrd, rd2], fun a => by rw [nwr, wr2]⟩
  · rw [nO32, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact ahash
  · rw [nO64, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a64
  · rw [nO72, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a56
  · rw [nO80, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a48
  · rw [nO88, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact a40
  · rw [nO96, Memory.readN_congr (fun j hj => bS _ (by omega) (by omega) (by omega))]; exact aarr
  · rw [nO224]; exact Memory.readN_congr (fun j hj => b0 _ (by omega) (by omega) (by omega))
  · rw [nR0]; try exact congrArg _ (by omega)
  · rw [nR8]; try exact congrArg _ (by omega)
  · rw [nfr a h0 (by omega) h2 h3]; exact b0 a h0 h1 h2

end Services.Bootstrap.Decode.CreateService
