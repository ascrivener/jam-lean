import Services.Bootstrap.Encode.ArmsHVecAssign
import Services.Bootstrap.Encode.VariantsVec2Gas

/-!
# `AssignForGasCost` (24) with growth (`EncOkMH`)

`Enc.assign_gas` re-proved over `GrowH.StDH`: `gas_loopH` (the hash loop 18722 … 18749, each hash's 32
octets appended straight from the kept stretch (q, 32 n), `heapDH`), the end from 18752 shared with
`Assign` (`assign_tailH`), `assign_gasH` the arm. The heap octets are the queue's stretch (q, 32 n) when
n > 0 (`SrcAtP`).
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}

/-- **`AssignForGasCost`'s hash loop, with growth** (`Enc.gas_loop`): from the loop's head for hash k
    (ω₆ = q + 32 k, ω₅ = 32 i, i = n − k > 0) in `StDH (preG k)` with S at F − 56, the hashes k … n − 1
    appended, at 18752 in `StDH (preG n)`, S kept at F − 56; or a failed `realloc`. -/
theorem gas_loopH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (q : Nat) (c : List UInt8) (n : Nat) (hs : List UInt8) (S : Nat)
    (hh : hs.length = 32 * n) (hsrc : SafeR s0 ptr0 F S1 v q (32 * n)) (rh : μ0.readN q (32 * n) = hs)
    (hlen : 2 * (len + (preG c n hs n).length) ≤ capBound) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (preG c n hs k) ω μ1 → ω[5] = UInt64.ofNat (32 * i) →
      ω[6] = UInt64.ofNat (q + 32 * k) → μ1.readN (F - 56) 8 = Num.encodeLE 8 S →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 18722 ω μ1 x 18752 ω' μ' x ((2000 + growGas) * (32 * i)) ∧
        StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (preG c n hs n) ω' μ' ∧
        μ'.readN (F - 56) 8 = Num.encodeLE 8 S) ∨
      ExhaustsW env K pb p P 18722 ω μ1 x ((2000 + growGas) * (32 * i)) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h6 hS0
    have hk : k < n := by omega
    have hlk := preG_len c n hs k (by omega)
    have hln := preG_len c n hs n (by omega)
    obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds W1.H Fr (W1.safe hsrc)
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bm, bfr, brd, bwr⟩ := seg_18722 (p := p) (P := P)
      (R := refineContractK K env) x ω μ1 (F - 56) v (q + 32 * k) (by omega) (by omega) (by omega) st.h1 h6
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun a h1 h2 => W1.H.st a (by omega) (by omega))
    have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 (q + 32 * k) 32 776 18743
        (bytes := μ0.readN (q + 32 * k) 32) (by simp [Memory.readN]) rfl b0 b7 b8 b9
        ⟨by decide, by decide, by decide⟩ jte_387 bs_18743 (by omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω3, μ3, run3, st3, c5, c6, kF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold stepGas growGas; omega))
    rw [← preG_succ μ0 q c n hs rh k hk] at st3
    have m8 : μ3.readN (F - 56 + 8) 8 = Num.encodeLE 8 (q + 32 * k + 32) := by
      rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact bm
    have m0 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
      rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hS0
    have h5' : ω3[5] = UInt64.ofNat (32 * (i + 1)) := by rw [c5, b5, h5]
    obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · obtain ⟨ω4, run4, d1⟩ := seg_18743_last (p := p) (P := P) (R := refineContractK K env) x ω3 μ3 (F - 56)
        (q + 32 * k + 32) (by omega) (by omega) st3.h1 (by rw [h5']) m8
        (fun a h1 h2 => Memory.readable_of_writable (W3.H.st a (by omega) (by omega)))
      have hkn : k + 1 = n := by omega
      exact Or.inl ⟨ω4, μ3, (run2.trans (run3.trans run4)).mono (by unfold stepGas growGas; omega),
        StDH.cast ⟨⟨d1.trans st3.h1, st3.w0, st3.w5, st3.w6, st3.buf⟩, st3.sv⟩ (by rw [hkn]), m0⟩
    · obtain ⟨ω4, run4, d1, d5, d6⟩ := seg_18743_more (p := p) (P := P) (R := refineContractK K env) x ω3 μ3
        (F - 56) (q + 32 * k + 32) (32 * (i + 1)) (by omega) (by omega) ⟨by omega, by omega⟩ st3.h1 h5' m8
        (fun a h1 h2 => Memory.readable_of_writable (W3.H.st a (by omega) (by omega)))
      rcases ih (k + 1) ω4 μ3 (by omega) hi ⟨⟨d1.trans st3.h1, st3.w0, st3.w5, st3.w6, st3.buf⟩, st3.sv⟩
          (by rw [d5, show 32 * (i + 1) - 32 = 32 * i by omega])
          (by rw [d6, show q + 32 * k + 32 = q + 32 * (k + 1) by omega]) m0 with
        ⟨ω5, μ5, run5, st5, m5⟩ | hx
      · exact Or.inl ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono (by unfold stepGas growGas; omega),
          st5, m5⟩
      · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))

end

/-- **`AssignForGasCost` (index 24), with growth** (`Enc.assign_gas` as `EncOkMH`):
    `AssignGasRepAt q c n hs g` encodes to 24 :: (c ++ ℰ(n) ++ hs ++ g), the heap octets the queue's
    stretch (q, 32 n) when n > 0. -/
theorem assign_gasH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q : Nat) (c : List UInt8) (n : Nat) (hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n)
    (hg : g.length = 4) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 192 (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)) (AssignGasRepAt q c n hs g)
      (SrcAtP q (32 * n)) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r32, r36, -, r16, r24, rh⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 24) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have c32 : μ.readN (S + 32) 4 = g := by rw [← slot_take μ S 32 4 (by decide)]; exact r32
  have c36 : μ.readN (S + 36) 2 = c := by rw [← slot_take μ S 36 2 (by decide)]; exact r36
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hE := encodeNat_pos n
  have hN : (24 :: (c ++ Blob.encodeNat n ++ hs ++ g) : List UInt8).length =
      7 + (Blob.encodeNat n).length + 32 * n := by simp [hc, hh, hg]; omega
  have hln := preG_len c n hs n (by omega)
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startDH (p := p) (P := P) K x ω μ L (by decide) 24
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 24 = 18639 from rfl] at run1
  -- the tag, and S to sp
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bS, bfr, brd, bwr⟩ := seg_18639 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega) (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 24] 1 770 18662 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_384 bs_18662 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, -, cF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact bS
  -- the core
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d7, d8, d9, dc, dfr, drd, dwr⟩ := seg_18662 (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 (by rw [c5, b5]) m3
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rw [st3.slot L.slot (by decide), c36] at dc
  have m4 : μ4.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega))]; exact m3
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 c 2 772 18685 hc (by decide)
      d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_385 bs_18685 (by simp; omega) dc with
    ⟨ω5, μ5, run5, st5, -, -, eF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  have m5 : μ5.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact m4
  -- the queue's count
  obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, fn, ffr, frd, fwr⟩ := seg_18685 (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st5.h1 m5
    (by rw [st5.slot L.slot (by decide)]; exact c16)
    (by rw [st5.slot L.slot (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
    (fun a h1 h2 => W5.safe_readable (by omega) (W5.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W5.H.st a (by omega) (by omega))
  have st6 := st5.scratch Fr f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
  have m6 : μ6.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact m5
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω6 μ6 Fr (by decide) st6 n 774 18715 f0
      (by rw [f7]; congr 1; omega) f8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact fn)
      ⟨by decide, by decide, by decide⟩ jte_386 bs_18715 (by simp [hc]; omega) with
    ⟨ω7, μ7, run7, st7, g5, g6, gF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
      (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  have st7' := st7.cast (show [] ++ [UInt8.ofNat 24] ++ c ++ Blob.encodeNat n = preG c n hs 0 by simp [preG])
  have m7 : μ7.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => gF _ (by omega) (by omega))]; exact m6
  have henc := preG_all c n hs g hh
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no hashes
    subst hn0
    obtain ⟨ω8, run8, e8⟩ := seg_18715_zero (p := p) (P := P) (R := refineContractK K env) x ω7 μ7
      (by rw [g5, f5])
    rw [← e8] at st7'
    rcases assign_tailH (p := p) (P := P) K hK1 hK x ω8 μ7 Fr (by decide) st7' S L.slot hS' g c32 m7
        (by omega) with
      ⟨ω9, μ9, run9, st9⟩ | hx
    · exact Or.inl (closeH L 20383 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
          run9))))))))
        (st9.toStH.cast henc))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
        (run7.trans run8))))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  · have hsq := hsrc q (32 * n) ⟨by omega, rfl, rfl⟩
    obtain ⟨ω8, run8, k1, k5, k6⟩ := seg_18715_pos (p := p) (P := P) (R := refineContractK K env) x ω7 μ7 n
      ⟨hn0, hn⟩ (by rw [g5, f5])
    rcases gas_loopH (p := p) (P := P) K hK1 hK x Fr (by decide) q c n hs S hh hsq rh (by omega) n 0 ω8 μ7
        (by omega) hn0 ⟨⟨k1.trans st7'.h1, st7'.w0, st7'.w5, st7'.w6, st7'.buf⟩, st7'.sv⟩
        (by rw [k5]) (by rw [k6, g6, f6]; congr 1) m7 with
      ⟨ω9, μ9, run9, st9, m9⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
        (run7.trans run8))))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
    rcases assign_tailH (p := p) (P := P) K hK1 hK x ω9 μ9 Fr (by decide) st9 S L.slot hS' g c32 m9
        (by omega) with
      ⟨ω10, μ10, run10, st10⟩ | hx
    · exact Or.inl (closeH L 20383 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
          (run9.trans run10)))))))))
        (st10.toStH.cast henc))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
        (run7.trans (run8.trans run9)))))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))

/-- `assign_gasH` at the depth 232. -/
theorem assign_gasH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q : Nat) (c : List UInt8) (n : Nat) (hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n)
    (hg : g.length = 4) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 232 (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)) (AssignGasRepAt q c n hs g)
      (SrcAtP q (32 * n)) :=
  (assign_gasH env K pb hK1 hK q c n hs g hc hh hg hn hq64).mono (by decide)

end Services.Bootstrap.Encode.GrowH
