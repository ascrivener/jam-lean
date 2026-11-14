import Services.Bootstrap.Encode.ArmsHVecCore

/-!
# `Bless` (11) with growth (`EncOkMH`)

`Enc.bless` re-proved over `GrowH.StDH`: `pieceU32DH` (`Enc.pieceU32D`), `bless_loopH` (the element loop
18315 … 18363, each element's `u32` and `u64` loaded from the heap into the scratch word and appended:
the loads read the kept stretch (q, 16 n), as at entry, `BufH.readN_safe`), `blessH` the arm. The heap
octets are the elements' array (q, 16 n) when n > 0 (`SrcAtP`).
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

/-- **A `u32` piece of `Bless`, with growth** (`Enc.pieceU32D`): the 4 octets at S + off (as at entry)
    appended, S in ω₅ and the writer in ω₆ kept. -/
theorem pieceU32DH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {pre : List UInt8} (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S : Nat) (hS : SafeR s0 ptr0 F S1 v S 232)
    (hS' : S + 256 < 4294967296) (e r off e' : Nat)
    (he : (e = 18186 ∧ r = 730 ∧ off = 32) ∨ (e = 18207 ∧ r = 732 ∧ off = 36) ∨
      (e = 18228 ∧ r = 734 ∧ off = 40) ∨ (e = 18249 ∧ r = 736 ∧ off = 44))
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h5 : ω[5] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat v) (hlen : 2 * (len + pre.length + 4) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas 4 + 12) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ0.readN (S + off) 4) ω' μ' ∧
      ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas 4 + 12) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by omega
  have hoff : off + 4 ≤ 232 := by omega
  obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_u32B (p := p) (P := P)
    (R := refineContractK K env) x ω μ e r off (F - 56) v S he (by omega) (by omega) (by omega) st.h1 h5 h6
    (fun a h1 h2 => W1.safe_readable (by omega) (W1.safe hS) a (by omega) (by omega))
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 (μ0.readN (S + off) 4) 4 r e'
      (by simp [Memory.readN]) (by decide) b0 b7 b8 b9 hr hje hbe hlen (by rw [bt, st.slot hS hoff]) with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  · exact Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans (b5.trans h5), c6.trans (b6.trans h6)⟩
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

/-- **`Bless`'s element loop, with growth** (`Enc.bless_loop`): from the loop's head for element k
    (ω₅ = q + 16 k, the writer in ω₆, the end q + 16 n at F − 48) in `StDH (pre0 ++ items.take (12 k))`,
    i = n − k > 0 elements left, each element's `u32` and `u64` (read from the kept stretch (q, 16 n))
    appended, at 20118 in `StDH (pre0 ++ items)`; or a failed `realloc`. -/
theorem bless_loopH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (q n : Nat) (pre0 items : List UInt8)
    (hi : items.length = 12 * n) (hsrc : SafeR s0 ptr0 F S1 v q (16 * n))
    (arr : ∀ j, j < n → μ0.readN (q + 16 * j) 4 = (items.drop (12 * j)).take 4 ∧
      μ0.readN (q + 16 * j + 8) 8 = (items.drop (12 * j + 4)).take 8)
    (hlen : 2 * (len + pre0.length + 12 * n) ≤ capBound) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ items.take (12 * k)) ω μ1 →
      ω[5] = UInt64.ofNat (q + 16 * k) → ω[6] = UInt64.ofNat v →
      μ1.readN (F - 56 + 8) 8 = Num.encodeLE 8 (q + 16 * n) →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 18315 ω μ1 x 20118 ω' μ' x ((2000 + growGas) * (12 * i)) ∧
        StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ items) ω' μ') ∨
      ExhaustsW env K pb p P 18315 ω μ1 x ((2000 + growGas) * (12 * i)) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h6 hz
    have hk : k < n := by omega
    have hlenk : (items.take (12 * k)).length = 12 * k := by simp [hi]; omega
    obtain ⟨ar4, ar8⟩ := arr k hk
    have s4 : SafeR s0 ptr0 F S1 v (q + 16 * k) 4 := hsrc.sub (by omega) (by omega)
    have s8 : SafeR s0 ptr0 F S1 v (q + 16 * k + 8) 8 := hsrc.sub (by omega) (by omega)
    obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds W1.H Fr (W1.safe hsrc)
    -- the element's u32
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18315 (p := p) (P := P)
      (R := refineContractK K env) x ω μ1 (F - 56) v (q + 16 * k) (by omega) (by omega) (by omega) st.h1 h5 h6
      (fun b h1 h2 => W1.safe_readable (by omega) (W1.safe s4) b h1 h2)
      (fun b h1 h2 => W1.H.st b (by omega) (by omega))
    have st2 := st.scratch Fr b1 (fun b h0 h1 => bfr b h0 (by omega)) brd bwr
    rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 ((items.drop (12 * k)).take 4) 4 740
        18336 (by simp [hi]; omega) (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_369 bs_18336
        (by simp [hlenk]; omega) (by rw [bt, W1.readN_safe s4]; exact ar4) with
      ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold stepGas growGas; omega))
    -- the element's u64
    obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_18336 (p := p) (P := P)
      (R := refineContractK K env) x ω3 μ3 (F - 56) v (q + 16 * k) (by omega) (by omega) (by omega) st3.h1
      (by rw [c5, b5, h5]) (by rw [c6, b6, h6])
      (fun b h1 h2 => W3.safe_readable (by omega) (W3.safe s8) b h1 h2)
      (fun b h1 h2 => W3.H.st b (by omega) (by omega))
    have st4 := st3.scratch Fr d1 (fun b h0 h1 => dfr b h0 (by omega)) drd dwr
    rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr hD st4 ((items.drop (12 * k + 4)).take 8) 8 742
        18357 (by simp [hi]; omega) (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_370 bs_18357
        (by simp [hlenk]; omega) (by rw [dt, W3.readN_safe s8]; exact ar8) with
      ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))
    have st5' := st5.cast (show pre0 ++ items.take (12 * k) ++ (items.drop (12 * k)).take 4 ++
      (items.drop (12 * k + 4)).take 8 = pre0 ++ items.take (12 * (k + 1)) by
        rw [take12_succ]; simp [List.append_assoc])
    have hz5 : μ5.readN (F - 56 + 8) 8 = Num.encodeLE 8 (q + 16 * n) := by
      rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hz
    have h5' : ω5[5] = UInt64.ofNat (q + 16 * k) := by rw [e5, d5, c5, b5, h5]
    obtain ⟨cap5, ptr5, s5, W5⟩ := st5'.buf
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω6, run6, f1⟩ := seg_18357_last (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 (F - 56)
        (q + 16 * k) (by omega) (by omega) st5'.h1 h5' (by rw [show q + 16 * k + 16 = q + 16 * n by omega]; exact hz5)
        (fun b h1 h2 => Memory.readable_of_writable (W5.H.st b (by omega) (by omega)))
      have hkn : 12 * (k + 1) = items.length := by omega
      exact Or.inl ⟨ω6, μ5, (run2.trans (run3.trans (run4.trans (run5.trans run6)))).mono
        (by unfold stepGas growGas; omega),
        StDH.cast ⟨⟨f1.trans st5'.h1, st5'.w0, st5'.w5, st5'.w6, st5'.buf⟩, st5'.sv⟩
          (by rw [hkn, List.take_length])⟩
    · obtain ⟨ω6, run6, f1, f5, f6⟩ := seg_18357_more (p := p) (P := P) (R := refineContractK K env) x ω5 μ5
        (F - 56) (q + 16 * k) (q + 16 * n) (by omega) (by omega) (by omega) (by omega) st5'.h1 h5' hz5
        (fun b h1 h2 => Memory.readable_of_writable (W5.H.st b (by omega) (by omega)))
      rcases ih (k + 1) ω6 μ5 (by omega) hi0 ⟨⟨f1.trans st5'.h1, st5'.w0, st5'.w5, st5'.w6, st5'.buf⟩, st5'.sv⟩
          (by rw [f5]; congr 1) (by rw [f6, e6, d6, c6, b6, h6]) hz5 with
        ⟨ω7, μ7, run7, st7⟩ | hx
      · exact Or.inl ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono
          (by unfold stepGas growGas; omega), st7⟩
      · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans (run4.trans (run5.trans run6)))) hx).mono
          (by unfold stepGas growGas; omega))

end

/-- **`Bless` (index 11), with growth** (`Enc.bless` as `EncOkMH`): `BlessRepAt q m a d r n items`
    encodes to 11 :: m ++ a ++ d ++ r ++ ℰ(n) ++ items, the heap octets the elements' array (q, 16 n)
    when n > 0. -/
theorem blessH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q : Nat) (m a d r : List UInt8) (n : Nat) (items : List UInt8)
    (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4) (hr4 : r.length = 4)
    (hi : items.length = 12 * n) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 192 (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items))
      (BlessRepAt q m a d r n items) (SrcAtP q (16 * n)) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, rm, ra, rd, rr, r8, r16, r24, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 11) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have cm : μ.readN (S + 32) 4 = m := by rw [← slot_take μ S 32 4 (by decide)]; exact rm
  have ca : μ.readN (S + 36) 4 = a := by rw [← slot_take μ S 36 4 (by decide)]; exact ra
  have cd : μ.readN (S + 40) 4 = d := by rw [← slot_take μ S 40 4 (by decide)]; exact rd
  have cr : μ.readN (S + 44) 4 = r := by rw [← slot_take μ S 44 4 (by decide)]; exact rr
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hE := encodeNat_pos n
  have hN : (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items) : List UInt8).length =
      17 + (Blob.encodeNat n).length + 12 * n := by
    simp [hm4, ha4, hd4, hr4, hi] <;> omega
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startDH (p := p) (P := P) K x ω μ L (by decide) 11
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 11 = 18163 from rfl] at run1
  rcases pieceTagDH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18163 11 728 18186
      (Or.inl ⟨rfl, rfl, rfl⟩) jte_363 bs_18186 a10 a11 (by omega) (by simp; omega) with
    ⟨ω2, μ2, run2, st2, b5, b6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run1 hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceU32DH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S L.slot hS' 18186 730 32 18207
      (Or.inl ⟨rfl, rfl, rfl⟩) jte_364 bs_18207 b5 b6 (by simp; omega) with
    ⟨ω3, μ3, run3, st3, c5, c6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceU32DH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S L.slot hS' 18207 732 36 18228
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) jte_365 bs_18228 c5 c6 (by simp [Memory.readN]; omega) with
    ⟨ω4, μ4, run4, st4, d5, d6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceU32DH (p := p) (P := P) K hK1 hK x ω4 μ4 Fr (by decide) st4 S L.slot hS' 18228 734 40 18249
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) jte_366 bs_18249 d5 d6 (by simp [Memory.readN]; omega) with
    ⟨ω5, μ5, run5, st5, e5, e6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceU32DH (p := p) (P := P) K hK1 hK x ω5 μ5 Fr (by decide) st5 S L.slot hS' 18249 736 44 18270
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) jte_367 bs_18270 e5 e6 (by simp [Memory.readN]; omega) with
    ⟨ω6, μ6, run6, st6, f5, f6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans run5)))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [cm, ca, cd, cr] at st6
  have hl6 : ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r : List UInt8).length = 17 := by
    simp [hm4, ha4, hd4, hr4]
  -- the length prefix
  obtain ⟨cap6, ptr6, s6, W6⟩ := st6.buf
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, g7, g8, gn, gfr, grd, gwr⟩ := seg_18270 (p := p) (P := P)
    (R := refineContractK K env) x ω6 μ6 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st6.h1 f5
    (by rw [st6.slot L.slot (by decide)]; exact c16)
    (by rw [st6.slot L.slot (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st6.sv)
    (fun a h1 h2 => W6.safe_readable (by omega) (W6.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W6.H.st a (by omega) (by omega))
  have st7 := st6.scratch Fr g1 (fun a h0 h1 => gfr a h0 (by omega)) grd gwr
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω7 μ7 Fr (by decide) st7 n 738 18298 g0
      (by rw [g7]; congr 1; omega) g8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact gn)
      ⟨by decide, by decide, by decide⟩ jte_368 bs_18298 (by rw [hl6]; omega) with
    ⟨ω8, μ8, run8, st8, k5, k6, kF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      run7)))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  have hpre0 : ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r ++ Blob.encodeNat n : List UInt8).length =
      17 + (Blob.encodeNat n).length := by simp [hm4, ha4, hd4, hr4] <;> omega
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no elements
    subst hn0
    have hi0 : items = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hi0
    obtain ⟨ω9, run9, rfl⟩ := seg_18298_zero (p := p) (P := P) (R := refineContractK K env) x ω8 μ8
      (by rw [k6, g6])
    exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
        run9))))))))
      (st8.toStH.cast (by simp)))
  · have hsq := hsrc q (16 * n) ⟨by omega, rfl, rfl⟩
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds L.H Fr hsq
    obtain ⟨cap8, ptr8, s8, W8⟩ := st8.buf
    obtain ⟨ω9, μ9, run9, h91, h95, h96, h9z, h9fr, h9rd, h9wr⟩ := seg_18298_pos (p := p) (P := P)
      (R := refineContractK K env) x ω8 μ8 (F - 56) v q n (by omega) (by omega) (by omega) hn0 st8.h1
      (by rw [k5, g5]) (by rw [k6, g6])
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st8.sv)
      (fun a h1 h2 => W8.H.st a (by omega) (by omega))
    have st9 := st8.scratch Fr h91 (fun a h0 h1 => h9fr a h0 (by omega)) h9rd h9wr
    have henc : (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items) : List UInt8) =
        ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r ++ Blob.encodeNat n) ++ items := by
      simp only [List.nil_append, List.cons_append, List.append_assoc] <;> rfl
    rcases bless_loopH (p := p) (P := P) K hK1 hK x Fr (by decide) q n
        ([] ++ [UInt8.ofNat 11] ++ m ++ a ++ d ++ r ++ Blob.encodeNat n) items hi hsq rarr (by rw [hpre0]; omega)
        n 0 ω9 μ9 (by omega) hn0 (st9.cast (by simp)) (by rw [h95]; congr 1) h96 h9z with
      ⟨ω10, μ10, run10, st10⟩ | hx
    · exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans
          (run9.trans run10)))))))))
        (st10.toStH.cast henc.symm))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
        (run7.trans (run8.trans run9)))))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))

/-- `blessH` at the depth 232. -/
theorem blessH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q : Nat) (m a d r : List UInt8) (n : Nat) (items : List UInt8)
    (hm4 : m.length = 4) (ha4 : a.length = 4) (hd4 : d.length = 4) (hr4 : r.length = 4)
    (hi : items.length = 12 * n) (hn : n < 4294967296) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 232 (11 :: (m ++ a ++ d ++ r ++ Blob.encodeNat n ++ items))
      (BlessRepAt q m a d r n items) (SrcAtP q (16 * n)) :=
  (blessH env K pb hK1 hK q m a d r n items hm4 ha4 hd4 hr4 hi hn hq64).mono (by decide)

end Services.Bootstrap.Encode.GrowH
