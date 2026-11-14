import Services.Bootstrap.Encode.ArmsHVecImported
import Services.Bootstrap.Encode.VariantsVec2

/-!
# `DeleteItems` (5) with growth (`EncOkMH`)

`Enc.delete_items` re-proved over `GrowH.StDH`, as `ArmsHVecImported` (the same code at other
addresses): `delete_items_loopH` (19193 … 19250) and `delete_itemsH`. The heap octets are
`VecVecSrcH q qs es`.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.VecVecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}

/-- **`DeleteItems`'s element loop, with growth** (`Enc.delete_items_loop`): from the loop's head for element k
    (ω₅ = q + 24 k + 16, ω₉ = 24 i, i = m − k > 0) in `StDH (preDI k)`, the elements k … m − 1 encoded, at
    20118 in `StDH (preDI m)`; or a failed `realloc`. -/
theorem delete_items_loopH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (Fr : FrH S0 S1 D F v) (hD : 192 ≤ D) (q : Nat) (qs : Nat → Nat) (es : List (List UInt8))
    (harr : SafeR s0 ptr0 F S1 v q (24 * es.length))
    (hel : ∀ j (hj : j < es.length), 0 < es[j].length → SafeR s0 ptr0 F S1 v (qs j) es[j].length)
    (arr : ∀ j (hj : j < es.length), μ0.readN (q + 24 * j + 8) 8 = Num.encodeLE 8 (qs j) ∧
      μ0.readN (q + 24 * j + 16) 8 = Num.encodeLE 8 es[j].length ∧ μ0.readN (qs j) es[j].length = es[j])
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616)
    (hlen : 2 * (len + (5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length) ≤
      capBound) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = es.length → 0 < i →
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (preDI es k) ω μ1 →
      ω[5] = UInt64.ofNat (q + 24 * k + 16) → ω[9] = UInt64.ofNat (24 * i) →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 19193 ω μ1 x 20118 ω' μ' x
          ((2000 + growGas) * ((5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length -
            (preDI es k).length)) ∧
        StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (preDI es es.length) ω' μ') ∨
      ExhaustsW env K pb p P 19193 ω μ1 x
        ((2000 + growGas) * ((5 :: (Blob.encodeNat es.length ++ (encs es).flatten) : List UInt8).length -
          (preDI es k).length)) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0; have := Fr.hF8
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h9
    have hk : k < es.length := by omega
    have hpk := preDI_len es k
    have sA : SafeR s0 ptr0 F S1 v (q + 24 * k + 8) 16 := harr.sub (by omega) (by omega)
    obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds W1.H Fr (W1.safe harr)
    have bqa := SafeR.apart W1.H (W1.safe harr)
    obtain ⟨ar8, ar16, arb⟩ := arr k hk
    have hn := hlens k hk
    have hqk := hqs k hk
    have hlenk := preDI_len es (k + 1)
    rw [preDI_succ es k hk] at hlenk
    simp only [List.length_append] at hlenk
    have hE := encodeNat_pos es[k].length
    -- the element's length prefix
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, be, br, bn, bfr, brd, bwr⟩ := seg_19193 (p := p) (P := P)
      (R := refineContractK K env) x ω μ1 (F - 56) v (q + 24 * k + 16) (qs k) es[k].length (24 * (i + 1))
      (by omega) (by omega) ⟨by omega, by omega⟩ hqk hn (by omega) st.h1 h5 h9
      (by rw [W1.readN_safe (sA.sub (q' := q + 24 * k + 16) (m' := 8) (by omega) (by omega))]; exact ar16)
      (by rw [show q + 24 * k + 16 - 8 = q + 24 * k + 8 by omega,
            W1.readN_safe (sA.sub (q' := q + 24 * k + 8) (m' := 8) (by omega) (by omega))]
          exact ar8)
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun a h1 h2 => W1.safe_readable (by omega) (W1.safe sA) a (by omega) (by omega)) (by omega)
      (fun a h1 h2 => W1.H.st a (by omega) (by omega))
    have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega) (by omega)) brd bwr
    rcases prefixDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 es[k].length 824 19227 b0
        (by rw [b7]; congr 1; omega) b8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact bn)
        ⟨by decide, by decide, by decide⟩ jte_411 bs_19227 (by omega) with
      ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold prefixGas growGas; omega))
    -- the element's octets
    obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := seg_19227 (p := p) (P := P) (R := refineContractK K env)
      x ω3 μ3 (F - 56) v (qs k) es[k].length (by omega) (by omega) hqk (by omega) st3.h1 (by rw [c6, b6])
      (by rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact be)
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
      (fun a h1 h2 => Memory.readable_of_writable (W3.H.st a (by omega) (by omega)))
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω4 μ3 Fr (by omega) ⟨⟨d1.trans st3.h1, st3.w0, st3.w5, st3.w6, st3.buf⟩,
        st3.sv⟩ (qs k) es[k].length 826 19241 rfl arb d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_412
        bs_19241 (by simp only [List.length_append]; omega)
        (by rcases Nat.eq_zero_or_pos es[k].length with h | h
            · exact Or.inl h
            · exact Or.inr (hel k hk h)) with
      ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono
        (by unfold prefixGas stepGas growGas; omega))
    have st5' := st5.cast (preDI_succ es k hk).symm
    have r8 : μ5.readN (F - 56 + 8) 8 = Num.encodeLE 8 (24 * (i + 1)) := by
      rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact br
    have h5' : ω5[5] = UInt64.ofNat (q + 24 * k + 16) := by rw [e5, d5, c5, b5]
    obtain ⟨cap5, ptr5, s5, W5⟩ := st5'.buf
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · -- the last element
      obtain ⟨ω6, run6, f1⟩ := seg_19241_last (p := p) (P := P) (R := refineContractK K env) x ω5 μ5 (F - 56)
        (by omega) st5'.h1 r8 (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
      have hkm : k + 1 = es.length := by omega
      refine Or.inl ⟨ω6, μ5, (run2.trans (run3.trans (run4.trans (run5.trans run6)))).mono ?_,
        StDH.cast ⟨⟨f1.trans st5'.h1, st5'.w0, st5'.w5, st5'.w6, st5'.buf⟩, st5'.sv⟩ (by rw [hkm])⟩
      unfold prefixGas stepGas growGas; omega
    · obtain ⟨ω6, run6, f1, f5, f6, f9⟩ := seg_19241_more (p := p) (P := P) (R := refineContractK K env) x ω5 μ5
        (F - 56) (q + 24 * k + 16) (24 * (i + 1)) (by omega) (by omega) ⟨by omega, by omega⟩ st5'.h1 h5' r8
        (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
      have hp1 := preDI_len es (k + 1)
      rw [preDI_succ es k hk] at hp1
      simp only [List.length_append] at hp1
      rcases ih (k + 1) ω6 μ5 (by omega) hi ⟨⟨f1.trans st5'.h1, st5'.w0, st5'.w5, st5'.w6, st5'.buf⟩, st5'.sv⟩
          (by rw [f5]; congr 1 <;> omega) (by rw [f9]; congr 1 <;> omega) with
        ⟨ω7, μ7, run7, st7⟩ | hx
      · refine Or.inl ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono ?_, st7⟩
        rw [preDI_succ es k hk]
        simp only [List.length_append]
        unfold prefixGas stepGas growGas; omega
      · refine Or.inr ((ExhaustsW.pre (run2.trans (run3.trans (run4.trans (run5.trans run6)))) hx).mono ?_)
        rw [preDI_succ es k hk]
        simp only [List.length_append]
        unfold prefixGas stepGas growGas; omega

end

/-- **`DeleteItems { items }` (index 5), with growth** (`Enc.delete_items` as `EncOkMH`): `DeleteItemsRepAt q qs es`
    encodes to 5 :: ℰ(m) ++ (ℰ(n₀) ++ e₀) ++ …, the heap octets `VecVecSrcH q qs es`. -/
theorem delete_itemsH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (hm : es.length < 4294967296)
    (hq64 : q < 18446744073709551616)
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616) :
    EncOkMH env K pb p P 192 (5 :: (Blob.encodeNat es.length ++ (encs es).flatten)) (DeleteItemsRepAt q qs es)
      (VecVecSrcH q qs es) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 5) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 es.length := by
    rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hp0 := preDI_len es 0
  have hl0 : (preDI es 0).length = 1 + (Blob.encodeNat es.length).length := by simp [preDI, encs] <;> omega
  have hNa := preDI_len es es.length
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startDH (p := p) (P := P) K x ω μ L (by decide) 5
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 5 = 19117 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19117 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega)
    (by omega) st1.h1 a10 a11 (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 5] 1 820 19140 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_409 bs_19140 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; omega))
  -- the count's length prefix
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dq, dn, dfr, drd, dwr⟩ := seg_19140 (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S q es.length (by omega) (by omega) (by omega) hq64 hm
    st3.h1 (by rw [c5, b5]) (by rw [c6, b6])
    (by rw [st3.slot L.slot (by decide)]; exact c16)
    (by rw [st3.slot L.slot (by decide)]; exact c24)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega) (by omega)) drd dwr
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 es.length 822 19173 d0
      (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
      ⟨by decide, by decide, by decide⟩ jte_410 bs_19173 (by simp; omega) with
    ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas prefixGas growGas; omega))
  have st5' := st5.cast (show [] ++ [UInt8.ofNat 5] ++ Blob.encodeNat es.length = preDI es 0 by simp [preDI, encs])
  have h5 : ω5[5] = UInt64.ofNat es.length := by rw [e5, d5]
  rcases Nat.eq_zero_or_pos es.length with hm0 | hm0
  · -- no elements
    obtain ⟨ω6, run6, rfl⟩ := seg_19173_zero (p := p) (P := P) (R := refineContractK K env) x ω5 μ5
      (by rw [h5, hm0])
    exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; omega)
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
      (st5'.toStH.cast (by rw [show (0 : Nat) = es.length from hm0.symm, preDI_all])))
  · have harr := hsrc q (24 * es.length) (Or.inl ⟨by omega, rfl, rfl⟩)
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds L.H Fr harr
    obtain ⟨cap5, ptr5, s5, W5⟩ := st5'.buf
    obtain ⟨ω6, run6, f1, f5, f6, f9⟩ := seg_19173_pos (p := p) (P := P) (R := refineContractK K env) x ω5 μ5
      (F - 56) q es.length (by omega) (by omega) ⟨hm0, hm⟩ st5'.h1 h5
      (by rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact dq)
      (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
    rcases delete_items_loopH (p := p) (P := P) K hK1 hK x Fr (by decide) q qs es harr
        (fun j hj hp => hsrc (qs j) es[j].length (Or.inr ⟨j, hj, hp, rfl, rfl⟩))
        (fun j hj => ⟨(rarr j hj).2.1, (rarr j hj).2.2.1, (rarr j hj).2.2.2⟩) hlens hqs hlen es.length 0 ω6 μ5
        (by omega) hm0 ⟨⟨f1.trans st5'.h1, st5'.w0, st5'.w5, st5'.w6, st5'.buf⟩, st5'.sv⟩ (by rw [f5])
        (by rw [f9]) with
      ⟨ω7, μ7, run7, st7⟩ | hx
    · exact Or.inl (closeH L 20118 _ (by decide) (by unfold encGas stepGas prefixGas growGas; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
        (st7.toStH.cast (preDI_all es)))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
        (by unfold encGas stepGas prefixGas growGas; omega))

/-- `delete_itemsH` at the depth 232. -/
theorem delete_itemsH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q : Nat) (qs : Nat → Nat) (es : List (List UInt8)) (hm : es.length < 4294967296)
    (hq64 : q < 18446744073709551616)
    (hlens : ∀ j (hj : j < es.length), es[j].length < 4294967296)
    (hqs : ∀ j (hj : j < es.length), qs j < 18446744073709551616) :
    EncOkMH env K pb p P 232 (5 :: (Blob.encodeNat es.length ++ (encs es).flatten)) (DeleteItemsRepAt q qs es)
      (VecVecSrcH q qs es) :=
  (delete_itemsH env K pb hK1 hK q qs es hm hq64 hlens hqs).mono (by decide)

end Services.Bootstrap.Encode.GrowH
