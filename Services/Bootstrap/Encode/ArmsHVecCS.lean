import Services.Bootstrap.Encode.ArmsHVecCore
import Services.Bootstrap.Encode.VariantsVec2CS

/-!
# `CreateService` (0) with growth (`EncOkMH`)

`Enc.create_service_none`, `create_service_some` and `create_service_empty_232` re-proved over
`GrowH.StDH`: `start0H` (`Enc.start0`), `csWordDH` / `csDirectDH` (`Enc.csWordD` / `csDirectD`),
`cs_headH` / `cs_tailH` (`Enc.cs_head` / `cs_tail`), and the arms. The `None` and `Some([])` cases read no
heap octets; the `Some` case reads the stretch (q, n) when n > 0 (`SrcAtP`).
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD Services.Bootstrap.Decode.CreateServiceElem

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **From 30145 to `CreateService`'s arm (17905)**, in `StDH []` (`Enc.start0`). -/
theorem start0H {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (K : Nat) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t' : Nat} {s : State}
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t' s μ) (hD : 136 ≤ D)
    (W : Nat) (hW : W < 9223372036854775808 ∨ W = 18446744073709551615)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hW8 : μ.readN S 8 = Num.encodeLE 8 W)
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p (refineContractK K env) 30145 ω μ x 17905 ω1 μ1 x 24 ∧
      StDH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ [] ω1 μ1 ∧
      ω1[5] = UInt64.ofNat 18446744073709551615 ∧ ω1[6] = UInt64.ofNat W ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨ω1, μ1, run1, st1, a5, a6, a10, a11⟩ := start0 (p := p) (P := P) (R := refineContractK K env) x ω μ
    L.toLayD0 hD W hW h0 h1 h7 h8 hW8 tab hrt
  have hk := keep_vl (Q := fun a => a < 4294967296 ∧ (a < F - D ∨ F ≤ a)) (by simpa using st1.vl) L.vl
    (fun a ha h => st1.keep a ha.1 ha.2 (by simp; omega) h)
  exact ⟨ω1, μ1, run1, ⟨⟨st1.h1, st1.s0, st1.s5, st1.s6, ⟨cap, ptr, s,
    L.init.frame (F - D) F (by omega) (Nat.le_refl _) (Or.inl n5) (fun a h0 h1 => hk a ⟨h0, h1⟩) st1.rd st1.wr⟩⟩,
    st1.sv⟩, a5, a6, a10, a11⟩

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}

/-- **A `u64` piece of `CreateService`, with growth** (`Enc.csWordD`). -/
theorem csWordDH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {pre : List UInt8} (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S : Nat) (hS : SafeR s0 ptr0 F S1 v S 232)
    (hS' : S + 256 < 4294967296) (e r off e' : Nat) (hc : CSWord e r off)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (hS0 : μ.readN (F - 56) 8 = Num.encodeLE 8 S) (hlen : 2 * (len + pre.length + 8) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas 8 + 12) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ0.readN (S + off) 8) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ μ'.readN (F - 56) 8 = Num.encodeLE 8 S) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas 8 + 12) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold CSWord at hc; omega
  have hoff : off + 8 ≤ 232 := by unfold CSWord at hc; omega
  obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_csWord (p := p) (P := P)
    (R := refineContractK K env) x ω μ e r off (F - 56) v S hc (by omega) (by omega) (by omega) st.h1 hS0
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => W1.safe_readable (by omega) (W1.safe hS) a (by omega) (by omega))
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rw [st.slot hS hoff] at bt
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 (μ0.readN (S + off) 8) 8 r e'
      (by simp [Memory.readN]) (by decide) b0 b7 b8 b9 hr hje hbe hlen bt with
    ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
  · refine Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6, ?_⟩
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact hS0
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

/-- **A direct piece of `CreateService`, with growth** (`Enc.csDirectD`: the hash or the array). -/
theorem csDirectDH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {pre : List UInt8} (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S : Nat) (hS : SafeR s0 ptr0 F S1 v S 232)
    (hS' : S + 256 < 4294967296) (e r off n e' : Nat) (hc : CSDirect e r off n)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (hS0 : μ.readN (F - 56) 8 = Num.encodeLE 8 S) (hlen : 2 * (len + pre.length + n) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas n + 6) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ0.readN (S + off) n) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ μ'.readN (F - 56) 8 = Num.encodeLE 8 S) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas n + 6) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold CSDirect at hc; omega
  have hoff : off + n ≤ 232 := by unfold CSDirect at hc; omega
  obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := seg_csDirect (p := p) (P := P) (R := refineContractK K env)
    x ω μ e r off n (F - 56) v S hc (by omega) (by omega) (by omega) st.h1 hS0
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => Memory.readable_of_writable (W1.H.st a (by omega) (by omega)))
  rcases ext_stepDH (p := p) (P := P) env K hK1 hK x ω2 μ Fr hD
      ⟨⟨b1.trans st.h1, st.w0, st.w5, st.w6, st.buf⟩, st.sv⟩ (S + off) n r e' b0 b7 b8 b9 hr hje hbe hlen
      (hS.sub (q' := S + off) (m' := n) (by omega) (by omega)).ext with
    ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
  · rw [st.slot hS hoff] at st3
    refine Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6, ?_⟩
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact hS0
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

end

/-- **`CreateService`'s head, with growth** (`Enc.cs_head`): from the dispatch with first word W, the
    tag 0, h, u₁ … u₄ and the array appended, at 18058 with ω₅ = 2^64 − 1, ω₆ = W and S at F − 56. -/
theorem cs_headH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t : Nat} {s : State}
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t s μ) (hD : 136 ≤ D)
    (W : Nat) (hW : W < 9223372036854775808 ∨ W = 18446744073709551615)
    (h u1 u2 u3 u4 arr : List UInt8) (hlen : 2 * (len + 193) ≤ capBound)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hW8 : μ.readN S 8 = Num.encodeLE 8 W)
    (c32 : μ.readN (S + 32) 32 = h) (c64 : μ.readN (S + 64) 8 = u1) (c72 : μ.readN (S + 72) 8 = u2)
    (c80 : μ.readN (S + 80) 8 = u3) (c88 : μ.readN (S + 88) 8 = u4) (c96 : μ.readN (S + 96) 128 = arr)
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 30145 ω μ x 18058 ω' μ' x (4000 + 7 * growGas) ∧
      StDH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ
        (UInt8.ofNat 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr)) ω' μ' ∧
      ω'[5] = UInt64.ofNat 18446744073709551615 ∧ ω'[6] = UInt64.ofNat W ∧
      μ'.readN (F - 56) 8 = Num.encodeLE 8 S) ∨
    ExhaustsW env K pb p P 30145 ω μ x (4000 + 7 * growGas) := by
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have lh : h.length = 32 := by rw [← c32]; simp [Memory.readN]
  have l1 : u1.length = 8 := by rw [← c64]; simp [Memory.readN]
  have l2 : u2.length = 8 := by rw [← c72]; simp [Memory.readN]
  have l3 : u3.length = 8 := by rw [← c80]; simp [Memory.readN]
  have l4 : u4.length = 8 := by rw [← c88]; simp [Memory.readN]
  obtain ⟨ω1, μ1, run1, st1, a5, a6, a10, a11⟩ := start0H (p := p) (P := P) K x ω μ L hD W hW h0 h1 h7 h8
    hW8 tab hrt
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bS, bfr, brd, bwr⟩ := seg_17905 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega) (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 [UInt8.ofNat 0] 1 704 17925 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_351 bs_17925 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold stepGas growGas; omega))
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega))]; exact bS
  rcases csDirectDH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr hD st3 S L.slot hS' 17925 706 32 32 17943
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) jte_352 bs_17943 m3 (by simp; omega) with
    ⟨ω4, μ4, run4, st4, d5, d6, m4⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono (by unfold stepGas growGas; omega))
  rcases csWordDH (p := p) (P := P) K hK1 hK x ω4 μ4 Fr hD st4 S L.slot hS' 17943 708 64 17967
      (Or.inl ⟨rfl, rfl, rfl⟩) jte_353 bs_17967 m4 (by simp [c32, lh]; omega) with
    ⟨ω5, μ5, run5, st5, e5, e6, m5⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold stepGas growGas; omega))
  rcases csWordDH (p := p) (P := P) K hK1 hK x ω5 μ5 Fr hD st5 S L.slot hS' 17967 710 72 17991
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) jte_354 bs_17991 m5 (by simp [c32, c64, lh, l1]; omega) with
    ⟨ω6, μ6, run6, st6, f5, f6, m6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans run5)))) hx).mono
      (by unfold stepGas growGas; omega))
  rcases csWordDH (p := p) (P := P) K hK1 hK x ω6 μ6 Fr hD st6 S L.slot hS' 17991 712 80 18015
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) jte_355 bs_18015 m6
      (by simp [c32, c64, c72, lh, l1, l2]; omega) with
    ⟨ω7, μ7, run7, st7, g5, g6, m7⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
      (by unfold stepGas growGas; omega))
  rcases csWordDH (p := p) (P := P) K hK1 hK x ω7 μ7 Fr hD st7 S L.slot hS' 18015 714 88 18039
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) jte_356 bs_18039 m7
      (by simp [c32, c64, c72, c80, lh, l1, l2, l3]; omega) with
    ⟨ω8, μ8, run8, st8, i5, i6, m8⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      run7)))))) hx).mono (by unfold stepGas growGas; omega))
  rcases csDirectDH (p := p) (P := P) K hK1 hK x ω8 μ8 Fr hD st8 S L.slot hS' 18039 716 96 128 18058
      (Or.inr ⟨rfl, rfl, rfl, rfl⟩) jte_357 bs_18058 m8
      (by simp [c32, c64, c72, c80, c88, lh, l1, l2, l3, l4]; omega) with
    ⟨ω9, μ9, run9, st9, j5, j6, m9⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      (run7.trans run8))))))) hx).mono (by unfold stepGas growGas; omega))
  refine Or.inl ⟨ω9, μ9, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
    (run8.trans run9)))))))).mono (by unfold stepGas growGas; omega), st9.cast ?_,
    by rw [j5, i5, g5, f5, e5, d5, c5, b5, a5], by rw [j6, i6, g6, f6, e6, d6, c6, b6, a6], m9⟩
  rw [c32, c64, c72, c80, c88, c96]; simp

/-- **`CreateService`'s tail, with growth** (`Enc.cs_tail`): from 20239 with the writer in ω₅ and S at
    F − 56, u₅ and the `Option<u32>` ou appended, at the end 20329. -/
theorem cs_tailH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ1 : Memory)
    {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}
    {pre : List UInt8} (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ1) (S : Nat) (hS : SafeR s0 ptr0 F S1 v S 232)
    (hS' : S + 256 < 4294967296) (u5 ou : List UInt8) (hou : OptU32Enc ou)
    (hlen : 2 * (len + pre.length + 8 + ou.length) ≤ capBound) (h5 : ω[5] = UInt64.ofNat v)
    (hS0 : μ1.readN (F - 56) 8 = Num.encodeLE 8 S) (c224 : μ0.readN (S + 224) 8 = u5)
    (c24 : μ0.readN (S + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat)
    (c28 : ou.headD 0 = 1 → μ0.readN (S + 28) 4 = ou.tail) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 20239 ω μ1 x 20329 ω' μ' x (1500 + 3 * growGas) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ u5 ++ ou) ω' μ') ∨
    ExhaustsW env K pb p P 20239 ω μ1 x (1500 + 3 * growGas) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have l5 : u5.length = 8 := by rw [← c224]; simp [Memory.readN]
  obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_20239 (p := p) (P := P)
    (R := refineContractK K env) x ω μ1 (F - 56) v S (by omega) (by omega) (by omega) st.h1 h5 hS0
    (fun a h1 h2 => W1.safe_readable (by omega) (W1.safe hS) a (by omega) (by omega))
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rw [st.slot hS (by decide), c224] at bt
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 u5 8 912 20263 l5 (by decide) b0 b7 b8 b9
      ⟨by decide, by decide, by decide⟩ jte_455 bs_20263 (by omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold stepGas growGas; omega))
  have k24 : μ3.readN (S + 24) 4 = μ0.readN (S + 24) 4 := st3.slot hS (by decide)
  have k28 : μ3.readN (S + 28) 4 = μ0.readN (S + 28) 4 := st3.slot hS (by decide)
  have h5' : ω3[5] = UInt64.ofNat v := by rw [c5, b5, h5]
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  rcases hou with rfl | ⟨u, hu, rfl⟩
  · have r24 : rdN μ3 (S + 24) 4 = 0 := by
      show Num.decodeLE _ = _; rw [k24, c24]; rfl
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_20263_none (p := p) (P := P)
      (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 h5'
      (by rw [c6, b6]) r24
      (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe hS) a (by omega) (by omega))
      (fun a h1 h2 => W3.H.st a (by omega) (by omega))
    have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
    rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr hD st4 [UInt8.ofNat 0] 1 916 20329 rfl (by decide)
        d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_457 bs_20329 (by simp at hlen ⊢; omega) dt with
      ⟨ω5, μ5, run5, st5, -, -, -⟩ | hx
    · exact Or.inl ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono (by unfold stepGas growGas; omega),
        st5.cast (by simp)⟩
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))
  · have r24 : rdN μ3 (S + 24) 4 = 1 := by
      show Num.decodeLE _ = _
      rw [k24, c24, show ((1 :: u : List UInt8).headD 0).toNat = 1 from rfl]; rfl
    have c28' := c28 rfl
    simp only [List.tail_cons] at c28'
    obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_20263_some (p := p) (P := P)
      (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1 h5'
      (by rw [c6, b6]) r24
      (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe hS) a (by omega) (by omega))
      (fun a h1 h2 => W3.H.st a (by omega) (by omega))
    have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
    rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr hD st4 [UInt8.ofNat 1] 1 914 20288 rfl (by decide)
        d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_456 bs_20288 (by simp [hu] at hlen ⊢; omega) dt with
      ⟨ω5, μ5, run5, st5, e5, e6, -⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))
    obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
    obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ft, ffr, frd, fwr⟩ := seg_20288 (p := p) (P := P)
      (R := refineContractK K env) x ω5 μ5 (F - 56) v S (by omega) (by omega) (by omega) st5.h1
      (by rw [e5, d5, h5']) (by rw [e6, d6, c6, b6])
      (fun a h1 h2 => W5.safe_readable (by omega) (W5.safe hS) a (by omega) (by omega))
      (fun a h1 h2 => W5.H.st a (by omega) (by omega))
    have st6 := st5.scratch Fr f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
    rw [st5.slot hS (by decide), c28'] at ft
    rcases scratchDH (p := p) (P := P) env K hK1 hK x ω6 μ6 Fr hD st6 u 4 916 20329 hu (by decide)
        f0 f7 f8 f9 ⟨by decide, by decide, by decide⟩ jte_457 bs_20329 (by simp [hu] at hlen ⊢; omega) ft with
      ⟨ω7, μ7, run7, st7, -, -, -⟩ | hx
    · exact Or.inl ⟨ω7, μ7, (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))).mono
        (by unfold stepGas growGas; omega), st7.cast (by simp)⟩
    · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans (run4.trans (run5.trans run6)))) hx).mono
        (by unfold stepGas growGas; omega))

/-- `create_service_noneH`'s gas, closed form. -/
theorem cs_none_gas (L : Nat) (hL : L ≤ 5) :
    4000 + 7 * growGas + (12 + (stepGas 1 + (1500 + 3 * growGas))) + 7 ≤
      2000 * (202 + L) + 4000 + growGas * (202 + L) := by
  unfold stepGas growGas; omega

/-- `create_service_someH`'s gas, closed form. -/
theorem cs_some_gas (n L : Nat) (hE : 1 ≤ (Blob.encodeNat n).length) (hL : L ≤ 5) :
    4000 + 7 * growGas + (12 + (stepGas 1 + (20 + (prefixGas n + (6 + (stepGas n +
        (1500 + 3 * growGas))))))) + 7 ≤
      2000 * (202 + (Blob.encodeNat n).length + n + L) + 4000 +
        growGas * (202 + (Blob.encodeNat n).length + n + L) := by
  unfold stepGas prefixGas growGas; omega

/-- **`CreateService` with `Option<Vec<u8>>` = `None` (index 0), with growth**
    (`Enc.create_service_none` as `EncOkMH`): no heap octets. -/
theorem create_service_noneH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMH env K pb p P 136 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceNoneRep h u1 u2 u3 u4 arr u5 ou bs) (fun _ _ => False) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t g0 g1 g7 g8 rep L hlen tab hrt _
  obtain ⟨r0, f24, f28, f32, f64, f72, f80, f88, f96, f224⟩ := rep
  have hW8 : μ.readN S 8 = Num.encodeLE 8 18446744073709551615 := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c24 : μ.readN (S + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat := by
    rw [← slot_take μ S 24 4 (by decide)]; exact f24
  have c28 : ou.headD 0 = 1 → μ.readN (S + 28) 4 = ou.tail := fun h1 => by
    rw [← slot_take μ S 28 4 (by decide)]; exact f28 h1
  have c32 : μ.readN (S + 32) 32 = h := by rw [← slot_take μ S 32 32 (by decide)]; exact f32
  have c64 : μ.readN (S + 64) 8 = u1 := by rw [← slot_take μ S 64 8 (by decide)]; exact f64
  have c72 : μ.readN (S + 72) 8 = u2 := by rw [← slot_take μ S 72 8 (by decide)]; exact f72
  have c80 : μ.readN (S + 80) 8 = u3 := by rw [← slot_take μ S 80 8 (by decide)]; exact f80
  have c88 : μ.readN (S + 88) 8 = u4 := by rw [← slot_take μ S 88 8 (by decide)]; exact f88
  have c96 : μ.readN (S + 96) 128 = arr := by rw [← slot_take μ S 96 128 (by decide)]; exact f96
  have c224 : μ.readN (S + 224) 8 = u5 := by rw [← slot_take μ S 224 8 (by decide)]; exact f224
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hol := hou.length
  have hN : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou) : List UInt8).length =
      202 + ou.length := by simp [hh, h1, h2, h3, h4, harr, h5]; omega
  rw [hN] at hlen
  rcases cs_headH (p := p) (P := P) K hK1 hK x ω μ L (by decide) 18446744073709551615 (Or.inr rfl)
      h u1 u2 u3 u4 arr (by omega) g0 g1 g7 g8 hW8 c32 c64 c72 c80 c88 c96 tab hrt with
    ⟨ω1, μ1, run1, st1, a5, a6, m1⟩ | hx
  rotate_left
  · exact Or.inr (hx.mono (by unfold encGas growGas; rw [hN]; omega))
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18058_none (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v (by omega) (by omega) st1.h1 a5 a6
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st1.sv)
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 0] 1 910 20239 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_454 bs_20239
      (by simp [hh, h1, h2, h3, h4, harr]; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, -, cF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact m1
  rcases cs_tailH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S L.slot hS' u5 ou hou
      (by simp [hh, h1, h2, h3, h4, harr]; omega) (by rw [c5, b5]) m3 c224 c24 c28 with
    ⟨ω4, μ4, run4, st4⟩ | hx
  · have run := run1.trans (run2.trans (run3.trans run4))
    have st := st4.toStH.cast (pre' := 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (by simp only [List.nil_append, List.cons_append, List.append_assoc] <;> rfl)
    have hk : 4000 + 7 * growGas + (12 + (stepGas 1 + (1500 + 3 * growGas))) + 7 ≤
        encGas (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou)) :=
      Nat.le_trans (cs_none_gas _ hol.2) (Nat.le_of_eq (by unfold encGas; rw [hN]))
    exact Or.inl (closeH L 20329 _ (by decide) hk run st)
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))

/-- `create_service_noneH` at the depth 232. -/
theorem create_service_noneH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMH env K pb p P 232 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceNoneRep h u1 u2 u3 u4 arr u5 ou bs) (fun _ _ => False) :=
  (create_service_noneH env K pb hK1 hK h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5 hou).mono (by decide)

/-- **`CreateService` with `Option<Vec<u8>>` = `Some(bytes)` (index 0), with growth**
    (`Enc.create_service_some` as `EncOkMH`): the heap octets the stretch (q, n) when n > 0. -/
theorem create_service_someH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMH env K pb p P 192 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (CSSomeRepAt q n bytes h u1 u2 u3 u4 arr u5 ou) (SrcAtP q n) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t g0 g1 g7 g8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r16, rb, f24, f28, f32, f64, f72, f80, f88, f96, f224⟩ := rep
  have hW8 : μ.readN S 8 = Num.encodeLE 8 n := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 8 8 (by decide)]; exact r8
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 4 = Num.encodeLE 4 (ou.headD 0).toNat := by
    rw [← slot_take μ S 24 4 (by decide)]; exact f24
  have c28 : ou.headD 0 = 1 → μ.readN (S + 28) 4 = ou.tail := fun h1 => by
    rw [← slot_take μ S 28 4 (by decide)]; exact f28 h1
  have c32 : μ.readN (S + 32) 32 = h := by rw [← slot_take μ S 32 32 (by decide)]; exact f32
  have c64 : μ.readN (S + 64) 8 = u1 := by rw [← slot_take μ S 64 8 (by decide)]; exact f64
  have c72 : μ.readN (S + 72) 8 = u2 := by rw [← slot_take μ S 72 8 (by decide)]; exact f72
  have c80 : μ.readN (S + 80) 8 = u3 := by rw [← slot_take μ S 80 8 (by decide)]; exact f80
  have c88 : μ.readN (S + 88) 8 = u4 := by rw [← slot_take μ S 88 8 (by decide)]; exact f88
  have c96 : μ.readN (S + 96) 128 = arr := by rw [← slot_take μ S 96 128 (by decide)]; exact f96
  have c224 : μ.readN (S + 224) 8 = u5 := by rw [← slot_take μ S 224 8 (by decide)]; exact f224
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hol := hou.length
  have hE := encodeNat_pos n
  have hN : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou) :
      List UInt8).length = 202 + (Blob.encodeNat n).length + n + ou.length := by
    simp [hh, h1, h2, h3, h4, harr, h5, hbn]; omega
  rw [hN] at hlen
  have hL0 : (UInt8.ofNat 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr)).length = 193 := by
    simp [hh, h1, h2, h3, h4, harr]
  rcases cs_headH (p := p) (P := P) K hK1 hK x ω μ L (by decide) n (Or.inl (by omega))
      h u1 u2 u3 u4 arr (by omega) g0 g1 g7 g8 hW8 c32 c64 c72 c80 c88 c96 tab hrt with
    ⟨ω1, μ1, run1, st1, a5, a6, m1⟩ | hx
  rotate_left
  · exact Or.inr (hx.mono (by unfold encGas growGas; rw [hN]; omega))
  -- the option's tag
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18058_some (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v n (by omega) (by omega) (by omega) st1.h1 a5 a6
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st1.sv)
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 1] 1 718 18084 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_358 bs_18084 (by rw [hL0]; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, -, cF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  have m3 : μ3.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => cF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact m1
  -- the length prefix
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, dq, dn, dfr, drd, dwr⟩ := seg_18084 (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st3.h1
    (by rw [c5, b5]) m3
    (by rw [st3.slot L.slot (by decide)]; exact c8)
    (by rw [st3.slot L.slot (by decide)]; exact c16)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega) (by omega)) drd dwr
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 n 720 18117 d0
      (by rw [d7]; congr 1; omega) d8 (by rw [show F - 32 = F - 56 + 24 by omega]; exact dn)
      ⟨by decide, by decide, by decide⟩ jte_359 bs_18117 (by simp; omega) with
    ⟨ω5, μ5, run5, st5, e5, e6, eF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  -- the octets
  obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
  obtain ⟨ω6, run6, g0', g1', g5', g6', g7', g8', g9'⟩ := seg_18117 (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 (F - 56) v q n (by omega) hq64 (by omega) (by omega) st5.h1
    (by rw [e5, d5, c5, b5]) (by rw [e6, d6])
    (by rw [Memory.readN_congr (fun j hj => eF _ (by omega) (by omega))]; exact dq)
    (fun a h1 h2 => Memory.readable_of_writable (W5.H.st a (by omega) (by omega)))
  rcases heapDH (p := p) (P := P) env K hK1 hK x ω6 μ5 Fr (by decide)
      ⟨⟨g1'.trans st5.h1, st5.w0, st5.w5, st5.w6, st5.buf⟩, st5.sv⟩ q n 910 20239 hbn rb g0' g7' g8' g9'
      ⟨by decide, by decide, by decide⟩ jte_454 bs_20239 (by simp; omega)
      (by rcases Nat.eq_zero_or_pos n with h | h
          · exact Or.inl h
          · exact Or.inr (hsrc q n ⟨h, rfl, rfl⟩)) with
    ⟨ω7, μ7, run7, st7, k5, -, kF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
      (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  have m7 : μ7.readN (F - 56) 8 = Num.encodeLE 8 S := by
    rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => eF _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega) (by omega))]; exact m3
  -- u₅ and the `Option<u32>`
  rcases cs_tailH (p := p) (P := P) K hK1 hK x ω7 μ7 Fr (by decide) st7 S L.slot hS' u5 ou hou
      (by simp [hbn]; omega) (by rw [k5, g5', e5, d5, c5, b5]) m7 c224 c24 c28 with
    ⟨ω8, μ8, run8, st8⟩ | hx
  · have hk : 4000 + 7 * growGas + (12 + (stepGas 1 + (20 + (prefixGas n + (6 + (stepGas n +
        (1500 + 3 * growGas))))))) + 7 ≤
        encGas (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou)) :=
      Nat.le_trans (cs_some_gas n _ hE hol.2) (Nat.le_of_eq (by unfold encGas; rw [hN]))
    exact Or.inl (closeH L 20329 _ (by decide) hk
      (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans run8)))))))
      (st8.toStH.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc] <;> rfl)))
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      run7)))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))

/-- `create_service_someH` at the depth 232. -/
theorem create_service_someH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMH env K pb p P 232 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat n ++ bytes)) ++ u5 ++ ou))
      (CSSomeRepAt q n bytes h u1 u2 u3 u4 arr u5 ou) (SrcAtP q n) :=
  (create_service_someH env K pb hK1 hK q n bytes hbn hn hq64 h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5
    hou).mono (by decide)

/-- **`CreateService` with `Option<Vec<u8>>` = `Some([])`, with growth** (`Enc.create_service_empty_232`
    as `EncOkMH`): `create_service_someH_232` with q = 1 and n = 0, no heap octets. -/
theorem create_service_emptyH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (h u1 u2 u3 u4 arr u5 ou : List UInt8) (hh : h.length = 32) (h1 : u1.length = 8) (h2 : u2.length = 8)
    (h3 : u3.length = 8) (h4 : u4.length = 8) (harr : arr.length = 128) (h5 : u5.length = 8)
    (hou : OptU32Enc ou) :
    EncOkMH env K pb p P 232 (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou))
      (fun bs _ => CreateServiceEmptyRep h u1 u2 u3 u4 arr u5 ou bs) (fun _ _ => False) := by
  have H := create_service_someH_232 (p := p) (P := P) env K pb hK1 hK 1 0 [] rfl (by decide) (by decide)
    h u1 u2 u3 u4 arr u5 ou hh h1 h2 h3 h4 harr h5 hou
  have he : (0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ (1 :: (Blob.encodeNat 0 ++ [])) ++ u5 ++ ou) :
      List UInt8) = 0 :: (h ++ u1 ++ u2 ++ u3 ++ u4 ++ arr ++ [1, 0] ++ u5 ++ ou) := rfl
  rw [he] at H
  intro x ω μ s S0 S1 F S v cap ptr len ret t g0 g1 g7 g8 rep L hlen tab hrt _
  obtain ⟨r0, r8, r16, rf⟩ := rep
  exact H x ω μ s S0 S1 F S v cap ptr len ret t g0 g1 g7 g8 ⟨r0, r8, r16, by simp [Memory.readN], rf⟩ L hlen tab
    hrt (fun q m hq => absurd hq.1 (Nat.lt_irrefl 0))

end Services.Bootstrap.Encode.GrowH
