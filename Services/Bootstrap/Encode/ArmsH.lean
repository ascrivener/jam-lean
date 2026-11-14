import Services.Bootstrap.Encode.EncMH
import Services.Bootstrap.Encode.Variants
import Services.Bootstrap.Encode.VariantsVec

/-!
# Worked arms with growth: `Transfer` and `LookedUp { Some }` as `EncOkMH`

Templates for converting an arm of `Instruction::encode_to` from `EncOk`/`EncOkMD` (no growth) to
`EncOkMH` (growth, refine's contract):

* `pieceTagH`, `pieceFieldH`, `pieceDirectH`: `Fixed.pieceTag`, `pieceField`, `pieceDirect` over `StH`,
  each the same code segment (`Fixed.tagSeg`, `fieldSeg`, `directSeg`) and then `ext_stepH`.
* `transferH`: `Variants.transfer` (a fixed-width arm, `EncOkMH … 136`).
* `looked_up_someH`: `VariantsVec.looked_up_some` (a `Vec` arm, with the length prefix and heap octets,
  `EncOkMH … 192`), its heap octets the stretch (q, n) (`SrcAt`).

The proofs follow the originals line by line: each append becomes an `rcases … with ⟨…⟩ | hx` whose
second case closes with `Or.inr ((ExhaustsW.pre run_so_far hx).mono _)`.
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
  {pre : List UInt8}

/-- **A tag piece, with growth** (`Fixed.pieceTag`). -/
theorem pieceTagH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S e tag r e' : Nat) (hc : TagCase e tag r)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S) (hS : S < 18446744073709551616)
    (hlen : 2 * (len + pre.length + 1) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas 1 + 10) ∧
      StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ [UInt8.ofNat tag]) ω' μ' ∧
      ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas 1 + 10) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold TagCase at hc; omega
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := tagSeg (p := p) (P := P)
    (R := refineContractK K env) x ω μ e tag r (F - 56) v S hc (by omega) (by omega) hS st.h1 h10 h11
    (fun a h1 h2 => W.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases ext_stepH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 (F - 32) 1 r e' b0 b7 (by rw [b8]; congr 1; omega) b9 hr hje
      hbe hlen (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  · rw [show F - 32 = F - 56 + 24 by omega, bt] at st3
    exact Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6⟩
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

/-- **A field piece, with growth** (`Fixed.pieceField`): the w octets at S + off of the value, as at entry. -/
theorem pieceFieldH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S e r e' off w : Nat)
    (hc : FieldCase e r off w) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) (hS' : S + 256 < 4294967296)
    (hslot : SafeR s0 ptr0 F S1 v S 232) (hlen : 2 * (len + pre.length + w) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas w + 12) ∧
      StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ0.readN (S + off) w) ω' μ' ∧
      ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas w + 12) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hle := hc.le
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold FieldCase at hc; omega
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := fieldSeg (p := p) (P := P)
    (R := refineContractK K env) x ω μ e r off w (F - 56) v S hc (by omega) (by omega) (by omega) st.h1 h5 h6
    (fun a h1 h2 => W.safe_readable (by omega) (W.safe hslot) a (by omega) (by omega))
    (fun a h1 h2 => W.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases ext_stepH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 (F - 32) w r e' b0 b7 (by rw [b8]; congr 1; omega) b9 hr hje
      hbe hlen (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  · rw [show F - 32 = F - 56 + 24 by omega, bt, st.slot hslot (by omega)] at st3
    exact Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans (b5.trans h5), c6.trans (b6.trans h6)⟩
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

/-- **A direct piece, with growth** (`Fixed.pieceDirect`): the n octets at S + off of the value, as at
    entry. -/
theorem pieceDirectH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S e r e' off n : Nat)
    (hc : DirectCase e r off n) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat S) (hS' : S + 256 < 4294967296)
    (hslot : SafeR s0 ptr0 F S1 v S 232) (hlen : 2 * (len + pre.length + n) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas n + 6) ∧
      StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ0.readN (S + off) n) ω' μ' ∧
      ω'[5] = UInt64.ofNat v ∧ ω'[6] = UInt64.ofNat S) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas n + 6) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1
  have hle := hc.le
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by unfold DirectCase at hc; omega
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := directSeg (p := p) (P := P) (R := refineContractK K env) x ω μ
    e r off n (F - 56) v S hc (by omega) (by omega) h5 h6
  have hsrc : n = 0 ∨ (F - 56 ≤ S + off ∧ S + off + n ≤ S1 ∧ (S + off + n ≤ v ∨ v + 24 ≤ S + off)) ∨
      HeapSrc s0 ptr0 (S + off) n := by
    rcases hslot with ⟨h1, h2, h3⟩ | ⟨e, he, heu, hne, h1, h2⟩
    · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨e, he, heu, hne, by omega, by omega⟩)
  rcases ext_stepH (p := p) (P := P) env K hK1 hK x ω2 μ Fr hD ⟨b1.trans st.h1, st.w0, st.w5, st.w6, st.buf⟩ (S + off) n r e' b0 b7
      b8 b9 hr hje hbe hlen hsrc with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  · rw [st.slot hslot (by omega)] at st3
    exact Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans (b5.trans h5), c6.trans (b6.trans h6)⟩
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

end

/-- **`Transfer` (tag 2), with growth** (`Variants.transfer` as `EncOkMH`). -/
theorem transferH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (d a g m : List UInt8) (hd : d.length = 4) (ha : a.length = 8) (hg : g.length = 8) (hm : m.length = 128) :
    EncOkMH env K pb p P 136 (2 :: (d ++ a ++ g ++ m))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775809 ∧ (bs.drop 8).take 128 = m ∧
        (bs.drop 136).take 8 = a ∧ (bs.drop 144).take 8 = g ∧ (bs.drop 152).take 4 = d) (fun _ _ => False) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (2 :: (d ++ a ++ g ++ m)).length = 149 := by simp [hd, ha, hg, hm]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 2) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 128 = m := by rw [← slot_take μ S 8 128 (by decide)]; exact rep.2.1
  have c1 : μ.readN (S + 136) 8 = a := by rw [← slot_take μ S 136 8 (by decide)]; exact rep.2.2.1
  have c2 : μ.readN (S + 144) 8 = g := by rw [← slot_take μ S 144 8 (by decide)]; exact rep.2.2.2.1
  have c3 : μ.readN (S + 152) 4 = d := by rw [← slot_take μ S 152 4 (by decide)]; exact rep.2.2.2.2
  have Fr := L.fr
  have hS64 : S < 18446744073709551616 := by have := L.hS'; omega
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 2 (by decide) h0 h1 h7 h8 hD tab hrt
  rw [show arm 2 = 18778 from rfl] at run1
  rcases pieceTagH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18778 2 780 18801 (by unfold TagCase; decide) jte_389
      bs_18801 a10 a11 hS64 (by simp; omega) with ⟨ω2, μ2, run2, st2, b25, b26⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run1 hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω2 μ2 Fr (by decide) st2 S 18801 782 18823 152 4 (by unfold FieldCase; decide)
      jte_390 bs_18823 b25 b26 L.hS' L.slot (by simp; omega) with ⟨ω3, μ3, run3, st3, b35, b36⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω3 μ3 Fr (by decide) st3 S 18823 784 18845 136 8 (by unfold FieldCase; decide)
      jte_391 bs_18845 b35 b36 L.hS' L.slot (by simp; omega) with ⟨ω4, μ4, run4, st4, b45, b46⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceFieldH (p := p) (P := P) K hK1 hK x ω4 μ4 Fr (by decide) st4 S 18845 786 18867 144 8 (by unfold FieldCase; decide)
      jte_392 bs_18867 b45 b46 L.hS' L.slot (by simp; omega) with ⟨ω5, μ5, run5, st5, b55, b56⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rcases pieceDirectH (p := p) (P := P) K hK1 hK x ω5 μ5 Fr (by decide) st5 S 18867 916 20329 8 128 (by unfold DirectCase; decide)
      jte_457 bs_20329 b55 b56 L.hS' L.slot (by simp; omega) with ⟨ω6, μ6, run6, st6, b65, b66⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans run5)))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [c0, c1, c2, c3] at st6
  exact Or.inl (closeH L 20329 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
    (st6.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- The heap octets of a `Vec` of n octets at q, as `EncOkMH`'s stretches: (q, n). -/
def SrcAt (q n : Nat) (q' m : Nat) : Prop := q' = q ∧ m = n

/-- **`LookedUp { data: Some(bytes) }` (tag 18), with growth** (`VariantsVec.looked_up_some` as
    `EncOkMH`): encodes to 18 :: 1 :: ℰ(n) ++ bytes, the heap octets the stretch (q, n). -/
theorem looked_up_someH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (bytes : List UInt8) (hbn : bytes.length = n) (hn : n < 4294967296)
    (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 192 (18 :: 1 :: (Blob.encodeNat n ++ bytes)) (LookedUpSomeRepAt q n bytes)
      (SrcAt q n) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, rb⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 18) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 8 8 (by decide)]; exact r8
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS := L.hS; have hS' := L.hS'
  have hN : (18 :: 1 :: (Blob.encodeNat n ++ bytes) : List UInt8).length = 2 + (Blob.encodeNat n).length + n := by
    simp [hbn] <;> omega
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startVH (p := p) (P := P) K x ω μ L (by decide) 18 (Or.inl rfl) h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 18 = 19538 from rfl] at run1
  have wst : ∀ (μ' : Memory) (cap' ptr' : Nat) (s' : State) (pre : List UInt8),
      BufH env pb S0 S1 F v len ptr s μ pre cap' ptr' s' μ' → ∀ a, F - 56 ≤ a → a < F → μ'.writable a = true :=
    fun μ' cap' ptr' s' pre W a h1 h2 => W.H.st a (by omega) (by omega)
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19538 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => wst _ _ _ _ _ W1 a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 18] 1 856 19559 rfl (by decide) b0 b7 b8 b9
      ⟨by decide, by decide, by decide⟩ jte_427 bs_19559 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19559_some (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S n (by omega) (by omega) (by omega) (by omega) st3.h1
    (by rw [c5, b5, a5]) (by rw [c6, b6])
    (by rw [st3.slot L.slot (by decide)]; exact c8)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => wst _ _ _ _ _ W3 a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 [UInt8.ofNat 1] 1 858 19586 rfl (by decide) d0 d7 d8 d9
      ⟨by decide, by decide, by decide⟩ jte_428 bs_19586 (by simp; omega) dt with
    ⟨ω5, μ5, run5, st5, e5, e6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
  -- the length prefix
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, fq, fn, fv, ffr, frd, fwr⟩ := seg_19586 (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 (F - 56) v S q n (by omega) (by omega) (by omega) hq64 hn st5.h1
    (by rw [e6, d6, c6, b6])
    (by rw [st5.slot L.slot (by decide)]; exact c16)
    (by rw [st5.slot L.slot (by decide)]; exact c24)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st5.sv)
    (fun a h1 h2 => W5.safe_readable (by omega) (W5.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => wst _ _ _ _ _ W5 a (by omega) (by omega))
  have st6 := st5.scratch Fr f1 (fun a h0 h1 => ffr a h0 (by omega) (by omega)) frd fwr
  rcases prefixDH (p := p) (P := P) env K hK1 hK x ω6 μ6 Fr (by decide) st6 n 860 19622 f0 (by rw [f7]; congr 1; omega) f8
      (by rw [show F - 32 = F - 56 + 24 by omega]; exact fn) ⟨by decide, by decide, by decide⟩ jte_429 bs_19622
      (by simp; omega) with
    ⟨ω7, μ7, run7, st7, g5, g6, gF⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
      hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  -- the octets
  obtain ⟨ω8, run8, h80, h81, h85, h86, h87, h88, h89⟩ := seg_19622 (p := p) (P := P) (R := refineContractK K env)
    x ω7 μ7 (F - 56) v q n (by omega) hq64 (by omega) (by omega) st7.h1 (by rw [g5, f5]) (by rw [g6, f6])
    (by rw [Memory.readN_congr (fun j hj => gF _ (by omega) (by omega))]; exact fq)
    (fun a h1 h2 => by
      obtain ⟨cap7, ptr7, s7, W7⟩ := st7.buf
      exact Memory.readable_of_writable (W7.H.st a (by omega) (by omega)))
  rcases heapDH (p := p) (P := P) env K hK1 hK x ω8 μ7 Fr (by decide) ⟨⟨h81.trans st7.h1, st7.w0, st7.w5, st7.w6, st7.buf⟩, st7.sv⟩
      q n 862 19636 hbn rb h80 h87 h88 h89 ⟨by decide, by decide, by decide⟩ jte_430 bs_19636 (by simp; omega)
      (by rcases Nat.eq_zero_or_pos n with h | h
          · exact Or.inl h
          · exact Or.inr (hsrc q n ⟨rfl, rfl⟩)) with
    ⟨ω9, μ9, run9, st9, -, -, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      (run7.trans run8))))))) hx).mono (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega))
  exact Or.inl (closeH L 19636 _ (by decide) (by unfold encGas stepGas prefixGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9))))))))
    (st9.toStH.cast (by simp)))

end Services.Bootstrap.Encode.GrowH
