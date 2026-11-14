import Services.Bootstrap.Encode.ArmsH
import Services.Bootstrap.Encode.VariantsVec3Core
import Services.Bootstrap.Encode.VariantsVec3Bless

/-!
# Shared pieces for the `Vec` arms with growth (`EncOkMH`)

* `SrcAtP q n`: the stretch (q, n) when n > 0 (`ArmsH.SrcAt` with nothing for an empty `Vec`, whose
  pointer is dangling and lies in no chunk).
* `SafeR.sub`, `SafeR.ext`, `SafeR.bounds`: a sub-stretch of a kept stretch is kept; a kept stretch is
  a source for `ext_stepH`; its numeric bounds.
* `startDH`: the dispatch (`Enc.startD`) into `StDH []` for any variant 1 ≤ t ≤ 24.
* `pieceTagDH`: `Enc.pieceTagD` (the tag of `Bless` / `Assign`) over `StDH`.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.VecU8
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The heap octets of a `Vec` of n octets at q when n > 0: the stretch (q, n). -/
def SrcAtP (q n : Nat) (q' m : Nat) : Prop := 0 < n ∧ q' = q ∧ m = n

/-- A sub-stretch of a kept stretch is kept. -/
theorem SafeR.sub {s : State} {ptr B S1 v q m q' m' : Nat} (h : SafeR s ptr B S1 v q m) (h1 : q ≤ q')
    (h2 : q' + m' ≤ q + m) : SafeR s ptr B S1 v q' m' := by
  rcases h with ⟨b1, b2, b3⟩ | ⟨e, he, heu, hne, e1, e2⟩
  · exact Or.inl ⟨by omega, by omega, by omega⟩
  · exact Or.inr ⟨e, he, heu, hne, by omega, by omega⟩

/-- A kept stretch is a source of `ext_stepH`. -/
theorem SafeR.ext {s : State} {ptr F S1 v q m : Nat} (h : SafeR s ptr F S1 v q m) :
    m = 0 ∨ (F - 56 ≤ q ∧ q + m ≤ S1 ∧ (q + m ≤ v ∨ v + 24 ≤ q)) ∨ HeapSrc s ptr q m := by
  rcases h with ⟨b1, b2, b3⟩ | h
  · exact Or.inr (Or.inl ⟨by omega, b2, b3⟩)
  · exact Or.inr (Or.inr h)

/-- **A kept stretch's bounds**: at or above 2^16 and below S1 < 2^32. -/
theorem SafeR.bounds {env : RefineHost.Env} {pb S0 S1 D F v : Nat} {μ : Memory} {s : State}
    {ptr q m : Nat} (H : HeapCtx env pb S0 S1 μ s) (Fr : FrH S0 S1 D F v) (h : SafeR s ptr F S1 v q m) :
    65536 ≤ q ∧ q + m ≤ S1 ∧ S1 < 4294967296 := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := H.hS1
  rcases h with ⟨b1, b2, b3⟩ | ⟨e, he, heu, hne, e1, e2⟩
  · exact ⟨by omega, b2, H.hS1⟩
  · have := chunk_in H.wf he heu
    have := H.hb0; have := H.hbT
    exact ⟨by omega, by omega, H.hS1⟩

/-- **A kept stretch lies above the frame base F or below 2^31** (in the heap). -/
theorem SafeR.apart {env : RefineHost.Env} {pb S0 S1 F v : Nat} {μ : Memory} {s : State}
    {ptr q m : Nat} (H : HeapCtx env pb S0 S1 μ s) (h : SafeR s ptr F S1 v q m) :
    F ≤ q ∨ q + m < 2147483648 := by
  rcases h with ⟨b1, b2, b3⟩ | ⟨e, he, heu, hne, e1, e2⟩
  · exact Or.inl b1
  · have := chunk_in H.wf he heu
    have := H.hbT
    exact Or.inr (by omega)

/-- **From 30145 to the arm of a variant with a discriminant word** (2^63 + t − 1, 1 ≤ t ≤ 24), in
    `StDH []`, the writer in ω₁₀ and the value in ω₁₁ (`Enc.startD`). -/
theorem startDH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (K : Nat) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {env : RefineHost.Env} {pb S0 S1 D F S v cap ptr len ret t' : Nat} {s : State}
    (L : LayDH env pb S0 S1 P D F S v cap ptr len ret t' s μ) (hD : 136 ≤ D) (t : Nat) (ht : 1 ≤ t ∧ t < 25)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p (refineContractK K env) 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StDH env pb S0 S1 F v len ptr ret ω[5].toNat ω[6].toNat s μ [] ω1 μ1 ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startD (p := p) (P := P) (R := refineContractK K env) x ω μ
    L.toLayD0 hD t ht h0 h1 h7 h8 hD8 tab hrt
  have hk := keep_vl (Q := fun a => a < 4294967296 ∧ (a < F - D ∨ F ≤ a)) (by simpa using st1.vl) L.vl
    (fun a ha h => st1.keep a ha.1 ha.2 (by simp; omega) h)
  exact ⟨ω1, μ1, run1, ⟨⟨st1.h1, st1.s0, st1.s5, st1.s6, ⟨cap, ptr, s,
    L.init.frame (F - D) F (by omega) (Nat.le_refl _) (Or.inl n5) (fun a h0 h1 => hk a ⟨h0, h1⟩) st1.rd st1.wr⟩⟩,
    st1.sv⟩, a10, a11⟩

section
variable {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
  {env : RefineHost.Env} {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory}
  {pre : List UInt8}

/-- **The tag of `Bless` (18163) or `Assign` (18429), with growth** (`Enc.pieceTagD`): `StDH pre` becomes
    `StDH (pre ++ [tag])` at e', S in ω₅ and the writer in ω₆. -/
theorem pieceTagDH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S e tag r e' : Nat)
    (he : (e = 18163 ∧ tag = 11 ∧ r = 728) ∨ (e = 18429 ∧ tag = 12 ∧ r = 752))
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e') (hbe : P.isBlockStart e' = true)
    (h10 : ω[10] = UInt64.ofNat v) (h11 : ω[11] = UInt64.ofNat S) (hS : S < 18446744073709551616)
    (hlen : 2 * (len + pre.length + 1) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) e ω μ x e' ω' μ' x (stepGas 1 + 10) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ [UInt8.ofNat tag]) ω' μ' ∧
      ω'[5] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat v) ∨
    ExhaustsW env K pb p P e ω μ x (stepGas 1 + 10) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0 := by omega
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_tagB (p := p) (P := P)
    (R := refineContractK K env) x ω μ e tag r (F - 56) v S he (by omega) (by omega) hS st.h1 h10 h11
    (fun a h1 h2 => W.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 [UInt8.ofNat tag] 1 r e' rfl (by decide)
      b0 b7 b8 b9 hr hje hbe hlen bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  · exact Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3, c5.trans b5, c6.trans b6⟩
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

end

end Services.Bootstrap.Encode.GrowH
