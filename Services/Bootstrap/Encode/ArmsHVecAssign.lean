import Services.Bootstrap.Encode.ArmsHVecCore
import Services.Bootstrap.Encode.VariantsVec3Assign

/-!
# `Assign` (12) with growth (`EncOkMH`)

`Enc.assign` re-proved over `GrowH.StDH`: `assign_loopH` (the queue loop, 18492 … 18513, each hash's 32
octets appended straight from the heap, `heapDH`), `assign_tailH` (the assigner's four octets, 18752 to
the end 20383), `assignH` the arm. The heap octets are the queue's stretch (q, 32 n) when n > 0
(`SrcAtP`).
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

/-- **`Assign`'s queue loop, with growth** (`Enc.assign_loop`): from the loop's head for hash k
    (ω₈ = q + 32 k, ω₅ = 32 i, i = n − k > 0) in `StDH (pre0 ++ hb.take (32 k))`, the hashes' octets (the
    kept stretch (q, 32 n)) appended, at 18752 in `StDH (pre0 ++ hb)`, the frame [F − 56, F) kept; or a
    failed `realloc`. -/
theorem assign_loopH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (q n : Nat) (pre0 hb : List UInt8) (hhb : hb.length = 32 * n)
    (hsrc : SafeR s0 ptr0 F S1 v q (32 * n))
    (arr : ∀ k, k < n → μ0.readN (q + 32 * k) 32 = (hb.drop (32 * k)).take 32)
    (hlen : 2 * (len + pre0.length + 32 * n) ≤ capBound) :
    ∀ i k (ω : Regs) (μ1 : Memory), k + i = n → 0 < i →
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ hb.take (32 * k)) ω μ1 →
      ω[5] = UInt64.ofNat (32 * i) → ω[8] = UInt64.ofNat (q + 32 * k) →
      (∃ ω' μ', FreeStepsH p (refineContractK K env) 18492 ω μ1 x 18752 ω' μ' x ((2000 + growGas) * (32 * i)) ∧
        StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre0 ++ hb) ω' μ' ∧
        (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ1.read a)) ∨
      ExhaustsW env K pb p P 18492 ω μ1 x ((2000 + growGas) * (32 * i)) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  intro i
  induction i with
  | zero => intro k ω μ1 _ h; omega
  | succ i ih =>
    intro k ω μ1 hki _ st h5 h8
    have hk : k < n := by omega
    obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds W1.H Fr (W1.safe hsrc)
    have hlenk : (hb.take (32 * k)).length = 32 * k := by simp [hhb]; omega
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := seg_18492 (p := p) (P := P) (R := refineContractK K env)
      x ω μ1 (F - 56) v (q + 32 * k) (by omega) (by omega) (by omega) st.h1 h8
      (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
      (fun b h1 h2 => Memory.readable_of_writable (W1.H.st b (by omega) (by omega)))
    rcases heapDH (p := p) (P := P) env K hK1 hK x ω2 μ1 Fr hD ⟨⟨b1.trans st.h1, st.w0, st.w5, st.w6, st.buf⟩, st.sv⟩
        (q + 32 * k) 32 756 18508 (by simp [hhb]; omega) (arr k hk) b0 b7 b8 b9
        ⟨by decide, by decide, by decide⟩ jte_377 bs_18508 (by simp [hlenk]; omega)
        (Or.inr (hsrc.sub (by omega) (by omega))) with
      ⟨ω3, μ3, run3, st3, c5, c6, cF⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by unfold stepGas growGas; omega))
    have st3' := st3.cast (show pre0 ++ hb.take (32 * k) ++ (hb.drop (32 * k)).take 32 =
      pre0 ++ hb.take (32 * (k + 1)) by rw [show 32 * (k + 1) = 32 * k + 32 by omega, List.take_add]; simp)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · obtain ⟨ω4, run4, d1⟩ := seg_18508_last (p := p) (P := P) (R := refineContractK K env) x ω3 μ3
        (by rw [c5, b5, h5])
      have hkn : 32 * (k + 1) = hb.length := by omega
      exact Or.inl ⟨ω4, μ3, (run2.trans (run3.trans run4)).mono (by unfold stepGas growGas; omega),
        StDH.cast ⟨⟨d1.trans st3'.h1, st3'.w0, st3'.w5, st3'.w6, st3'.buf⟩, st3'.sv⟩
          (by rw [hkn, List.take_length]), cF⟩
    · obtain ⟨ω4, run4, d1, d5, d8⟩ := seg_18508_more (p := p) (P := P) (R := refineContractK K env) x ω3 μ3
        (i + 1) (q + 32 * k + 32) ⟨by omega, by omega⟩ (by omega) (by rw [c5, b5, h5]) (by rw [c6, b6])
      rcases ih (k + 1) ω4 μ3 (by omega) hi0 ⟨⟨d1.trans st3'.h1, st3'.w0, st3'.w5, st3'.w6, st3'.buf⟩, st3'.sv⟩
          (by rw [d5]; congr 1) (by rw [d8]; congr 1) with
        ⟨ω5, μ5, run5, st5, kF5⟩ | hx
      · exact Or.inl ⟨ω5, μ5, (run2.trans (run3.trans (run4.trans run5))).mono (by unfold stepGas growGas; omega),
          st5, fun a h1 h2 => by rw [kF5 a h1 h2, cF a h1 h2]⟩
      · exact Or.inr ((ExhaustsW.pre (run2.trans (run3.trans run4)) hx).mono (by unfold stepGas growGas; omega))

/-- **`Assign`'s end, with growth** (`Enc.assign_tail`): with S at F − 56, the assigner's four octets w4
    (S + 32, as at entry) appended, at 20383. -/
theorem assign_tailH (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {pre : List UInt8} (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D)
    (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (S : Nat) (hS : SafeR s0 ptr0 F S1 v S 232)
    (hS' : S + 256 < 4294967296) (w4 : List UInt8) (hw4 : μ0.readN (S + 32) 4 = w4)
    (sS : μ.readN (F - 56) 8 = Num.encodeLE 8 S) (hlen : 2 * (len + pre.length + 4) ≤ capBound) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 18752 ω μ x 20383 ω' μ' x (stepGas 4 + 12) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ w4) ω' μ') ∨
    ExhaustsW env K pb p P 18752 ω μ x (stepGas 4 + 12) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1; have := Fr.hFS0
  have hw4l : w4.length = 4 := by rw [← hw4]; simp [Memory.readN]
  obtain ⟨cap1, ptr1, s1, W1⟩ := st.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_18752 (p := p) (P := P)
    (R := refineContractK K env) x ω μ (F - 56) v S (by omega) (by omega) (by omega) st.h1 sS
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st.sv)
    (fun a h1 h2 => W1.safe_readable (by omega) (W1.safe hS) a (by omega) (by omega))
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr hD st2 w4 4 918 20383 hw4l (by decide) b0 b7 b8 b9
      ⟨by decide, by decide, by decide⟩ jte_458 bs_20383 hlen (by rw [bt, st.slot hS (by decide), hw4]) with
    ⟨ω3, μ3, run3, st3, -, -, -⟩ | hx
  · exact Or.inl ⟨ω3, μ3, (run2.trans run3).mono (by omega), st3⟩
  · exact Or.inr ((ExhaustsW.pre run2 hx).mono (by omega))

end

/-- **`Assign` (index 12), with growth** (`Enc.assign` as `EncOkMH`): `AssignRepAt q n c2 hb w4` encodes
    to 12 :: c2 ++ hb ++ w4, the heap octets the queue's stretch (q, 32 n) when n > 0. -/
theorem assignH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * n)
    (hw4 : w4.length = 4) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 136 (12 :: (c2 ++ hb ++ w4)) (AssignRepAt q n c2 hb w4) (SrcAtP q (32 * n)) := by
  intro x ω μ s S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt hsrc
  obtain ⟨r0, r8, r16, r24, r32, r36, rarr⟩ := rep
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 12) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact r0
  have c16 : μ.readN (S + 16) 8 = Num.encodeLE 8 q := by rw [← slot_take μ S 16 8 (by decide)]; exact r16
  have c24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n := by rw [← slot_take μ S 24 8 (by decide)]; exact r24
  have c32 : μ.readN (S + 32) 4 = w4 := by rw [← slot_take μ S 32 4 (by decide)]; exact r32
  have c36 : μ.readN (S + 36) 2 = c2 := by rw [← slot_take μ S 36 2 (by decide)]; exact r36
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨a1, a2, a3⟩ := L.slot_apart
  have hS := L.hS; have hS' := L.hS'
  have hN : (12 :: (c2 ++ hb ++ w4) : List UInt8).length = 7 + 32 * n := by
    simp [hc2, hhb, hw4]; omega
  rw [hN] at hlen
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startDH (p := p) (P := P) K x ω μ L (by decide) 12
    ⟨by decide, by decide⟩ h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 12 = 18429 from rfl] at run1
  rcases pieceTagDH (p := p) (P := P) K hK1 hK x ω1 μ1 Fr (by decide) st1 S 18429 12 752 18452
      (Or.inr ⟨rfl, rfl, rfl⟩) jte_375 bs_18452 a10 a11 (by omega) (by simp; omega) with
    ⟨ω2, μ2, run2, st2, b5, b6⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre run1 hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  -- the core
  obtain ⟨cap2, ptr2, s2, W2⟩ := st2.buf
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, ct, cfr, crd, cwr⟩ := seg_18452 (p := p) (P := P)
    (R := refineContractK K env) x ω2 μ2 (F - 56) v S (by omega) (by omega) (by omega) st2.h1 b5 b6
    (fun a h1 h2 => W2.safe_readable (by omega) (W2.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W2.H.st a (by omega) (by omega))
  have st3 := st2.scratch Fr c1 (fun a h0 h1 => cfr a h0 (by omega)) crd cwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω3 μ3 Fr (by decide) st3 c2 2 754 18473 hc2 (by decide)
      c0 c7 c8 c9 ⟨by decide, by decide, by decide⟩ jte_376 bs_18473 (by simp; omega)
      (by rw [ct, st2.slot L.slot (by decide), c36]) with
    ⟨ω4, μ4, run4, st4, d5, d6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans run3)) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  have hl4 : ([] ++ [UInt8.ofNat 12] ++ c2 : List UInt8).length = 3 := by simp [hc2]
  have h45 : ω4[5] = UInt64.ofNat S := by rw [d5, c5, b5]
  obtain ⟨cap4, ptr4, s4, W4⟩ := st4.buf
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- an empty queue
    subst hn0
    have hb0 : hb = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hb0
    obtain ⟨ω5, μ5, run5, e1, e0, efr, erd, ewr⟩ := seg_18473_zero (p := p) (P := P)
      (R := refineContractK K env) x ω4 μ4 (F - 56) S (by omega) (by omega) st4.h1 h45
      (by rw [st4.slot L.slot (by decide)]; exact c24)
      (fun a h1 h2 => W4.safe_readable (by omega) (W4.safe L.slot) a (by omega) (by omega))
      (fun a h1 h2 => W4.H.st a (by omega) (by omega)) (by omega)
    have st5 := st4.scratch Fr (e1.trans st4.h1) (fun a h0 h1 => efr a h0 (by omega)) erd ewr
    rcases assign_tailH (p := p) (P := P) K hK1 hK x ω5 μ5 Fr (by decide) st5 S L.slot hS' w4 c32 e0
        (by rw [hl4]; omega) with
      ⟨ω6, μ6, run6, st6⟩ | hx
    · exact Or.inl (closeH L 20383 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) (st6.toStH.cast (by simp)))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans run5)))) hx).mono
        (by unfold encGas stepGas growGas; rw [hN]; omega))
  · have hsq := hsrc q (32 * n) ⟨by omega, rfl, rfl⟩
    obtain ⟨bq1, bq2, bq3⟩ := SafeR.bounds L.H Fr hsq
    obtain ⟨ω5, μ5, run5, e1, e5, e8, e0, efr, erd, ewr⟩ := seg_18473_pos (p := p) (P := P)
      (R := refineContractK K env) x ω4 μ4 (F - 56) S q n (by omega) (by omega) hq64 ⟨hn0, by omega⟩ st4.h1 h45
      (by rw [st4.slot L.slot (by decide)]; exact c16)
      (by rw [st4.slot L.slot (by decide)]; exact c24)
      (fun a h1 h2 => W4.safe_readable (by omega) (W4.safe L.slot) a (by omega) (by omega))
      (fun a h1 h2 => W4.H.st a (by omega) (by omega)) (by omega)
    have st5 := st4.scratch Fr (e1.trans st4.h1) (fun a h0 h1 => efr a h0 (by omega)) erd ewr
    have henc : (12 :: (c2 ++ hb ++ w4) : List UInt8) = ([] ++ [UInt8.ofNat 12] ++ c2) ++ hb ++ w4 := by
      simp only [List.nil_append, List.cons_append, List.append_assoc] <;> rfl
    rcases assign_loopH (p := p) (P := P) K hK1 hK x Fr (by decide) q n ([] ++ [UInt8.ofNat 12] ++ c2) hb hhb
        hsq rarr (by rw [hl4]; omega) n 0 ω5 μ5 (by omega) hn0 (st5.cast (by simp)) (by rw [e5])
        (by rw [e8]; congr 1) with
      ⟨ω6, μ6, run6, st6, kF6⟩ | hx
    rotate_left
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans run5)))) hx).mono
        (by unfold encGas stepGas growGas; rw [hN]; omega))
    rcases assign_tailH (p := p) (P := P) K hK1 hK x ω6 μ6 Fr (by decide) st6 S L.slot hS' w4 c32
        (by rw [Memory.readN_congr (fun j hj => kF6 _ (by omega) (by omega))]; exact e0)
        (by simp [hc2, hhb]; omega) with
      ⟨ω7, μ7, run7, st7⟩ | hx
    · exact Or.inl (closeH L 20383 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
        (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7))))))
        (st7.toStH.cast henc.symm))
    · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) hx).mono
        (by unfold encGas stepGas growGas; rw [hN]; omega))

/-- `assignH` at the depth 232. -/
theorem assignH_232 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (q n : Nat) (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * n)
    (hw4 : w4.length = 4) (hq64 : q < 18446744073709551616) :
    EncOkMH env K pb p P 232 (12 :: (c2 ++ hb ++ w4)) (AssignRepAt q n c2 hb w4) (SrcAtP q (32 * n)) :=
  (assignH env K pb hK1 hK q n c2 hb w4 hc2 hhb hw4 hq64).mono (by decide)

end Services.Bootstrap.Encode.GrowH
