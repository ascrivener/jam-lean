import Services.Bootstrap.Encode.ArmsH
import Services.Bootstrap.Encode.Yield

/-!
# More fixed-width arms with growth: the unit variants, `Yield`, `Provide { Hash }`, `LookedUp { None }`

`Dispatch.unit`, `Yield.yield`, `VariantsVec.provide_hash` and `VariantsVec.looked_up_none` as `EncOkMH`
elements (the same encodings and slot representations, no heap octets), each following its original
step by step, every append either succeeding or reaching a failed `realloc` (`ExhaustsW`):

* `scratchH`: an append from the scratch word F − 32 over `StH` (`GrowH.scratchDH` for `StH`);
* `slot_src`: a stretch of the value slot as `ext_stepH`'s source;
* `unitH` (t = 15, 16, 23), `yieldH`, `provide_hashH`, `looked_up_noneH`, all at depth 136.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow Services.Bootstrap.Encode.Enc
  Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **An append from the scratch word** F − 32 over `StH` (`scratchDH` without the saved writer): k ≤ 8
    octets `bs`. -/
theorem scratchH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (bs : List UInt8) (k r e : Nat) (hk : bs.length = k) (hk8 : k ≤ 8)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat (F - 56 + 24))
    (h9 : ω[9] = UInt64.ofNat k) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hlen : 2 * (len + pre.length + k) ≤ capBound)
    (hbs : μ.readN (F - 56 + 24) k = bs) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x e ω' μ' x (stepGas k) ∧
      StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ bs) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (stepGas k) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1
  rcases ext_stepH env K hK1 hK x ω μ Fr hD st (F - 56 + 24) k r e h0 h7 h8 h9 hr hje hbe hlen
      (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨ω', μ', run, st', e5, e6, kF⟩ | hx
  · rw [hbs] at st'; exact Or.inl ⟨ω', μ', run, st', e5, e6, kF⟩
  · exact Or.inr hx

/-- A stretch of a kept value slot, as `ext_stepH`'s source. -/
theorem slot_src {s0 : State} {ptr0 F S1 v S : Nat} (hslot : SafeR s0 ptr0 F S1 v S 232) (off n : Nat)
    (h : off + n ≤ 232) :
    n = 0 ∨ (F - 56 ≤ S + off ∧ S + off + n ≤ S1 ∧ (S + off + n ≤ v ∨ v + 24 ≤ S + off)) ∨
      HeapSrc s0 ptr0 (S + off) n := by
  rcases hslot with ⟨h1, h2, h3⟩ | ⟨e, he, heu, hne, h1, h2⟩
  · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨e, he, heu, hne, by omega, by omega⟩)

/-- **`Checkpoint`, `Panic`, `Benchmark` (t = 15, 16, 23), with growth** (`Dispatch.unit` as `EncOkMH`). -/
theorem unitH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (t : Nat) (ht : t = 15 ∨ t = 16 ∨ t = 23) :
    EncOkMH env K pb p P 136 [UInt8.ofNat t]
      (fun bs _ => bs.take 8 = Num.encodeLE 8 (9223372036854775807 + t)) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : ([UInt8.ofNat t] : List UInt8).length = 1 := rfl
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) t (by omega)
    h0 h1 h7 h8 hD tab hrt
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := unit_arm (p := p) (P := P) (R := refineContractK K env) x
    ω1 μ1 (F - 56) v t ht (by omega) (by omega) st1.h1 a10 (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have back2 : ∀ a, a < 4294967296 → (a < F - 56 ∨ F - 24 ≤ a) →
      (μ1.writeN (F - 56 + 24) [UInt8.ofNat t]).read a = μ1.read a := fun a h0 h1 =>
    Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have st2 := st1.scratch Fr b1 back2 (fun a => Memory.readable_writeN _ _ _ _)
    (fun a => Memory.writable_writeN _ _ _ _)
  rcases scratchH (p := p) (P := P) env K hK1 hK x ω2 _ Fr (by decide) st2 [UInt8.ofNat t] 1 904 20155 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_451 bs_20155 (by simp; omega)
      (Memory.readN_writeN_same _ _ _ _ rfl (by simp [two32])) with
    ⟨ω3, μ3, run3, st3, -, -, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  exact Or.inl (closeH L 20155 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans run3)) (st3.cast (by simp)))

/-- **`Yield` (tag 14), with growth** (`Yield.yield` as `EncOkMH`). -/
theorem yieldH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (h : List UInt8) (hh : h.length = 32) :
    EncOkMH env K pb p P 136 (14 :: h)
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775821 ∧ (bs.drop 8).take 32 = h)
      (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (14 :: h : List UInt8).length = 33 := by simp [hh]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 14) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c0 : μ.readN (S + 8) 32 = h := by rw [← slot_take μ S 8 32 (by decide)]; exact rep.2
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS' := L.hS'
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 14 (by decide)
    h0 h1 h7 h8 hD tab hrt
  rw [show arm 14 = 18138 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := yieldSeg1 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 14] 1 906 20190 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_452 bs_20190 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨ω4, run4, d0, d1, -, -, d7, d8, d9⟩ := yieldSeg2 (p := p) (P := P) (R := refineContractK K env) x ω3 μ3
    v (S + 8) (by omega) (by omega) (c5.trans b5) (c6.trans b6)
  rcases ext_stepH (p := p) (P := P) env K hK1 hK x ω4 μ3 Fr (by decide)
      ⟨d1.trans st3.h1, st3.w0, st3.w5, st3.w6, st3.buf⟩ (S + 8) 32 908 20204 d0 d7 d8 d9
      ⟨by decide, by decide, by decide⟩ jte_453 bs_20204 (by simp; omega) (slot_src L.slot 8 32 (by decide)) with
    ⟨ω5, μ5, run5, st5, -, -, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [st3.slot L.slot (by decide), c0] at st5
  exact Or.inl (closeH L 20204 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans run5))))
    (st5.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`Provide { service, preimage: Hash(h) }` (tag 17), with growth** (`VariantsVec.provide_hash` as
    `EncOkMH`). -/
theorem provide_hashH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (s h : List UInt8) (hs : s.length = 4) (hh : h.length = 32) :
    EncOkMH env K pb p P 136 (17 :: (s ++ 0 :: h))
      (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775824 ∧
        (bs.drop 8).take 1 = [0] ∧ (bs.drop 9).take 32 = h ∧ (bs.drop 48).take 4 = s) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t' h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : (17 :: (s ++ 0 :: h) : List UInt8).length = 38 := by simp [hs, hh]
  rw [hN] at hlen
  have hD : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 17) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c8 : μ.readN (S + 8) 1 = [0] := by rw [← slot_take μ S 8 1 (by decide)]; exact rep.2.1
  have c9 : μ.readN (S + 9) 32 = h := by rw [← slot_take μ S 9 32 (by decide)]; exact rep.2.2.1
  have c48 : μ.readN (S + 48) 4 = s := by rw [← slot_take μ S 48 4 (by decide)]; exact rep.2.2.2
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS' := L.hS'
  obtain ⟨ω1, μ1, run1, st1, a10, a11⟩ := startH (p := p) (P := P) K x ω μ L (by decide) 17 (by decide)
    h0 h1 h7 h8 hD tab hrt
  rw [show arm 17 = 18990 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_tag5 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 18990 17 806 (F - 56) v S (Or.inl ⟨rfl, rfl, rfl⟩) (by omega)
    (by omega) (by omega) st1.h1 a10 a11 (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 17] 1 806 19013 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_402 bs_19013 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19013 (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1
    (by rw [c5, b5]) (by rw [c6, b6])
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases scratchH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 (μ3.readN (S + 48) 4) 4 808 19034
      (by simp) (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_403 bs_19034 (by simp; omega) dt with
    ⟨ω5, μ5, run5, st5, e5, e6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [st3.slot L.slot (by decide), c48] at st5
  obtain ⟨cap5, ptr5, s5, W5⟩ := st5.buf
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ft, ffr, frd, fwr⟩ := seg_19034_hash (p := p) (P := P)
    (R := refineContractK K env) x ω5 μ5 (F - 56) v S (by omega) (by omega) (by omega) st5.h1
    (by rw [e5, d5, c5, b5]) (by rw [e6, d6, c6, b6])
    (by show Num.decodeLE _ = _; rw [st5.slot L.slot (by decide), c8]; rfl)
    (fun a h1 h2 => W5.safe_readable (by omega) (W5.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W5.H.st a (by omega) (by omega))
  have st6 := st5.scratch Fr f1 (fun a h0 h1 => ffr a h0 (by omega)) frd fwr
  rcases scratchH (p := p) (P := P) env K hK1 hK x ω6 μ6 Fr (by decide) st6 [UInt8.ofNat 0] 1 906 20190 rfl
      (by decide) f0 f7 f8 f9 ⟨by decide, by decide, by decide⟩ jte_452 bs_20190 (by simp; omega) ft with
    ⟨ω7, μ7, run7, st7, g5, g6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6)))))
      hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨ω8, run8, k0, k1, -, -, k7, k8, k9⟩ := seg_20190 (p := p) (P := P) (R := refineContractK K env) x ω7 μ7
    v (S + 9) (by omega) (by omega) (by rw [g5, f5]) (by rw [g6, f6, e6, d6, c6, b6])
  rcases ext_stepH (p := p) (P := P) env K hK1 hK x ω8 μ7 Fr (by decide)
      ⟨k1.trans st7.h1, st7.w0, st7.w5, st7.w6, st7.buf⟩ (S + 9) 32 908 20204 k0 k7 k8 k9
      ⟨by decide, by decide, by decide⟩ jte_453 bs_20204 (by simp; omega) (slot_src L.slot 9 32 (by decide)) with
    ⟨ω9, μ9, run9, st9, -, -, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
      (run7.trans run8))))))) hx).mono (by unfold encGas stepGas growGas; rw [hN]; omega))
  rw [st7.slot L.slot (by decide), c9] at st9
  exact Or.inl (closeH L 20204 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans (run8.trans run9))))))))
    (st9.cast (by simp only [List.nil_append, List.cons_append, List.append_assoc]; rfl)))

/-- **`LookedUp { data: None }` (tag 18), with growth** (`VariantsVec.looked_up_none` as `EncOkMH`). -/
theorem looked_up_noneH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K pb : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616) :
    EncOkMH env K pb p P 136 [18, 0] (fun bs _ => bs.take 8 = Num.encodeLE 8 9223372036854775825 ∧
      (bs.drop 8).take 8 = Num.encodeLE 8 18446744073709551615) (fun _ _ => False) := by
  intro x ω μ σ S0 S1 F S v cap ptr len ret t h0 h1 h7 h8 rep L hlen tab hrt _
  have hN : ([18, 0] : List UInt8).length = 2 := rfl
  rw [hN] at hlen
  have hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + 18) := by
    rw [← readN_take _ _ 232 8 (by decide)]; exact rep.1
  have c8 : μ.readN (S + 8) 8 = Num.encodeLE 8 18446744073709551615 := by
    rw [← slot_take μ S 8 8 (by decide)]; exact rep.2
  have Fr := L.fr
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := L.nums
  have hS' := L.hS'
  obtain ⟨ω1, μ1, run1, st1, a5, a10, a11⟩ := startVH (p := p) (P := P) K x ω μ L (by decide) 18 (Or.inl rfl)
    h0 h1 h7 h8 hD8 tab hrt
  rw [show arm 18 = 19538 from rfl] at run1
  obtain ⟨cap1, ptr1, s1, W1⟩ := st1.buf
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b9, bt, bfr, brd, bwr⟩ := seg_19538 (p := p) (P := P)
    (R := refineContractK K env) x ω1 μ1 (F - 56) v S (by omega) (by omega) (by omega) st1.h1 a10 a11
    (fun a h1 h2 => W1.H.st a (by omega) (by omega))
  have st2 := st1.scratch Fr b1 (fun a h0 h1 => bfr a h0 (by omega)) brd bwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω2 μ2 Fr (by decide) st2 [UInt8.ofNat 18] 1 856 19559 rfl
      (by decide) b0 b7 b8 b9 ⟨by decide, by decide, by decide⟩ jte_427 bs_19559 (by simp; omega) bt with
    ⟨ω3, μ3, run3, st3, c5, c6, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans run2) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  obtain ⟨cap3, ptr3, s3, W3⟩ := st3.buf
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, d7, d8, d9, dt, dfr, drd, dwr⟩ := seg_19559_none (p := p) (P := P)
    (R := refineContractK K env) x ω3 μ3 (F - 56) v S (by omega) (by omega) (by omega) st3.h1
    (by rw [c5, b5, a5]) (by rw [c6, b6])
    (by rw [st3.slot L.slot (by decide)]; exact c8)
    (by rw [show F - 56 + 16 = F - 40 by omega]; exact st3.sv)
    (fun a h1 h2 => W3.safe_readable (by omega) (W3.safe L.slot) a (by omega) (by omega))
    (fun a h1 h2 => W3.H.st a (by omega) (by omega))
  have st4 := st3.scratch Fr d1 (fun a h0 h1 => dfr a h0 (by omega)) drd dwr
  rcases scratchDH (p := p) (P := P) env K hK1 hK x ω4 μ4 Fr (by decide) st4 [UInt8.ofNat 0] 1 918 20383 rfl
      (by decide) d0 d7 d8 d9 ⟨by decide, by decide, by decide⟩ jte_458 bs_20383 (by simp; omega) dt with
    ⟨ω5, μ5, run5, st5, -, -, -⟩ | hx
  rotate_left
  · exact Or.inr ((ExhaustsW.pre (run1.trans (run2.trans (run3.trans run4))) hx).mono
      (by unfold encGas stepGas growGas; rw [hN]; omega))
  exact Or.inl (closeH L 20383 _ (by decide) (by unfold encGas stepGas growGas; rw [hN]; omega)
    (run1.trans (run2.trans (run3.trans (run4.trans run5)))) (st5.toStH.cast rfl))

end Services.Bootstrap.Encode.GrowH
