import Services.Bootstrap.Refine.DecodeVec
import Services.Bootstrap.Decode.LoopAPassC
import Services.Bootstrap.Decode.VecVecOwn

/-!
# `Vec<Instruction>::decode`, the slots' chunks seen (interim: one batch)

`vec_oneC` is `DecodeVec.vec_one` over the Vec session's `loopAFC_low`: each element is an `ElemOkAFC`, its slot
property seeing the chunks it allocated (as `VecVecOwn.VecVecRepC` does for `ExportSegs`). GP v0.8.0 Appendix B.4;
`Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeVecC

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.VecU8
  Services.Bootstrap.Refine.DecodeVec

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Picoalloc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop in
/-- **`Vec<Instruction>::decode`, one batch, the slots' chunks seen** (482 … 20420): as `vec_one`, each element
    given as an `ElemOkAFC` and its slot property `reps j cs` seeing the chunks cs it allocated.
    `Vec<Instruction>::decode`, one batch (482 … 20420): `vec_pre`, the element loop (`loopAF_low`, each
    element decoded by its `ElemOkAF`), and the return: the output `{n, q, n}` at out = S + 552 (the `Vec` of
    the n decoded instructions, in the new chunk cb), element j satisfying `reps j` (with the chunks it
    allocated), the reader past the instructions, the allocator's context for a heap s' keeping every allocated
    chunk of s with its data, the stack above S + 552 kept apart from out and the reader. Or an allocation
    fails. -/
theorem vec_oneC {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb pb : Nat} (gl : Nat → UInt8)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s)
    (S rd P0 Lt v5 v6 : Nat) (es : List (List UInt8)) (reps : Nat → List Chunk → List UInt8 → Memory → Prop) (cp : Chunk)
    (Ns : Nat → Nat)
    (hel : ∀ j (hj : j < es.length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (S - 56) rd (Ns j) es[j] (reps j))
    (hg : ∀ a, Glob a → μ.read a = gl a)
    (hn : 1 ≤ es.length ∧ es.length ≤ 70) (hne : ∀ j (hj : j < es.length), 1 ≤ es[j].length)
    (hS : S0 + 2104 ≤ S ∧ S + 552 + 24 ≤ rd ∧ rd + 16 ≤ S1 ∧ S % 8 = 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base)
    (hcpd : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → InData cp a) (hP0 : 206864 ≤ P0)
    (hLt : es.flatten.length ≤ Lt ∧ Lt < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 922) (h1 : ω[1] = UInt64.ofNat (S + 552)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat (S + 552)) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat es.length)
    (sR0 : μ.readN rd 8 = Num.encodeLE 8 P0) (sR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 Lt)
    (pay : μ.readN P0 es.flatten.length = es.flatten)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (q N : Nat),
      FreeStepsH p (refineContractK cap0 env) 482 ω μ x 20420 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (S + 552) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN (S + 552) 8 = Num.encodeLE 8 es.length ∧ μ'.readN (S + 552 + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 552 + 16) 8 = Num.encodeLE 8 es.length ∧
      μ'.readN rd 8 = Num.encodeLE 8 (P0 + es.flatten.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (Lt - es.flatten.length) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ a, q ≤ a → a < q + 232 * es.length → InData ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ a) ∧
      (∃ csOf : Nat → List Chunk, (∀ j, j < es.length → (∀ c ∈ csOf j, c ∈ chunks s' ∧ c.used = true ∧
        c ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩ ∧ c ≠ cp) ∧
        ∀ μ'' : Memory, (∀ c ∈ csOf j, ∀ a, InData c a → μ''.read a = μ'.read a) →
          reps j (csOf j) (μ'.readN (q + 232 * j) 232) μ'') ∧
        ∀ j j', j < es.length → j' < es.length → j ≠ j' → ∀ c ∈ csOf j, c ∉ csOf j') ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (232 * es.length + 31) / 32 + 1, true⟩) ∧
      (∀ a, a < 4294967296 → S + 552 + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ∃ N, Exhausts env cap0 pb p P 482 ω μ x N := by
  obtain ⟨hS0, hSr, hrS, hS8⟩ := hS
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  rcases vec_pre (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω μ s H S (S + 552) rd P0 Lt v5 v6 es
      (fun _ _ _ => True) cp hn
      hne ⟨hS0, by omega, hrS, hS8⟩ (by omega) hv5 hv6 hcp hcpd hP0 hLt h0 h1 h5 h6 h7 h8 h9 sR0 sR8 pay tab rt with
    ⟨ω1, μ1, s1, q, N1, run1, inv1, ok, w0, w8, w16, w544, w536, w528, keep1, fresh1, hi1, hgl1⟩ | hx
  rotate_left
  · exact Or.inr hx
  rcases loopAFC_low (p := p) (P := P) env cap0 pb gl (S - 56) rd P0 Lt Ns x es reps q cp _ ok hel es.length 0 ω1 μ1 s1
      (by omega) (by omega) (InvAF.toC_zero reps inv1) (fun a ha => (hgl1 a ha).trans (hg a ha)) with
    ⟨ω2, μ2, s2, run2, inv2, fr2, low2⟩ | hx
  rotate_left
  · exact Or.inr ⟨_, Exhausts.pre run1 hx⟩
  obtain ⟨fr2a, fr2b, fr2c, fr2d, fr2e, fr2f⟩ := fr2
  have hq := inv2.heap.hbT
  obtain ⟨hcbm, hcbu⟩ := inv2.cbm
  obtain ⟨hqb, hqT, hqT'⟩ := Decode.VecU8.chunk_in inv2.heap.wf hcbm hcbu
  simp only at hqb hqT hqT'
  have hb2 := inv2.heap.hb0
  have hst2 := inv2.heap.st
  have l2 : ∀ a l, S ≤ a → a + l ≤ S + 24 → μ2.readN a l = μ1.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => low2 _ (by omega) (by omega))
  have hi2 : ∀ a l, S + 528 ≤ a → a + l ≤ 4294967296 → (a + l ≤ rd ∨ rd + 16 ≤ a) → μ2.readN a l = μ1.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj => fr2a _ (by omega) (by omega) (by omega))
  have hoffn : off es es.length = es.flatten.length := by simp [off]
  obtain ⟨ω3, μ3, run3, c1, c7, c11, c296, c304, cfr, crd, cwr⟩ := v3a (p := p) (P := P)
    (R := refineContractK cap0 env) x ω2 μ2 S (S + 552) es.length es.length q es.length ⟨by omega, by omega, hS8⟩
    (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [inv2.r1]; congr 1; omega)
    (by rw [l2 _ _ (by omega) (by omega)]; exact w0) (by rw [l2 _ _ (by omega) (by omega)]; exact w8)
    (by rw [l2 _ _ (by omega) (by omega)]; exact w16)
    (by have := inv2.m40; rwa [show S - 56 + 96 = S + 40 by omega] at this)
    (by have := inv2.m48; rwa [show S - 56 + 104 = S + 48 by omega] at this)
    (by have := inv2.m56; rwa [show S - 56 + 112 = S + 56 by omega] at this)
    (fun a h1 h2 => hst2 a (by omega) (by omega))
  have k3 : ∀ a l, S + 312 ≤ a → a + l ≤ 4294967296 → μ3.readN a l = μ2.readN a l :=
    fun a l h0 h1 => Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, d1, d5, d6, d0, d8, d16, dfr, drd, dwr⟩ := v3b (p := p) (P := P)
    (R := refineContractK cap0 env) x ω3 μ3 S (S + 552) es.length q es.length v5 v6 ⟨by omega, by omega, hS8⟩
    ⟨by omega, by omega, Or.inr (Nat.le_refl _)⟩ (by omega) (by omega) (by omega) hv5 hv6 c1 c7 c11 c296 c304
    (by rw [k3 _ _ (by omega) (by omega), hi2 _ _ (by omega) (by omega) (by omega)]; exact w544)
    (by rw [k3 _ _ (by omega) (by omega), hi2 _ _ (by omega) (by omega) (by omega)]; exact w536)
    (by rw [k3 _ _ (by omega) (by omega), hi2 _ _ (by omega) (by omega) (by omega)]; exact w528)
    (fun a h1 h2 => by rw [crd]; exact Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (fun a h1 h2 => by rw [cwr]; exact hst2 a (by omega) (by omega))
  have k42 : ∀ a, a < 4294967296 → (a < S + 296 ∨ S + 312 ≤ a) → (a < S + 552 ∨ S + 576 ≤ a) →
      μ4.read a = μ2.read a := fun a h0 h1 h2 => by rw [dfr a h0 h2, cfr a h0 h1]
  have hlow4 : ∀ a, a < 2147483648 → μ4.read a = μ2.read a := fun a h => k42 a (by omega) (by omega) (by omega)
  have H4 : HeapCtx env pb S0 S1 μ4 s2 := Decode.GrowOne.ctx_high inv2.heap hlow4 (fun a => by rw [dwr, cwr])
  refine Or.inl ⟨ω4, μ4, s2, q, _, run1.trans (run2.trans (run3.trans run4)), d1, d5, d6, d0, d8, d16, ?_, ?_, H4,
    hcbm, inv2.cbd, ?_, fun c hc hu => ?_, fresh1, fun a h0 h1 h2 => ?_, fun a ha => ?_⟩
  · rw [Memory.readN_congr (fun j hj => k42 _ (by omega) (by omega) (by omega))]
    have := inv2.rP; rwa [hoffn] at this
  · rw [Memory.readN_congr (fun j hj => k42 _ (by omega) (by omega) (by omega))]
    have := inv2.rL; rwa [hoffn] at this
  · obtain ⟨csOf, hel, hdis⟩ := inv2.el
    refine ⟨csOf, fun j hj => ⟨(hel j hj).1, fun μ'' h => ?_⟩, hdis⟩
    obtain ⟨hcs, hr⟩ := hel j hj
    rw [Memory.readN_congr (fun i hi => hlow4 _ (by omega))]
    exact hr μ'' (fun c hc a ha => by
      obtain ⟨hc2, hcu, -⟩ := hcs c hc
      obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in inv2.heap.wf hc2 hcu
      have ha' := ha; unfold InData at ha'
      rw [h c hc a ha, hlow4 a (by omega)])
  · obtain ⟨hc1, hd1⟩ := keep1 c hc hu
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hu
    have hbTs := H.hbT
    have hcne := fresh1 c hc hu
    refine ⟨fr2b c hc1 hu, fun a ha => ?_⟩
    have ha' := ha; unfold InData at ha'
    have hdj := Decode.VecU8.data_disj inv2.heap.wf (fr2b c hc1 hu) hcbm hcne ha
    simp only at hdj
    rw [hlow4 a (by omega), fr2c c hc1 hu a ha (by omega), hd1 a ha]
  · rw [k42 a h0 (by omega) (by omega), fr2a a (by omega) h0 h2, hi1 a h0 (by omega)]
  · have hg' := ha; unfold Glob at hg'
    rw [hlow4 a (by omega), fr2e a ha, hgl1 a ha]

end Services.Bootstrap.Refine.DecodeVecC
