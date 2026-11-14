import Services.Bootstrap.Refine.Decode
import Services.Bootstrap.Refine.DecodeVec2C

/-!
# `Instructions::decode` in refine, the slots' chunks seen

`decode_oneC` is `Decode.decode_one` over `DecodeVec2C.vec_anyC` (one batch for n ≤ 70, two above): each instruction an `ElemOkAFC`, its slot
property seeing the chunks it allocated. GP v0.8.0 Appendix B.4; `Spec.refine`'s `decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeC

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.Loop
  Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Instructions::decode`, one batch, the slots' chunks seen**: as `decode_one`, each instruction given as
    an `ElemOkAFC` (`DecodeVecC.vec_oneC`).
    `Instructions::decode` (4792 … 4842, 1 ≤ n < 128): refine's frame M (its reader at
    M + 272, the payload's copy q at M + 112 and its length Ly in ω₆), the payload n :: es.flatten ⌢ salt ⌢ …
    in the heap's first chunk cp, each instruction decoded by its `ElemOkAF` (frame M − 744, reader M + 272).
    Result: `{n, E, n}` and the salt at M + 168 (the instructions' buffer E in the new chunk cb, element j
    satisfying `reps j`), the reader past the salt, ω₁ = M, ω₅ restored and ω₆ = Ly; the allocator's context
    for a heap s' keeping every allocated chunk of s with its data; refine's frame from M up kept apart from
    M + 168 … M + 224 and the reader. Or an allocation fails. -/
theorem decode_oneC {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (cap0 : Nat)
    (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616) {hb pb : Nat} (gl : Nat → UInt8)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (H : HeapCtx env pb S0 S1 μ s)
    (M q Ly r5 : Nat) (es : List (List UInt8)) (salt : List UInt8)
    (reps : Nat → List Chunk → List UInt8 → Memory → Prop)
    (cp : Chunk) (Ns : Nat → Nat)
    (hel : ∀ j (hj : j < es.length), Decode.VecVecOwn.ElemOkAFC env cap0 pb gl p P (M - 744) (M + 272) (Ns j) es[j]
      (reps j))
    (hg : ∀ a, Glob a → μ.read a = gl a)
    (hn : 1 ≤ es.length ∧ es.length < 128) (hne : ∀ j (hj : j < es.length), 1 ≤ es[j].length)
    (hM : S0 + 2848 ≤ M ∧ M + 288 ≤ S1 ∧ M % 8 = 0) (hr5 : r5 < 18446744073709551616)
    (hcp : cp ∈ chunks s ∧ cp.used = true ∧ cp.addr = s.base)
    (hcpd : ∀ a, q ≤ a → a < q + Ly → InData cp a)
    (hLy : 1 + es.flatten.length + 32 ≤ Ly ∧ Ly < 4294967296)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat r5) (h6 : ω[6] = UInt64.ofNat Ly)
    (s112 : μ.readN (M + 112) 8 = Num.encodeLE 8 q) (sb : μ.read q = UInt8.ofNat es.length)
    (pay : μ.readN (q + 1) es.flatten.length = es.flatten)
    (ssalt : μ.readN (q + 1 + es.flatten.length) 32 = salt)
    (tab : μ.readN 67476 100 = Decode.Tag.table) (rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (E N : Nat),
      FreeStepsH p (refineContractK cap0 env) 4792 ω μ x 4842 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat Ly ∧
      μ'.readN (M + 168) 8 = Num.encodeLE 8 es.length ∧ μ'.readN (M + 176) 8 = Num.encodeLE 8 E ∧
      μ'.readN (M + 184) 8 = Num.encodeLE 8 es.length ∧ μ'.readN (M + 192) 32 = salt ∧
      μ'.readN (M + 272) 8 = Num.encodeLE 8 (q + 1 + es.flatten.length + 32) ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (Ly - 1 - es.flatten.length - 32) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (⟨E - 32, (232 * es.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ a, E ≤ a → a < E + 232 * es.length → InData ⟨E - 32, (232 * es.length + 31) / 32 + 1, true⟩ a) ∧
      (∃ csOf : Nat → List Chunk, (∀ j, j < es.length → (∀ c ∈ csOf j, c ∈ chunks s' ∧ c.used = true ∧
        c ≠ ⟨E - 32, (232 * es.length + 31) / 32 + 1, true⟩ ∧ c ≠ cp) ∧
        ∀ μ'' : Memory, (∀ c ∈ csOf j, ∀ a, InData c a → μ''.read a = μ'.read a) →
          reps j (csOf j) (μ'.readN (E + 232 * j) 232) μ'') ∧
        ∀ j j', j < es.length → j' < es.length → j ≠ j' → ∀ c ∈ csOf j, c ∉ csOf j') ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s' ∧ ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨E - 32, (232 * es.length + 31) / 32 + 1, true⟩) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 224 ≤ a) → (a < M + 272 ∨ M + 288 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ∃ N, Exhausts env cap0 pb p P 4792 ω μ x N := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨hcpm, hcpu, hcpa⟩ := hcp
  obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hcpm hcpu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hst := H.st
  have hq1 := hcpd q (Nat.le_refl _) (by omega)
  have hq2 := hcpd (q + Ly - 1) (by omega) (by omega)
  unfold InData at hq1 hq2
  -- the head: the reader, the length, the call of `Vec<Instruction>::decode`
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a272, a280, a128, a120, a112, afr, ard, awr⟩ :=
    DecodeTail.head (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M q Ly r5 es.length
      ⟨by omega, by omega, hM8⟩ ⟨by omega, by omega⟩ ⟨by omega, hLy.2⟩ hr5 ⟨hn.1, by omega⟩ h1 h5 h6 s112 sb
      (fun a h1 h2 => Memory.readable_of_writable (Decode.VecU8.heap_writable H hcpm hcpu (hcpd a h1 (by omega))))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have hlow1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a h => afr a (by omega) (Or.inl (by omega))
    (Or.inl (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := Decode.GrowOne.ctx_high H hlow1 awr
  have r1 : ∀ a l, a + l ≤ 2147483648 → μ1.readN a l = μ.readN a l :=
    fun a l h => Memory.readN_congr (fun j hj => hlow1 _ (by omega))
  obtain ⟨kp1, kr1⟩ := ExitRun.ro_keep H run1 (a := 67476) (l := 100) (by omega)
  rcases DecodeVec2C.vec_anyC (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 gl x ω1 μ1 s H1 (M - 688) (M + 272)
      (q + 1) (Ly - 1) (M + 168) (M + 272) es reps cp Ns
      (by rw [show M - 688 - 56 = M - 744 by omega]; exact hel)
      (fun a ha => (hlow1 a (by unfold Glob at ha; omega)).trans (hg a ha)) hn hne
      ⟨by omega, by omega, by omega, by omega⟩ (by omega) (by omega) ⟨hcpm, hcpu, hcpa⟩
      (fun a h1 h2 => hcpd a (by omega) (by omega)) (by omega) ⟨by omega, by omega⟩ a0
      (by rw [a1]; congr 1; omega) a5 a6 (by rw [a7]; congr 1; omega) a8 a9 a272 a280
      (by rw [r1 _ _ (by omega)]; exact pay) (by rw [kp1]; exact tab) (fun a h1 h2 => by rw [kr1 a h1 h2]; exact rt a h1 h2)
    with ⟨ω2, μ2, s2, E, N2, run2, b1, b5, b6, b0, b8, b16, bR0, bR8, H2, hcb, hcbd, hel2, keep2, fresh2, hi2, hgl2⟩ | hx
  rotate_left
  · obtain ⟨N, hx⟩ := hx
    exact Or.inr ⟨_, Exhausts.pre run1 hx⟩
  have hst2 := H2.st
  have hb2 := H2.hb0
  have hbT2 := H2.hbT
  obtain ⟨hE0, -, hET⟩ := Decode.VecU8.chunk_in H2.wf hcb rfl
  simp only at hE0 hET
  -- the tail: the salt, `Instructions` at M + 168, back to refine
  have g2 : ∀ a l, M - 136 + 24 ≤ a → a + l ≤ 4294967296 → (a + l ≤ M + 272 ∨ M + 288 ≤ a) →
      μ2.readN a l = μ1.readN a l :=
    fun a l h0 h1 h2 => Memory.readN_congr (fun j hj => hi2 _ (by omega) (by omega) (by omega))
  obtain ⟨ω3, μ3, run3, c1, c5, c6, c0, c8, c16, csalt, cR0, cR8, cfr, crd, cwr⟩ := DecodeTail.tail (p := p) (P := P)
    (R := refineContractK cap0 env) x ω2 μ2 (M - 136) (M + 168) (M + 272) es.length E es.length
    (q + 1 + es.flatten.length) (Ly - 1 - es.flatten.length) r5 Ly salt ⟨by omega, by omega, by omega⟩
    ⟨by omega, by omega⟩ ⟨by omega, by omega, Or.inr (by omega)⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hr5 (by omega)
    (by rw [b1]; congr 1; omega) b5 b6 (by rw [show M - 136 = M - 688 + 552 by omega]; exact b0)
    (by rw [show M - 136 + 8 = M - 688 + 552 + 8 by omega]; exact b8)
    (by rw [show M - 136 + 16 = M - 688 + 552 + 16 by omega]; exact b16)
    (by rw [g2 _ _ (by omega) (by omega) (by omega)]; exact a128)
    (by rw [g2 _ _ (by omega) (by omega) (by omega)]; exact a120)
    (by rw [g2 _ _ (by omega) (by omega) (by omega)]; exact a112)
    bR0 bR8
    (by rw [Memory.readN_congr (fun j hj => (keep2 cp hcpm hcpu).2 _ (hcpd _ (by omega) (by omega))),
      r1 _ _ (by omega), show q + 1 + es.flatten.length = q + 1 + es.flatten.length from rfl]; exact ssalt)
    (fun a h1 h2 => hst2 a (by omega) (by omega)) (fun a h1 h2 => hst2 a (by omega) (by omega))
    (fun a h1 h2 => hst2 a (by omega) (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (Decode.VecU8.heap_writable H2 (keep2 cp hcpm hcpu).1 hcpu
      (hcpd a (by omega) (by omega))))
  have hlow3 : ∀ a, a < 2147483648 → μ3.read a = μ2.read a := fun a h => cfr a (by omega) (Or.inl (by omega))
    (Or.inl (by omega)) (Or.inl (by omega))
  have H3 : HeapCtx env pb S0 S1 μ3 s2 := Decode.GrowOne.ctx_high H2 hlow3 cwr
  refine Or.inl ⟨ω3, μ3, s2, E, _, run1.trans (run2.trans run3), by rw [c1]; congr 1; omega, c5, c6, c0, c8, c16,
    csalt, cR0, cR8, H3, hcb, hcbd, ?_,
    fun c hc hu => ?_, fresh2, fun a h0 h1 h2 h3 => ?_, fun a ha => ?_⟩
  · obtain ⟨csOf, hel, hdis⟩ := hel2
    refine ⟨csOf, fun j hj => ⟨(hel j hj).1, fun μ'' h => ?_⟩, hdis⟩
    obtain ⟨hcs, hr⟩ := hel j hj
    rw [Memory.readN_congr (fun i hi => hlow3 _ (by omega))]
    exact hr μ'' (fun c hc a ha => by
      obtain ⟨hc2, hcu, -⟩ := hcs c hc
      obtain ⟨hc0', -, hcT'⟩ := Decode.VecU8.chunk_in H2.wf hc2 hcu
      have ha' := ha; unfold InData at ha'
      rw [h c hc a ha, hlow3 a (by omega)])
  · obtain ⟨hc2, hd2⟩ := keep2 c hc hu
    obtain ⟨hc0', -, hcT'⟩ := Decode.VecU8.chunk_in H.wf hc hu
    refine ⟨hc2, fun a ha => ?_⟩
    have ha' := ha; unfold InData at ha'
    rw [hlow3 a (by omega), hd2 a ha, hlow1 a (by omega)]
  · rw [cfr a h0 (Or.inr (by omega)) h3 (by omega), hi2 a h0 (by omega) h3, afr a h0 (Or.inr h1) h3]
  · have hg' := ha; unfold Glob at hg'
    rw [hlow3 a (by omega), hgl2 a ha, hlow1 a (by omega)]

end Services.Bootstrap.Refine.DecodeC
