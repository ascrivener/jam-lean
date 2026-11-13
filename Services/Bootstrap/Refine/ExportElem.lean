import Services.Bootstrap.Refine.ExportStep
import Services.Bootstrap.Refine.PassLoop

/-!
# Refine's transform loop: one `ExportSegs` instruction

`export_step` is one instruction of index 10 (`ExportSegs`, a `Vec<Vec<u8>>`) from the loop head 5042 back
to it: `PInv k` becomes `PInv (k + 1)`, the output slot k holding `Exported(n)`, the host context the n
segments exported in order (`ExportSeg.expUpTo`), and the segments' buffers and their `Vec`'s buffer freed.
GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code) and B.6 (Ω_E, export); `Spec.refineInstr`'s
`.exportSegs ds`.
-/

namespace Services.Bootstrap.Refine.ExportElem

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Refine.PassLoop Services.Bootstrap.Refine.Export Services.Bootstrap.Refine.ExportStep

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `ExportSeg.expUpTo` reads only the segments' words and their octets. -/
theorem expUpTo_congr {env : RefineHost.Env} {μ μ' : Memory} {ptr : Nat} {x : RefineCtx} (n : Nat)
    (h : ∀ a, (ptr ≤ a ∧ a < ptr + 24 * n) ∨ (∃ j, j < n ∧ rdN μ (ptr + 24 * j + 8) 8 ≤ a ∧
      a < rdN μ (ptr + 24 * j + 8) 8 + rdN μ (ptr + 24 * j + 16) 8) → μ'.read a = μ.read a) :
    ExportSeg.expUpTo env μ' ptr x n = ExportSeg.expUpTo env μ ptr x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have r8 : rdN μ' (ptr + 24 * n + 8) 8 = rdN μ (ptr + 24 * n + 8) 8 := by
      unfold rdN; rw [Memory.readN_congr (fun j hj => h _ (Or.inl ⟨by omega, by omega⟩))]
    have r16 : rdN μ' (ptr + 24 * n + 16) 8 = rdN μ (ptr + 24 * n + 16) 8 := by
      unfold rdN; rw [Memory.readN_congr (fun j hj => h _ (Or.inl ⟨by omega, by omega⟩))]
    have ih' := ih (fun a ha => h a (by
      rcases ha with ⟨h1, h2⟩ | ⟨j, hj, h1, h2⟩
      · exact Or.inl ⟨h1, by omega⟩
      · exact Or.inr ⟨j, by omega, h1, h2⟩))
    simp only [ExportSeg.expUpTo]
    rw [r8, r16, ih', ExportSeg.expSeg_congr (fun a h1 h2 => h a (Or.inr ⟨n, by omega, h1, h2⟩))]

/-- **`Export` up to the push** (5042 … 5810): instruction k (index 10, the `Vec<Vec<u8>>` `{capv, ptrv, ns}`
    whose segment i is `{capf i, qf i, lf i}`, all read in chunks to keep) is staged and dispatched, and its
    segments exported in order (`ExportSeg.segs`): the context becomes `expUpTo … ns`. The handler's words
    are set (M + 56 … M + 112), the cursor advanced (M + 144, M + 280); the allocated chunks of s keep their
    data; the stack from M up is kept apart from the handler's words. Or an allocation fails. -/
theorem mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    {pb S0 S1 : Nat} (fmt : ExportSeg.ExportFmtOk p cap0 env pb S0 S1)
    (x : RefineCtx) (ω : Regs) (μ μ0 : Memory) (s : State)
    {M E n capI : Nat} {ce : Chunk} {Kp : Chunk → Prop} {O : Nat → List UInt8 → Prop}
    (L : LayP S0 S1 M E n ce) (k : Nat) (hk : k < n)
    (capv ptrv ns : Nat) (co : Chunk) (qf lf : Nat → Nat)
    (sD0 : μ0.readN (E + 232 * k) 8 = Num.encodeLE 8 (9223372036854775807 + 10))
    (sv8 : μ0.readN (E + 232 * k + 8) 8 = Num.encodeLE 8 capv)
    (sv16 : μ0.readN (E + 232 * k + 16) 8 = Num.encodeLE 8 ptrv)
    (sv24 : μ0.readN (E + 232 * k + 24) 8 = Num.encodeLE 8 ns)
    (hcv : 24 * capv < 18446744073709551616) (hnc : ns ≤ capv) (hp : ptrv + 24 * ns + 8 ≤ 2147483648)
    (hco : capv ≠ 0 → Kp co)
    (hcoD : ∀ a, ptrv ≤ a → a < ptrv + 24 * ns → InData co a)
    (hw0 : ∀ i, i < ns → μ0.readN (ptrv + 24 * i + 8) 8 = Num.encodeLE 8 (qf i) ∧
      μ0.readN (ptrv + 24 * i + 16) 8 = Num.encodeLE 8 (lf i))
    (hql : ∀ i, i < ns → qf i + lf i ≤ 2147483648)
    (hsd : ∀ i, i < ns → ∀ a, qf i ≤ a → a < qf i + lf i → ∃ d, Kp d ∧ InData d a)
    (hoff : env.exportOffset + x.2.length + ns < 18446744073709551615)
    (st : PInv env pb S0 S1 M E n ce capI μ0 Kp O k ω μ s) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 5042 ω μ x 5810 ω' μ' (ExportSeg.expUpTo env μ0 ptrv x ns) N ∧
      HeapCtx env pb S0 S1 μ' s' ∧ ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 144) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      μ'.readN (M + 280) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      μ'.readN (M + 56) 8 = Num.encodeLE 8 ns ∧ μ'.readN (M + 64) 8 = Num.encodeLE 8 capv ∧
      μ'.readN (M + 72) 8 = Num.encodeLE 8 10 ∧ μ'.readN (M + 96) 8 = Num.encodeLE 8 (24 * ns) ∧
      μ'.readN (M + 104) 8 = Num.encodeLE 8 ptrv ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 56 ∨ (M + 80 ≤ a ∧ a < M + 96) ∨ (M + 112 ≤ a ∧ a < M + 144) ∨
        (M + 200 ≤ a ∧ a < M + 280) ∨ (M + 288 ≤ a ∧ a < M + 304) ∨ (M + 536 ≤ a ∧ a < M + 552) ∨
        M + 608 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5042 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := L.hM
  have hn := L.hn
  obtain ⟨hE0, hE1⟩ := L.hE
  have hEtop := L.hEtop
  have hS1 := st.H.hS1
  have hbT := st.H.hbT
  have hb0 := st.H.hb0
  obtain ⟨hce0, -, hceT⟩ := Decode.VecU8.chunk_in st.H.wf st.hce.1 st.hce.2
  have inE : ∀ a, E ≤ a → a < E + 232 * n → InData ce a := fun a h1 h2 => ⟨by omega, by omega⟩
  have e0 : ∀ a l, E + 232 * k ≤ a → a + l ≤ E + 232 * k + 232 → μ.readN a l = μ0.readN a l :=
    fun a l h1 h2 => Memory.readN_congr (fun j hj => st.data _ (inE _ (by omega) (by omega)))
  have rE : ∀ a, E + 232 * k ≤ a → a < E + 232 * k + 232 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (Decode.VecU8.heap_writable st.H st.hce.1 st.hce.2 (inE a (by omega) (by omega)))
  have wM : ∀ a, M - 48 ≤ a → a < M + 632 → μ.writable a = true := fun a h1 h2 => st.H.st a (by omega) (by omega)
  obtain ⟨ω1, μ1, run1, a1, a5, a8, a144, a280, afr, ard, awr⟩ := xhead (p := p) (P := P)
    (R := refineContractK cap0 env) x ω μ M (E + 232 * k) (E + 232 * n) ⟨by omega, by omega, hM8⟩
    ⟨by omega, by omega⟩ (Or.inl (by omega)) (by omega) (by omega) st.h1 st.cur st.en
    (by rw [e0 _ _ (by omega) (by omega)]; exact sD0) st.c128 st.c136 rE wM
  have l1 : ∀ a l, a + l ≤ M - 48 → μ1.readN a l = μ.readN a l :=
    fun a l h => Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)))
  have s8 : μ1.readN (E + 232 * k + 8) 8 = Num.encodeLE 8 capv := by
    rw [l1 _ _ (by omega), e0 _ _ (by omega) (by omega)]; exact sv8
  have s16 : μ1.readN (E + 232 * k + 16) 8 = Num.encodeLE 8 ptrv := by
    rw [l1 _ _ (by omega), e0 _ _ (by omega) (by omega)]; exact sv16
  have s24 : μ1.readN (E + 232 * k + 24) 8 = Num.encodeLE 8 ns := by
    rw [l1 _ _ (by omega), e0 _ _ (by omega) (by omega)]; exact sv24
  have r1 : ∀ a, E + 232 * k + 8 ≤ a → a < E + 232 * k + 32 → μ1.readable a = true :=
    fun a h1 h2 => by rw [ard]; exact rE a (by omega) (by omega)
  have w1 : ∀ a, M + 56 ≤ a → a < M + 160 → μ1.writable a = true :=
    fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega)
  by_cases hns : ns = 0
  · subst hns
    obtain ⟨ω2, μ2, run2, b1, b72, b64, b104, b96, b56, bfr, brd, bwr⟩ := xa0 (p := p) (P := P)
      (R := refineContractK cap0 env) x ω1 μ1 M (E + 232 * k) capv ptrv ⟨by omega, by omega, hM8⟩ (by omega)
      (Or.inl (by omega)) (by omega) (by omega) a1 a5 a8 s8 s16 s24 r1 w1
    have k2 : ∀ a, a < 2147483648 → μ2.read a = μ.read a :=
      fun a h => by rw [bfr a (by omega) (Or.inl (by omega)), afr a (by omega) (Or.inl (by omega))]
    have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.VecU8.ctx_congr_data st.H st.hce.1
      (fun a h _ => k2 a h) (fun a => by rw [bwr, awr])
    have hx0 : ExportSeg.expUpTo env μ0 ptrv x 0 = x := rfl
    rw [hx0]
    refine Or.inl ⟨ω2, μ2, s, _, run1.trans run2, H2, by rw [b1, a1], ?_, ?_, b56, b64, b72, by simpa using b96,
      b104, fun a h0 h1 h => by rw [bfr a h0 (by omega), afr a h0 (by omega)], fun d hd hu => ⟨hd, fun a ha => ?_⟩⟩
    · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact a144
    · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact a280
    · obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in st.H.wf hd hu
      have ha' := ha; unfold InData at ha'
      exact k2 a (by omega)
  · obtain ⟨ω2, μ2, run2, b1, b5, b72, b64, b104, b96, b56, b152, bfr, brd, bwr⟩ := xa (p := p) (P := P)
      (R := refineContractK cap0 env) x ω1 μ1 M (E + 232 * k) capv ptrv ns ⟨by omega, by omega, hM8⟩ (by omega)
      (Or.inl (by omega)) (by omega) (by omega) hns a1 a5 a8 s8 s16 s24 r1 w1
    have k2 : ∀ a, a < 2147483648 → μ2.read a = μ.read a :=
      fun a h => by rw [bfr a (by omega) (Or.inl (by omega)), afr a (by omega) (Or.inl (by omega))]
    have H2 : HeapCtx env pb S0 S1 μ2 s := Decode.VecU8.ctx_congr_data st.H st.hce.1
      (fun a h _ => k2 a h) (fun a => by rw [bwr, awr])
    have m2 : ∀ a, (∃ d, Kp d ∧ InData d a) → μ2.read a = μ0.read a := fun a ⟨d, hd, ha⟩ => by
      obtain ⟨hds, hdu, hdd⟩ := st.kp d hd
      obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in st.H.wf hds hdu
      have ha' := ha; unfold InData at ha'
      rw [k2 a (by omega), hdd a ha]
    have hP : ∀ a, ptrv ≤ a → a < ptrv + 24 * ns → ∃ d, Kp d ∧ InData d a :=
      fun a h1 h2 => ⟨co, hco (by omega), hcoD a h1 h2⟩
    have rq : ∀ j, j < ns → rdN μ0 (ptrv + 24 * j + 8) 8 = qf j ∧ rdN μ0 (ptrv + 24 * j + 16) 8 = lf j :=
      fun j hj => ⟨rd8 (by have := hql j hj; omega) (hw0 j hj).1, rd8 (by have := hql j hj; omega) (hw0 j hj).2⟩
    have r2 : ∀ j o, j < ns → o + 8 ≤ 24 → rdN μ2 (ptrv + 24 * j + o) 8 = rdN μ0 (ptrv + 24 * j + o) 8 :=
      fun j o hj ho => by
        unfold rdN; rw [Memory.readN_congr (fun i hi => m2 _ (hP _ (by omega) (by omega)))]
    have hX : ∀ a, (ptrv ≤ a ∧ a < ptrv + 24 * ns) ∨ (∃ j, j < ns ∧ rdN μ0 (ptrv + 24 * j + 8) 8 ≤ a ∧
        a < rdN μ0 (ptrv + 24 * j + 8) 8 + rdN μ0 (ptrv + 24 * j + 16) 8) → ∃ d, Kp d ∧ InData d a := by
      intro a ha
      rcases ha with ⟨h1, h2⟩ | ⟨j, hj, h1, h2⟩
      · exact hP a h1 h2
      · rw [(rq j hj).1] at h1; rw [(rq j hj).1, (rq j hj).2] at h2
        exact hsd j hj a h1 h2
    rcases ExportSeg.segs (p := p) (P := P) env cap0 hcap1 hcap0 fmt x μ2 s M ptrv ns
        ⟨hS0M, hMS1, hM2, hM8⟩ (by omega) (by omega)
        (fun j hj => by rw [r2 j 8 hj (by omega), r2 j 16 hj (by omega), (rq j hj).1, (rq j hj).2]; exact hql j hj)
        hoff
        (fun a ha => by
          have ha' : (ptrv ≤ a ∧ a < ptrv + 24 * ns) ∨ (∃ j, j < ns ∧ rdN μ0 (ptrv + 24 * j + 8) 8 ≤ a ∧
              a < rdN μ0 (ptrv + 24 * j + 8) 8 + rdN μ0 (ptrv + 24 * j + 16) 8) := by
            rcases ha with h | ⟨j, hj, h1, h2⟩
            · exact Or.inl h
            · rw [r2 j 8 hj (by omega)] at h1; rw [r2 j 8 hj (by omega), r2 j 16 hj (by omega)] at h2
              exact Or.inr ⟨j, hj, h1, h2⟩
          obtain ⟨d, hd, hda⟩ := hX a ha'
          obtain ⟨hds, hdu, -⟩ := st.kp d hd
          exact ⟨d, hds, hdu, hda⟩)
        ns 0 ω2 μ2 s (by omega) (by omega) H2 (b1.trans a1) (by rw [b5, Nat.mul_zero, Nat.add_zero]) b152
        (fun d hd hu => ⟨hd, fun _ _ => rfl⟩) with
      ⟨ω3, μ3, s3, N3, run3, H3, c1, cfr, ckeep⟩ | ⟨N, hx⟩
    · have h0 : ExportSeg.expUpTo env μ2 ptrv x 0 = x := rfl
      have hc : ExportSeg.expUpTo env μ2 ptrv x ns = ExportSeg.expUpTo env μ0 ptrv x ns :=
        expUpTo_congr ns (fun a ha => m2 a (hX a ha))
      rw [h0, hc] at run3
      have k3 : ∀ a, a < 4294967296 → M ≤ a → (a < M + 160 ∨ M + 200 ≤ a) → (a < M + 552 ∨ M + 608 ≤ a) →
          μ3.read a = μ2.read a := cfr
      refine Or.inl ⟨ω3, μ3, s3, _, run1.trans (run2.trans run3), H3, c1, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun a h0 h1 h => by rw [k3 a h0 h1 (by omega) (by omega), bfr a h0 (by omega), afr a h0 (by omega)],
        fun d hd hu => ?_⟩
      · rw [Memory.readN_congr (fun j hj => (k3 _ (by omega) (by omega) (by omega) (by omega)).trans
          (bfr _ (by omega) (by omega)))]; exact a144
      · rw [Memory.readN_congr (fun j hj => (k3 _ (by omega) (by omega) (by omega) (by omega)).trans
          (bfr _ (by omega) (by omega)))]; exact a280
      · rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega) (by omega))]; exact b56
      · rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega) (by omega))]; exact b64
      · rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega) (by omega))]; exact b72
      · rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega) (by omega))]; exact b96
      · rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega) (by omega) (by omega))]; exact b104
      · obtain ⟨hd3, hk3⟩ := ckeep d hd hu
        refine ⟨hd3, fun a ha => ?_⟩
        obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in st.H.wf hd hu
        have ha' := ha; unfold InData at ha'
        rw [hk3 a ha, k2 a (by omega)]
    · exact Or.inr ⟨_, ExhaustsX.pre (run1.trans run2) hx⟩

/-- Distinct chunks of a well-formed heap have distinct data addresses. -/
theorem addr_ne {s : State} (hwf : WF s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s) (hcd : c ≠ d) :
    c.addr + 32 ≠ d.addr + 32 := fun h => hcd (by
  have ht := hwf.2.2.2.1; unfold TilesOk at ht
  exact Picoalloc.Tiles.addr_inj ht c hc d hd (by omega))

/-- **`Exported(n)` pushed** (5810 … 5868 / 5909), with room or after growing the output: the output
    `{cap, ptr, k}` becomes `{cap', ptr', k + 1}`, its buffer an allocated chunk none of the chunks of s
    other than the old buffer; slots j < k as they were and slot k `Exported(ns)` (`hO`); every other
    allocated chunk keeps its data, the stack from M up is kept apart from M + 248 … M + 272. Or the heap
    is exhausted. -/
theorem push {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P]
    (env : RefineHost.Env) (cap0 : Nat) (hcap1 : 134217728 ≤ cap0) (hcap0 : cap0 < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) {pb S0 S1 M n : Nat} (ns : Nat)
    {O : Nat → List UInt8 → Prop} (k : Nat) (hkn : k < n) (hn : n < 128)
    (hM : S0 + 456 ≤ M ∧ M + 648 ≤ S1 ∧ 2147484104 ≤ M ∧ M % 8 = 0)
    (H : HeapCtx env pb S0 S1 μ s) (h1 : ω[1] = UInt64.ofNat M) (hns : ns < 18446744073709551616)
    (s136 : μ.readN (M + 136) 8 = Num.encodeLE 8 9223372036854775809) (s56 : μ.readN (M + 56) 8 = Num.encodeLE 8 ns)
    (cap ptr : Nat) (vc : μ.readN (M + 248) 8 = Num.encodeLE 8 cap) (vp : μ.readN (M + 256) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (M + 264) 8 = Num.encodeLE 8 k) (hkc : k ≤ cap) (hcapn : cap ≤ 2 * n + 4)
    (hptr : ptr < 2147483648)
    (hold : (cap = 0 ∧ ptr = 8) ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * cap + 31) / 32 + 1)
    (hout : ∀ j, j < k → O j (μ.readN (ptr + 232 * j) 232))
    (hO : ∀ (μ' : Memory) (a : Nat), μ'.readN a 8 = Num.encodeLE 8 (9223372036854775807 + 20) →
      μ'.readN (a + 8) 8 = Num.encodeLE 8 ns → O k (μ'.readN a 232)) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N cap' ptr' : Nat),
      FreeStepsH p (refineContractK cap0 env) 5810 ω μ x (if ns = 0 then 5909 else 5868) ω' μ' x N ∧
      HeapCtx env pb S0 S1 μ' s' ∧ ω'[1] = UInt64.ofNat M ∧
      μ'.readN (M + 248) 8 = Num.encodeLE 8 cap' ∧ μ'.readN (M + 256) 8 = Num.encodeLE 8 ptr' ∧
      μ'.readN (M + 264) 8 = Num.encodeLE 8 (k + 1) ∧ k + 1 ≤ cap' ∧ cap' ≤ 2 * n + 4 ∧ ptr' < 2147483648 ∧
      (∃ c ∈ chunks s', c.addr + 32 = ptr' ∧ c.used = true ∧ c.size = (232 * cap' + 31) / 32 + 1 ∧
        ∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d ≠ c) ∧
      (∀ j, j < k + 1 → O j (μ'.readN (ptr' + 232 * j) 232)) ∧
      (∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 248 ∨ M + 272 ≤ a) → μ'.read a = μ.read a)) ∨
    ∃ N, ExhaustsX env cap0 pb p 5810 ω μ x N := by
  obtain ⟨hS0M, hMS1, hM2, hM8⟩ := hM
  have hS1 := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  by_cases hroom : k = cap
  · subst hroom
    have hold' : k = 0 ∨ ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true ∧ c.size = (232 * k + 31) / 32 + 1 := by
      rcases hold with ⟨h0, _⟩ | h
      · exact Or.inl h0
      · exact Or.inr h
    rcases push_grow (p := p) (P := P) (hb := hb) env cap0 hcap1 hcap0 x ω μ s M ptr k ns pb S0 S1 H hold'
        (by omega) hns ⟨hS0M, hMS1, hM2, hM8⟩ (by omega) h1 vc vp vl s136 s56 with
      ⟨q, s', ω', μ', run, e1, ecap, eptr, elen, hnew, emove, e0, e8, H', keep, fresh, efr⟩ | hx
    · obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H'.wf hnew rfl
      simp only at hq0 hqT
      have hb0' := H'.hb0
      have hbT' := H'.hbT
      refine Or.inl ⟨ω', μ', s', _, max (2 * k) 4, q, run, H', e1, ecap, eptr, elen, by omega, by omega, by omega,
        ⟨_, hnew, by simp; omega, rfl, rfl, fun d hd hu hne h => ?_⟩, fun j hj => ?_, keep, efr⟩
      · have := fresh d hd hu hne
        rw [h] at this; simp at this; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [PassLoop.slot_eq emove hj]; exact hout j hj
        · exact hO μ' _ e0 e8
    · exact Or.inr ⟨_, hx⟩
  · obtain ⟨c, hc, hca, hcu, hcs⟩ := hold.resolve_left (fun h => hroom (by omega))
    obtain ⟨hc0, -, hcT⟩ := Decode.VecU8.chunk_in H.wf hc hcu
    have hcs' : 232 * cap + 32 ≤ 32 * c.size := by rw [hcs]; omega
    obtain ⟨ω', μ', run, b1, b0, b8, b264, bfr, brd, bwr⟩ := push_room (p := p) (P := P)
      (R := refineContractK cap0 env) x ω μ M cap ptr k ns ⟨by omega, by omega, hM8⟩ hroom (by omega) (by omega)
      hns (by omega) h1 vc vp vl s136 s56 (fun a h1 h2 => Memory.readable_of_writable (H.st a (by omega) (by omega)))
      (fun a h1 h2 => Decode.VecU8.heap_writable H hc hcu ⟨by omega, by omega⟩)
      (fun a h1 h2 => H.st a (by omega) (by omega))
    have H' : HeapCtx env pb S0 S1 μ' s := Decode.VecU8.ctx_congr_data H hc
      (fun a ha h => bfr a (by omega) (by omega) (Or.inl (by omega))) bwr
    refine Or.inl ⟨ω', μ', s, _, cap, ptr, run, H', b1.trans h1,
      by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (Or.inl (by omega)))]; exact vc,
      by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (Or.inl (by omega)))]; exact vp,
      b264, by omega, hcapn, hptr, ⟨c, hc, hca, hcu, hcs, fun d hd hu hne h => hne (by rw [h, hca])⟩,
      fun j hj => ?_, fun d hd hu hne => ⟨hd, fun a ha => ?_⟩, fun a h0 h1 h => bfr a h0 (by omega) (by omega)⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Memory.readN_congr (fun i hi => bfr _ (by omega) (by omega) (Or.inl (by omega)))]; exact hout j hj
      · exact hO μ' _ b0 b8
    · have hdc : d ≠ c := fun h => hne (by rw [h, hca])
      have hdj := Decode.VecU8.data_disj H.wf hd hc hdc ha
      obtain ⟨hd0, -, hdT⟩ := Decode.VecU8.chunk_in H.wf hd hu
      have ha' := ha; unfold InData at ha'
      exact bfr a (by omega) (by omega) (Or.inl (by omega))

end Services.Bootstrap.Refine.ExportElem
