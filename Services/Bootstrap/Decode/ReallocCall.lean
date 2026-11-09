import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Decode.ReallocKeepAll
import Services.Bootstrap.Decode.VecU8Heap

/-!
# `realloc` under `refineContractK cap`, and one call of its wrapper on the allocator's context

`ReallocKeepAll`'s fallback chain (`fallback_tail_heap_keep` … `realloc_wrap_cases_keep`) is stated
under `refineContract` (cap = `hostCostMax`), so a heap growth there is limited to 14 pages
(`pb ≤ ph + 14`). This file restates it under `refineContractK cap` for any cap ≥ `hostCostMax`
(names with a `K`): the fallback's `alloc` may grow the heap by any amount within the cap, and every
other step lifts from `refineContract` (`FreeStepsH.weaken`, `refineContract_le`). Then
`realloc_call`: one call of the `realloc` wrapper (40701 → 40821) on `HeapCtx`, cap ≥ 2²⁷.
-/

namespace Services.Bootstrap.Decode.ReallocCall

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.ReallocKeepAll Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- A run under `refineContract` is a run under `refineContractK cap`, cap ≥ `hostCostMax`. -/
theorem liftG {X : Type} {p : ByteArray} {env : HeapHost X} {cap : Nat} (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616) {i ω μ x i' ω' μ' x' n}
    (run : FreeStepsH p (env.rel hostCostMax) i ω μ x i' ω' μ' x' n) :
    FreeStepsH p (env.rel cap) i ω μ x i' ω' μ' x' n :=
  run.weaken (fun _ _ _ _ _ _ _ hr => env.le cap hcap1 hcap _ _ _ _ _ _ _ hr)

/-- `liftG` for the refine contract (`refineHeap env`). -/
theorem lift {p : ByteArray} {env : RefineHost.Env} {cap : Nat} (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616) {i ω μ x i' ω' μ' x' n}
    (run : FreeStepsH p (refineContract env) i ω μ x i' ω' μ' x' n) :
    FreeStepsH p (refineContractK cap env) i ω μ x i' ω' μ' x' n :=
  liftG (p := p) (env := (refineHeap env)) (cap := cap) hcap1 hcap run

theorem fallback_tail_heap_keepKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat) (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p (env.rel cap) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨hkeep, hnew, hq32, hb1⟩ := alloc_keeps hwf h
  by_cases hng : s1.allocated = s.allocated
  · obtain ⟨ω', μ', dat, run, rep, wf, fo, ww, stk, k7, k0, k1, k5, k6, kp⟩ := fallback_tail'_keep (p := p) (P := P)
      (R := env.rel cap) x ω μ (grow := growTo pb) (hb := hb) s s1 sp ptr req q u v5 v6 hwf hrep hfo hc
      hu hur h hng h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA hHTs hHT hS hw
    exact ⟨ω', μ', dat, run.mono (by omega), rep, wf, fo,
      ⟨ph, HeapPages.of_eq hp ww, by rw [hb1, hng]; exact hHT, Nat.le_refl _, hhb⟩,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, k7, k0, k1, k5, k6, kp⟩
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨hc1, hdis⟩ := hkeep c hcm hcu
  have hwf1 : WF s1 := alloc_wf hwf h
  have hfo1 : FirstOk s1 := alloc_first hwf hfo h
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcsz : c.size = u + 1 := chunk_size_usable hcm hca hcu hu hcl.2.2
  -- the call to `alloc_impl`, which grows the heap
  obtain ⟨ω1, μ1, r1, a5, a8, a9, a10, a0, a104, fr1, ww1, g1⟩ := rf_call (p := p) (P := P)
    (R := env.rel cap) x ω μ sp ptr 1 req h1 h7 h8 h9 h10 (by omega) (by decide) (by omega) (by omega)
    hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, -, e7, e0, e5, e6, e1, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, hk2⟩ :=
    alloc_refines_growK_hdrG (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω1 μ1 s s1 sp req q pb ph hwf rep1 hbd h48
      hhb hbs h hng (by rw [fget g1 1 (by decide) (by decide)]; exact h1)
      (by rw [fget g1 7 (by decide) (by decide)]; exact h7) a8 a9 a10 hsp (by omega) hb0 hbT hA hfo hcost hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp ww1) (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHT
  have rj := al_ret_realloc (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (by rw [e0, a0])
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => (stk2 _ (by omega) (by omega)).trans (fr1 _ (by omega) (Or.inr (by omega)))
  have h104 : rdN μ2 (sp + 104) 8 = 196792 := by
    rw [← a104]; exact rdN_frame fun j hj => stk2 _ (by omega) (by omega)
  obtain ⟨ω3, μ3, dat3, r3, rep3, wf3, fo3, ww3, stk3, k7, k0, k1, k5, k6, kp3⟩ := fallback_after_keep (p := p) (P := P)
    (R := env.rel cap) x ω2 μ2 s1 sp ptr q u req v5 v6 hwf1 rep2 hfo1 ⟨c, hc1, hca, hcu, hcsz, hdis⟩ hnew
    hq32 (by omega) (by rw [e1, fget g1 1 (by decide) (by decide)]; exact h1) e7 (by rw [e5]; exact a5)
    (by rw [e6, fget g1 6 (by decide) (by decide)]; exact h6) h104
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    hsp hsp1 hsp8 (by rw [hb1]; exact hba) (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT)
    hE' hS (HeapPages.wrAt hpH hpb hst2)
  have dat : μ3.readN q (32 * u) = μ.readN ptr (32 * u) := by
    rw [dat3, hk2.readN fun j hj => off_hdr_data hwf1 (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hc1
      (by omega) (by omega)]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  refine ⟨ω3, μ3, dat, (((r1.trans r2).trans rj).trans r3).mono (by omega), rep3, wf3, fo3,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a h1 h2 => ((stk3 a h1 (by omega)).trans (stk2 a h1 (by omega))).trans (fr1 a h1 (Or.inr (by omega))),
    k7, k0, k1, k5, k6, fun a ha => ?_⟩
  obtain ⟨c', hc'm, hc'u, hc'p, hin⟩ := ha
  obtain ⟨hc'1, hc'd⟩ := hkeep c' hc'm hc'u
  have ha1 : OthersData s1 ptr a := ⟨c', hc'1, hc'u, hc'p, hin⟩
  have hbb : s1.base = s.base := hb1
  have := others_lt hwf1 (by rw [hbb]; exact hb0) (by rw [hbb]; exact hbT) ha1
  unfold InData at hin
  rw [kp3 a ha1 (by omega), keep_of_hkeep hwf1 (by rw [hbb]; exact hb0) (by rw [hbb]; exact hbT)
    (fun h hh => Or.inl hh) hk2.hkeep a ha1]
  exact fr1 a (by omega) (Or.inl (by omega))

/-- `fallback_tail_heap_keepKG` for the refine contract (`refineHeap env`). -/
theorem fallback_tail_heap_keepK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat) (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p (refineContractK cap env) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  fallback_tail_heap_keepKG (p := p) (P := P) (refineHeap env) cap hcap1 hcap x ω μ (hb := hb) s s1 sp ptr req q u v5 v6 pb ph hwf hrep hfo hc hu hur hbd h48 hhb hbs h hcost h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

theorem fallback_refines_heap_keepKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat) (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (env.rel cap) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  refine ⟨realloc_fallback hr hnone ha, ?_⟩
  obtain ⟨ω1, μ1, r1, rep1, hp1, hst1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_entryG
    (p := p) (P := P) env x ω μ s sp ptr req pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone h1 h8 h7 h10
    (by omega) hsp1 hb0 hbT hA hHT ⟨by omega, by omega⟩ hSb hp hst
  replace r1 := liftG hcap1 hcap r1
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, dat2, r2, rep2, wf2, fo2, hpH, hst2, stk2, e7, e0, e1, e5, e6, kp2⟩ := fallback_tail_heap_keepKG (p := p)
    (P := P) env cap hcap1 hcap x ω1 μ1 (hb := hb) s s1 (sp - 152) ptr req q (usable s ptr) ω[5].toNat ω[6].toNat pb ph hwf
    rep1 hfo hc rfl hr hbd h48 hhb hbs ha hcost a1 a7 a8 (by rw [a9]; exact h9) a10 a6 (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) (by omega) hba hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  have hdl := data_lt hwf hbT hc
  have dat : μ2.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    rw [dat2]; exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  refine ⟨ω2, μ2, dat, (r1.trans r2).mono (by omega), rep2, wf2, fo2, hpH, hst2,
    fun a h1 h2 => (stk2 a h1 (by omega)).trans (fr1 a h1 (Or.inr h2)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat], fun a ha => ?_⟩
  have := others_lt hwf hb0 hbT ha
  rw [kp2 a ha]; exact fr1 a (by omega) (Or.inl (by omega))

/-- `fallback_refines_heap_keepKG` for the refine contract (`refineHeap env`). -/
theorem fallback_refines_heap_keepK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat) (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (refineContractK cap env) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  fallback_refines_heap_keepKG (p := p) (P := P) (refineHeap env) cap hcap1 hcap x ω μ (hb := hb) s s1 sp ptr req q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h8 h7 h9 h10 h0 hsp hsp1 hsp8 hba hb0 hbT hA hfo (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

theorem realloc_wrap_fallback_keepKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat) (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hal : (al + 31) / 32 = 1 := by omega
  rw [hal]
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a8, a7, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := env.rel cap) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      (by omega) (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨e, ω2, μ2, dat2, r2, rep2, wf2, fo2, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, e7, e0, e1, e5, e6, kp2⟩ :=
    fallback_refines_heap_keepKG (p := p) (P := P) env cap hcap1 hcap x ω1 μ1 (hb := hb) s s1 (sp - 16) ptr ((size + 31) / 32) q pb ph
      hwf rep1 hc hr hr1 hbd h48 hhb hbs hnone ha hcost a1 a8 a7 (by rw [a9, hal]) a10 a0 (by omega) (by omega)
      (by omega) hba hb0 hbT hA hfo hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hpH hpb hst2)
  have hb' : (free s1 ptr).base = s.base := free_base'.trans (alloc_keeps hwf ha).2.2.2
  have hdl := data_lt hwf hbT hc
  have hq : 206864 ≤ q ∧ q + 32 * usable s ptr < 2147483648 := by
    obtain ⟨-, hnew, hq32, hb1⟩ := alloc_keeps hwf ha
    have ht1 := (alloc_wf hwf ha).2.2.2.1
    unfold TilesOk at ht1
    have := ht1.mem_lt _ hnew
    have htop1 : s1.top = s1.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    simp only at this; omega
  have dat : μ3.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    have e3 : μ3.readN q (32 * usable s ptr) = μ2.readN q (32 * usable s ptr) :=
      readN_congr2 fun j hj => fr3 _ (by omega) (by omega)
    rw [e3, dat2]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨e, ω3, μ3, dat, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]
  · intro a ha
    obtain ⟨hl1, hl2⟩ := others_lt hwf hb0 hbT ha
    rw [fr3 a (by omega) (by omega), kp2 a ha]
    exact fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))

/-- `realloc_wrap_fallback_keepKG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_fallback_keepK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat) (hcap1 : 2000 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        (∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_fallback_keepKG (p := p) (P := P) (refineHeap env) cap hcap1 hcap x ω μ (hb := hb) s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

open Services.Bootstrap.Decode.ReallocOk Services.Bootstrap.Decode.VecU8 in
/-- **`realloc_wrap_cases_hdataG`, keeping the other chunks' data**: as `realloc_wrap_cases_hdataG`, and
    whenever the model's `realloc` returns a block, every octet of the data of an allocated chunk of
    `s` other than ptr's is as it was. -/
theorem realloc_wrap_cases_keepKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ 0 → μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
          μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32))) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ s'.base = s.base ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ∀ a, OthersData s ptr a → μ'.read a = μ.read a) := by
  have hwr := HeapPages.wrAt hp hhb hst
  have hpb20 : pb < 1048576 := by omega
  have hal : al + 31 < 68719476736 := by omega
  by_cases hin : (size + 31) / 32 ≤ usable s ptr ∧ size ≠ 0
  · -- in place (the same usable size, or shrunk)
    obtain ⟨s', e, ω', μ', dat, run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6, kp⟩ :=
      realloc_wrap_inplace_keep (p := p) (P := P) (R := env.rel cap) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al size hwf hrep hc
        hin.2 hin.1 h1 h7 h9 h10 hal (by omega) (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_right hin.1]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [e] at hrr; cases hrr; obtain ⟨eb, ea⟩ := realloc_inplace_state hin.1 (by omega) e; exact ⟨e7, rep, wf, fo, eb, ph, HeapPages.of_eq hp ww, by rw [eb, ea]; exact hHT, Nat.le_refl _, hhb⟩,
      fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
  by_cases hs0 : size = 0
  · -- to size 0: freed, null
    subst hs0
    obtain ⟨e, ω', μ', run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6, kp⟩ :=
      realloc_wrap_zero_keep (p := p) (P := P) (R := env.rel cap) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al hwf hrep hc
        (hz rfl) h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr hn => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn,
      fun r s'' b hrr _ hn2 => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn2,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr
        exact ⟨e7, rep, wf, fo, free_base', ph, HeapPages.of_eq hp ww, by rw [free_base', free_allocated]; exact hHT, Nat.le_refl _, hhb⟩,
      fun hrr => (by rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
  have hr : usable s ptr < (size + 31) / 32 := by omega
  cases hg : growInplace (growTo pb) s ptr ((size + 31) / 32) with
  | some s' =>
    by_cases hng : s'.allocated = s.allocated
    · -- grown in place
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6, kp⟩ :=
        realloc_wrap_grow_keep (p := p) (P := P) (R := env.rel cap) (hb := hb) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 hg hng
          h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo hl hHT ⟨by omega, by omega⟩ hwr
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
        fun r s'' b hrr => by
          rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, growInplace_base hg, ph, HeapPages.of_eq hp ww, by rw [growInplace_base hg, hng]; exact hHT, Nat.le_refl _, hhb⟩,
        fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
    · -- grown in place, the heap grown
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, hB, hph, hpb⟩, hst', stk, e0, e1, e5, e6, kp⟩ :=
        realloc_wrap_grow_heapK_keepG (p := p) (P := P) (hb := hb) env cap hcap x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs hg
          hng h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo
          (by have := growInplace_pages hr hg hng; omega) hl hHT ⟨by omega, by omega⟩ hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, growInplace_base hg, h', hpH, hB, hph, hpb⟩,
        fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
  | none =>
    cases ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s with
    | some qs =>
      obtain ⟨q, s1⟩ := qs
      have hc1 : 275 + 121 * (pagesOf (s.base + 32 * s1.allocated) - ph) ≤ cap := by
        by_cases hng : s1.allocated = s.allocated
        · rw [hng]; have := pagesOf_le hHT; omega
        · have := alloc_pages hwf ha hng; omega
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, hB, hph, hpb⟩, hst', stk, e0, e1, e5, e6, kp⟩ :=
        realloc_wrap_fallback_keepKG (p := p) (P := P) (hb := hb) env cap (by omega) hcap x ω μ s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha hc1 h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr _ _ => by rw [e] at hrr; cases hrr; exact dat,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, by rw [free_base', (alloc_block hwf hbT ha).1], h', hpH, by rw [free_base', free_allocated]; exact hB, hph, hpb⟩,
        fun hrr => (by rw [e] at hrr; cases hrr), fun _ _ _ _ => kp⟩
    | none =>
      obtain ⟨e, ω', μ', run, rep, e7, cl, hp', hst', fr, -, e0, e1, e5, e6⟩ :=
        realloc_wrap_fallback_failG (p := p) (P := P) (hb := hb) env x ω μ s sp ptr al size pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha h1 h7 h9 h10 hal1 hal2 hsp hsp1 hb0 hbT hA hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr => (by rw [e] at hrr; cases hrr),
      fun r s'' b hrr => (by rw [e] at hrr; cases hrr),
      (liftG (by omega) hcap run).mono (by omega), cl, hst',
        fun a h1 h2 => fr a h1 (Or.inr h2) (Or.inr (by omega)) (Or.inr (by omega)), e0, e1, e5, e6,
        fun r s'' b hrr => (by rw [e] at hrr; cases hrr), fun _ => ⟨e7, rep, hp'⟩,
        fun r s'' b hrr => (by rw [e] at hrr; cases hrr)⟩

open Services.Bootstrap.Decode.ReallocOk Services.Bootstrap.Decode.VecU8 in
/-- `realloc_wrap_cases_keepKG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_cases_keepK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat) (hcap1 : 134217728 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ 0 → μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
          μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32))) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ s'.base = s.base ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ∀ a, OthersData s ptr a → μ'.read a = μ.read a) :=
  realloc_wrap_cases_keepKG (p := p) (P := P) (refineHeap env) cap hcap1 hcap x ω μ (hb := hb) s sp ptr al size pb ph hwf hrep hc hr1 hz hbd h48 hhb hbs h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **`realloc` keeps the other allocated chunks** (alignment one unit, a nonzero request, the data
    address of an allocated chunk): every allocated chunk of `s` other than ptr's is a chunk of the
    new state. -/
theorem realloc_keeps_used {grow : Grow} {hb : Nat} {s s' : State} {ptr newReq p : Nat} {cp : Bool} (hwf : WF s)
    (hptr : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (h0 : newReq ≠ 0)
    (h : realloc grow hb s ptr 1 newReq = some (p, s', cp)) :
    ∀ d ∈ chunks s, d.used = true → d.addr + 32 ≠ ptr → d ∈ chunks s' := by
  intro d hd hdu hda
  obtain ⟨c, hc, h1, h2⟩ := hptr
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  have hc' : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at h1 h2 ⊢; subst h2; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hc'] at hcs
  have hdpp : d ∈ pre ∨ d ∈ post := by
    rw [hcs] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact Or.inl hd
    · rcases List.mem_cons.mp hd with hd | hd
      · subst hd; simp only at hda; omega
      · exact Or.inr hd
  have hcur : wordSize (s.hdr (ptr - 32)).size = c.size := by
    have := chunks_hdr c hc
    rw [show c.addr = ptr - 32 by omega, h2] at this
    rw [this, wordSize_sizeWord]
  unfold realloc usable at h
  rw [hcur] at h
  by_cases e1 : newReq = c.size - 1
  · simp only [e1, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact hd
  by_cases e3 : newReq < c.size - 1
  · simp only [e1, h0, e3, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨R, post0, rest, hpo, hR, hch, -⟩ := shrink_ok (cur := c.size) (newReq := newReq) hwf hcs (by omega)
    rw [hch]
    rcases hdpp with hdp | hdp
    · exact List.mem_append_left _ hdp
    · rw [hpo] at hdp
      rcases List.mem_append.mp hdp with hdp | hdp
      · have := hR d hdp; rw [hdu] at this; simp at this
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hdp))
  simp only [e1, h0, e3, ↓reduceIte] at h
  cases hg : growInplace grow s ptr newReq with
  | some s2 =>
    simp only [hg, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨e, post', rest, hpo, heu, -, hch⟩ := growInplace_grows hwf hcs (by omega) hg
    rw [hch]
    rcases hdpp with hdp | hdp
    · exact List.mem_append_left _ hdp
    · rw [hpo] at hdp
      rcases List.mem_cons.mp hdp with hdp | hdp
      · subst hdp; rw [hdu] at heu; simp at heu
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hdp))
  | none =>
    simp only [hg] at h
    cases ha : alloc grow hb 1 newReq s with
    | none => simp [ha] at h
    | some r =>
      obtain ⟨p1, s1⟩ := r
      simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      have hw1 := alloc_wf hwf ha
      have hcold := HeapFrame.alloc_keeps_used hwf ha _ hc h2
      have hd1 := HeapFrame.alloc_keeps_used hwf ha d hd hdu
      rw [hc'] at hcold
      obtain ⟨pr1, po1, hcs1⟩ := List.append_of_mem hcold
      obtain ⟨pre0, L, R, post0, M, total, hpr, hpo, hLR, hchF, -, -⟩ := free_ok hw1 hcs1
      rw [hchF]
      rw [hcs1, hpr, hpo] at hd1
      simp only [List.mem_append, List.mem_cons] at hd1 ⊢
      rcases hd1 with (hd1 | hd1) | hd1 | hd1 | hd1
      · exact Or.inl hd1
      · have := hLR _ (List.mem_append_left _ hd1); rw [hdu] at this; simp at this
      · subst hd1; simp only at hda; omega
      · have := hLR _ (List.mem_append_right _ hd1); rw [hdu] at this; simp at this
      · exact Or.inr (Or.inr hd1)

open Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.ReallocOk Picoalloc in
/-- **One call of the `realloc` wrapper** (40701 → 40821) on the allocator's context `HeapCtx`,
    under `refineContractK cap` (cap ≥ 2²⁷, so any growth of the heap is within it): with ω₇ = ptr
    the data address of an allocated chunk, ω₉ = align (1 … 32) and ω₁₀ = size > 0 (the new size in
    octets), either the model's `realloc` gives `(r, s', b)` and the wrapper returns r with the
    context kept for `s'`, the old block's first min(usable, ⌈size/32⌉)·32 octets at r, every other
    allocated chunk of `s` still a chunk of `s'` with its data, r's chunk allocated of exactly
    ⌈size/32⌉ + 1 units, the stack from sp up, memory below 196608 and the stack's access kept; or
    the model's `realloc` fails and the wrapper returns null with the context kept for `s`. The heap
    base is 8-aligned (`hba`; `HeapCtx` does not record it). -/
theorem realloc_callG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : X) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp ptr al size pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hsz : 0 < size) (hr1 : (size + 31) / 32 < 33554431) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp ∧ sp % 8 = 0) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) :
    (∃ r s' b ω' μ', realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) ∧
      FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      ω'[7] = UInt64.ofNat r ∧ HeapCtxC env.code pb S0 S1 μ' s' ∧
      μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
        μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32)) ∧
      (∀ c ∈ chunks s, c.used = true → c.addr + 32 ≠ ptr → c ∈ chunks s') ∧
      (∃ c ∈ chunks s', c.addr + 32 = r ∧ c.used = true ∧ c.size = (size + 31) / 32 + 1) ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, S0 ≤ a → μ'.writable a = μ.writable a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      ω'[7] = UInt64.ofNat 0 ∧ HeapCtxC env.code pb S0 S1 μ' s ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  have hSb := H.hSb
  obtain ⟨ω', μ', dat, -, run, cl, hst', stk, e0, e1, e5, e6, hsome, hnone, kp⟩ :=
    realloc_wrap_cases_keepKG (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s sp ptr al size pb ph H.wf H.rep
      hc hr1 (fun h => absurd h (by omega)) H.bd h48 hhb (by omega) h1 h7 h9 h10 hal1 hal2 hsp.1 (by omega) hsp.2
      hba H.hb0 H.hbT H.hA H.fo H.lock hHTs hHT hS hSb hp H.st
  obtain ⟨kp', kr⟩ := HeapHost.keepRO H.bd run
  have ro' : ∀ a, a < 196608 → μ'.writable a = false := fun a ha => by
    have := H.ro a ha
    unfold Memory.writable at this ⊢
    rw [kp' _ (Or.inl (by unfold pageSize; omega))]; exact this
  have low : ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a := fun a ha => by
    refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha), ?_⟩
    unfold Memory.readable
    rw [kp' _ (Or.inl (by unfold pageSize; omega))]
  have wr : ∀ a, S0 ≤ a → μ'.writable a = μ.writable a := fun a ha => by
    unfold Memory.writable
    rw [kp' _ (Or.inr (by unfold pageSize; omega))]
  have hal : (al + 31) / 32 = 1 := by omega
  have h0 : (size + 31) / 32 ≠ 0 := by omega
  cases hrl : realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) with
  | some t =>
    obtain ⟨r, s', b⟩ := t
    obtain ⟨e7, rep', wf', fo', hbase, h', hpH, hE', hph, hpb⟩ := hsome r s' b hrl
    have hrl1 := hrl
    rw [hal] at hrl1
    obtain ⟨c', hc'm, hc'a, hc'u, hc's⟩ := realloc_chunk H.wf H.hbT hc h0 hrl1
    have hr0 : r ≠ 0 := by
      have := (VecU8.chunk_in wf' hc'm hc'u).1
      have hb0 := H.hb0
      omega
    left
    refine ⟨r, s', b, ω', μ', rfl, run, e7,
      ⟨wf', rep', fo', cl, by rw [hbase]; exact H.hb0, by rw [hbase]; exact H.hbT, by omega, H.bd,
        ⟨h', by omega, hpb, hpH, by omega, hE'⟩, hSb, hS1, hst', ro'⟩,
      dat r s' b hrl hr0, realloc_keeps_used H.wf hc h0 hrl1, ⟨c', hc'm, hc'a, hc'u, hc's⟩,
      kp r s' b hrl, stk, low, wr, e0, e1, e5, e6⟩
  | none =>
    obtain ⟨e7, rep', hp'⟩ := hnone hrl
    right
    exact ⟨rfl, ω', μ', run, e7, ⟨H.wf, rep', H.fo, cl, H.hb0, H.hbT, H.hA, H.bd,
      ⟨ph, h48, hhb, hp', hHTs, hHT⟩, hSb, hS1, hst', ro'⟩, stk, e0, e1, e5, e6⟩

open Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.ReallocOk Picoalloc in
/-- `realloc_callG` for the refine contract (`refineHeap env`). -/
theorem realloc_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    {hb : Nat} (s : State) (sp ptr al size pb S0 S1 : Nat) (H : HeapCtx env pb S0 S1 μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hsz : 0 < size) (hr1 : (size + 31) / 32 < 33554431) (hba : s.base % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp ∧ sp % 8 = 0) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) :
    (∃ r s' b ω' μ', realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) ∧
      FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      ω'[7] = UInt64.ofNat r ∧ HeapCtx env pb S0 S1 μ' s' ∧
      μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
        μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32)) ∧
      (∀ c ∈ chunks s, c.used = true → c.addr + 32 ≠ ptr → c ∈ chunks s') ∧
      (∃ c ∈ chunks s', c.addr + 32 = r ∧ c.used = true ∧ c.size = (size + 31) / 32 + 1) ∧
      (∀ a, OthersData s ptr a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, S0 ≤ a → μ'.writable a = μ.writable a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      ω'[7] = UInt64.ofNat 0 ∧ HeapCtx env pb S0 S1 μ' s ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) :=
  realloc_callG (p := p) (P := P) (refineHeap env) cap hcap1 hcap x ω μ (hb := hb) s sp ptr al size pb S0 S1 H hc hsz hr1 hba h1 h7 h9 h10 hal1 hal2 hsp hS

end Services.Bootstrap.Decode.ReallocCall
