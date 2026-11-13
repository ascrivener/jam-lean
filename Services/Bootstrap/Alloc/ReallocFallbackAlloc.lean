import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.ReallocFallbackCopy
import Services.Bootstrap.Alloc.AllocFailRefines

/-!
# The binary's `realloc_impl`: the fallback, for every outcome of its `alloc`

From 43259 the fallback calls `alloc_impl` (alignment one unit). By the model's `alloc` (under
`refineContract`, `grow` the host's `growTo pb`, GP Appendix B Ω_♊):

* `some (q, s₁)` without growing the heap: `fallback_tail'`, as `fallback_tail` for any usable
  size (the copy through `rf_memcpy`);
* `some (q, s₁)` growing the heap, or not: `fallback_tail_heap`, under `HeapPages`;
* `none`: `fallback_tail_fail` — `alloc_impl` returns null, `realloc_impl` returns null (43326) and
  memory changes only in the stack frame, so the old block and the whole heap are untouched.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- An allocated chunk's size from its usable size. -/
theorem chunk_size_usable {s : State} {c : Chunk} {ptr u : Nat} (hcm : c ∈ chunks s) (hca : c.addr + 32 = ptr)
    (hcu : c.used = true) (hu : usable s ptr = u) (h1 : 0 < c.size) : c.size = u + 1 := by
  have := chunks_hdr c hcm; rw [hcu] at this
  rw [← hu]; unfold usable; rw [← hca] at *; simp only [Nat.add_sub_cancel] at this ⊢
  rw [this, wordSize_sizeWord]; omega

/-- An allocated chunk's data lies in the heap, below 2³¹. -/
theorem data_lt {s : State} {ptr : Nat} (hwf : WF s) (hbT : s.base + 1073741824 < 2147483648)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) :
    s.base + 32 ≤ ptr ∧ ptr + 32 * usable s ptr < 2147483648 := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := chunk_size_usable hcm hca hcu rfl hcl.2.2
  omega

/-- **`fallback_tail'` with the copy**: as `fallback_tail'`, and the new block q's first u·32
    octets are the old block's (at ptr) as they were at 43259: `alloc_impl` (`alloc_refines_hdr`)
    changes only headers, outside the old chunk's data. -/
theorem fallback_tail'_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (h : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', μ'.readN q (32 * u) = μ.readN ptr (32 * u) ∧
      FreeStepsH p R 43259 ω μ x 40805 ω' μ' x (64 * u + 1000) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨hkeep, hnew, hq32, hb1⟩ := alloc_keeps hwf h
  obtain ⟨hc1, hdis⟩ := hkeep c hcm hcu
  have hwf1 : WF s1 := alloc_wf hwf h
  have hfo1 : FirstOk s1 := alloc_first hwf hfo h
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcsz : c.size = u + 1 := chunk_size_usable hcm hca hcu hu hcl.2.2
  -- the call to `alloc_impl`
  obtain ⟨ω1, μ1, r1, a5, a8, a9, a10, a0, a104, fr1, ww1, g1⟩ := rf_call (p := p) (P := P) (R := R) x ω μ
    sp ptr 1 req h1 h7 h8 h9 h10 (by omega) (by decide) (by omega) (by omega) hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, -, e7, e0, e5, e6, e1, ww2, stk2, hk2⟩ :=
    alloc_refines_hdr (p := p) (P := P) (R := R) x ω1 μ1 s s1 sp req q hwf rep1 h hng
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [fget g1 7 (by decide) (by decide)]; exact h7)
      a8 a9 a10 hsp (by omega) hb0 hbT hA hfo hHTs ⟨by omega, by omega⟩ hHT (hw.of_eq ww1)
  have rj := al_ret_realloc (p := p) (P := P) (R := R) x ω2 μ2 (by rw [e0, a0])
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => (stk2 _ (by omega) (by omega)).trans (fr1 _ (by omega) (Or.inr (by omega)))
  have h104 : rdN μ2 (sp + 104) 8 = 196792 := by
    rw [← a104]; exact rdN_frame fun j hj => stk2 _ (by omega) (by omega)
  obtain ⟨ω3, μ3, dat3, r3, rep3, wf3, fo3, ww3, stk3, k7, k0, k1, k5, k6⟩ := fallback_after_data (p := p) (P := P) (R := R)
    x ω2 μ2 s1 sp ptr q u req v5 v6 hwf1 rep2 hfo1 ⟨c, hc1, hca, hcu, hcsz, hdis⟩ hnew hq32 (by omega)
    (by rw [e1, fget g1 1 (by decide) (by decide)]; exact h1) e7 (by rw [e5]; exact a5)
    (by rw [e6, fget g1 6 (by decide) (by decide)]; exact h6) h104
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    hsp hsp1 hsp8 (by rw [hb1]; exact hba) (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT)
    (by rw [hb1, hng]; exact hHT) hS ((hw.of_eq ww1).of_eq ww2)
  have dat : μ3.readN q (32 * u) = μ.readN ptr (32 * u) := by
    rw [dat3, hk2.readN fun j hj => off_hdr_data hwf1 (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hc1
      (by omega) (by omega)]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  exact ⟨ω3, μ3, dat, (((r1.trans r2).trans rj).trans r3).mono (by omega), rep3, wf3, fo3,
    fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a h1 h2 => ((stk3 a h1 (by omega)).trans (stk2 a h1 (by omega))).trans (fr1 a h1 (Or.inr (by omega))),
    k7, k0, k1, k5, k6⟩

/-- **43259 … 40805, the fallback, any usable size**: as `fallback_tail`, without its u ≥ 1 (a
    chunk with no usable unit copies nothing, through `memcpy`'s byte loop). -/
theorem fallback_tail' {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (h : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43259 ω μ x 40805 ω' μ' x (64 * u + 1000) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨ω', μ', -, h⟩ := fallback_tail'_data (R := R) (p := p) (P := P) (grow := grow) (hb := hb) (HT := HT) (S0 := S0) (S1 := S1) x ω μ s s1 sp ptr req q u v5 v6 hwf hrep hfo hc hu hur h hng h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA hHTs hHT hS hw
  exact ⟨ω', μ', h⟩

/-- **`fallback_tail_heapG` with the copy**: as `fallback_tail_heapG`, and the new block q's first
    u·32 octets are the old block's (at ptr) as they were at 43259. -/
theorem fallback_tail_heap_dataG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
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
      FreeStepsH p (env.rel hostCostMax) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨hkeep, hnew, hq32, hb1⟩ := alloc_keeps hwf h
  by_cases hng : s1.allocated = s.allocated
  · obtain ⟨ω', μ', dat, run, rep, wf, fo, ww, stk, k7, k0, k1, k5, k6⟩ := fallback_tail'_data (p := p) (P := P)
      (R := env.rel hostCostMax) x ω μ (grow := growTo pb) (hb := hb) s s1 sp ptr req q u v5 v6 hwf hrep hfo hc
      hu hur h hng h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA hHTs hHT hS hw
    exact ⟨ω', μ', dat, run.mono (by omega), rep, wf, fo,
      ⟨ph, HeapPages.of_eq hp ww, by rw [hb1, hng]; exact hHT, Nat.le_refl _, hhb⟩,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, k7, k0, k1, k5, k6⟩
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
    (R := env.rel hostCostMax) x ω μ sp ptr 1 req h1 h7 h8 h9 h10 (by omega) (by decide) (by omega) (by omega)
    hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, -, e7, e0, e5, e6, e1, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, hk2⟩ :=
    alloc_refines_grow_hdrG (p := p) (P := P) (S0 := S0) (S1 := S1) env x ω1 μ1 s s1 sp req q pb ph hwf rep1 hbd h48
      hhb hbs h hng (by rw [fget g1 1 (by decide) (by decide)]; exact h1)
      (by rw [fget g1 7 (by decide) (by decide)]; exact h7) a8 a9 a10 hsp (by omega) hb0 hbT hA hfo hcost hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp ww1) (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHT
  have rj := al_ret_realloc (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 (by rw [e0, a0])
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => (stk2 _ (by omega) (by omega)).trans (fr1 _ (by omega) (Or.inr (by omega)))
  have h104 : rdN μ2 (sp + 104) 8 = 196792 := by
    rw [← a104]; exact rdN_frame fun j hj => stk2 _ (by omega) (by omega)
  obtain ⟨ω3, μ3, dat3, r3, rep3, wf3, fo3, ww3, stk3, k7, k0, k1, k5, k6⟩ := fallback_after_data (p := p) (P := P)
    (R := env.rel hostCostMax) x ω2 μ2 s1 sp ptr q u req v5 v6 hwf1 rep2 hfo1 ⟨c, hc1, hca, hcu, hcsz, hdis⟩ hnew
    hq32 (by omega) (by rw [e1, fget g1 1 (by decide) (by decide)]; exact h1) e7 (by rw [e5]; exact a5)
    (by rw [e6, fget g1 6 (by decide) (by decide)]; exact h6) h104
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    hsp hsp1 hsp8 (by rw [hb1]; exact hba) (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT)
    hE' hS (HeapPages.wrAt hpH hpb hst2)
  have dat : μ3.readN q (32 * u) = μ.readN ptr (32 * u) := by
    rw [dat3, hk2.readN fun j hj => off_hdr_data hwf1 (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hc1
      (by omega) (by omega)]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  exact ⟨ω3, μ3, dat, (((r1.trans r2).trans rj).trans r3).mono (by omega), rep3, wf3, fo3,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a h1 h2 => ((stk3 a h1 (by omega)).trans (stk2 a h1 (by omega))).trans (fr1 a h1 (Or.inr (by omega))),
    k7, k0, k1, k5, k6⟩

/-- `fallback_tail_heap_dataG` for the refine contract (`refineHeap env`). -/
theorem fallback_tail_heap_data {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
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
      FreeStepsH p (refineContract env) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 :=
  fallback_tail_heap_dataG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr req q u v5 v6 pb ph hwf hrep hfo hc hu hur hbd h48 hhb hbs h hcost h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **43259 … 40805, the fallback, the heap grown or not**: under `refineContract`, the model's
    `grow` the host's (`growTo pb`), when the model's `alloc` at one unit gives q and s₁ (growing
    the heap by at most 14 pages, or not at all): the binary allocates q the same way, copies the
    old usable size there, frees ptr and returns q into `realloc` (40805), the memory holding
    `free s₁ ptr` and the heap's writable pages covering its allocated space. -/
theorem fallback_tail_heapG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨ω', μ', -, h⟩ := fallback_tail_heap_dataG (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s s1 sp ptr req q u v5 v6 pb ph hwf hrep hfo hc hu hur hbd h48 hhb hbs h hcost h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA hHTs hHT hS hSb hp hst
  exact ⟨ω', μ', h⟩

/-- `fallback_tail_heapG` for the refine contract (`refineHeap env`). -/
theorem fallback_tail_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hur : u < req)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 43259 ω μ x 40805 ω' μ' x (64 * u + 1100) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 :=
  fallback_tail_heapG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr req q u v5 v6 pb ph hwf hrep hfo hc hu hur hbd h48 hhb hbs h hcost h1 h7 h8 h9 h10 h6 hrq s0 s5 s6 hsp hsp1 hsp8 hba hb0 hbT hA (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **`alloc_refines_failG`, with its frame**: as `alloc_refines_failG`, and memory changes only in
    `alloc_impl`'s stack frame (sp − 152 … sp); in particular the heap is untouched. -/
theorem alloc_refines_fail'G {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = none) (hrq : req < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 41177 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) := by
  have hw := HeapPages.wrAt hp hhb hst
  rw [alloc_one hwf.1] at h
  have hb0' : s.base ≠ 0 := hwf.1
  have hbase : rdN μ 206520 8 = s.base := by have := hrep.base; unfold A0 at this; exact this
  have hpri : rdN μ 206832 8 = s.primary := by have := hrep.pri; unfold A0 at this; exact this
  have halc : rdN μ 206840 4 = s.allocated := by have := hrep.alloc; unfold A0 at this; exact this
  have hsec : ∀ q, q < 38 → rdN μ (q * 8 + 204984 + 1544) 8 = s.secondary q := fun q hq => by
    have := hrep.sec q hq; unfold A0 at this; rw [show q * 8 + 204984 + 1544 = 196792 + 9736 + 8 * q by omega]
    exact this
  have hwf0 := hwf
  obtain ⟨-, -, -, htiles, -, -, hlists, hspace⟩ := hwf0
  unfold ListsOk' at hlists
  unfold TilesOk at htiles
  unfold SpaceOk at hspace
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  -- every failure path writes only the frame below sp
  suffices key : ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 41177 ω μ x 41423 ω' μ' x 500 ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) by
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, hp', hst', fr⟩ := key
    exact ⟨ω', μ', run, hrep.congr_lock hwf hb0 hbT (fun a _ ha2 _ => fr a (by omega) (Or.inl (by omega))),
      e7, e0, e5, e6, e1, hp', hst', fr⟩
  rcases alloc1_none h with hbig | ⟨hmax, hnone⟩ | ⟨bin, hmax, hbin, hsmall⟩ | ⟨bin, hmax, hbin, hS, hlt, hgr⟩
  · rw [maxSize_val] at hbig
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_big (p := p) (P := P) (R := env.rel hostCostMax)
      x ω μ sp req s.base h1 h7 h8 h9 hsp hsp1 hbase hb0' hbig hrq hHTs hSTk hw
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, HeapPages.of_eq hp ww,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, fr⟩
  · have hm : req + 1 ≤ 33554432 := by rw [← maxSize_val]; exact hmax
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_nobin (p := p) (P := P) (R := env.rel hostCostMax)
      x ω μ s sp req hbits h1 h7 h8 h9 hsp hsp1 hbase hb0' hpri hsec hm hnone hHTs hSTk hw
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, HeapPages.of_eq hp ww,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, fr⟩
  all_goals
    have hm : req + 1 ≤ 33554432 := by rw [← maxSize_val]; exact hmax
    obtain ⟨hbc, -, -, -, ⟨pre, post, hcs⟩, -, -⟩ := bin_chunk hwf hmax hbin
    have hCm : (⟨s.heads bin, wordSize (s.hdr (s.heads bin)).size, false⟩ : Chunk) ∈ chunks s := by
      rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
    have hsz : rdN μ (s.heads bin + 4) 4 = (s.hdr (s.heads bin)).size := hrep.size _ hCm
    have hheads : rdN μ (196792 + 4 * bin) 4 = s.heads bin := by
      have := hrep.heads bin hbc; unfold A0 at this; exact this
    have hCl := htiles.mem_lt _ hCm
    have hCsp := (hspace _ hCm).2
    simp only at hCl hCsp
    rw [htop] at hCl
    generalize hC : s.heads bin = C at *
    generalize hSd : wordSize (s.hdr C).size = S at *
    have hwS : (s.hdr C).size / 2 = S := by rw [← hSd]; rfl
  · obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_small (p := p) (P := P) (R := env.rel hostCostMax)
      x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9 hsp hsp1 hbase hb0' hpri hsec hm hbin hheads hsz
      (by omega) (by rw [hwS]; exact hsmall) hHTs hSTk ⟨by omega, by omega⟩ hw
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, HeapPages.of_eq hp ww,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, fr⟩
  · have hR : pb < pagesOf (s.base + 32 * ((C - s.base) / 32 + 1 + req + (if S - req - 1 = 0 then 0 else 1))) := by
      unfold growTo at hgr; have := of_decide_eq_false hgr; omega
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, hp', hst', fr⟩ := alloc_fail_growG (p := p) (P := P) (S0 := S0)
      (S1 := S1) env x ω μ s sp req bin C (s.hdr C).size pb ph hbits h1 h7 h8 h9 hsp hsp1 hbase hb0' hpri hsec halc
      hal hm hbin hheads hsz hbT (by omega) (by rw [hwS]; exact hS) (by rw [hwS]; omega) (by rw [hwS]; exact hlt)
      hbd h48 hhb hbs (by rw [hwS]; exact hR) hHTs hSTk hSb ⟨by omega, by omega⟩ hp hst
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, hp', hst', fr⟩

/-- `alloc_refines_fail'G` for the refine contract (`refineHeap env`). -/
theorem alloc_refines_fail' {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = none) (hrq : req < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 41177 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) :=
  alloc_refines_fail'G (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s sp req pb ph hwf hrep hbd h48 hhb hbs h hrq h1 h7 h8 h9 hsp hsp1 hb0 hbT hal (S0 := S0) (S1 := S1) hHTs hSTk hSb hp hst hHT

/-- **43259 … 40805, the fallback's `alloc` failing**: under `refineContract`, the model's `grow`
    the host's (`growTo pb`), when the model's `alloc` at one unit returns `none` for `req` units:
    `alloc_impl` returns null, and `realloc_impl` returns null into `realloc` (40805, through
    43326) with memory still holding `s`, the heap's pages as they were, and memory changed only
    in the frame below sp + 152 (sp + 104 … sp + 112 and `alloc_impl`'s frame below sp): the old
    block, and the whole heap, untouched. -/
theorem fallback_tail_failG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr req v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (h : alloc (growTo pb) hb 1 req s = none) (hrq : req < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (hp64 : ptr < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 43259 ω μ x 40805 ω' μ' x 520 ∧ Rep μ' s ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, -, a8, a9, -, a0, -, fr1, ww1, g1⟩ := rf_call (p := p) (P := P)
    (R := env.rel hostCostMax) x ω μ sp ptr 1 req h1 h7 h8 h9 h10 hp64 (by decide) (by omega) (by omega)
    hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, e7, e0, -, -, e1, hp2, hst2, fr2⟩ :=
    alloc_refines_fail'G (p := p) (P := P) (S0 := S0) (S1 := S1) env x ω1 μ1 s sp req pb ph hwf rep1 hbd h48 hhb hbs
      h hrq (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [fget g1 7 (by decide) (by decide)]; exact h7)
      a8 a9 hsp (by omega) hb0 hbT hA hHTs ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp ww1)
      (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHT
  have rj := al_ret_realloc (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 (by rw [e0, a0])
  have fr : ∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) →
      μ2.read a = μ.read a := fun a h1 h2 h3 => (fr2 a h1 h2).trans (fr1 a h1 h3)
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ2 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => fr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  obtain ⟨ω3, r3, k7, k0, k1, k5, k6⟩ := rf_null (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 sp v5 v6
    (by rw [e1, fget g1 1 (by decide) (by decide)]; exact h1) e7 (by omega) hsp1
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    ⟨by omega, by omega⟩ (HeapPages.wrAt hp2 hhb hst2).rd
  exact ⟨ω3, μ2, (((r1.trans r2).trans rj).trans r3).mono (by omega), rep2, hp2, hst2, fr, k7, k0, k1, k5, k6⟩

/-- `fallback_tail_failG` for the refine contract (`refineHeap env`). -/
theorem fallback_tail_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr req v5 v6 pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (h : alloc (growTo pb) hb 1 req s = none) (hrq : req < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (hp64 : ptr < 4294967296)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 43259 ω μ x 40805 ω' μ' x 520 ∧ Rep μ' s ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → (a < sp + 104 ∨ sp + 112 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 :=
  fallback_tail_failG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s sp ptr req v5 v6 pb ph hwf hrep hbd h48 hhb hbs h hrq h1 h7 h8 h9 h10 hp64 s0 s5 s6 hsp hsp1 hb0 hbT hA (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

end Services.Bootstrap.Alloc
