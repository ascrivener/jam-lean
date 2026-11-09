import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.ReallocFallbackHeap
import Services.Bootstrap.Alloc.ReallocGrowHeapRefines

/-!
# The binary's `realloc` refines the model's `realloc`: the fallback, through the wrapper

`realloc` (40701) takes the allocator's lock, calls `realloc_impl` (42980) with the address, the
alignment and the size in 32-octet units, and clears the lock (`rw_lock`, `rw_unlock`). Around
the fallback (`fallback_refines'`, `fallback_refines_heap`, `fallback_refines_fail`) this gives the
model's `realloc` at an alignment of 1 … 32 octets (one unit):

* `realloc_wrap_fallback'`: any host, the heap not grown;
* `realloc_wrap_fallback`: under `refineContract`, every way to the fallback, the heap grown or not;
* `realloc_wrap_fallback_fail`: the model's `realloc` is `none` and `realloc` returns null, with
  memory holding `s` and changed only in the stack and the lock (so the heap is untouched).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`realloc_wrap_fallback'` with the copy**: as `realloc_wrap_fallback'`, and the returned
    block q's first `usable s ptr`·32 octets are the old block's (at ptr) as they were when
    `realloc` (40701) was called. -/
theorem realloc_wrap_fallback'_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr al size q : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * (usable s ptr + 1) ∨
      wordUsed (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size = true ∨
      usable s ptr + 1 + wordSize (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size < (size + 31) / 32 + 1)
    (ha : alloc grow hb 1 ((size + 31) / 32) s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p R 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1120) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hal : (al + 31) / 32 = 1 := by omega
  rw [hal]
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  obtain ⟨ω1, μ1, r1, a1, a8, a7, a9, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := R) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      (by omega) (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨e, ω2, μ2, dat2, r2, rep2, wf2, fo2, ww2, stk2, e7, e0, e1, e5, e6⟩ :=
    fallback_refines'_data (p := p) (P := P) (R := R) x ω1 μ1 (grow := grow) (hb := hb) s s1 (sp - 16) ptr
      ((size + 31) / 32) q hwf rep1 hc hr hr1 hcase ha hng a1 a8 a7 (by rw [a9, hal]) a10 a0 (by omega)
      (by omega) (by omega) hba hb0 hbT hA hfo hHTs hHT ⟨by omega, by omega⟩ (hw.of_eq ww1)
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega) (by omega)
      (by omega) ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
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
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- **The binary's `realloc` refines the model's `realloc`, through the fallback** (any host):
    from memory holding a well-formed `s` (its first chunk's `prev` 0), the lock byte clear, ω₇
    the data address of an allocated chunk, ω₉ = `al` (1 … 32 octets, one unit) and ω₁₀ = `size`
    octets with `⌈size/32⌉` units above the usable size, when the chunk's next chunk lies past the
    heap's end, is used, or with it the chunk is still too small, and the model's `alloc` gives q
    and s₁ without growing the heap: the model's `realloc` gives `(q, free s₁ ptr, true)`, and
    `realloc` (40701) reaches its return (the `jumpInd` at 40821) with ω₇ = q, memory holding
    `free s₁ ptr`, the lock byte clear again, the caller's ω₀, ω₁, ω₅, ω₆ restored and the stack
    from sp up untouched. -/
theorem realloc_wrap_fallback' {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr al size q : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * (usable s ptr + 1) ∨
      wordUsed (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size = true ∨
      usable s ptr + 1 + wordSize (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size < (size + 31) / 32 + 1)
    (ha : alloc grow hb 1 ((size + 31) / 32) s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT)
    (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1120) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨e, ω', μ', -, h⟩ := realloc_wrap_fallback'_data (R := R) (p := p) (P := P) (grow := grow) (hb := hb) (HT := HT) (S0 := S0) (S1 := S1) x ω μ s s1 sp ptr al size q hwf hrep hc hr hr1 hcase ha hng h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hw
  exact ⟨e, ω', μ', h⟩

/-- **`realloc_wrap_fallbackG` with the copy** (GP Appendix B, Ω_♊ as the host's `growTo pb`):
    as `realloc_wrap_fallbackG`, and the returned block q's first `usable s ptr`·32 octets are the
    old block's (at ptr) as they were when `realloc` (40701) was called. -/
theorem realloc_wrap_fallback_dataG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
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
      FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
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
    rw_lock (p := p) (P := P) (R := env.rel hostCostMax) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      (by omega) (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨e, ω2, μ2, dat2, r2, rep2, wf2, fo2, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, e7, e0, e1, e5, e6⟩ :=
    fallback_refines_heap_dataG (p := p) (P := P) env x ω1 μ1 (hb := hb) s s1 (sp - 16) ptr ((size + 31) / 32) q pb ph
      hwf rep1 hc hr hr1 hbd h48 hhb hbs hnone ha hcost a1 a8 a7 (by rw [a9, hal]) a10 a0 (by omega) (by omega)
      (by omega) hba hb0 hbT hA hfo hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
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
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- `realloc_wrap_fallback_dataG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_fallback_data {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
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
      FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_fallback_dataG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **The binary's `realloc` refines the model's `realloc`, through any fallback**: under
    `refineContract` (the model's `grow` the host's `growTo pb`, GP Appendix B Ω_♊), as
    `realloc_wrap_fallback'` whenever the model's `growInplace` fails (the host's refusal to grow
    the heap included) and its `alloc` gives q and s₁, growing the heap by at most 14 pages or not:
    `realloc` returns q, memory holding `free s₁ ptr` and the heap's pages covering its allocated
    space. -/
theorem realloc_wrap_fallbackG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨e, ω', μ', -, h⟩ := realloc_wrap_fallback_dataG (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hSb hp hst
  exact ⟨e, ω', μ', h⟩

/-- `realloc_wrap_fallbackG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_fallback {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr al size q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1270) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_fallbackG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **The binary's `realloc` fails where the model's `realloc` does**: as `realloc_wrap_fallbackG`,
    when the model's `alloc` returns `none`: the model's `realloc` is `none`, and `realloc` returns
    null with memory still holding `s`, the lock byte clear again, the heap's pages as they were,
    and memory changed only in the stack below sp, the allocator's lock word and 196608 … 196615:
    the old block, and the whole heap from `s.base`, untouched. -/
theorem realloc_wrap_fallback_failG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none ∧
      ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x 690 ∧ Rep μ' s ∧
        ω'[7] = UInt64.ofNat 0 ∧ rdN μ' 206848 1 = 0 ∧ HeapPages μ' 48 pb ph ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → (a < sp - 320 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
          (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, s.base ≤ a → a < 2147483648 → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
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
    rw_lock (p := p) (P := P) (R := env.rel hostCostMax) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      (by omega) (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨e, ω2, μ2, r2, rep2, hp2, hst2, fr2, e7, e0, e1, e5, e6⟩ :=
    fallback_refines_failG (p := p) (P := P) env x ω1 μ1 (hb := hb) s (sp - 16) ptr ((size + 31) / 32) pb ph
      hwf rep1 hc hr hr1 hbd h48 hhb hbs hnone ha a1 a8 a7 (by rw [a9, hal]) a10 a0 (by omega) (by omega)
      hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel hostCostMax) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hp2 hhb hst2)
  have fr : ∀ a, a < 4294967296 → (a < sp - 320 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
      (a < 206848 ∨ 206852 ≤ a) → μ3.read a = μ.read a := fun a h1 h2 h3 h4 =>
    ((fr3 a h1 (by omega)).trans (fr2 a h1 (by omega))).trans (fr1 a h1 (by omega) h3 h4)
  have stk2 : ∀ a, a < 4294967296 → sp - 16 ≤ a → μ2.read a = μ1.read a := fun a h1 h2 => fr2 a h1 (Or.inr h2)
  refine ⟨e, ω3, μ3, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)),
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, HeapPages.of_eq hp2 ww3,
    fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2, fr,
    fun a h1 h2 => fr a (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega)), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- `realloc_wrap_fallback_failG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_fallback_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < (size + 31) / 32) (hr1 : (size + 31) / 32 < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr ((size + 31) / 32) = none)
    (ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none ∧
      ∃ ω' μ', FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x 690 ∧ Rep μ' s ∧
        ω'[7] = UInt64.ofNat 0 ∧ rdN μ' 206848 1 = 0 ∧ HeapPages μ' 48 pb ph ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → (a < sp - 320 ∨ sp ≤ a) → (a < 196608 ∨ 196616 ≤ a) →
          (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, s.base ≤ a → a < 2147483648 → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_fallback_failG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s sp ptr al size pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha h1 h7 h9 h10 hal1 hal2 hsp hsp1 hb0 hbT hA hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

end Services.Bootstrap.Alloc
