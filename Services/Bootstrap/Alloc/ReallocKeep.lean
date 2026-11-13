import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.ReallocFallbackAlloc
import Services.Bootstrap.Alloc.ReallocGrowHeapRefines

/-!
# The binary's `realloc` keeps the data when it does not move the block

On every path that returns the old address (Gray Paper v0.8.0, Appendix B: the model's `realloc`
with the same size, a smaller one, or growing in place, the heap grown or not), the block's first
`min (usable s ptr) ⌈size/32⌉`·32 octets are as they were when `realloc` (40701) was called. The
heap frames of the paths (`shrink_refines_hdr`, `grow_refines_hdr`, `grow_heap_refinesK_hdr`) say
that only chunk headers of `s` and the new tail's header change; `readN_inplace` reads the kept
data off them.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The kept data, against a frame**: the first k units of the data of an allocated chunk at
    ptr − 32 (k below its usable size) lie off the headers of the chunks of `s` and off a header
    at N ≥ ptr + 32·k, so a frame for those headers keeps them. -/
theorem readN_inplace {s : State} (hwf : WF s) (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    {c : Chunk} (hc : c ∈ chunks s) {ptr k N : Nat} (hca : c.addr + 32 = ptr) (hk : k + 1 ≤ c.size)
    (hN : ptr + 32 * k ≤ N) {μ μ' : Memory} (h : HKeep μ μ' (fun a => (∃ d ∈ chunks s, d.addr = a) ∨ a = N)) :
    μ'.readN ptr (32 * k) = μ.readN ptr (32 * k) :=
  h.readN fun j hj => by
    have := off_hdr_data hwf hb0 hbT hc (a := ptr + j) (by omega) (by omega)
    unfold OffHdr at this ⊢
    exact ⟨this.1, this.2.1, fun b hb => by rcases hb with hb | hb; exact this.2.2 b hb; omega⟩

/-- **`same_refines` with the data**: as `same_refines`, and the block's first `req`·32 octets
    are kept (only the stack frame changes). -/
theorem same_refines_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : req = usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) {HT S0 S1 : Nat}
    (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', μ'.readN ptr (32 * req) = μ.readN ptr (32 * req) ∧ FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' s ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hdl := data_lt hwf hbT hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hsz : (s.hdr c.addr).size = sizeWord c.size true := by rw [chunks_hdr c hcm, hcu]
  have hca' : c.addr = ptr - 32 := by omega
  have hcT : c.addr + 32 ≤ HT := by
    have hsp' := hwf.2.2.2.2.2.2.2; unfold SpaceOk at hsp'; have := (hsp' c hcm).2; omega
  have hw' : rdN μ (ptr - 28) 4 = 2 * c.size + 1 := by
    rw [show ptr - 28 = c.addr + 4 by omega, hrep.size c hcm, hsz]; unfold sizeWord; simp
  have hus : usable s ptr = c.size - 1 := by
    unfold usable; rw [← hca', hsz, wordSize_sizeWord]
  obtain ⟨ω1, μ1, r1, a1, -, a6, st0, st5, st6, sf1, ww1, g1⟩ := rl_pro (p := p) (P := P) (R := R) x ω μ sp
    ptr (2 * c.size + 1) h1 h8 (by omega) (by omega) hw' (by omega) hsp hsp1 ⟨by omega, by omega⟩ hS hw
  have b := rl_br_same (p := p) (P := P) (R := R) x ω1 μ1 req
    (by rw [fget g1 10 (by decide) (by decide)]; exact h10)
    (by rw [a6, hr, hus]; congr 1; omega)
  have hr1 := (hw.of_eq ww1).rd
  obtain ⟨ω2, r2, e7, e0, e1, e5, e6, -⟩ := rl_ret (p := p) (P := P) (R := R) x ω1 μ1 (sp - 152) ptr
    ω[5].toNat ω[6].toNat a1 (by rw [fget g1 8 (by decide) (by decide)]; exact h8) (by omega) (by omega) (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega, rd_enc st0 (UInt64.toNat_lt _), h0]; rfl)
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd_enc st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd_enc st6 (UInt64.toNat_lt _))
    ⟨by omega, by omega⟩ hr1
  refine ⟨ω2, μ1, readN_congr2 fun j hj => sf1 _ (by omega) (Or.inl (by omega)),
    ((r1.trans b).trans r2).mono (by omega),
    hrep.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => sf1 a (by omega) (Or.inl (by omega))), ww1,
    fun a h1 h2 => sf1 a h1 (Or.inr h2), e7, e0, by rw [e1]; congr 1; omega,
    by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

/-- **`realloc_inplace_refines` with the data**: as `realloc_inplace_refines`, and the block's
    first `req`·32 octets are kept. -/
theorem realloc_inplace_refines_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr align req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr0 : req ≠ 0) (hr : req ≤ usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT) (hS : S0 + 152 ≤ sp ∧ sp ≤ S1)
    (hw : WrAt μ HT S0 S1) :
    ∃ s', realloc grow hb s ptr align req = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * req) = μ.readN ptr (32 * req) ∧
        FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcs := chunk_size_usable hcm hca hcu rfl (ht.mem_lt c hcm).2.2
  refine ⟨_, realloc_inplace hr0 hr, ?_⟩
  by_cases e : req = usable s ptr
  · rw [if_pos e]
    obtain ⟨ω', μ', dat, run, rep, ww, stk, e7, e0, e1, e5, e6⟩ := same_refines_data (p := p) (P := P) (R := R)
      x ω μ s sp ptr req hwf hrep hc e h1 h8 h10 h0 hsp hsp1 hb0 hbT hHT hS hw
    exact ⟨ω', μ', dat, run, rep, hwf, hfo, ww, stk, e7, e0, e1, e5, e6⟩
  · rw [if_neg e]
    obtain ⟨ω', μ', hk, rest⟩ := shrink_refines_hdr (p := p) (P := P) (R := R) x ω μ s sp ptr req hwf hrep hc hr0
      (by omega) h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT hfo hHT hS hw
    exact ⟨ω', μ', readN_inplace hwf hb0 hbT hcm hca (by omega) (by omega) hk.hkeep, rest⟩

/-- **`realloc` around a refinement of `realloc_impl`, with data**: as `realloc_wrap`, when
    `realloc_impl` also brings m octets at ptr to r (both in the heap below 2³¹), so does
    `realloc`. -/
theorem realloc_wrap_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s s' : State) (sp ptr al size r n m : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hb' : s'.base = s.base)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hp0 : ptr ≠ 0) (hp1 : ptr < 4294967296)
    (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hS : S0 + 16 ≤ sp ∧ sp ≤ S1)
    (hw : WrAt μ HT S0 S1)
    (hpm : 206864 ≤ ptr ∧ ptr + m ≤ 2147483648) (hrm : 206864 ≤ r ∧ r + m ≤ 2147483648)
    (impl : ∀ ω1 μ1, Rep μ1 s → WrAt μ1 HT S0 S1 → ω1[1] = UInt64.ofNat (sp - 16) →
      ω1[8] = UInt64.ofNat ptr → ω1[7] = UInt64.ofNat 196792 → ω1[10] = UInt64.ofNat ((size + 31) / 32) →
      ω1[0] = UInt64.ofNat 1988 →
      ∃ ω2 μ2, μ2.readN r m = μ1.readN ptr m ∧ FreeStepsH p R 42980 ω1 μ1 x 40805 ω2 μ2 x n ∧ Rep μ2 s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ2.writable a = μ1.writable a) ∧ (∀ a, a < 4294967296 → sp - 16 ≤ a → μ2.read a = μ1.read a) ∧
        ω2[7] = UInt64.ofNat r ∧ ω2[1] = UInt64.ofNat (sp - 16) ∧ ω2[5] = ω1[5] ∧ ω2[6] = ω1[6]) :
    ∃ ω' μ', μ'.readN r m = μ.readN ptr m ∧ FreeStepsH p R 40701 ω μ x 40821 ω' μ' x (n + 45) ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
      ω'[7] = UInt64.ofNat r ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := R) x ω μ sp ptr al size h1 h7 h9 h10 hp0 hp1 hal hs hsp hsp1 hl hH
      hS hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, dat2, r2, rep2, hwf', hfo', ww2, stk2, e7, e1, e5, e6⟩ := impl ω1 μ1 rep1 (hw.of_eq ww1) a1 a8 a7 a10 a0
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega) (by omega) hH
      ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  have dat : μ3.readN r m = μ.readN ptr m := by
    have e3 : μ3.readN r m = μ2.readN r m := readN_congr2 fun j hj => fr3 _ (by omega) (by omega)
    rw [e3, dat2]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨ω3, μ3, dat, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock hwf' (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), hwf', hfo',
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- **`realloc_wrap_inplace` with the data**: as `realloc_wrap_inplace`, and the block's first
    ⌈size/32⌉·32 octets are as they were when `realloc` was called. -/
theorem realloc_wrap_inplace_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s : State) (sp ptr al size : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr0 : size ≠ 0)
    (hr : (size + 31) / 32 ≤ usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ s', realloc grow hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * ((size + 31) / 32)) = μ.readN ptr (32 * ((size + 31) / 32)) ∧ FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 225 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hq0 : (size + 31) / 32 ≠ 0 := by omega
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hdl := data_lt hwf hbT hc
  refine ⟨_, realloc_inplace hq0 hr, ?_⟩
  exact realloc_wrap_data (p := p) (P := P) (R := R) x ω μ s _ sp ptr al size ptr 180 (32 * ((size + 31) / 32)) hwf hrep
    (by split <;> simp [shrink_base]) h1 h7 h9 h10 (by omega) (by omega) hal hs (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨s'', e, ω2, μ2, dat, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6⟩ :=
        realloc_inplace_refines_data (grow := grow) (hb := hb) (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr
          ((al + 31) / 32) ((size + 31) / 32) hwf rep1 hc hq0 hr a1 a8 a7 a10 a0 (by omega) (by omega) hb0 hbT
          hfo hHT ⟨by omega, by omega⟩ W1
      rw [realloc_inplace hq0 hr] at e
      simp only [Option.some.injEq, Prod.mk.injEq, true_and, and_true] at e
      subst e
      exact ⟨ω2, μ2, dat, run, rep, wf, fo, ww, stk, e7, e1, e5, e6⟩)

/-- **`realloc_wrap_grow` with the data**: as `realloc_wrap_grow`, and the block's first
    `usable s ptr`·32 octets are as they were when `realloc` was called. -/
theorem realloc_wrap_grow_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp ptr al size : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (h : growInplace grow s ptr ((size + 31) / 32) = some s') (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p R 40701 ω μ x 40821 ω' μ' x 295 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  have hca' := hca
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hdl := data_lt hwf hbT hc
  have hcs := chunk_size_usable hcm hca hcu rfl hcl.2.2
  refine ⟨realloc_grow hr h, ?_⟩
  exact realloc_wrap_data (p := p) (P := P) (R := R) x ω μ s s' sp ptr al size ptr 250 (32 * usable s ptr) hwf hrep
    (growInplace_base h) h1 h7 h9 h10 (by omega) (by omega) hal (by omega) (by omega) hsp1 hb0 hbT hl
    (by omega) ⟨by omega, by omega⟩ hw ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun ω1 μ1 rep1 W1 a1 a8 a7 a10 a0 => by
      obtain ⟨ω2, μ2, hk, run, rep, wf, fo, ww, stk, e7, -, e1, e5, e6⟩ :=
        grow_refines_hdr (p := p) (P := P) (R := R) x ω1 μ1 s s' (sp - 16) ptr
          ((size + 31) / 32) hwf rep1 hc hr hr1 h hng a1 a8 a7 a10 a0 (by omega) (by omega)
          hb0 hbT hA hfo hHT ⟨by omega, by omega⟩ W1
      exact ⟨ω2, μ2, readN_inplace hwf hb0 hbT hcm hca' (by omega) (by omega) hk.hkeep, run, rep, wf, fo, ww, stk, e7, e1, e5, e6⟩)

/-- **`realloc_wrap_grow_heapKG` with the data**: as `realloc_wrap_grow_heapKG`, and the block's
    first `usable s ptr`·32 octets are as they were when `realloc` was called.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem realloc_wrap_grow_heapK_dataG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (env.rel cap) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  refine ⟨realloc_grow hr h, ?_⟩
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  have hdl := data_lt hwf hbT hc
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := env.rel cap) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      hal (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨ω2, μ2, hk, r2, rep2, wf2, fo2, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, e7, e0, e1, e5, e6⟩ :=
    grow_heap_refinesK_hdrG (p := p) (P := P) env cap hcap x ω1 μ1 s s' (sp - 16) ptr ((size + 31) / 32) hwf rep1 hc hr hr1
      pb ph hbd h48 hhb hbs h hgrown a1 a8 a7 a10 a0 (by omega) (by omega) hb0 hbT hA hfo hcost hHT
      ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hpH hpb hst2)
  have hb' : s'.base = s.base := growInplace_base h
  have hcs := chunk_size_usable hcm hca hcu rfl hcl.2.2
  have dat : μ3.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    have e3 : μ3.readN ptr (32 * usable s ptr) = μ2.readN ptr (32 * usable s ptr) :=
      readN_congr2 fun j hj => fr3 _ (by omega) (by omega)
    rw [e3, readN_inplace hwf hb0 hbT hcm hca (by omega) (by omega) hk.hkeep]
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
  refine ⟨ω3, μ3, dat, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- `realloc_wrap_grow_heapK_dataG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_grow_heapK_data {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_grow_heapK_dataG (p := p) (P := P) (refineHeap env) cap hcap x ω μ (hb := hb) s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo hcost hl (S0 := S0) (S1 := S1) hHT hS hSb hp hst

/-- `realloc_wrap_grow_heapK_dataG` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem realloc_wrap_grow_heap_dataG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_grow_heapK_dataG (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1)
    env hostCostMax (by decide) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs
    h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo (by unfold hostCostMax; omega) hl hHT hS hSb
    hp hst

/-- `realloc_wrap_grow_heap_dataG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_grow_heap_data {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', μ'.readN ptr (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧ FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_grow_heap_dataG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo hcost hl (S0 := S0) (S1 := S1) hHT hS hSb hp hst

end Services.Bootstrap.Alloc
