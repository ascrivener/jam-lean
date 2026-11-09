import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.ReallocFallbackAlloc
import Services.Bootstrap.Alloc.ReallocFallbackGrowFail
import Services.Bootstrap.Alloc.ReallocFallbackRefines

/-!
# The binary's `realloc_impl` refines the model's `realloc`: every fallback

The model's `realloc` (alignment one unit, above the usable size) takes the fallback when
`growInplace` returns `none`: the next chunk lies past the heap's end, is used, or is too small
with the chunk — or it is free and large enough but the heap must grow and `grow` refuses
(`growInplace_none_cases`). The binary reaches the fallback (43259) in each case: through
`fallback_pre`, or, when the host leaves the heap short, through `fallback_pre_grow`
(`fallback_entry`). Then, by the model's `alloc` (GP Appendix B Ω_♊ as the host's `growTo pb`):

* `some (q, s₁)`, growing the heap or not: `fallback_refines_heap` — the model's `realloc` gives
  `(q, free s₁ ptr, true)` and the binary returns q with memory holding `free s₁ ptr`;
* `none`: `fallback_refines_fail` — the model's `realloc` is `none` and the binary returns null
  with memory still holding `s`, changed only in the stack frame (the old block and the heap
  untouched).

`fallback_refines'` is `fallback_refines` (no heap growth, any host) without its u ≥ 1.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`fallback_refines'` with the copy**: as `fallback_refines'`, and the new block q's first
    `usable s ptr`·32 octets are the old block's as they were at `realloc_impl`'s entry (42980). -/
theorem fallback_refines'_data {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * (usable s ptr + 1) ∨
      wordUsed (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size = true ∨
      usable s ptr + 1 + wordSize (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size < req + 1)
    (ha : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p R 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1070) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = cur at hcs
  have hXmem : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s := by
    rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
  have hXs : (s.hdr (ptr - 32)).size = sizeWord cur true := by
    have := chunks_hdr _ hXmem; simp only at this; exact this
  have hcur : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hXs, wordSize_sizeWord]
  have husable : usable s ptr = cur - 1 := by unfold usable; rw [hcur]
  have hc1 : 1 ≤ cur := by
    have ht0 := hwf.2.2.2.1
    unfold TilesOk at ht0
    have := ht0.mem_lt _ hXmem; simp only at this; omega
  rw [husable, show cur - 1 + 1 = cur by omega] at hcase
  have hlt : cur < req + 1 := by omega
  refine ⟨realloc_fallback hr (growInplace_none_of hcur hlt hcase) ha, ?_⟩
  have hwf' := hwf
  obtain ⟨-, -, -, htiles, -, -, -, hspace⟩ := hwf'
  unfold TilesOk at htiles
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles henc
  rw [htop] at htiles
  -- the header addresses
  generalize hH : HA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := fun a h => by
    rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have unHF : ∀ a, H a ∨ F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := by
    rintro a (h | h)
    · exact unH a h
    · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ := unHF a h
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hcs' : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post := hcs
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
    unfold SpaceOk at hspace; have := (hspace c (hcs' ▸ hc)).2; omega
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs' ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs' ▸ hc) hu⟩
  have hXm : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post :=
    List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  simp only at hXl
  obtain ⟨-, hph, -, -⟩ := Tiles.around htiles
  -- the next chunk, when below the heap's end, is a chunk
  have hnc : ptr - 32 + 32 * cur < s.base + 1073741824 → H (ptr - 32 + 32 * cur) := by
    intro hlt'
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      rw [show ptr - 32 + 32 * cur = e.addr from (hph e (by rw [hp]; rfl)).symm]
      exact mkH e (List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [hp]; simp)))
  have hcase' : s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨
      (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
        (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1) ∨
      (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
        (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 ∧ cur + (s.hdr (ptr - 32 + 32 * cur)).size / 2 < req + 1) := by
    by_cases hin : s.base + 1073741824 ≤ ptr - 32 + 32 * cur
    · exact Or.inl hin
    · have hH' := hnc (by omega)
      by_cases hodd : (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1
      · exact Or.inr (Or.inl ⟨by omega, hH', hodd⟩)
      · refine Or.inr (Or.inr ⟨by omega, hH', by omega, ?_⟩)
        rcases hcase with h | h | h
        · omega
        · exfalso; unfold wordUsed at h; simp at h; omega
        · unfold wordSize at h; exact h
  obtain ⟨ω1, μ1, r1, -, ww1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_pre (p := p) (P := P)
    (R := R) x ω μ s H F sp ptr req cur hrep' h1 h8 h7 h10 (by omega) hsp1 hb0 hbT (hHF _ (Or.inl (mkH _ hXm)))
    (by omega) (mkH _ hXm) hHF (by rw [hXs]; unfold sizeWord; simp) hlt (by omega) hc1 (by omega) hcase'
    hHFT ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, dat2, r2, rep2, wf2, fo2, ww2, stk2, e7, e0, e1, e5, e6⟩ := fallback_tail'_data (p := p) (P := P) (R := R)
    x ω1 μ1 (grow := grow) (hb := hb) s s1 (sp - 152) ptr req q (cur - 1) ω[5].toNat ω[6].toNat hwf rep1 hfo hc
    husable (by omega) ha hng a1 a7 a8 (by rw [a9]; exact h9) a10 a6 (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) (by omega) hba hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ (hw.of_eq ww1)
  have hdl := data_lt hwf hbT hc
  have dat : μ2.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    rw [husable, dat2]; rw [husable] at hdl
    exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  refine ⟨ω2, μ2, dat, (r1.trans r2).mono (by rw [husable]; omega), rep2, wf2, fo2,
    fun a => (ww2 a).trans (ww1 a), fun a h1 h2 => (stk2 a h1 (by omega)).trans (fr1 a h1 (Or.inr h2)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

/-- **`fallback_refines` for any usable size**: as `fallback_refines`, without its u ≥ 1 (a chunk
    with no usable unit copies nothing, through `memcpy`'s byte loop, `rf_memcpy`). -/
theorem fallback_refines' {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * (usable s ptr + 1) ∨
      wordUsed (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size = true ∨
      usable s ptr + 1 + wordSize (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size < req + 1)
    (ha : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1070) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨e, ω', μ', -, h⟩ := fallback_refines'_data (R := R) (p := p) (P := P) (grow := grow) (hb := hb) (HT := HT) (S0 := S0) (S1 := S1) x ω μ s s1 sp ptr req q hwf hrep hc hr hr1 hcase ha hng h1 h8 h7 h9 h10 h0 hsp hsp1 hsp8 hba hb0 hbT hA hfo hHTs hHT hS hw
  exact ⟨e, ω', μ', h⟩

/-- **Why `growInplace` fails**, above the usable size: the next chunk lies past the heap's end,
    is used, or with it the chunk is too small; or it is free and large enough but the allocated
    space must grow to the end E and `grow` refuses. -/
theorem growInplace_none_cases {grow : Grow} {s : State} {ptr req cur : Nat}
    (hsz : wordSize (s.hdr (ptr - 32)).size = cur) (hlt : cur < req + 1)
    (h : growInplace grow s ptr req = none) :
    (s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨ wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = true ∨
      cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size < req + 1) ∨
    (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = false ∧
      req + 1 ≤ cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size ∧
      s.allocated < (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
        (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1) ∧
      grow s.base ((ptr - 32 + 32 * (req + 1) - s.base) / 32 +
        (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1)) = false) := by
  unfold growInplace at h
  simp only [hsz, maxSize_val, Nat.reduceMul] at h
  rw [if_neg (by omega)] at h
  by_cases h1 : ptr - 32 + 32 * cur ≥ s.base + 1073741824
  · exact Or.inl (Or.inl h1)
  rw [if_neg h1] at h
  generalize hw : (s.hdr (ptr - 32 + 32 * cur)).size = w at h ⊢
  by_cases h2 : wordUsed w = true
  · exact Or.inl (Or.inr (Or.inl h2))
  rw [if_neg h2] at h
  by_cases h3 : cur + wordSize w < req + 1
  · exact Or.inl (Or.inr (Or.inr h3))
  rw [if_neg h3] at h
  generalize hE : (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
    (if cur + wordSize w - (req + 1) = 0 then 0 else 1) = E at h ⊢
  by_cases h4 : s.allocated < E
  · rw [if_pos h4] at h
    by_cases hgr : grow s.base E = true
    · rw [if_pos hgr] at h; simp at h
    · exact Or.inr ⟨by omega, by simpa using h2, by omega, h4, by simpa using hgr⟩
  · rw [if_neg h4] at h; simp at h

/-- The model's `realloc` above the usable size, when `growInplace` and then `alloc` fail: `none`. -/
theorem realloc_fallback_none {grow : Grow} {hb : Nat} {s : State} {ptr align req : Nat}
    (hr : usable s ptr < req) (h : growInplace grow s ptr req = none)
    (ha : alloc grow hb align req s = none) : realloc grow hb s ptr align req = none := by
  unfold realloc
  have e1 : req ≠ usable s ptr := by omega
  have e2 : req ≠ 0 := by omega
  have e3 : ¬ req < usable s ptr := by omega
  simp [e1, e2, e3, h, ha]

/-- **42980 … 43259, every way to the fallback**: under `refineContract` (the model's `grow` the
    host's `growTo pb`), from memory holding a well-formed `s`, ω₈ = ptr the data address of an
    allocated chunk and ω₁₀ = req above its usable size, when the model's `growInplace` fails: the
    binary reaches the fallback with the frame at sp − 152, ω₆ = the usable size, ω₇ the allocator,
    ω₈ = ptr, ω₉ kept and ω₁₀ = req, the caller's ω₀, ω₅, ω₆ saved, memory still holding `s`
    (changed only in the frame) and the heap's pages as they were. -/
theorem fallback_entryG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) (s : State) (sp ptr req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 43259 ω' μ' x 120 ∧ Rep μ' s ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[6] = UInt64.ofNat (usable s ptr) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat req := by
  have hw := HeapPages.wrAt hp hhb hst
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = cur at hcs
  have hXmem : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s := by
    rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
  have hXs : (s.hdr (ptr - 32)).size = sizeWord cur true := by
    have := chunks_hdr _ hXmem; simp only at this; exact this
  have hcur : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hXs, wordSize_sizeWord]
  have husable : usable s ptr = cur - 1 := by unfold usable; rw [hcur]
  have hwf' := hwf
  obtain ⟨-, -, -, htiles, -, -, -, hspace⟩ := hwf'
  unfold TilesOk at htiles
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles henc
  rw [htop] at htiles
  -- the header addresses
  generalize hH : HA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := fun a h => by
    rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have unHF : ∀ a, H a ∨ F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := by
    rintro a (h | h)
    · exact unH a h
    · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ := unHF a h
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hcs' : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post := hcs
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * ph := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
    unfold SpaceOk at hspace; have := (hspace c (hcs' ▸ hc)).2; omega
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs' ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs' ▸ hc) hu⟩
  have hXm : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post :=
    List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  simp only at hXl
  have hc1 : 1 ≤ cur := by omega
  have hlt : cur < req + 1 := by omega
  obtain ⟨-, hph, -, -⟩ := Tiles.around htiles
  -- the next chunk, when below the heap's end, is a chunk
  have hnx : ptr - 32 + 32 * cur < s.base + 1073741824 →
      ∃ e ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, e.addr = ptr - 32 + 32 * cur := by
    intro hlt'
    cases hpo : post with
    | nil =>
      rw [hpo] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      exact ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ (by simp)), hph e (by rw [hpo]; rfl)⟩
  have hnc : ptr - 32 + 32 * cur < s.base + 1073741824 → H (ptr - 32 + 32 * cur) := fun hlt' => by
    obtain ⟨e, hem, hea⟩ := hnx hlt'; rw [← hea]; exact mkH e hem
  rcases growInplace_none_cases hcur hlt hnone with hcase | ⟨hin, hfree, hav, hgr, hno⟩
  · -- the next chunk past the end, used, or too small
    have hcase' : s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨
        (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
          (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1) ∨
        (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
          (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 ∧ cur + (s.hdr (ptr - 32 + 32 * cur)).size / 2 < req + 1) := by
      by_cases hin : s.base + 1073741824 ≤ ptr - 32 + 32 * cur
      · exact Or.inl hin
      · have hH' := hnc (by omega)
        by_cases hodd : (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1
        · exact Or.inr (Or.inl ⟨by omega, hH', hodd⟩)
        · refine Or.inr (Or.inr ⟨by omega, hH', by omega, ?_⟩)
          rcases hcase with h | h | h
          · omega
          · exfalso; unfold wordUsed at h; simp at h; omega
          · unfold wordSize at h; exact h
    obtain ⟨ω1, μ1, r1, -, ww1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_pre (p := p) (P := P)
      (R := env.rel hostCostMax) x ω μ s H F sp ptr req cur hrep' h1 h8 h7 h10 hsp hsp1 hb0 hbT
      (hHF _ (Or.inl (mkH _ hXm))) (by omega) (mkH _ hXm) hHF (by rw [hXs]; unfold sizeWord; simp) hlt hr1 hc1
      (by omega) hcase' hHFT hS hw
    exact ⟨ω1, μ1, r1.mono (by omega),
      hrep.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))),
      HeapPages.of_eq hp ww1, fun a h1 h2 => by rw [ww1]; exact hst a h1 h2, fr1, st0, st5, st6, a1,
      by rw [a6, husable], a7, a8, a9, a10⟩
  · -- the next chunk free and large enough, the host refusing the growth
    obtain ⟨e, hem, hea⟩ := hnx hin
    have hes := henc e hem
    rw [hea] at hes
    have hel := htiles.mem_lt e hem
    have hw0 : (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 := by
      unfold wordUsed at hfree; simp only [beq_eq_false_iff_ne, ne_eq] at hfree; omega
    have hw2 : (s.hdr (ptr - 32 + 32 * cur)).size = 2 * e.size := by
      rw [hes] at hw0 ⊢; unfold sizeWord at hw0 ⊢
      cases hu : e.used
      · simp
      · simp [hu] at hw0
    have hws : wordSize (s.hdr (ptr - 32 + 32 * cur)).size = e.size := by rw [hw2]; unfold wordSize; omega
    rw [hws] at hav hgr hno
    have hR : pb < pagesOf (s.base + 32 * ((ptr - 32 + 32 * (req + 1) - s.base) / 32 +
        (if cur + e.size - (req + 1) = 0 then 0 else 1))) := by
      unfold growTo at hno; have := of_decide_eq_false hno; omega
    obtain ⟨ω1, μ1, r1, rep1, hp1, hst1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_pre_growG
      (p := p) (P := P) env x ω μ s H F sp ptr req cur e.size hrep' h1 h8 h7 h10 hsp hsp1 hb0 hbT hA
      (hHF _ (Or.inl (mkH _ hXm))) (by omega) (mkH _ hXm) hHF (by rw [hXs]; unfold sizeWord; simp) hlt hr1 hc1
      hin (hnc hin) hw2 (by omega) (by omega) hav (by omega) _ rfl hgr pb ph hbd h48 hhb hbs hR hHFT hS hSb hp hst
    exact ⟨ω1, μ1, r1, hrep.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))),
      hp1, hst1, fr1, st0, st5, st6, a1, by rw [a6, husable], a7, a8, a9, a10⟩

/-- `fallback_entryG` for the refine contract (`refineHeap env`). -/
theorem fallback_entry {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s : State) (sp ptr req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 42980 ω μ x 43259 ω' μ' x 120 ∧ Rep μ' s ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧
      ω'[1] = UInt64.ofNat (sp - 152) ∧ ω'[6] = UInt64.ofNat (usable s ptr) ∧ ω'[7] = UInt64.ofNat 196792 ∧
      ω'[8] = UInt64.ofNat ptr ∧ ω'[9] = ω[9] ∧ ω'[10] = UInt64.ofNat req :=
  fallback_entryG (p := p) (P := P) (refineHeap env) x ω μ s sp ptr req pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone h1 h8 h7 h10 hsp hsp1 hb0 hbT hA (S0 := S0) (S1 := S1) hHT hS hSb hp hst

/-- **`fallback_refines_heapG` with the copy**: as `fallback_refines_heapG`, and the new block q's
    first `usable s ptr`·32 octets are the old block's as they were at `realloc_impl`'s entry
    (42980). -/
theorem fallback_refines_heap_dataG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  refine ⟨realloc_fallback hr hnone ha, ?_⟩
  obtain ⟨ω1, μ1, r1, rep1, hp1, hst1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_entryG
    (p := p) (P := P) env x ω μ s sp ptr req pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone h1 h8 h7 h10
    (by omega) hsp1 hb0 hbT hA hHT ⟨by omega, by omega⟩ hSb hp hst
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, dat2, r2, rep2, wf2, fo2, hpH, hst2, stk2, e7, e0, e1, e5, e6⟩ := fallback_tail_heap_dataG (p := p)
    (P := P) env x ω1 μ1 (hb := hb) s s1 (sp - 152) ptr req q (usable s ptr) ω[5].toNat ω[6].toNat pb ph hwf
    rep1 hfo hc rfl hr hbd h48 hhb hbs ha hcost a1 a7 a8 (by rw [a9]; exact h9) a10 a6 (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) (by omega) hba hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  have hdl := data_lt hwf hbT hc
  have dat : μ2.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) := by
    rw [dat2]; exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  exact ⟨ω2, μ2, dat, (r1.trans r2).mono (by omega), rep2, wf2, fo2, hpH, hst2,
    fun a h1 h2 => (stk2 a h1 (by omega)).trans (fr1 a h1 (Or.inr h2)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

/-- `fallback_refines_heap_dataG` for the refine contract (`refineHeap env`). -/
theorem fallback_refines_heap_data {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', μ'.readN q (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr) ∧
      FreeStepsH p (refineContract env) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  fallback_refines_heap_dataG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr req q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h8 h7 h9 h10 h0 hsp hsp1 hsp8 hba hb0 hbT hA hfo (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **The binary's `realloc_impl` refines the model's `realloc`, through any fallback**: under
    `refineContract` (the model's `grow` the host's `growTo pb`, GP Appendix B Ω_♊), from memory
    holding a well-formed `s` (its first chunk's `prev` 0), ω₈ = ptr the data address of an
    allocated chunk, ω₉ = 1 (the alignment, one unit) and ω₁₀ = req above its usable size, when the
    model's `growInplace` fails (for any reason, the host's refusal to grow the heap included) and
    its `alloc` at one unit gives q and s₁ (growing the heap by at most 14 pages, or not): the
    model's `realloc` gives `(q, free s₁ ptr, true)`, and `realloc_impl` (42980) allocates q, copies
    the old usable size there, frees ptr and returns q into `realloc` (40805), memory holding
    `free s₁ ptr`, the heap's pages covering its allocated space, the caller's ω₀, ω₁, ω₅, ω₆
    restored and the stack from sp up untouched. -/
theorem fallback_refines_heapG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨e, ω', μ', -, h⟩ := fallback_refines_heap_dataG (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s s1 sp ptr req q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h8 h7 h9 h10 h0 hsp hsp1 hsp8 hba hb0 hbT hA hfo hHTs hHT hS hSb hp hst
  exact ⟨e, ω', μ', h⟩

/-- `fallback_refines_heapG` for the refine contract (`refineHeap env`). -/
theorem fallback_refines_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (sp ptr req q pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = some (q, s1))
    (hcost : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p (refineContract env) 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1220) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s1.base + 32 * s1.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  fallback_refines_heapG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s1 sp ptr req q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha hcost h1 h8 h7 h9 h10 h0 hsp hsp1 hsp8 hba hb0 hbT hA hfo (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

/-- **The binary's `realloc_impl` fails where the model's `realloc` does**: as
    `fallback_refines_heapG`, when the model's `alloc` returns `none`: the model's `realloc` is
    `none`, and `realloc_impl` returns null into `realloc` (40805, through 43326) with memory still
    holding `s`, the heap's pages as they were, and memory changed only in the stack below sp (in
    sp − 304 … sp): the old block, and the whole heap, untouched. -/
theorem fallback_refines_failG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr req pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = none ∧
      ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 42980 ω μ x 40805 ω' μ' x 640 ∧ Rep μ' s ∧
        HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → (a < sp - 304 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  refine ⟨realloc_fallback_none hr hnone ha, ?_⟩
  have hp32 : ptr < 4294967296 := by
    obtain ⟨c, hcm, hca, -⟩ := hc
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    have := ht.mem_lt c hcm
    have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    omega
  obtain ⟨ω1, μ1, r1, rep1, hp1, hst1, fr1, st0, st5, st6, a1, -, a7, a8, a9, a10⟩ := fallback_entryG
    (p := p) (P := P) env x ω μ s sp ptr req pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone h1 h8 h7 h10
    (by omega) hsp1 hb0 hbT hA hHT ⟨by omega, by omega⟩ hSb hp hst
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, r2, rep2, hp2, hst2, fr2, e7, e0, e1, e5, e6⟩ := fallback_tail_failG (p := p) (P := P) env x
    ω1 μ1 (hb := hb) s (sp - 152) ptr req ω[5].toNat ω[6].toNat pb ph hwf rep1 hbd h48 hhb hbs ha (by omega)
    a1 a7 a8 (by rw [a9]; exact h9) a10 hp32
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ hSb hp1 hst1
  exact ⟨ω2, μ2, (r1.trans r2).mono (by omega), rep2, hp2, hst2,
    fun a h1 h2 => (fr2 a h1 (by omega) (by omega)).trans (fr1 a h1 (by omega)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

/-- `fallback_refines_failG` for the refine contract (`refineHeap env`). -/
theorem fallback_refines_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr req pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hnone : growInplace (growTo pb) s ptr req = none) (ha : alloc (growTo pb) hb 1 req s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr 1 req = none ∧
      ∃ ω' μ', FreeStepsH p (refineContract env) 42980 ω μ x 40805 ω' μ' x 640 ∧ Rep μ' s ∧
        HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → (a < sp - 304 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  fallback_refines_failG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s sp ptr req pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hnone ha h1 h8 h7 h9 h10 h0 hsp hsp1 hb0 hbT hA (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst

end Services.Bootstrap.Alloc
