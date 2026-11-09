import Services.Bootstrap.Decode.HeapFrame
import Services.Bootstrap.Decode.HeapWrap
import Services.Bootstrap.Alloc.AllocWrap
import Services.Bootstrap.Alloc.AllocFailRefines

/-!
# The allocator's context, and one call of its `alloc` wrapper

`HeapCtx env pb S0 S1 μ s`: memory μ holds picoalloc's state `s` (well formed, with the first
chunk's `prev` 0 and the lock clear), the heap's writable pages run from 48 to some h ≤ pb (the blob's
heap bound) and cover the allocated space, and the stack S0 … S1 above the heap is writable. Under
`refineContractK cap env` with a cap of at least 2^27 (so any growth of the heap is within it),
one call of the `alloc` wrapper (40494 → 40611) either returns the model's block with the context
kept for the new state (`alloc_call`, from main's `alloc_wrap_refines` and
`alloc_wrap_refines_growK`), or returns null when the model's `alloc` fails
(`alloc_wrap_refines_failK`).
-/

namespace Services.Bootstrap.Decode.HeapCtx

open PVM Picoalloc Services.Bootstrap.Code Services.Bootstrap.Alloc JAM

/-- **The allocator's context**: picoalloc's state `s` in memory, its heap pages, and the stack. -/
structure HeapCtx (env : RefineHost.Env) (pb S0 S1 : Nat) (μ : Memory) (s : State) : Prop where
  wf : WF s
  rep : Rep μ s
  fo : FirstOk s
  lock : rdN μ 206848 1 = 0
  hb0 : 206864 ≤ s.base
  hbT : s.base + 1073741824 < 2147483648
  hA : s.allocated < 2147483648
  bd : heapBounds env.code = (48, pb)
  pages : ∃ ph, 48 ≤ ph ∧ ph ≤ pb ∧ HeapPages μ 48 pb ph ∧ 208896 ≤ 4096 * ph ∧
    s.base + 32 * s.allocated ≤ 4096 * ph
  hSb : 4096 * pb ≤ S0
  hS1 : S1 < 4294967296
  st : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true

theorem alloc_base {grow : Grow} {hb r p : Nat} {s s' : State} (hwf : WF s)
    (h : alloc grow hb 1 r s = some (p, s')) : s'.base = s.base := by
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, a1, -, -, -, -, -, -, rfl⟩ := alloc1_eq h
  rw [allocPost_base]

/-- **One call of the `alloc` wrapper**, from 40494 with ω₇ = size and ω₈ = align (1 … 32) and the
    stack pointer in S0 + 168 … S1: either the model's `alloc` returns block `ptr` and state `s'` and
    the wrapper returns `ptr` at 40611 with the context kept for `s'`, every allocated chunk of `s`
    still allocated, the block a new allocated chunk at `ptr − 32` of ⌈size/32⌉ + 1 units, the heap
    off the new headers kept (`HKeepG`), the stack from sp up untouched and ω₀, ω₁, ω₅, ω₆ restored; or the model's
    `alloc` fails and the wrapper returns null. -/
theorem alloc_call {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp size al pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (ptr, s') ∧
      FreeStepsH p (refineContractK cap env) 40494 ω μ x 40611 ω' μ' x 540 ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, (size + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (size + 31) / 32 + 1, true⟩) ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) ∧ ω'[7] = UInt64.ofNat ptr ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 ((size + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (refineContractK cap env) 40494 ω μ x 40611 ω' μ' x 540 ∧ ω'[7] = UInt64.ofNat 0 ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp1 : sp < 4294967296 := by have := H.hS1; omega
  have hbs : pb < 4294967296 := by have := H.hSb; omega
  cases ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s with
  | none =>
    right
    obtain ⟨ω', μ', run, -, e7, -, -, -, efr, e0, e1, e5, e6⟩ := alloc_wrap_refines_failK (p := p) (P := P)
      (hb := hb) (S0 := S0) (S1 := S1) env cap hcap (by omega) x ω μ s sp size al pb ph H.wf H.rep H.bd h48 hhb
      hbs ha h1 h7 h8 hal hal1 hs hsp hsp1 H.hb0 H.hbT H.hA H.lock hHTs hSTk H.hSb hp H.st hHT
    exact ⟨rfl, ω', μ', run, e7, efr, e0, e1, e5, e6⟩
  | some q =>
    obtain ⟨ptr, s'⟩ := q
    left
    have hb' := alloc_base H.wf ha
    have keep := HeapFrame.alloc_keeps_used H.wf ha
    have fo' := alloc_first H.wf H.fo ha
    obtain ⟨pre, post, S, hcs, -, hcs'⟩ := alloc_chunks H.wf ha
    have hnew : (⟨ptr - 32, (size + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' := by
      rw [hcs']; exact List.mem_append_right _ List.mem_cons_self
    have hfresh : ∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (size + 31) / 32 + 1, true⟩ := by
      intro d hd hu e
      have ht := H.wf.2.2.2.1
      unfold TilesOk at ht
      rw [hcs] at ht hd
      have hfree : (⟨ptr - 32, S, false⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, S, false⟩ :: post :=
        List.mem_append_right _ List.mem_cons_self
      have := Tiles.addr_inj ht d hd _ hfree (by rw [e])
      rw [this] at hu; simp at hu
    by_cases hg : s'.allocated = s.allocated
    · obtain ⟨ω', μ', run, rep', wf', e7, lk, ww, efr, e0, e1, e5, e6, hk⟩ :=
        HeapWrap.alloc_wrap_refines_hdr (p := p) (P := P)
        (R := refineContractK cap env) (HT := 4096 * ph) (S0 := S0) (S1 := S1) x ω μ s s' sp size al ptr H.wf
        H.rep ha hg h1 h7 h8 hal hal1 hs hsp hsp1 H.hb0 H.hbT H.hA H.fo H.lock hHTs hSTk hHT
        (HeapPages.wrAt hp hhb H.st)
      refine ⟨ptr, s', ω', μ', rfl, run.mono (by omega), ⟨wf', rep', fo', lk, by rw [hb']; exact H.hb0,
        by rw [hb']; exact H.hbT, by rw [hg]; exact H.hA, H.bd,
        ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', hg]; exact hHT⟩, H.hSb, H.hS1,
        fun a h1 h2 => by rw [ww]; exact H.st a h1 h2⟩, keep, hnew, hfresh, hk, e7, efr, e0, e1, e5, e6⟩
    · obtain ⟨bin, -, -, -, -, hgrow, -, hs'⟩ := alloc1_grown (by rw [alloc_one H.wf.1] at ha; exact ha) hg
      have hpg : pagesOf (s.base + 32 * s'.allocated) ≤ pb := by
        rw [hs', allocPost_allocated]
        simpa [growTo] using hgrow
      obtain ⟨ω', μ', run, rep', wf', e7, lk, ⟨h', hp', hHT', hph', hh'b⟩, wst, efr, e0, e1, e5, e6, hk⟩ :=
        HeapWrap.alloc_wrap_refines_growK_hdr (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env cap hcap x ω μ s s'
          sp size al ptr pb ph H.wf H.rep H.bd h48 hhb hbs ha hg h1 h7 h8 hal hal1 hs hsp hsp1 H.hb0 H.hbT H.hA
          H.fo H.lock (by have := H.hSb; omega) hHTs hSTk H.hSb hp H.st hHT
      refine ⟨ptr, s', ω', μ', rfl, run, ⟨wf', rep', fo', lk, by rw [hb']; exact H.hb0,
        by rw [hb']; exact H.hbT, by have := H.hSb; rw [hb'] at hHT'; omega, H.bd,
        ⟨h', by omega, hh'b, hp', by omega, hHT'⟩, H.hSb, H.hS1, wst⟩, keep, hnew, hfresh, hk, e7, efr, e0, e1, e5, e6⟩

end Services.Bootstrap.Decode.HeapCtx
