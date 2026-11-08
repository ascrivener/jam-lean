import Services.Bootstrap.Alloc.ReallocFallbackWrap

/-!
# The binary's `realloc` refines every outcome of the model's `realloc`, at one unit's alignment

`realloc_wrap_cases` splits the model's `realloc` (GP Appendix B's Ω_♊ as the host's `growTo pb`)
on its own cases and composes the theorem for each:

| model                                  | binary                         | theorem                      |
|----------------------------------------|--------------------------------|------------------------------|
| new size = usable, or below (nonzero)  | in place, maybe shrunk         | `realloc_wrap_inplace`       |
| new size 0 (usable nonzero)            | free, null                     | `realloc_wrap_zero`          |
| `growInplace` some, same allocated     | grow in place                  | `realloc_wrap_grow`          |
| `growInplace` some, heap grown         | grow in place, `grow_heap`     | `realloc_wrap_grow_heap`     |
| `growInplace` none, `alloc` some       | alloc + copy + free            | `realloc_wrap_fallback`      |
| `growInplace` none, `alloc` none       | null, nothing in the heap moved | `realloc_wrap_fallback_fail` |

Assumed throughout: an alignment of 1 … 32 octets (one unit), a new size below 2²⁵ − 1 units,
not both the new size and the usable size 0, and a heap bound within 14 pages of the heap's top
(each `grow_heap` call is costed for at most 14 pages).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem pagesOf_le {x h : Nat} (hx : x ≤ 4096 * h) : pagesOf x ≤ h := by unfold pagesOf; split <;> omega

/-- `growInplace` with the host's `growTo pb`, growing the allocated space, stays within pb pages. -/
theorem growInplace_pages {pb : Nat} {s s' : State} {ptr req : Nat} (hr : usable s ptr < req)
    (h : growInplace (growTo pb) s ptr req = some s') (hg : s'.allocated ≠ s.allocated) :
    pagesOf (s.base + 32 * s'.allocated) ≤ pb := by
  obtain ⟨-, -, -, -, hgr, he⟩ := growInplace_grown rfl (by unfold usable at hr; omega) h hg
  rw [he]
  simp only [freeFinal_allocated, growHdr, setHdr_allocated, unregister_allocated]
  unfold growTo at hgr; exact of_decide_eq_true hgr

/-- `alloc` with the host's `growTo pb`, growing the allocated space, stays within pb pages. -/
theorem alloc_pages {pb hb req q : Nat} {s s1 : State} (hwf : WF s)
    (h : alloc (growTo pb) hb 1 req s = some (q, s1)) (hg : s1.allocated ≠ s.allocated) :
    pagesOf (s.base + 32 * s1.allocated) ≤ pb := by
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, -, -, -, -, hgr, -, rfl⟩ := alloc1_grown h hg
  simp only [allocPost_allocated]
  unfold growTo at hgr; exact of_decide_eq_true hgr

/-- **`realloc_wrap_cases` with the copy**: as `realloc_wrap_cases`, and when the model's
    `realloc` moves the block (returns r other than ptr and null, which only its fallback does),
    r's first `usable s ptr`·32 octets are the old block's as they were when `realloc` (40701) was
    called. -/
theorem realloc_wrap_cases_data {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) := by
  have hwr := HeapPages.wrAt hp hhb hst
  have hal : al + 31 < 68719476736 := by omega
  by_cases hin : (size + 31) / 32 ≤ usable s ptr ∧ size ≠ 0
  · -- in place (the same usable size, or shrunk)
    obtain ⟨s', e, ω', μ', run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
      realloc_wrap_inplace (p := p) (P := P) (R := refineContract env) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al size hwf hrep hc
        hin.2 hin.1 h1 h7 h9 h10 hal (by omega) (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, ph, HeapPages.of_eq hp ww, Nat.le_refl _, hhb⟩,
      fun hrr => by rw [e] at hrr; cases hrr⟩
  by_cases hs0 : size = 0
  · -- to size 0: freed, null
    subst hs0
    obtain ⟨e, ω', μ', run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
      realloc_wrap_zero (p := p) (P := P) (R := refineContract env) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al hwf hrep hc
        (hz rfl) h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr _ hn2 => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn2,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr
        exact ⟨e7, rep, wf, fo, ph, HeapPages.of_eq hp ww, Nat.le_refl _, hhb⟩,
      fun hrr => by rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr⟩
  have hr : usable s ptr < (size + 31) / 32 := by omega
  cases hg : growInplace (growTo pb) s ptr ((size + 31) / 32) with
  | some s' =>
    by_cases hng : s'.allocated = s.allocated
    · -- grown in place
      obtain ⟨e, ω', μ', run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
        realloc_wrap_grow (p := p) (P := P) (R := refineContract env) (hb := hb) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 hg hng
          h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo hl hHT ⟨by omega, by omega⟩ hwr
      exact ⟨ω', μ',
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
        fun r s'' b hrr => by
          rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, ph, HeapPages.of_eq hp ww, Nat.le_refl _, hhb⟩,
        fun hrr => by rw [e] at hrr; cases hrr⟩
    · -- grown in place, the heap grown
      obtain ⟨e, ω', μ', run, rep, wf, fo, e7, cl, ⟨h', hpH, -, hph, hpb⟩, hst', stk, e0, e1, e5, e6⟩ :=
        realloc_wrap_grow_heap (p := p) (P := P) (hb := hb) env x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs hg
          hng h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo
          (Nat.le_trans (growInplace_pages hr hg hng) hcost) hl hHT ⟨by omega, by omega⟩ hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, h', hpH, hph, hpb⟩,
        fun hrr => by rw [e] at hrr; cases hrr⟩
  | none =>
    cases ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s with
    | some qs =>
      obtain ⟨q, s1⟩ := qs
      have hc1 : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14 := by
        by_cases hng : s1.allocated = s.allocated
        · rw [hng]; exact Nat.le_trans (pagesOf_le hHT) (by omega)
        · exact Nat.le_trans (alloc_pages hwf ha hng) hcost
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, -, hph, hpb⟩, hst', stk, e0, e1, e5, e6⟩ :=
        realloc_wrap_fallback_data (p := p) (P := P) (hb := hb) env x ω μ s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha hc1 h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ _ => by rw [e] at hrr; cases hrr; exact dat,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, h', hpH, hph, hpb⟩,
        fun hrr => by rw [e] at hrr; cases hrr⟩
    | none =>
      obtain ⟨e, ω', μ', run, rep, e7, cl, hp', hst', fr, -, e0, e1, e5, e6⟩ :=
        realloc_wrap_fallback_fail (p := p) (P := P) (hb := hb) env x ω μ s sp ptr al size pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha h1 h7 h9 h10 hal1 hal2 hsp hsp1 hb0 hbT hA hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr => by rw [e] at hrr; cases hrr,
      run.mono (by omega), cl, hst',
        fun a h1 h2 => fr a h1 (Or.inr h2) (Or.inr (by omega)) (Or.inr (by omega)), e0, e1, e5, e6,
        fun r s'' b hrr => (by rw [e] at hrr; cases hrr), fun _ => ⟨e7, rep, hp'⟩⟩

/-- **The binary's `realloc` refines the model's `realloc`, every outcome** (alignment 1 … 32
    octets): under `refineContract` (the model's `grow` the host's `growTo pb`, GP Appendix B Ω_♊),
    from memory holding a well-formed `s` (its first chunk's `prev` 0), the lock byte clear, ω₇ the
    data address of an allocated chunk, ω₉ = `al` and ω₁₀ = `size` octets: `realloc` (40701)
    reaches its return (the `jumpInd` at 40821) with the lock byte clear again, the stack writable,
    the stack from sp up untouched and the caller's ω₀, ω₁, ω₅, ω₆ restored, and

    * if the model's `realloc` gives `(r, s', _)`: ω₇ = r and memory holds `s'` (well-formed, its
      first chunk's `prev` 0), the heap's pages grown to some h' ≤ pb;
    * if it gives `none`: ω₇ = 0 (null) and memory still holds `s`, the heap's pages as they were. -/
theorem realloc_wrap_cases {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) := by
  obtain ⟨ω', μ', -, h⟩ := realloc_wrap_cases_data (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s sp ptr al size pb ph hwf hrep hc hr1 hz hbd h48 hhb hbs hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hSb hp hst
  exact ⟨ω', μ', h⟩

end Services.Bootstrap.Alloc
