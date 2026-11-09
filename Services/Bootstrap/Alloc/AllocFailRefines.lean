import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.AllocFailModel
import Services.Bootstrap.Alloc.AllocFailGrow
import Services.Bootstrap.Alloc.AllocWrapGrow

/-!
# The binary's `alloc` failing where the model fails

When the model's `alloc` (alignment one unit, the heap initialised, `grow` the host's `growTo pb`)
returns `none`, the binary's `alloc_impl` returns null (ω₇ = 0) and so does the locked wrapper
`alloc`, leaving memory holding the same state, the heap's pages as they were and the caller's
stack untouched. With `alloc_refines_grow` / `alloc_wrap_refines_grow` (and their no-growth
forms), a caller covers every outcome by case analysis on the model's result.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The binary's `alloc_impl` fails where the model's `alloc` does** (alignment one unit, the
    heap in use; under `refineContract`, the model's `grow` the host's `growTo pb`, GP Appendix B
    Ω_♊): from memory holding a well-formed `s`, when the model returns `none` for `req` units, the
    binary returns null in ω₇, memory still holds `s`, the heap's pages are as they were, the
    caller's ω₀, ω₁, ω₅, ω₆ are restored and the stack from sp up is untouched. The request is
    below 2³¹ units (as the wrapper `alloc` ensures): the binary sizes it in 32-bit arithmetic.
    Under `refineContractK cap`, for any cap covering the call's 275. -/
theorem alloc_refines_failKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = none) (hrq : req < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 41177 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) := by
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
  suffices key : ∃ ω' μ', FreeStepsH p (env.rel cap) 41177 ω μ x 41423 ω' μ' x 500 ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → μ'.read a = μ.read a) by
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, hp', hst', fr⟩ := key
    exact ⟨ω', μ', run, hrep.congr_lock hwf hb0 hbT (fun a _ ha2 _ => fr a (by omega) (Or.inl (by omega))),
      e7, e0, e5, e6, e1, hp', hst', fun a ha h' => fr a ha (Or.inr h')⟩
  rcases alloc1_none h with hbig | ⟨hmax, hnone⟩ | ⟨bin, hmax, hbin, hsmall⟩ | ⟨bin, hmax, hbin, hS, hlt, hgr⟩
  · rw [maxSize_val] at hbig
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_big (p := p) (P := P) (R := env.rel cap)
      x ω μ sp req s.base h1 h7 h8 h9 hsp hsp1 hbase hb0' hbig hrq hHTs hSTk hw
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, HeapPages.of_eq hp ww,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, fr⟩
  · have hm : req + 1 ≤ 33554432 := by rw [← maxSize_val]; exact hmax
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_nobin (p := p) (P := P) (R := env.rel cap)
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
  · obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, ww, fr⟩ := alloc_fail_small (p := p) (P := P) (R := env.rel cap)
      x ω μ s sp req bin C (s.hdr C).size hbits h1 h7 h8 h9 hsp hsp1 hbase hb0' hpri hsec hm hbin hheads hsz
      (by omega) (by rw [hwS]; exact hsmall) hHTs hSTk ⟨by omega, by omega⟩ hw
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, HeapPages.of_eq hp ww,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, fr⟩
  · have hR : pb < pagesOf (s.base + 32 * ((C - s.base) / 32 + 1 + req + (if S - req - 1 = 0 then 0 else 1))) := by
      unfold growTo at hgr; have := of_decide_eq_false hgr; omega
    obtain ⟨ω', μ', run, e7, e0, e5, e6, e1, hp', hst', fr⟩ := alloc_fail_growKG (p := p) (P := P) (S0 := S0)
      (S1 := S1) env cap hcap h275 x ω μ s sp req bin C (s.hdr C).size pb ph hbits h1 h7 h8 h9 hsp hsp1 hbase hb0' hpri hsec halc
      hal hm hbin hheads hsz hbT (by omega) (by rw [hwS]; exact hS) (by rw [hwS]; omega) (by rw [hwS]; exact hlt)
      hbd h48 hhb hbs (by rw [hwS]; exact hR) hHTs hSTk hSb ⟨by omega, by omega⟩ hp hst
    exact ⟨ω', μ', run.mono (by omega), e7, e0, e5, e6, e1, hp', hst', fr⟩

/-- `alloc_refines_failKG` for the refine contract (`refineHeap env`). -/
theorem alloc_refines_failK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp req pb ph : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 req s = none) (hrq : req < 2147483648)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hal : s.allocated < 2147483648)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 41177 ω μ x 41423 ω' μ' x 500 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[0] = ω[0] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[1] = ω[1] ∧
      HeapPages μ' 48 pb ph ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) :=
  alloc_refines_failKG (p := p) (P := P) (refineHeap env) cap hcap h275 x ω μ (hb := hb) s sp req pb ph hwf hrep hbd h48 hhb hbs h hrq h1 h7 h8 h9 hsp hsp1 hb0 hbT hal (S0 := S0) (S1 := S1) hHTs hSTk hSb hp hst hHT

/-- `alloc_refines_failK` at `hostCostMax`, the cap of `refineContract`. -/
theorem alloc_refines_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
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
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) :=
  alloc_refines_failK (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1)
    env hostCostMax (by decide) (by decide) x ω μ s sp req pb ph hwf hrep hbd h48 hhb hbs h hrq h1
    h7 h8 h9 hsp hsp1 hb0 hbT hal hHTs hSTk hSb hp hst hHT

/-- **The binary's `alloc` fails where the model's `alloc` does** (under `refineContract`, the
    model's `grow` the host's `growTo pb`): from memory holding a well-formed `s`, the lock byte
    clear, ω₇ = `size` and ω₈ = `align` octets (1 … 32), when the model returns `none` for the
    `⌈size/32⌉` units, `alloc` (40494) reaches its return (the `jumpInd` at 40611) with null in ω₇,
    memory still holding `s`, the lock byte clear again, the heap's pages as they were, the
    caller's ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched.
    Under `refineContractK cap`, for any cap covering the call's 275. -/
theorem alloc_wrap_refines_failKG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp size al pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (env.rel cap) 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ rdN μ' 206848 1 = 0 ∧ HeapPages μ' 48 pb ph ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hw := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a7, a8, a9, -, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    al_lock (p := p) (P := P) (R := env.rel cap) (S0 := S0) (S1 := S1) x ω μ sp size al h1 h7 h8 hal hal1 hs
      (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, e7, e0, e5, e6, e1, hp2, hst2, stk2⟩ :=
    alloc_refines_failKG (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap h275 x ω1 μ1 s (sp - 16) _ pb ph hwf rep1 hbd h48
      hhb hbs h (by omega) a1 a7 a8 a9 (by omega) (by omega) hb0 hbT hA hHTs ⟨by omega, by omega⟩ hSb
      (HeapPages.of_eq hp ww1) (fun a h1 h2 => by rw [ww1]; exact hst a h1 h2) hHT
  have rj := al_ret_jump (p := p) (P := P) (R := env.rel cap) x ω2 μ2 (by rw [e0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    al_unlock (p := p) (P := P) (R := env.rel cap) (S0 := S0) (S1 := S1) x ω2 μ2 (sp - 16) (by rw [e1, a1])
      (by rw [e5, a5]) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hp2 hhb hst2)
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock hwf hb0 hbT (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)),
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl, HeapPages.of_eq hp2 ww3,
    fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    exact rd_restore st8
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    exact rd_restore st16
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- `alloc_wrap_refines_failKG` for the refine contract (`refineHeap env`). -/
theorem alloc_wrap_refines_failK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (h275 : 275 ≤ cap)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp size al pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ rdN μ' 206848 1 = 0 ∧ HeapPages μ' 48 pb ph ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  alloc_wrap_refines_failKG (p := p) (P := P) (refineHeap env) cap hcap h275 x ω μ (hb := hb) s sp size al pb ph hwf hrep hbd h48 hhb hbs h h1 h7 h8 hal hal1 hs hsp hsp1 hb0 hbT hA hl (S0 := S0) (S1 := S1) hHTs hSTk hSb hp hst hHT

/-- `alloc_wrap_refines_failK` at `hostCostMax`, the cap of `refineContract`. -/
theorem alloc_wrap_refines_fail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp size al pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s ∧
      ω'[7] = UInt64.ofNat 0 ∧ rdN μ' 206848 1 = 0 ∧ HeapPages μ' 48 pb ph ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  alloc_wrap_refines_failK (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1)
    env hostCostMax (by decide) (by decide) x ω μ s sp size al pb ph hwf hrep hbd h48 hhb hbs h h1
    h7 h8 hal hal1 hs hsp hsp1 hb0 hbT hA hl hHTs hSTk hSb hp hst hHT

end Services.Bootstrap.Alloc
