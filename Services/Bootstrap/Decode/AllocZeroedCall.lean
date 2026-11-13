import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Alloc.AllocZeroedGrow
import Services.Bootstrap.Alloc.AllocFailRefines
import Services.Bootstrap.Alloc.ReallocFallbackTail
import Services.Bootstrap.Decode.HeapFrame

/-!
# One call of `alloc_impl` with the zero flag, the lock held

`fetch_vec` (47417) takes the allocator's lock itself and calls `alloc_impl` (41177) directly, with
ω₁₀ = 1: a zeroed allocation. `alloc_implZ_callG` is that call from the context with the lock held
(`HeapCtxL`), for any zero flag z: either the model's `alloc` returns block `ptr` and state `s'` and
the call returns `ptr` to the caller's return target with the context (lock held) kept for `s'`, or
the model's `alloc` fails and the call returns null. The block's data is not described: when the
flag is set the tail may zero it (`memzero`), and the heap is kept off the headers and off the
block's data (`HKeepGD`).
-/

namespace Services.Bootstrap.Decode.AllocZeroedCall

open PVM Picoalloc Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
open Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `alloc_impl`'s return (41423) to t, the address ω₀ resolves to. -/
theorem ai_ret {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) : FreeStepsH p R 41423 ω μ x t ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0, hret, hjt, hbt]

/-- The context with the lock held, for μ' = μ's twin with μ₀'s lock words: from the context's facts
    at μ' (all but the lock). -/
theorem heldOf {code : ByteArray} {pb S0 S1 : Nat} {μ₀ μ' : Memory} {s s' : State}
    (H₀ : HeapCtxC code pb S0 S1 μ₀ s) (wf' : WF s') (rep' : Rep μ' s') (fo' : FirstOk s')
    (hb0 : 206864 ≤ s'.base) (hbT : s'.base + 1073741824 < 2147483648) (hA : s'.allocated < 2147483648)
    (pages : ∃ ph, 48 ≤ ph ∧ ph ≤ pb ∧ HeapPages μ' 48 pb ph ∧ 208896 ≤ 4096 * ph ∧
      s'.base + 32 * s'.allocated ≤ 4096 * ph)
    (st : ∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) (ro : ∀ a, a < 196608 → μ'.writable a = false) :
    HeapCtxL code pb S0 S1 μ' s' := by
  let μ₀' := (μ'.writeN 196608 (μ₀.readN 196608 8)).writeN 206848 (μ₀.readN 206848 4)
  have ag' : ∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
      μ'.read a = μ₀'.read a := fun a ha h1 h2 => by
    simp only [μ₀']
    rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Memory.length_readN]; omega)
        (by simp only [Memory.length_readN, two32]; omega) (by simp only [two32]; omega),
      Memory.read_writeN_disjoint _ _ _ _ (by simp only [Memory.length_readN]; omega)
        (by simp only [Memory.length_readN, two32]; omega) (by simp only [two32]; omega)]
  have wa' : ∀ a, μ₀'.writable a = μ'.writable a := fun a => by
    simp only [μ₀', Memory.writable_writeN]
  have hlk : rdN μ₀' 206848 1 = 0 := by
    rw [← H₀.lock]
    apply rdN_frame
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [μ₀']
    rw [show (206848 + 0 : Nat) = 206848 + 0 from rfl,
      Memory.read_writeN_at _ _ _ (by simp only [Memory.length_readN, two32]; omega) 0
        (by simp only [Memory.length_readN]; omega)]
    simp [Memory.readN]
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := pages
  exact ⟨μ₀', ⟨wf', rep'.congr_lock wf' hb0 hbT
      (fun a ha1 ha2 ha3 => (ag' a (by omega) (Or.inr (by unfold A0 at ha1; omega)) ha3).symm),
    fo', hlk, hb0, hbT, hA, H₀.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp (fun a => (wa' a).symm), hHTs, hHT⟩,
    H₀.hSb, H₀.hS1, fun a h1 h2 => by rw [wa']; exact st a h1 h2, fun a ha => by rw [wa']; exact ro a ha⟩,
    ag', fun a => (wa' a).symm⟩

/-- **One call of `alloc_impl` (41177) with the zero flag z, the lock held**, under `HeapHost`'s
    relation with a cap of at least 2^27: with ω₇ = 196792 (the allocator), ω₈ = 1 (alignment one
    unit), ω₉ = req ≥ 1 units, ω₁₀ = z, and a return address ω₀ that **j** resolves to tg, either the
    model's `alloc` returns block `ptr` and state `s'` and the call returns `ptr` (ω₇) at tg with the
    context, lock held, kept for `s'`, every allocated chunk of `s` still allocated, the block a new
    allocated chunk at `ptr − 32` of req + 1 units, the heap off the new headers and the block's data
    kept (`HKeepGD`), the stack from sp up untouched and ω₀, ω₁, ω₅, ω₆ restored; or the model's
    `alloc` fails and the call returns null at tg. -/
theorem alloc_implZ_callG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp req z ret tg pb S0 S1 : Nat)
    (H : HeapCtxL env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat z) (hz : z < 18446744073709551616)
    (h0 : ω[0] = UInt64.ofNat ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true)
    (hreq : 1 ≤ req) (hrq : req < 2147483648)
    (hsp : 2147483800 ≤ sp) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 req s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 41177 ω μ x tg ω' μ' x (96 * req + 560) ∧
      HeapCtxL env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, req + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, req + 1, true⟩) ∧
      HKeepGD μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) ptr (ptr + 32 * req) ∧
      (∀ d ∈ chunks s, d.used = true → ∀ a, d.addr + 32 ≤ a → a < d.addr + 32 * d.size → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 req s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 41177 ω μ x tg ω' μ' x (96 * req + 560) ∧ ω'[7] = UInt64.ofNat 0 ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  obtain ⟨ph, h48, hhb, hp0, hHTs, hHT⟩ := H₀.pages
  have hp : HeapPages μ 48 pb ph := HeapPages.of_eq hp0 hwa
  have hsp1 : sp < 4294967296 := by have := H₀.hS1; omega
  have hbs : pb < 4294967296 := by have := H₀.hSb; omega
  have rep : Rep μ s := H₀.rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a ha1 ha2 ha3 => hag a (by omega) (Or.inr (by
    unfold A0 at ha1; omega)) ha3
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := fun a h1 h2 => by rw [hwa]; exact H₀.st a h1 h2
  have hro : ∀ a, a < 196608 → μ.writable a = false := fun a ha => by rw [hwa]; exact H₀.ro a ha
  cases ha : alloc (growTo pb) hb 1 req s with
  | none =>
    right
    obtain ⟨ω', μ', run, -, e7, e0, e5, e6, e1, -, -, efr⟩ := alloc_refines_failKG (p := p) (P := P)
      (hb := hb) (S0 := S0) (S1 := S1) env cap hcap (by omega) x ω μ s sp req pb ph H₀.wf rep H₀.bd h48 hhb
      hbs ha hrq h1 h7 h8 h9 hsp hsp1 H₀.hb0 H₀.hbT H₀.hA hHTs hSTk H₀.hSb hp hst hHT
    exact ⟨rfl, ω', μ', (run.trans (ai_ret (R := env.rel cap) (p := p) (P := P) x ω' μ' ret tg (e0.trans h0) hret
      hjt hbt)).mono (by omega), e7, efr, e0, e1, e5, e6⟩
  | some q =>
    obtain ⟨ptr, s'⟩ := q
    left
    have hb' := alloc_base H₀.wf ha
    have keep := HeapFrame.alloc_keeps_used H₀.wf ha
    have fo' := alloc_first H₀.wf H₀.fo ha
    obtain ⟨pre, post, S, hcs, hrS, hcs'⟩ := alloc_chunks H₀.wf ha
    have hnew : (⟨ptr - 32, req + 1, true⟩ : Chunk) ∈ chunks s' := by
      rw [hcs']; exact List.mem_append_right _ List.mem_cons_self
    have hfresh : ∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, req + 1, true⟩ := by
      intro d hd hu e
      have ht := H₀.wf.2.2.2.1
      unfold TilesOk at ht
      rw [hcs] at ht hd
      have hfree : (⟨ptr - 32, S, false⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, S, false⟩ :: post :=
        List.mem_append_right _ List.mem_cons_self
      have := Tiles.addr_inj ht d hd _ hfree (by rw [e])
      rw [this] at hu; simp at hu
    -- the data of every used chunk of s lies off the headers of s' and off the new block
    have hdata : ∀ (μ' : Memory), HKeepGD μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) ptr (ptr + 32 * req) →
        ∀ d ∈ chunks s, d.used = true → ∀ a, d.addr + 32 ≤ a → a < d.addr + 32 * d.size →
          μ'.read a = μ.read a := fun μ' hk d hd hu a h1 h2 => by
      have ht := H₀.wf.2.2.2.1
      unfold TilesOk at ht
      have hFm : (⟨ptr - 32, S, false⟩ : Chunk) ∈ chunks s := by rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
      have hdis := HeapFrame.Tiles.disjoint ht d hd _ hFm (by intro e; rw [e] at hu; simp at hu)
      have hFl := ht.mem_lt _ hFm
      have hoff := off_hdr_data (alloc_wf H₀.wf ha) (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT)
        (keep d hd hu) h1 h2
      simp only at hdis hFl
      exact hk a ⟨Or.inr hoff.1, hoff.2.1, hoff.2.2⟩ (by omega)
    by_cases hg : s'.allocated = s.allocated
    · obtain ⟨ω', μ', run, rep', wf', e7, e0, e5, e6, e1, ww, stk, hk⟩ := alloc_refines_hdrZ (p := p) (P := P)
        (R := env.rel cap) (HT := 4096 * ph) (S0 := S0) (S1 := S1) x ω μ s s' sp req ptr H₀.wf rep ha hg h1 h7 h8 h9
        z hz h10 ret tg h0 hret hjt hbt hreq hsp hsp1 H₀.hb0 H₀.hbT H₀.hA H₀.fo hHTs hSTk hHT
        (HeapPages.wrAt hp hhb hst)
      refine ⟨ptr, s', ω', μ', rfl, run.mono (by omega),
        heldOf H₀ wf' rep' fo' (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT) (by rw [hg]; exact H₀.hA)
          ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', hg]; exact hHT⟩
          (fun a h1 h2 => by rw [ww]; exact hst a h1 h2) (fun a ha => by rw [ww]; exact hro a ha),
        keep, hnew, hfresh, hk, hdata μ' hk, e7, stk, e0, e1, e5, e6⟩
    · obtain ⟨bin, -, -, -, -, hgrow, -, hs'⟩ := alloc1_grown (by rw [alloc_one H₀.wf.1] at ha; exact ha) hg
      have hpg : pagesOf (s.base + 32 * s'.allocated) ≤ pb := by
        rw [hs', allocPost_allocated]
        simpa [growTo] using hgrow
      obtain ⟨ω', μ', run, rep', wf', e7, e0, e5, e6, e1, ⟨h', hp', hHT', hph', hh'b⟩, wst, stk, hk⟩ :=
        alloc_refines_growK_hdrGZ (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env cap hcap x ω μ s s'
          sp req ptr pb ph H₀.wf rep H₀.bd h48 hhb hbs ha hg h1 h7 h8 h9 z hz h10 ret tg h0 hret hjt hbt hreq
          hsp hsp1 H₀.hb0 H₀.hbT H₀.hA H₀.fo (by have := H₀.hSb; have := pagesOf_ge (s.base + 32 * s'.allocated); omega)
          hHTs hSTk H₀.hSb hp hst hHT
      refine ⟨ptr, s', ω', μ', rfl, run,
        heldOf H₀ wf' rep' fo' (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT)
          (by have := H₀.hSb; rw [hb'] at hHT'; omega)
          ⟨h', by omega, hh'b, hp', by omega, hHT'⟩ wst
          (ro_of_pages hro fun q hq => (HeapHost.keepRO H₀.bd run).1 q (Or.inl hq)),
        keep, hnew, hfresh, hk, hdata μ' hk, e7, stk, e0, e1, e5, e6⟩

/-- **One call of `alloc_impl` (41177) with the zero flag 0, the lock held**: `alloc_implZ_callG` for
    z = 0, where the tail never zeroes, with the full heap frame (`HKeepG`). As `alloc_implZ_callG`:, under `HeapHost`'s
    relation with a cap of at least 2^27: with ω₇ = 196792 (the allocator), ω₈ = 1 (alignment one
    unit), ω₉ = req ≥ 1 units, ω₁₀ = z, and a return address ω₀ that **j** resolves to tg, either the
    model's `alloc` returns block `ptr` and state `s'` and the call returns `ptr` (ω₇) at tg with the
    context, lock held, kept for `s'`, every allocated chunk of `s` still allocated, the block a new
    allocated chunk at `ptr − 32` of req + 1 units, the heap off the new headers and the block's data
    kept (`HKeepGD`), the stack from sp up untouched and ω₀, ω₁, ω₅, ω₆ restored; or the model's
    `alloc` fails and the call returns null at tg. -/
theorem alloc_impl0_callG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp req ret tg pb S0 S1 : Nat)
    (H : HeapCtxL env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat 1)
    (h9 : ω[9] = UInt64.ofNat req) (h10 : ω[10] = UInt64.ofNat 0)
    (h0 : ω[0] = UInt64.ofNat ret) (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = tg) (hbt : P.isBlockStart tg = true)
    (hreq : 1 ≤ req) (hrq : req < 2147483648)
    (hsp : 2147483800 ≤ sp) (hSTk : S0 + 152 ≤ sp ∧ sp ≤ S1) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 req s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 41177 ω μ x tg ω' μ' x (96 * req + 560) ∧
      HeapCtxL env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, req + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, req + 1, true⟩) ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) ∧
      (∀ d ∈ chunks s, d.used = true → ∀ a, d.addr + 32 ≤ a → a < d.addr + 32 * d.size → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 req s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 41177 ω μ x tg ω' μ' x (96 * req + 560) ∧ ω'[7] = UInt64.ofNat 0 ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  obtain ⟨ph, h48, hhb, hp0, hHTs, hHT⟩ := H₀.pages
  have hp : HeapPages μ 48 pb ph := HeapPages.of_eq hp0 hwa
  have hsp1 : sp < 4294967296 := by have := H₀.hS1; omega
  have hbs : pb < 4294967296 := by have := H₀.hSb; omega
  have rep : Rep μ s := H₀.rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a ha1 ha2 ha3 => hag a (by omega) (Or.inr (by
    unfold A0 at ha1; omega)) ha3
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := fun a h1 h2 => by rw [hwa]; exact H₀.st a h1 h2
  have hro : ∀ a, a < 196608 → μ.writable a = false := fun a ha => by rw [hwa]; exact H₀.ro a ha
  cases ha : alloc (growTo pb) hb 1 req s with
  | none =>
    right
    obtain ⟨ω', μ', run, -, e7, e0, e5, e6, e1, -, -, efr⟩ := alloc_refines_failKG (p := p) (P := P)
      (hb := hb) (S0 := S0) (S1 := S1) env cap hcap (by omega) x ω μ s sp req pb ph H₀.wf rep H₀.bd h48 hhb
      hbs ha hrq h1 h7 h8 h9 hsp hsp1 H₀.hb0 H₀.hbT H₀.hA hHTs hSTk H₀.hSb hp hst hHT
    exact ⟨rfl, ω', μ', (run.trans (ai_ret (R := env.rel cap) (p := p) (P := P) x ω' μ' ret tg (e0.trans h0) hret
      hjt hbt)).mono (by omega), e7, efr, e0, e1, e5, e6⟩
  | some q =>
    obtain ⟨ptr, s'⟩ := q
    left
    have hb' := alloc_base H₀.wf ha
    have keep := HeapFrame.alloc_keeps_used H₀.wf ha
    have fo' := alloc_first H₀.wf H₀.fo ha
    obtain ⟨pre, post, S, hcs, hrS, hcs'⟩ := alloc_chunks H₀.wf ha
    have hnew : (⟨ptr - 32, req + 1, true⟩ : Chunk) ∈ chunks s' := by
      rw [hcs']; exact List.mem_append_right _ List.mem_cons_self
    have hfresh : ∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, req + 1, true⟩ := by
      intro d hd hu e
      have ht := H₀.wf.2.2.2.1
      unfold TilesOk at ht
      rw [hcs] at ht hd
      have hfree : (⟨ptr - 32, S, false⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, S, false⟩ :: post :=
        List.mem_append_right _ List.mem_cons_self
      have := Tiles.addr_inj ht d hd _ hfree (by rw [e])
      rw [this] at hu; simp at hu
    -- the data of every used chunk of s lies off the headers of s' and off the new block
    have hdata : ∀ (μ' : Memory), HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) →
        ∀ d ∈ chunks s, d.used = true → ∀ a, d.addr + 32 ≤ a → a < d.addr + 32 * d.size →
          μ'.read a = μ.read a := fun μ' hk d hd hu a h1 h2 => by
      have ht := H₀.wf.2.2.2.1
      unfold TilesOk at ht
      have hFm : (⟨ptr - 32, S, false⟩ : Chunk) ∈ chunks s := by rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
      have hdis := HeapFrame.Tiles.disjoint ht d hd _ hFm (by intro e; rw [e] at hu; simp at hu)
      have hFl := ht.mem_lt _ hFm
      have hoff := off_hdr_data (alloc_wf H₀.wf ha) (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT)
        (keep d hd hu) h1 h2
      simp only at hdis hFl
      exact hk a ⟨Or.inr hoff.1, hoff.2.1, hoff.2.2⟩
    by_cases hg : s'.allocated = s.allocated
    · obtain ⟨ω', μ', run, rep', wf', e7, e0, e5, e6, e1, ww, stk, hk⟩ := alloc_refines_hdr (p := p) (P := P)
        (R := env.rel cap) (HT := 4096 * ph) (S0 := S0) (S1 := S1) x ω μ s s' sp req ptr H₀.wf rep ha hg h1 h7 h8 h9
        h10 hsp hsp1 H₀.hb0 H₀.hbT H₀.hA H₀.fo hHTs hSTk hHT (HeapPages.wrAt hp hhb hst)
      refine ⟨ptr, s', ω', μ', rfl, (run.trans (ai_ret (R := env.rel cap) (p := p) (P := P) x ω' μ' ret tg (e0.trans h0)
        hret hjt hbt)).mono (by omega),
        heldOf H₀ wf' rep' fo' (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT) (by rw [hg]; exact H₀.hA)
          ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', hg]; exact hHT⟩
          (fun a h1 h2 => by rw [ww]; exact hst a h1 h2) (fun a ha => by rw [ww]; exact hro a ha),
        keep, hnew, hfresh, hk, hdata μ' hk, e7, stk, e0, e1, e5, e6⟩
    · obtain ⟨bin, -, -, -, -, hgrow, -, hs'⟩ := alloc1_grown (by rw [alloc_one H₀.wf.1] at ha; exact ha) hg
      have hpg : pagesOf (s.base + 32 * s'.allocated) ≤ pb := by
        rw [hs', allocPost_allocated]
        simpa [growTo] using hgrow
      obtain ⟨ω', μ', run, rep', wf', e7, e0, e5, e6, e1, ⟨h', hp', hHT', hph', hh'b⟩, wst, stk, hk⟩ :=
        alloc_refines_growK_hdrG (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env cap hcap x ω μ s s'
          sp req ptr pb ph H₀.wf rep H₀.bd h48 hhb hbs ha hg h1 h7 h8 h9 h10
          hsp hsp1 H₀.hb0 H₀.hbT H₀.hA H₀.fo (by have := H₀.hSb; have := pagesOf_ge (s.base + 32 * s'.allocated); omega)
          hHTs hSTk H₀.hSb hp hst hHT
      refine ⟨ptr, s', ω', μ', rfl, (run.trans (ai_ret (R := env.rel cap) (p := p) (P := P) x ω' μ' ret tg (e0.trans h0)
        hret hjt hbt)).mono (by omega),
        heldOf H₀ wf' rep' fo' (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT)
          (by have := H₀.hSb; rw [hb'] at hHT'; omega)
          ⟨h', by omega, hh'b, hp', by omega, hHT'⟩ wst
          (ro_of_pages hro fun q hq => (HeapHost.keepRO H₀.bd run).1 q (Or.inl hq)),
        keep, hnew, hfresh, hk, hdata μ' hk, e7, stk, e0, e1, e5, e6⟩

end Services.Bootstrap.Decode.AllocZeroedCall
