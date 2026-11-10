import Services.Bootstrap.Acc.Inputs.FinishGrow
import Services.Bootstrap.Decode.HeapCtx

/-!
# One call of accumulate's `finish_grow` with no current block, on the allocator's context

`fg_new_call`: under a host fit for the allocator (`HeapHost`) with a cap of at least 2²⁷ (any growth
of the heap within it), one call of `finish_grow` (40852 → 41175) with no current block either
writes `Ok(ptr, size)` for the model's block with the context `HeapCtxC` kept for the new state, or,
when the model's `alloc` fails, writes `Err(align, size)` with the context kept for the old state.
The counterpart of `HeapCtx.alloc_callG` for the lock `finish_grow` inlines.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

/-- **One `finish_grow` call with no current block** on `HeapCtxC` (see the module doc). -/
theorem fg_new_call {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out ncap al el pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat 0) (h10 : ω[10] = UInt64.ofNat ncap) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat el) (hal : 1 ≤ al ∧ al ≤ 32)
    (hsz : 0 < ncap * el) (hs : ncap * el + 31 < 68719476736)
    (hsp : 2147483840 ≤ sp) (hout : sp ≤ out) (hSTk : S0 + 192 ≤ sp ∧ out + 24 ≤ S1) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 ((ncap * el + 31) / 32) s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 40852 ω μ x 41175 ω' μ' x 600 ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, (ncap * el + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (ncap * el + 31) / 32 + 1, true⟩) ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s', c.addr = a) ∧
      rdN μ' out 8 = 0 ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = ncap * el ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 ((ncap * el + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 40852 ω μ x 41175 ω' μ' x 600 ∧ HeapCtxC env.code pb S0 S1 μ' s ∧
      rdN μ' out 8 = 1 ∧ rdN μ' (out + 8) 8 = al ∧ rdN μ' (out + 16) 8 = ncap * el ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  have hSb := H.hSb
  have hbs : pb < 4294967296 := by omega
  cases ha : alloc (growTo pb) hb 1 ((ncap * el + 31) / 32) s with
  | none =>
    right
    obtain ⟨ω', μ', run, rep', o0, o8, o16, ol, hp', hst', fr, e0, e1, e5, e6⟩ :=
      fg_new_fail (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap (by omega) x ω μ s sp out ncap al el pb ph
        H.wf H.rep H.bd h48 hhb hbs ha h1 h7 h8 h10 h11 h12 hal hsz hs ⟨hsp, by omega⟩ ⟨hout, by omega⟩
        H.hb0 H.hbT H.hA H.lock hHTs hSTk hSb hp H.st hHT
    refine ⟨rfl, ω', μ', run, ⟨H.wf, rep', H.fo, ol, H.hb0, H.hbT, H.hA, H.bd,
      ⟨ph, h48, hhb, hp', hHTs, hHT⟩, hSb, hS1, hst',
      ro_of_pages H.ro fun q hq => (HeapHost.keepRO H.bd run).1 q (Or.inl hq)⟩,
      o0, o8, o16, fr, e0, e1, e5, e6⟩
  | some q =>
    obtain ⟨ptr, s'⟩ := q
    left
    have hb' := alloc_base H.wf ha
    have keep := Services.Bootstrap.Decode.HeapFrame.alloc_keeps_used H.wf ha
    have fo' := alloc_first H.wf H.fo ha
    obtain ⟨pre, post, S, hcs, -, hcs'⟩ := alloc_chunks H.wf ha
    have hnew : (⟨ptr - 32, (ncap * el + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' := by
      rw [hcs']; exact List.mem_append_right _ List.mem_cons_self
    have hfresh : ∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (ncap * el + 31) / 32 + 1, true⟩ := by
      intro d hd hu e
      have ht := H.wf.2.2.2.1
      unfold TilesOk at ht
      rw [hcs] at ht hd
      have hfree : (⟨ptr - 32, S, false⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, S, false⟩ :: post :=
        List.mem_append_right _ List.mem_cons_self
      have := Tiles.addr_inj ht d hd _ hfree (by rw [e])
      rw [this] at hu; simp at hu
    by_cases hg : s'.allocated = s.allocated
    · obtain ⟨ω', μ', run, rep', wf', o0, o8, o16, ol, ww, fr, e0, e1, e5, e6, hk⟩ :=
        fg_new_hdr (p := p) (P := P) (R := env.rel cap) (HT := 4096 * ph) (S0 := S0) (S1 := S1) x ω μ s s' sp out
          ncap al el ptr H.wf H.rep ha hg h1 h7 h8 h10 h11 h12 hal hsz hs ⟨hsp, by omega⟩ ⟨hout, by omega⟩
          H.hb0 H.hbT H.hA H.fo H.lock hHTs hSTk hHT (HeapPages.wrAt hp hhb H.st)
      refine ⟨ptr, s', ω', μ', rfl, run.mono (by omega), ⟨wf', rep', fo', ol, by rw [hb']; exact H.hb0,
        by rw [hb']; exact H.hbT, by rw [hg]; exact H.hA, H.bd,
        ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', hg]; exact hHT⟩, hSb, hS1,
        fun a h1 h2 => by rw [ww]; exact H.st a h1 h2, fun a ha => by rw [ww]; exact H.ro a ha⟩,
        keep, hnew, hfresh, hk, o0, o8, o16, fr, e0, e1, e5, e6⟩
    · obtain ⟨bin, -, -, -, -, hgrow, -, hs'⟩ := alloc1_grown (by rw [alloc_one H.wf.1] at ha; exact ha) hg
      have hpg : pagesOf (s.base + 32 * s'.allocated) ≤ pb := by
        rw [hs', allocPost_allocated]
        simpa [growTo] using hgrow
      obtain ⟨ω', μ', run, rep', wf', o0, o8, o16, ol, ⟨h', hp', hHT', hph', hh'b⟩, wst, fr, e0, e1, e5, e6, hk⟩ :=
        fg_new_grow (p := p) (P := P) (S0 := S0) (S1 := S1) env cap hcap x ω μ s s' sp out ncap al el ptr pb ph
          H.wf H.rep H.bd h48 hhb hbs ha hg h1 h7 h8 h10 h11 h12 hal hsz hs ⟨hsp, by omega⟩ ⟨hout, by omega⟩
          H.hb0 H.hbT H.hA H.fo H.lock (by omega) hHTs hSTk hSb hp H.st hHT
      refine ⟨ptr, s', ω', μ', rfl, run, ⟨wf', rep', fo', ol, by rw [hb']; exact H.hb0,
        by rw [hb']; exact H.hbT, by rw [hb'] at hHT'; omega, H.bd,
        ⟨h', by omega, hh'b, hp', by omega, hHT'⟩, hSb, hS1, wst,
        ro_of_pages H.ro fun q hq => (HeapHost.keepRO H.bd run).1 q (Or.inl hq)⟩,
        keep, hnew, hfresh, hk, o0, o8, o16, fr, e0, e1, e5, e6⟩

end Services.Bootstrap.Acc
