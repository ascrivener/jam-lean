import Services.Bootstrap.Acc.Handlers.InstrLoopEntry

/-!
# R5 and R7 composed: the instruction loop and row 11 (8492 → 6766)

Spec `onWorkItem` after the checkpoint (GP v0.8.0 Appendix B, Ω_W; quirk Q4):

```
for i in is do
  match i with
  | .checkpoint => store key (encodeResults results)
  | _ => pure ()
  let r ← onInstr C now i
  results := results ++ [r]
unless is.any isZomb do store key (encodeResults results)
```

`loop_row11`: from row 9's end (8492, `EntryHyp`) the run implements it and reaches the items loop's head
6766 in `R57Post`: the allocator's context, every allocated chunk of the entry outside the instructions'
buffers (`vecFree`) and row 11's `tailFree` kept with its data, the frame words `StableKeep` kept.
- some instructions: `il_entry`, `il_loop`, `loop_exit` (row 11 from 15028);
- none: 8492 → 15050 (`il_setup0`), the drop of the empty `IntoIter` (`r11_di1`, `DropInstrsH`, return
  560), `row_eleven_store` (15060).
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.InstrRep
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop
  Services.Bootstrap.Acc.Handlers.ResStore
open JAM.Codec (fixed)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The state after the instruction loop and row 11** (6766), against the entry's memory μ₀ and
    allocator state st₀ (8492), with G the instructions' buffers: ω₁ = sp; the allocator's context for some
    st′; every allocated chunk of st₀ whose data address is neither in G nor in row 11's `tailFree` (the
    buffers at sp + 104 and sp + 272) kept with its data; the frame words `StableKeep` kept. -/
def R57Post (code : ByteArray) (pb S0 S1 sp : Nat) (st₀ : State) (μ₀ : Memory) (G : List Nat)
    (s' : St Stream) : Prop :=
  s'.i = 6766 ∧ s'.ω[1] = UInt64.ofNat sp ∧ ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧
    (∀ d ∈ chunks st₀, d.used = true → d.addr + 32 ∉ G ++ tailFree μ₀ sp → d ∈ chunks st' ∧
      ∀ a, InData d a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 4294967296 → StableKeep sp a → s'.μ.read a = μ₀.read a)

/-- The two frame buffers of `tailBufs` agree when their words do. -/
theorem tailBufs23 {μ μ' : Memory} {sp : Nat} (h : ∀ a, a < 4294967296 → StableKeep sp a → μ'.read a = μ.read a)
    (hsp : sp + 1632 < 4294967296) :
    optBuf (rdN μ' (sp + 128) 8) (rdN μ' (sp + 104) 8) ++ optBuf (rdN μ' (sp + 264) 8) (rdN μ' (sp + 272) 8) =
      optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) ++ optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8) := by
  have e : ∀ o, (104 ≤ o ∧ o + 8 ≤ 152) ∨ (264 ≤ o ∧ o + 8 ≤ 280) → rdN μ' (sp + o) 8 = rdN μ (sp + o) 8 :=
    fun o ho => rdN_frame fun j hj => h _ (by omega) (by unfold StableKeep; omega)
  rw [e 128 (by omega), e 104 (by omega), e 264 (by omega), e 272 (by omega)]

/-- An address outside `tailFree` is outside the frame buffers and the results buffer. -/
theorem not_tailFree0 {μ : Memory} {sp q : Nat} (h : q ∉ tailFree μ sp) :
    q ∉ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) ∧
    q ∉ optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) ++ optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8) := by
  unfold tailFree tailBufs at h
  simp only [List.mem_append, not_or] at h ⊢
  exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

/-- **R5 and R7, 8492 → 6766** (see the module doc): from row 9's end with `EntryHyp` for the instructions
    is in the `Vec` { cap c, ptr b = ω₆ }, the run implements the loop over is with body f (through its
    equations `hck` and `hother`, as `il_loop`) followed by `unless is.any isZomb (store key
    (encodeResults results))` (GP v0.8.0 Appendix B, Ω_W; quirk Q4), key the results key of the package at
    sp + 312 and the item index at sp + 176, under `accContractS` with abort reasons Ab covering heap
    exhaustion, and ends in `R57Post`. Named hypotheses: `InstrLogH`, `ResultLogH`, `HandlerH`, `PushH`,
    `ExtendH`, `OkEncH`, `DropInstrsH`. Premises: the context invariant Inv (kept by every operation,
    giving `StoreFit`); the read-only facts (the key-size word, `set`'s error table, the dispatch table);
    `hBall` (open: the size bound on the results' encoding, see `docs/t2-remaining.md`). -/
theorem loop_row11 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (B : InstrRep) {C : Consts} {now pb S0 S1 : Nat} {Ab : St Stream → Prop}
    (hL : InstrLogH B p env pb S0 S1) (hR : ResultLogH p env pb S0 S1) (hH : HandlerH B p env C now pb S0 S1 Ab)
    (hP : PushH p env pb S0 S1) (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (hD : DropInstrsH B p P env.code pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s) (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s)
    (hAbX : ∀ s : St Stream, s.i = 40611 ∨ s.i = 40821 → Ab s)
    (Inv : AccCtx → Prop)
    (hIst : ∀ {β : Type} (o : AOp β) (c c₁ : AccCtx) (b : β), Inv c → ASem.step env o c = some (b, c₁) → Inv c₁)
    (hIfit : ∀ c, Inv c → StoreFit c)
    (s : St Stream) (st : State) (sp b c item kc : Nat) (is : List Spec.Instr)
    (hi : s.i = 8492) (h1 : s.ω[1] = UInt64.ofNat sp) (h6 : s.ω[6] = UInt64.ofNat b)
    (E : EntryHyp B env.code pb S0 S1 sp b c is s.μ st) (hinv : Inv s.c)
    (f : Spec.Instr → List Spec.Result → Prog AOp (ForInStep (List Spec.Result)))
    (hck : ∀ rs, f .checkpoint rs = Prog.bind (store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults rs))
      (fun _ => Prog.bind (onInstr C now .checkpoint) (fun r => Prog.pure (.yield (rs ++ [r])))))
    (hother : ∀ i rs, i ≠ .checkpoint → f i rs = Prog.bind (onInstr C now i) (fun r => Prog.pure (.yield (rs ++ [r]))))
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item)
    (mkc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true)
    (hjt : s.μ.readN 65736 100 = jumpTab) (hjr : ∀ a, 65736 ≤ a → a < 65836 → s.μ.readable a = true)
    (hBall : ∀ rs : List Spec.Result, rs.length ≤ is.length →
      2 * (144 * rs.length + 4) + 4 * (encodeResults rs).length + 64 < 1073741760) :
    Impl p (accContractS env) env Ab
      (Prog.bind (forIn is [] f) (fun rs =>
        if is.any isZomb then pure () else store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults rs)))
      (fun _ => R57Post env.code pb S0 S1 sp st s.μ (vecFree B s.μ b c is.length)) s := by
  obtain ⟨i0, ω, μ, c0, f0⟩ := s
  dsimp only at hi h1 h6 E hinv hck hitem mkc ht8 ht4 hro hjt hjr ⊢
  subst hi
  have H := E.H
  have hT := H.hS1
  have hSt := H.st
  obtain ⟨hs1, hs2, hs3⟩ := E.hsp
  have hs8 := E.hs8
  by_cases hn0 : is = []
  · ---------------- no instructions: 8492 → 15050 → 33214 → 15060 → 6766
    subst hn0
    show Impl p (accContractS env) env Ab (store (.results (μ.readN (sp + 312) 32) item) (encodeResults [])) _ _
    have hb : b < 2 ^ 64 := by have := E.hb; simp at this; omega
    have hcl : c < 2 ^ 64 := by rw [← E.mc]; exact rdN_lt8 μ _
    obtain ⟨ω0, run0, e1, e5, e6⟩ := il_ft (R := KeepCtx (accContractS env)) (P := P) (c0, f0) ω μ
    obtain ⟨ω1, μ1, run1, a1, a5, a6, m472, m480, m488, m496, m504, fr1, rd1, wr1⟩ :=
      il_setup0 (R := KeepCtx (accContractS env)) (P := P) (c0, f0) ω0 μ sp b c (e1.trans h1) (e6.trans h6)
        ⟨by omega, by omega⟩ hb hcl (by rw [← E.mc]; exact KeyEnc.readN_enc μ _ 8)
        (by have := E.ml; simp at this; rw [← this]; exact KeyEnc.readN_enc μ _ 8)
        (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
        (fun a h1 h2 => hSt a (by omega) (by omega))
    have heap1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (.inl (by omega))
    have H1 : HeapCtxC env.code pb S0 S1 μ1 st := HeapKeep.keepHi H heap1 wr1
    have hk1 : ChunksKept μ st μ1 st := fun d hd _ => ⟨hd, fun a ha => heap1 a (data_lt H hd ha)⟩
    have r472 : rdN μ1 (sp + 472) 8 = b := DesignateAlloc.rd8 hb m472
    have r480 : rdN μ1 (sp + 480) 8 = b := DesignateAlloc.rd8 hb m480
    have r488 : rdN μ1 (sp + 488) 8 = c := DesignateAlloc.rd8 hcl m488
    have r496 : rdN μ1 (sp + 496) 8 = b := DesignateAlloc.rd8 hb m496
    have hIF : iterFree B μ1 (sp + 472) ([] : List Spec.Instr).length = vecFree B μ b c 0 := by
      unfold iterFree vecFree
      rw [show sp + 472 + 16 = sp + 488 by omega, r488, r472]; rfl
    have I : IterOwn B μ1 st (sp + 472) [] := by
      refine ⟨?_, fun k hk' => absurd hk' (by simp), ?_, ?_, fun h => absurd rfl h⟩
      · rw [show sp + 472 + 24 = sp + 496 by omega, show sp + 472 + 8 = sp + 480 by omega, r496, r480]; simp
      · rw [hIF]; exact E.V.nodup
      · rw [hIF]; exact E.V.owned
    obtain ⟨T1, tf1⟩ := E.T.keepW H1 hk1 fun a h1 h2 h3 => fr1 a (by omega) (.inl h2)
    -- 15050 → 33214 → 15060
    obtain ⟨ω2, run2, w0, w1, w5, w6, w7⟩ :=
      r11_di1 (R := KeepCtx (accContractS env)) (P := P) (c0, f0) ω1 μ1 sp (a1.trans (e1.trans h1)) (by omega)
    obtain ⟨ω3, μ3, N3, run3, H3, K3, Fm3, g1, g5, -⟩ :=
      hD (KeepCtx (accContractS env)) (c0, f0) ω2 μ1 st sp (sp + 472) 560 15060 [] H1 I w0
        (w1.trans (a1.trans (e1.trans h1))) w7 hs1 hs2 (by omega) (by omega) (by decide) jte_279 bs_15060
    rw [hIF] at H3 K3
    have fr3 : ∀ a, sp ≤ a → a < 4294967296 → μ3.read a = μ1.read a := fun a h1 h2 => Fm3.1 a h2 h1
    have hdis : ∀ q ∈ tailFree μ1 sp, q ∉ vecFree B μ b c 0 := by
      intro q hq hF
      rw [tf1] at hq
      have hnd := E.hnd
      simp only [List.length_nil] at hnd
      exact (List.nodup_append.1 hnd).2.2 q hF q hq rfl
    have h464 : rdN μ1 (sp + 464) 8 = 0 := by
      rw [rdN_frame fun j hj => fr1 _ (by omega) (.inl (by omega))]; exact E.h464
    obtain ⟨T3, tf3⟩ := T1.keepF H3 (fun d hd hu hn => K3 d hd hu hn) hdis
      (fun k hk => by rw [h464] at hk; omega) fun a h1 h2 => fr3 a h1 (by omega)
    have L3 : LoopHyp pb S0 S1 sp (rdN μ3 (sp + 456) 8) (rdN μ3 (sp + 464) 8) []
        ((vecFree B μ b c 0).foldl free st) μ3 := by
      refine ⟨⟨by omega, by omega, hs8, by omega⟩, hT, ?_, ⟨rdN_lt8 _ _, fun h => absurd ?_ h⟩, ?_,
        ⟨fun k hk => absurd hk (by simp), fun j hj => absurd hj (by simp)⟩⟩
      · rw [rdN_frame fun j hj => fr3 _ (by omega) (by omega), h464]; rfl
      · rw [rdN_frame fun j hj => fr3 _ (by omega) (by omega), h464]
      · rw [rdN_frame fun j hj => fr3 _ (by omega) (by omega), h464]; decide
    have hro3 : ∀ a, a < 196608 → μ3.read a = μ.read a := fun a ha =>
      (Fm3.2.2.1 a (by unfold two32; omega) (H1.ro a ha)).trans (heap1 a (by omega))
    have SS := row_eleven_store env hE hO cap hcap1 hcap Ab hAb1 hAb2 hAbX ⟨15060, ω3, μ3, c0, f0⟩ _ sp item kc []
      rfl (g1.trans (w1.trans (a1.trans (e1.trans h1)))) T3 L3 hs3
      (by rw [← hitem]; exact Memory.readN_congr fun j hj => ((fr3 _ (by omega) (by omega)).trans
            (fr1 _ (by omega) (.inl (by omega)))))
      (by rw [← mkc]; exact Memory.readN_congr fun j hj => hro3 _ (by omega)) hkc
      (by rw [← ht8]; exact rdN_frame fun j hj => hro3 _ (by omega))
      (by rw [← ht4]; exact rdN_frame fun j hj => hro3 _ (by omega))
      (fun a h1 h2 => by rw [Fm3.2.2.2.1 a, rd1 a]; exact hro a h1 h2) (hIfit c0 hinv)
    dsimp only at SS
    have hq : μ3.readN (sp + 312) 32 = μ.readN (sp + 312) 32 :=
      Memory.readN_congr fun j hj => (fr3 _ (by omega) (by omega)).trans (fr1 _ (by omega) (.inl (by omega)))
    rw [hq] at SS
    refine Impl.pre _ _ (s' := ⟨15060, ω3, μ3, c0, f0⟩) ⟨_, run0.trans (run1.trans (run2.trans run3))⟩ rfl ?_
    refine Impl.then ?_ _ _ SS
    rintro _ s' ⟨hi', h1', -, st', H', hk', stk', -⟩
    refine Impl.pure_of ⟨hi', h1', st', H', fun d hd hu hn => ?_, fun a h0 hs => ?_⟩
    · have hn1 : d.addr + 32 ∉ vecFree B μ b c 0 := fun h => hn (List.mem_append_left _ (by simpa using h))
      have hn2 : d.addr + 32 ∉ tailFree μ3 sp := fun h => hn (List.mem_append_right _ (by rw [tf3, tf1] at h; exact h))
      obtain ⟨g1, g2⟩ := K3 d hd hu hn1
      obtain ⟨g3, g4⟩ := hk' d g1 hu hn2
      exact ⟨g3, fun a ha => (g4 a ha).trans ((g2 a ha).trans ((hk1 d hd hu).2 a ha))⟩
    · unfold StableKeep at hs
      exact (stk' a h0 (by omega) (by unfold ResultsInit.R9Out; omega)).trans ((fr3 a (by omega) h0).trans
        (fr1 a h0 (by omega)))
  · ---------------- some instructions: 8492 → 8554, the loop, 8540 → 15028 → 6766
    obtain ⟨ω', μ', N, run, -, LI⟩ := il_entry (R := KeepCtx (accContractS env)) (P := P) B Inv (c0, f0) ω μ st sp
      b c is hn0 h1 h6 E
    refine Impl.pre _ _ (s' := ⟨8554, ω', μ', c0, f0⟩) ⟨_, run⟩ rfl ?_
    refine Impl.bind _ _ _ _ ?_
    have LP := il_loop (P := P) env B hL hR hH hP hE hO cap hcap1 hcap hAb1 hAb2 hAbX Inv hIst hIfit sp item kc μ st
      (vecFree B μ b c is.length ++ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8)) (is.any isZomb) is.length hs8
      f hck hother hitem mkc hkc ht8 ht4 hro hjt hjr hBall
      is [] _ (LI c0 f0 hinv)
    refine Impl.mono_post ?_ _ _ LP
    rintro rs ⟨i', ω'', μ'', c'', f''⟩ LIe
    have hi' : i' = 8540 := by
      rcases LIe.hi with h | ⟨-, -, h⟩
      · exact h
      · exact absurd rfl h
    subst hi'
    obtain ⟨st', zs, LA, hz, KO⟩ := LIe.la
    simp only [List.any_nil, Bool.or_false] at hz
    subst hz
    have h1' := LIe.h1
    have hlen := LIe.hlen
    simp only [List.length_nil, Nat.add_zero] at hlen
    dsimp only at h1' LA KO
    have stab := LIe.stab
    have ro := LIe.ro
    dsimp only at stab ro
    have hT' := LA.H.hS1
    have he : rdN μ'' (sp + 480) 8 = rdN μ'' (sp + 496) 8 := by
      have := LA.I.hend
      rw [show sp + 472 + 24 = sp + 496 by omega, show sp + 472 + 8 = sp + 480 by omega] at this
      simp at this; omega
    have lt8 : ∀ b, rdN μ'' b 8 < 2 ^ 64 := fun b => rdN_lt8 μ'' b
    have LH : LoopHyp pb S0 S1 sp (rdN μ'' (sp + 456) 8) (rdN μ'' (sp + 464) 8) rs st' μ'' := by
      refine ⟨⟨by omega, by omega, hs8, by omega⟩, hT', LA.hn.symm, ⟨lt8 _, fun hn0 => ?_⟩,
        by rw [LA.hn]; exact hBall rs (by omega), LA.hav.toAt⟩
      have hcap0 := LA.hcap
      have hn' := LA.hn
      have hc0 : rdN μ'' (sp + 448) 8 ≠ 0 := by omega
      obtain ⟨dr, hdr, hur, hdra, hdrr⟩ := LA.hroom hc0
      have := data_ge LA.H hdr hur (a := rdN μ'' (sp + 456) 8) ⟨by omega, by omega⟩
      have := Services.Bootstrap.Decode.VecU8.chunk_in LA.H.wf hdr hur
      have := LA.H.hbT
      have : 144 * rdN μ'' (sp + 464) 8 ≤ 144 * rdN μ'' (sp + 448) 8 := by omega
      exact ⟨by omega, by omega⟩
    have hq : μ''.readN (sp + 312) 32 = μ.readN (sp + 312) 32 :=
      Memory.readN_congr fun j hj => stab _ (by omega) (by unfold StableKeep; omega)
    have LX := loop_exit env hE hO B hD cap hcap1 hcap Ab hAb1 hAb2 hAbX ⟨8540, ω'', μ'', c'', f''⟩ st' sp item kc
      [] rs (is.any isZomb) rfl h1' LA he LH
      (by rw [← hitem]; exact Memory.readN_congr fun j hj => stab _ (by omega) (by unfold StableKeep; omega))
      (by rw [← mkc]; exact Memory.readN_congr fun j hj => (ro _ (by omega)).1) hkc
      (by rw [← ht8]; exact rdN_frame fun j hj => (ro _ (by omega)).1)
      (by rw [← ht4]; exact rdN_frame fun j hj => (ro _ (by omega)).1)
      (fun a h1 h2 => by rw [(ro a (by omega)).2]; exact hro a h1 h2) (hIfit _ LIe.inv)
    dsimp only at LX
    rw [hq] at LX
    refine Impl.mono_post ?_ _ _ LX
    rintro _ s' ⟨hi', h1'', -, st'', H'', hk'', stk'', -⟩
    refine ⟨hi', h1'', st'', H'', fun d hd hu hn => ?_, fun a h0 hs => ?_⟩
    · have hTF : d.addr + 32 ∉ tailFree μ sp := fun h => hn (List.mem_append_right _ h)
      have hG : d.addr + 32 ∉ vecFree B μ b c is.length ++ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) :=
        fun h => by
          rcases List.mem_append.1 h with h | h
          · exact hn (List.mem_append_left _ h)
          · exact (not_tailFree0 hTF).1 h
      obtain ⟨k1, k2, k3, k4, k5⟩ := KO d hd hu hG
      have hTF' : d.addr + 32 ∉ tailFree μ'' sp := by
        unfold tailFree tailBufs
        rw [LA.hn]
        have e := tailBufs23 (sp := sp) stab (by omega)
        intro h
        simp only [List.mem_append, or_assoc] at h
        rcases h with h | h | h | h
        · exact k5 h
        · exact k4 h
        · exact (not_tailFree0 hTF).2 (by rw [← e]; exact List.mem_append.2 (.inl h))
        · exact (not_tailFree0 hTF).2 (by rw [← e]; exact List.mem_append.2 (.inr h))
      obtain ⟨g3, g4⟩ := hk'' d k1 hu (fun h => by
        rcases List.mem_append.1 h with h | h
        · exact k3 h
        · exact hTF' h)
      exact ⟨g3, fun a ha => (g4 a ha).trans (k2 a ha)⟩
    · have hs' := hs
      unfold StableKeep at hs'
      exact (stk'' a h0 (by omega) (by unfold ResultsInit.R9Out; omega)).trans (stab a h0 hs)

end Services.Bootstrap.Acc.Handlers.InstrLoop
