import Services.Bootstrap.Acc.Handlers.RowEleven
import Services.Bootstrap.Acc.Handlers.ResStoreCall
import Services.Bootstrap.Acc.Handlers.NoCall
import Services.Bootstrap.Acc.Handlers.RowElevenSeg

/-!
# Row 11 (R7): the final results write, from the `Zombify` flag (15038) to 6766

`row_eleven_core`: from 15038 (after the instructions' drop), the run implements
`unless b (store key (encodeResults rs))` (GP v0.8.0 Appendix B, Ω_W; quirk Q4: b is "some instruction
is a `Zombify`", the low bit of the word at sp + 160), with key = `Key.results package item` (the package
hash at sp + 312, the item index at sp + 176), against `ExtendH` (R8) and `OkEncH` (R9), and ends at
6766 in `R7Post`: the results' buffers and the frame's three buffers (`tailFree`) freed, every other
allocated chunk kept with its data, the memory from sp up kept off the key slot (`R9Out`), the globals
kept, ω₁ = sp, ω₅ kept.
-/

namespace Services.Bootstrap.Acc.Handlers.RowEleven

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.KeyEnc
  Services.Bootstrap.Acc.Handlers.RecentSlotWrite Services.Bootstrap.Acc.Handlers.ResultsInit
  Services.Bootstrap.Acc.Handlers.ResStore Services.Bootstrap.Acc.Handlers.ResultsDrop
  Services.Bootstrap.Acc.Handlers.InstrRep
open JAM.Codec (fixed)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`Impl` with its post-condition continued**: if a run from s implements `prog` with Q, and from
    every state where Q a holds a run implements `pure a` with Q′, the run implements `prog` with Q′. -/
theorem Impl.then {Qu : Type} {p : ByteArray} {R : HostRel (AccCtx × Qu)} {env : AccEnv} {Ab : St Qu → Prop}
    {α : Type} {Q Q' : α → St Qu → Prop} (hQ : ∀ a s, Q a s → Impl p R env Ab (Prog.pure a) Q' s) :
    ∀ (prog : Prog AOp α) (s : St Qu), Impl p R env Ab prog Q s → Impl p R env Ab prog Q' s := by
  intro prog
  induction prog with
  | pure a =>
    intro s h
    rcases h with h | ⟨s', h1, h2, h3⟩
    · exact .inl h
    · exact Impl.pre (Prog.pure a) Q' h1 h2 (hQ a s' h3)
  | panic => intro s h; exact h
  | call op k ih =>
    intro s h
    unfold Impl at h ⊢
    rcases h with h | ⟨s₁, h1, h2, h3⟩
    · exact .inl h
    refine .inr ⟨s₁, h1, h2, ?_⟩
    revert h3
    cases ASem.step env op s.c with
    | some bc =>
      intro h3
      rcases h3 with h3 | ⟨s₂, g1, g2, g3⟩
      · exact .inl h3
      · exact .inr ⟨s₂, g1, g2, ih bc.1 s₂ g3⟩
    | none => exact id

theorem BufOK.keep {st st' : State} {FR : List Nat} {c q : Nat} {μ μ' : Memory}
    (hk : ChunksKept μ st μ' st') (h : BufOK st FR c q) : BufOK st' FR c q := fun hc => by
  obtain ⟨⟨d, hd, hu, ha⟩, hn⟩ := h hc
  exact ⟨⟨d, (hk d hd hu).1, hu, ha⟩, hn⟩

/-- **`TailHyp` survives a run that keeps every allocated chunk with its data and the frame's words**;
    `tailFree` is unchanged. -/
theorem TailHyp.keep {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {st st' : State} {sp : Nat}
    (T : TailHyp code pb S0 S1 μ st sp) (H' : HeapCtxC code pb S0 S1 μ' st') (hk : ChunksKept μ st μ' st')
    (fr : ∀ a, sp ≤ a → a < sp + 472 → μ'.read a = μ.read a) :
    TailHyp code pb S0 S1 μ' st' sp ∧ tailFree μ' sp = tailFree μ sp := by
  have e : ∀ o, o + 8 ≤ 472 → rdN μ' (sp + o) 8 = rdN μ (sp + o) 8 := fun o ho =>
    rdN_frame fun j hj => fr _ (by omega) (by omega)
  have hr : resPtrs μ' (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) =
      resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) := resPtrs_keep T.O hk _ (Nat.le_refl _)
  have tf : tailFree μ' sp = tailFree μ sp := by
    unfold tailFree tailBufs
    rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), e 128 (by omega), e 104 (by omega),
      e 264 (by omega), e 272 (by omega), hr]
  refine ⟨⟨H', T.hsp, ?_, ?_, ?_, ?_⟩, tf⟩
  · rw [e 456 (by omega), e 464 (by omega)]; exact T.O.keep hk
  · rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), hr]; exact T.b1.keep hk
  · rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), e 128 (by omega), e 104 (by omega), hr]
    exact T.b2.keep hk
  · rw [e 456 (by omega), e 464 (by omega), e 448 (by omega), e 128 (by omega), e 104 (by omega),
      e 264 (by omega), e 272 (by omega), hr]
    exact T.b3.keep hk

/-- **The state after row 11** (6766), against the memory μ₀ and allocator state st at 15038: ω₁ = sp,
    ω₅ = v5; the allocator's context for some st′; every allocated chunk of st whose data address is not
    in F kept with its data; the memory from sp up kept off the key slot (`R9Out`), and the globals. -/
def R7Post (code : ByteArray) (pb S0 S1 sp : Nat) (v5 : UInt64) (st : State) (μ₀ : Memory) (F : List Nat)
    (s' : St Stream) : Prop :=
  s'.i = 6766 ∧ s'.ω[1] = UInt64.ofNat sp ∧ s'.ω[5] = v5 ∧
  ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧
    (∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ F → d ∈ chunks st' ∧
      ∀ a, InData d a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 4294967296 → sp ≤ a → ¬ R9Out sp a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, Glob a → s'.μ.read a = μ₀.read a)

/-- **Row 11's store and drops (15060 → 6766)** implement `store (Key.results package item) (encodeResults rs)`
    (GP v0.8.0 Appendix B, Ω_W), as `row_eleven_core`'s branch without a `Zombify`, entered here directly
    too (the loop's empty case, `r11_di1`'s return 560). Same hypotheses as `row_eleven_core` but the
    flag; it ends in `R7Post` with `tailFree` freed. -/
theorem row_eleven_store {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s) (hAbX : ∀ s : St Stream, s.i = 40611 ∨ s.i = 40821 → Ab s)
    (s : St Stream) (st : State) (sp item kc : Nat) (rs : List Spec.Result)
    (hi : s.i = 15060) (h1 : s.ω[1] = UInt64.ofNat sp)
    (T : TailHyp env.code pb S0 S1 s.μ st sp)
    (L : LoopHyp pb S0 S1 sp (rdN s.μ (sp + 456) 8) (rdN s.μ (sp + 464) 8) rs st s.μ) (hS1 : sp + 1632 ≤ S1)
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item)
    (mc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true) (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab (store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults rs))
      (fun _ => R7Post env.code pb S0 S1 sp s.ω[5] st s.μ (tailFree s.μ sp)) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h1 T L hitem mc ht8 ht4 hro hvals ⊢
  subst hi
  have H := T.H
  have hSt := H.st
  have hT := H.hS1
  obtain ⟨hs1, hs2, hs3⟩ := T.hsp
  have hspL := L.hsp
  have e8 : ∀ b, μ.readN b 8 = Num.encodeLE 8 (rdN μ b 8) := fun b => readN_enc μ b 8
  have lt8 : ∀ b, rdN μ b 8 < 2 ^ 64 := fun b => rdN_lt8 μ b
  have rd0 : ∀ a, sp ≤ a → a < sp + 1632 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hSt a (by omega) (by omega))
  obtain ⟨ωA, μA, runA, c0', cA1, cA5, cA6, cA7, cA8, cA9, mk0, mk1, mq0, mq1, mq2, mq3, frA, rdA, wrA⟩ :=
    r11_pre (R := KeepCtx (accContractS env)) (P := P) (c0, f) ω μ sp _ _ _ _ _ _ _ h1
      ⟨by omega, by omega⟩ (e8 (sp + 312)) (e8 (sp + 320)) (e8 (sp + 328)) (e8 (sp + 336)) (lt8 _) (lt8 _)
      (lt8 _) (lt8 _) (e8 (sp + 176)) (lt8 _) (e8 (sp + 456)) (lt8 _) (e8 (sp + 464)) (lt8 _)
      (fun a h1 h2 => rd0 a (by omega) (by omega)) (fun a h1 h2 => hSt a (by omega) (by omega))
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega))) wrA
  -- the key
  have cq : μA.readN (sp + 1572) 32 = μ.readN (sp + 312) 32 := by
    rw [RecentMatch.readN_32, RecentMatch.readN_32 μ, show sp + 1572 + 8 = sp + 1580 by omega,
      show sp + 1572 + 16 = sp + 1588 by omega, show sp + 1572 + 24 = sp + 1596 by omega,
      show sp + 312 + 8 = sp + 320 by omega, show sp + 312 + 16 = sp + 328 by omega,
      show sp + 312 + 24 = sp + 336 by omega, mq0, mq1, mq2, mq3, ← e8, ← e8, ← e8, ← e8]
  have c34 : μA.readN (sp + 1570) 2 = fixed 2 item := by
    rw [mk1, ← hitem, readN_2of8 (e8 (sp + 176))]
  have hkE : keyEnc μA (sp + 1568) 2 = (Key.results (μ.readN (sp + 312) 32) item).encode := by
    unfold keyEnc Key.encode
    simp only [show (2 : Nat) = 1 ↔ False by decide, if_false, if_true, show sp + 1568 + 4 = sp + 1572 by omega,
      show sp + 1568 + 2 = sp + 1570 by omega, cq, c34]
    rfl
  -- the store's premises at 36170
  have hkH : ∀ d ∈ chunks st, d.used = true → d ∈ chunks st ∧ ∀ a, InData d a → μA.read a = μ.read a :=
    fun d hd _ => ⟨hd, fun a ha => frA a (by have := data_lt H hd ha; omega)
      (.inl (by have := data_lt H hd ha; omega))⟩
  have LA : LoopHyp pb S0 S1 sp (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) rs st μA :=
    { L with hR := ResultsAt.keep hkH L.hR }
  have hrA : ∀ a, a < 196608 → μA.read a = μ.read a := fun a ha => frA a (by omega) (.inl (by omega))
  have mcA : μA.readN 68696 8 = Num.encodeLE 8 kc := by
    rw [← mc]; exact Memory.readN_congr fun j hj => hrA _ (by omega)
  have ht8A : rdN μA 69072 4 = 4294900408 := by
    rw [← ht8]; exact rdN_frame fun j hj => hrA _ (by omega)
  have ht4A : rdN μA 69056 4 = 4294900402 := by
    rw [← ht4]; exact rdN_frame fun j hj => hrA _ (by omega)
  have herr : ∀ (c : AccCtx) (q : Stream) (ω : Regs) (μ : Memory), ω[7] = UInt64.ofNat 3 →
      ∃ ω' μ' q', FreeRunH p (KeepCtx (accContractS env)) 15121 ω μ (c, q) .panic ω' μ' (c, q') := by
    intro c q ω μ h7
    obtain ⟨ω', run⟩ := r11_err (R := KeepCtx (accContractS env)) (P := P) (c, q) ω μ h7
    exact ⟨ω', μ, q, FreeRunH.prepend run (.exit (FreeRun.exit (trap_15361 (P := P) ω' μ)) (by simp))⟩
  have SC := store_core (P := P) env hE hO cap hcap1 hcap Ab hAb1 hAb2 hAbX 562 15121
    (.inr (.inr ⟨rfl, rfl⟩)) herr ⟨36170, ωA, μA, c0, f⟩ st sp (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) kc rs
    HA rfl c0' cA1 cA7 cA8 cA9 LA hS1 mk0 mcA hkc ht8A ht4A (fun a h1 h2 => by rw [rdA]; exact hro a h1 h2)
    hvals
  dsimp only at SC
  rw [hkE] at SC
  show Impl p (accContractS env) env Ab (store (.results (μ.readN (sp + 312) 32) item) (encodeResults rs)) _ _
  unfold store
  refine Impl.pre _ _ (s' := ⟨36170, ωA, μA, c0, f⟩) ⟨_, runA⟩ rfl ?_
  refine Impl.then ?_ _ _ SC
  -- after the store: 15121 → 15133 → 6766
  rintro _ ⟨i', ω', μ', c', f'⟩ ⟨hi', h7', h1', h5', -, st', H', hk', stk', gl', -, -⟩
  dsimp only at hi' h7' h1' h5' H' hk' stk' gl' ⊢
  subst hi'
  obtain ⟨ω3, run3, d1, d5, -⟩ := r11_ok (R := KeepCtx (accContractS env)) (P := P) (c', f') ω' μ' h7'
  have hk2 : ChunksKept μ st μ' st' := fun d hd hu =>
    ⟨(hk' d hd hu).1, fun a ha => ((hk' d hd hu).2 a ha).trans ((hkH d hd hu).2 a ha)⟩
  obtain ⟨T', tf⟩ := T.keep H' hk2 fun a h1 h2 =>
    (stk' a (by omega) h1).trans (frA a (by omega) (.inl (by omega)))
  obtain ⟨ω4, μ4, s4, N4, run4, C4, e1, e5, -⟩ :=
    r11_tail (R := KeepCtx (accContractS env)) (P := P) (c', f') ω3 μ' st' sp T' (d1.trans h1')
  refine .inr ⟨⟨6766, ω4, μ4, c', f'⟩, ⟨_, run3.trans run4⟩, rfl, rfl, e1,
    e5.trans (d5.trans (h5'.trans cA5)), s4, C4.H, fun d hd hu hn => ?_, fun a h1 h2 h3 => ?_,
    fun a ha => ?_⟩
  · rw [← tf] at hn
    obtain ⟨g1, g2⟩ := hk2 d hd hu
    obtain ⟨g3, g4⟩ := C4.K d g1 hu hn
    exact ⟨g3, fun a ha => (g4 a ha).trans (g2 a ha)⟩
  · unfold R9Out at h3
    exact (C4.Fm.1 a h1 h2).trans ((stk' a h1 h2).trans (frA a h1 (by omega)))
  · have := ha.2
    exact (C4.Fm.2.1 a ha).trans ((gl' a ha).trans (frA a (by omega) (.inl (by unfold Glob at ha; omega))))

/-- **Row 11 from the `Zombify` flag (15038 → 6766) implements
    `unless b (store (Key.results package item) (encodeResults rs))`** (GP v0.8.0 Appendix B, Ω_W;
    quirk Q4), with b ↔ the low bit of the word z at sp + 160, the package hash at sp + 312 and the item
    index at sp + 176, under `accContractS` against `ExtendH` (R8) and `OkEncH` (R9), with abort reasons
    `Ab` covering the allocation-failure traps 36528 and 34070 and the failed allocator calls 40611 and
    40821 (heap exhaustion). It ends in `R7Post` with `tailFree` freed. Hypotheses: `TailHyp` (the
    results owned as `ResultsOwn`, the frame's buffers), `LoopHyp` (the results hold rs), the key-size
    word kc at 68696, `set`'s error table, `StoreFit`. -/
theorem row_eleven_core {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s) (hAbX : ∀ s : St Stream, s.i = 40611 ∨ s.i = 40821 → Ab s)
    (s : St Stream) (st : State) (sp z item kc : Nat) (rs : List Spec.Result) (b : Bool)
    (hi : s.i = 15038) (h1 : s.ω[1] = UInt64.ofNat sp)
    (T : TailHyp env.code pb S0 S1 s.μ st sp)
    (L : LoopHyp pb S0 S1 sp (rdN s.μ (sp + 456) 8) (rdN s.μ (sp + 464) 8) rs st s.μ) (hS1 : sp + 1632 ≤ S1)
    (mz : rdN s.μ (sp + 160) 8 = z) (hz : z % 2 = 1 ↔ b = true)
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item)
    (mc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true) (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab
      (if b then pure () else store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults rs))
      (fun _ => R7Post env.code pb S0 S1 sp s.ω[5] st s.μ (tailFree s.μ sp)) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h1 T L mz hitem mc ht8 ht4 hro hvals ⊢
  subst hi
  have H := T.H
  have hSt := H.st
  have hT := H.hS1
  obtain ⟨hs1, hs2, hs3⟩ := T.hsp
  have hspL := L.hsp
  have e8 : ∀ b, μ.readN b 8 = Num.encodeLE 8 (rdN μ b 8) := fun b => readN_enc μ b 8
  have lt8 : ∀ b, rdN μ b 8 < 2 ^ 64 := fun b => rdN_lt8 μ b
  have rd0 : ∀ a, sp ≤ a → a < sp + 1632 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hSt a (by omega) (by omega))
  cases b with
  | true =>
    have hz1 : z % 2 = 1 := hz.2 rfl
    obtain ⟨ω1, run1, a1, a5, -⟩ := r11_flag1 (R := KeepCtx (accContractS env)) (P := P) (c0, f) ω μ sp z h1
      (by omega) (mz ▸ lt8 _) hz1 (by rw [← mz]; exact e8 _) (fun a h1 h2 => rd0 a (by omega) (by omega))
    obtain ⟨ω2, μ2, s2, N2, run2, C2, b1, b5, -⟩ :=
      r11_tail (R := KeepCtx (accContractS env)) (P := P) (c0, f) ω1 μ st sp T (a1.trans h1)
    show Impl p (accContractS env) env Ab (Prog.pure ()) _ _
    exact .inr ⟨⟨6766, ω2, μ2, c0, f⟩, ⟨_, run1.trans run2⟩, rfl, rfl, b1, b5.trans a5, s2, C2.H,
      fun d hd hu hn => C2.K d hd hu hn, fun a h1 h2 _ => C2.Fm.1 a h1 h2, C2.Fm.2.1⟩
  | false =>
    have hz0 : z % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one z with h | h
      · exact h
      · exact absurd (hz.1 h) (by decide)
    obtain ⟨ω1, run1, a1, a5, -⟩ := r11_flag0 (R := KeepCtx (accContractS env)) (P := P) (c0, f) ω μ sp z h1
      (by omega) (mz ▸ lt8 _) hz0 (by rw [← mz]; exact e8 _) (fun a h1 h2 => rd0 a (by omega) (by omega))
    have SS := row_eleven_store env hE hO cap hcap1 hcap Ab hAb1 hAb2 hAbX ⟨15060, ω1, μ, c0, f⟩ st sp item kc rs
      rfl (a1.trans h1) T L hS1 hitem mc hkc ht8 ht4 hro hvals
    dsimp only at SS
    rw [a5] at SS
    show Impl p (accContractS env) env Ab (store (.results (μ.readN (sp + 312) 32) item) (encodeResults rs)) _ _
    exact Impl.pre _ _ (s' := ⟨15060, ω1, μ, c0, f⟩) ⟨_, run1⟩ rfl SS

end Services.Bootstrap.Acc.Handlers.RowEleven
