import Services.Bootstrap.Acc.Handlers.ResStoreImpl
import Services.Bootstrap.Acc.Handlers.ResultsInitSeg
import Services.Bootstrap.Acc.Handlers.RecentAddGen

/-!
# Row 9: the empty results write and the checkpoint as `Impl` (8416 → 8492)

`results_init`: from 8416 (after `add_recent`), the run implements spec `onWorkItem`'s
`store (Key.results package item) (encodeResults [])` then `op AOp.checkpoint` (GP v0.8.0 Appendix B:
Ω_W of ℰ(↕[]) = [0], then Ω_C), with the package the 32 octets at sp + 312 and ℰ₂(item) the two at
sp + 176:
- `r9_pre` (8416 → 36170) builds the tag-2 key value at sp + 1568;
- `res_head` (36170 → `set`), `set_call` (Ω_W), `res_free` (→ 8477);
- `Ok` → 8490 (`r9_ok`), FULL → the trap at 15361 (`r9_err`, as `orPanic`);
- `r9_ck` (8490 → 8492) is Ω_C: y := x.
-/

namespace Services.Bootstrap.Acc.Handlers.ResultsInit

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc Services.Bootstrap.Acc.Handlers.RecentSlotWrite
  Services.Bootstrap.Acc.Handlers.ResStore

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The octets above sp that row 9 may change: the key value at sp + 1568 (36 octets). -/
def R9Out (sp a : Nat) : Prop := sp + 1568 ≤ a ∧ a < sp + 1604

/-- **The state after row 9** (8492, after the checkpoint), against the memory μ₀ and allocator state
    st at 8416: ω₁ = sp; the allocator's context for some st′ keeping every allocated chunk of st with
    its data; memory kept above sp off `R9Out`, at the globals 196616 … 196791 and below 196608
    (read-only data, with its access). -/
def R9Post (code : ByteArray) (pb S0 S1 sp : Nat) (st : State) (μ₀ : Memory) (s' : St Stream) : Prop :=
  s'.i = 8492 ∧ s'.ω[1] = UInt64.ofNat sp ∧
  ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧
    (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 4294967296 → sp ≤ a → ¬ R9Out sp a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, Glob a → s'.μ.read a = μ₀.read a) ∧ (∀ a, a < 196608 → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 196608 → s'.μ.readable a = μ₀.readable a)

theorem encodeResults_nil : encodeResults [] = [0] := rfl

theorem setR7_1 (ω : Regs) (v : Nat) : (setR7 ω v)[1] = ω[1] := by
  unfold setR7; rw [Vector.getElem_set]; simp

/-- **Row 9, 8416 → 8492, implements `store (results package item) (encodeResults [])` then
    `checkpoint`** (spec `onWorkItem`, GP v0.8.0 Appendix B's Ω_W then Ω_C), with the package the 32
    octets at sp + 312 and ℰ₂(item) the two at sp + 176, from the allocator's context for st, under
    `accContractS` with any abort reasons `Ab` that cover the allocation-failure traps 36528 and 34070
    (heap exhaustion). `Ok` ends in `R9Post` (8492); FULL ends ☇ at 15361, as `orPanic` does.
    Hypotheses: the results' count n = 0 at sp + 464; the key-size word kc for tag 2 at 68696
    (35 ≤ kc, kc + 31 < 2³⁶) and `set`'s error-table entries at 69056 and 69072, read-only data,
    readable; the stack frame [sp − 352, sp + 1632); every storage value shorter than 2⁶³ octets
    (`StoreFit`, from `ValuesFit`). -/
theorem results_init {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s) (item : Nat)
    (s : St Stream) (st : State) (sp kc pb S0 S1 : Nat) (H : HeapCtxC env.code pb S0 S1 s.μ st)
    (hi : s.i = 8416) (h1 : s.ω[1] = UInt64.ofNat sp)
    (hsp : 2147483648 + 352 ≤ sp ∧ sp % 8 = 0) (hS0 : S0 + 352 ≤ sp) (hS1 : sp + 1632 ≤ S1)
    (hn : s.μ.readN (sp + 464) 8 = Num.encodeLE 8 0)
    (mc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true)
    (hitem : s.μ.readN (sp + 176) 2 = fixed 2 item) (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab
      (Prog.bind (store (.results (s.μ.readN (sp + 312) 32) item) (encodeResults []))
        (fun _ => Prog.op AOp.checkpoint))
      (fun _ => R9Post env.code pb S0 S1 sp st s.μ) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h1 H hn mc ht8 ht4 hro hitem hvals ⊢
  subst hi
  have hSt := H.st
  have hS1' := H.hS1
  have e8 : ∀ b, μ.readN b 8 = Num.encodeLE 8 (rdN μ b 8) := fun b => readN_enc μ b 8
  have lt8 : ∀ b, rdN μ b 8 < 2 ^ 64 := fun b => decodeLE_readN_lt μ b 8
  generalize hkey : (Key.results (μ.readN (sp + 312) 32) item).encode = key
  have hkl : key.length = 35 := by
    rw [← hkey]; simp [Key.encode, JAM.Codec.fixed, Num.length_encodeLE, Memory.length_readN]
  rw [encodeResults_nil]
  refine Impl.bind _ _ _ _ ?_
  unfold store orPanic
  rw [hkey]
  refine Impl.bind _ _ _ _ ?_
  unfold Prog.op Impl
  -- 8416 → 36170
  obtain ⟨ωA, μA, runA, a0, a1, a5, a6, a7, a8, a9, mk0, mk1, mq0, mq1, mq2, mq3, frA, rdA, wrA⟩ :=
    r9_pre (R := (accHeapHost env).rel cap) (P := P) c0 ω μ sp _ _ _ _ _ _ 0 h1 ⟨by omega, by omega⟩
      (e8 (sp + 312)) (e8 (sp + 320)) (e8 (sp + 328)) (e8 (sp + 336)) (lt8 _) (lt8 _) (lt8 _) (lt8 _)
      (e8 (sp + 176)) (lt8 _) (e8 (sp + 456)) (lt8 _) hn (by decide)
      (fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega)))
      (fun a h1 h2 => hSt a (by omega) (by omega))
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
  have hkE : keyEnc μA (sp + 1568) 2 = key := by
    rw [← hkey]
    unfold keyEnc Key.encode
    simp only [show (2 : Nat) = 1 ↔ False by decide, if_false, if_true, show sp + 1568 + 4 = sp + 1572 by omega,
      show sp + 1568 + 2 = sp + 1570 by omega, cq, c34]
    rfl
  -- 36170 → 48104
  have hrA : ∀ a, a < 196608 → μA.read a = μ.read a := fun a ha => frA a (by omega) (.inl (by omega))
  rcases res_head (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c0 ωA μA st sp _ (sp + 1568) kc pb S0 S1 HA
      a1 a7 a8 a9 (lt8 _) hsp hS0 ⟨by omega, by omega, by omega⟩ mk0
      (by rw [← mc]; exact Memory.readN_congr fun j hj => hrA _ (by omega)) hkc
      (fun a h1 h2 => by rw [rdA]; exact hro a (by omega) (by omega)) with
    ⟨ωB, μB, nB, runB⟩ | ⟨ωB, μB, nB, runB⟩ |
    ⟨vp, kp, s2, ωB, μB, nB, runB, HB, keepB, hCv, hCk, hfr, hne, hv1, hv2, hk1, hk2, b0, b1, b5, b6, b7, b8,
      b9, b10, b11, mkey, mval, mkc, m4, mvp, m294, m5, m6, dataB, frB, glB, roB, rdB⟩
  · obtain ⟨-, runS⟩ := FreeStepsH.growS f (runA.trans runB)
    exact .inl ⟨⟨36528, ωB, μB, c0, f⟩, ⟨_, runS⟩, hAb1 _ rfl, ωB, μB, f,
      .exit (FreeRun.exit (trap_36528 (P := P) ωB μB)) (by simp)⟩
  · obtain ⟨-, runS⟩ := FreeStepsH.growS f (runA.trans runB)
    exact .inl ⟨⟨34070, ωB, μB, c0, f⟩, ⟨_, runS⟩, hAb2 _ rfl, ωB, μB, f,
      .exit (FreeRun.exit (RecentCounter.trap_34070 (P := P) ωB μB)) (by simp)⟩
  obtain ⟨-, runBS⟩ := FreeStepsH.growS f (runA.trans runB)
  refine .inr ⟨⟨48104, ωB, μB, c0, f⟩, ⟨_, runBS⟩, rfl, ?_⟩
  rw [hkE] at mkey
  have hSB := HB.st
  -- `set`
  have kRO : ∀ a, a < 196608 → μB.read a = μ.read a := fun a ha => (roB a ha).trans (hrA a ha)
  have ht8B : rdN μB 69072 4 = 4294900408 := by
    rw [← ht8]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => kRO _ (by omega)
  have ht4B : rdN μB 69056 4 = 4294900402 := by
    rw [← ht4]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => kRO _ (by omega)
  have hkr : μB.rangeReadable kp 35 = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => Memory.readable_of_writable (HeapKeep.writableData HB hCk rfl
      (by unfold HeapKeep.InData; dsimp only; omega))) (by omega)
  have hvr : μB.rangeReadable vp 1 = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => Memory.readable_of_writable (HeapKeep.writableData HB hCv rfl
      (by unfold HeapKeep.InData; dsimp only; omega))) (by omega)
  obtain ⟨e, ωD, μD, he, runD, d0, d1, d5, d6, sO, frD, rdD, wrD⟩ := set_call (P := P) env c0 f ωB μB (sp - 96)
    (sp - 96 + 56) kp 35 vp 1 key [0] b1 b7 b8 b9 b10 b11 (by decide) (by decide) (by omega)
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun a h1 h2 => hSB a (by omega) (by omega))
    (fun a h1 h2 => hSB a (by omega) (by omega)) (.inr (by omega)) hkr mkey hvr mval rfl (.inl (by omega))
    (.inl (by omega)) ht8B ht4B (fun a h1 h2 => by rw [rdB a (by omega), rdA]; exact hro a (by omega) (by omega))
    (by omega) (fun v hv => hvals _ v hv)
  have HD : HeapCtxC env.code pb S0 S1 μD s2 :=
    HeapKeep.keepHi HB (fun a ha => frD a (by omega) (.inl (by omega)) (.inl (by omega))) wrD
  have kD : ∀ b n, b + n ≤ 4294967296 → sp - 96 ≤ b → (b + n ≤ sp - 96 + 56 ∨ sp - 96 + 72 ≤ b) →
      μD.readN b n = μB.readN b n := fun b n h0 h1 h2 =>
    Memory.readN_congr fun j hj => frD _ (by omega) (.inr (by omega)) (by omega)
  -- after `set`, for its result word r and the octet b after it
  have rest : ∀ (x : AccCtx × Stream) r b, r < 2 ^ 64 → b < 256 →
      μD.readN (sp - 96 + 56) 8 = Num.encodeLE 8 r → μD.readN (sp - 96 + 64) 1 = Num.encodeLE 1 b →
      ∃ ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) e ωD μD x 8477 ω' μ' x n ∧
        ω'[1] = UInt64.ofNat sp ∧
        ω'[7] = (if r = 18446744073709551615 then UInt64.ofNat b else UInt64.ofNat 18446744073709551615) ∧
        HeapCtxC env.code pb S0 S1 μ' (free (free s2 kp) vp) ∧
        (∀ d ∈ chunks st, d.used = true → d ∈ chunks (free (free s2 kp) vp) ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → ¬ R9Out sp a → μ'.read a = μ.read a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
        (∀ a, a < 196608 → μ'.readable a = μ.readable a) := by
    intro x r b hr hb mr mb
    obtain ⟨ωG, μG, nG, runG, g1, -, -, g7, HG, keepG, stkG, glG, roG, rdG⟩ := res_free (P := P)
      (R := KeepCtx (accContractS env)) env.code pb S0 S1 x ωD μD s2 sp vp kp kc r b ωA[5].toNat ωA[6].toNat e
      HD hCv hCk hne (by omega) (by omega) he (d0.trans b0) d1 (d5.trans b5) (d6.trans b6) hsp.1
      ⟨hS0, by omega⟩ (by omega) (by omega) hr hb (UInt64.toNat_lt _) (UInt64.toNat_lt _)
      (by rw [kD _ _ (by omega) (by omega) (.inl (by omega))]; exact mkc) mr mb
      (by rw [kD _ _ (by omega) (by omega) (.inl (by omega))]; exact m4)
      (by rw [kD _ _ (by omega) (by omega) (.inl (by omega))]; exact mvp)
      (by rw [kD _ _ (by omega) (by omega) (.inr (by omega)), m294, a0]; rfl)
      (by rw [kD _ _ (by omega) (by omega) (.inr (by omega))]; exact m5)
      (by rw [kD _ _ (by omega) (by omega) (.inr (by omega))]; exact m6)
    refine ⟨ωG, μG, nG, runG, g1, g7, HG, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd hu
      obtain ⟨k1, k2⟩ := keepG d (keepB d hd hu) hu (hfr d hd hu).1 (hfr d hd hu).2
      refine ⟨k1, fun a ha => ?_⟩
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
      have := H.hbT
      have ha' := ha; unfold InData at ha'
      rw [k2 a ha, frD a (by omega) (.inl (by omega)) (.inl (by omega)), dataB d hd hu a ha,
        frA a (by omega) (.inl (by omega))]
    · intro a h0 ha hO
      unfold R9Out at hO
      rw [stkG a h0 (by omega) (by omega), frD a h0 (.inr (by omega)) (.inr (by omega)), frB a h0 ha,
        frA a h0 (by omega)]
    · intro a ha
      have hg := ha; unfold Glob at hg
      rw [glG a ha, frD a (by omega) (.inl (by omega)) (.inl (by omega)), glB a ha, frA a (by omega) (.inl (by omega))]
    · intro a ha
      rw [roG a (by omega) (HD.ro a ha), frD a (by omega) (.inl (by omega)) (.inl (by omega)), kRO a ha]
    · intro a ha
      rw [rdG, rdD, rdB a ha, rdA]
  -- Ω_W's outcome
  have hfit : ASem.argBase + key.length + [(0 : UInt8)].length ≤ ASem.outBase := by
    rw [hkl]; simp only [List.length_cons, List.length_nil]; decide
  have hold : ∀ v, c0.1.self.storage.get? key = some v → v.length < 2 ^ 63 := fun v hv => hvals _ v hv
  have hsw := ASem.step_write env key [0] c0 hfit hold
  rw [show ({ i := 8416, ω := ω, μ := μ, c := c0, q := f } : St Stream).c = c0 from rfl, hsw]
  by_cases hF : (ASem.writeAcct c0.1.self key [0]).minBalance > (ASem.writeAcct c0.1.self key [0]).balance
  · -- FULL: `Err`, then ☇ at 15361
    rw [if_pos hF]
    dsimp only
    have hS : writeSelf c0.1.self key [0] = c0.1.self := by unfold writeSelf; rw [if_pos hF]
    have hRw : writeR7 c0.1.self key [0] = Result.FULL := by unfold writeR7; rw [if_pos hF]
    rw [hRw] at sO
    unfold SetOut at sO
    rw [if_pos rfl] at sO
    rw [hS] at runD
    obtain ⟨ωG, μG, nG, runG, -, g7, -⟩ := rest ((c0.1.setSelf c0.1.self, c0.2), f) _ 3 (by decide) (by decide)
      sO.1 (by rw [show sp - 96 + 64 = sp - 96 + 56 + 8 by omega]; exact sO.2)
    refine .inr ⟨⟨e, ωD, μD, (c0.1.setSelf c0.1.self, c0.2), f⟩, ⟨_, runD⟩, rfl, .inr ⟨_, ⟨0, .refl⟩, rfl, ?_⟩⟩
    obtain ⟨ωE, runE⟩ := r9_err (P := P) (R := KeepCtx (accContractS env)) ((c0.1.setSelf c0.1.self, c0.2), f)
      ωG μG (by rw [g7]; simp)
    exact ⟨ωE, μG, f, (runG.trans runE).run (.exit (FreeRun.exit (Handlers.trap_15361 (P := P) ωE μG)) (by simp))⟩
  · -- `Ok`: on to 8490, then the checkpoint
    rw [if_neg hF]
    dsimp only
    have hRw : writeR7 c0.1.self key [0] ≠ Result.FULL := by
      unfold writeR7; rw [if_neg hF]
      cases hv : c0.1.self.storage.get? key with
      | none => simp [Result.NONE, Result.FULL]
      | some v => have := hold v hv; simp [Result.FULL]; omega
    have hS : writeSelf c0.1.self key [0] = ASem.writeAcct c0.1.self key [0] := by
      unfold writeSelf; rw [if_neg hF]
    unfold SetOut at sO
    rw [if_neg hRw] at sO
    have hrw : ∃ r, r < 2 ^ 64 ∧ r ≠ 18446744073709551615 ∧ μD.readN (sp - 96 + 56) 8 = Num.encodeLE 8 r := by
      by_cases hN : writeR7 c0.1.self key [0] = Result.NONE
      · rw [if_pos hN] at sO; exact ⟨0, by decide, by decide, sO⟩
      · rw [if_neg hN] at sO; exact ⟨1, by decide, by decide, sO.1⟩
    obtain ⟨r, hr, hr1, mr⟩ := hrw
    rw [hS] at runD
    have mb := readN_enc μD (sp - 96 + 64) 1
    generalize hc1 : (c0.1.setSelf (ASem.writeAcct c0.1.self key [0]), c0.2) = c1 at runD ⊢
    obtain ⟨ωG, μG, nG, runG, g1, g7, HG, keepG, stkG, glG, roG, rdG⟩ :=
      rest (c1, f) r _ hr (decodeLE_readN_lt μD (sp - 96 + 64) 1) mr mb
    rw [if_neg hr1] at g7
    refine .inr ⟨⟨e, ωD, μD, c1, f⟩, ⟨_, runD⟩, rfl, .inr ⟨_, ⟨0, .refl⟩, rfl, ?_⟩⟩
    obtain ⟨ωK, runK, k1⟩ := r9_ok (P := P) (R := KeepCtx (accContractS env)) (c1, f) ωG μG g7
    refine .inr ⟨⟨8490, ωK, μG, c1, f⟩, ⟨_, runG.trans runK⟩, rfl, ?_⟩
    -- the checkpoint
    unfold Prog.op Impl
    refine .inr ⟨⟨8490, ωK, μG, c1, f⟩, ⟨0, .refl⟩, rfl, ?_⟩
    rw [show ({ i := 8490, ω := ωK, μ := μG, c := c1, q := f } : St Stream).c = c1 from rfl,
      ASem.step_checkpoint]
    refine .inr ⟨⟨8492, setR7 ωK (f 0), μG, (c1.1, c1.1), f.tail⟩, ⟨1, r9_ck (P := P) env c1 f ωK μG⟩, rfl,
      .inr ⟨_, ⟨0, .refl⟩, rfl, rfl, by rw [setR7_1, k1, g1], free (free s2 kp) vp, HG, keepG, stkG, glG, roG, rdG⟩⟩

end Services.Bootstrap.Acc.Handlers.ResultsInit
