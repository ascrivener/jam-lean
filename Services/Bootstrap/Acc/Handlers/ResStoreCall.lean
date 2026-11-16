import Services.Bootstrap.Acc.Handlers.ResStoreGen
import Services.Bootstrap.Acc.Handlers.ResultsInit

/-!
# The results store as `Impl` (36170 → the caller), any n

`store_core`: from 36170 (called from row 9, the `Checkpoint` instruction or row 11, `RetOK`), the run
implements `orPanic (write key (encodeResults rs))` (GP v0.8.0 Appendix B, Ω_W of ℰ(↕rs)), with the key
the tag-2 key value at sp + 1568: `res_store` (to `set`'s call), `set_call` (Ω_W), `res_freeG` (both
deallocs, back to the caller's return address t). `Ok` ends at t with ω₇ = −1; FULL continues at t with
ω₇ = 3, from where the caller ends ☇ (`herr`). Early ☇ only for heap exhaustion: the traps 36528 and
34070, and `ExhaustsP` (a failed allocator call at 40611 or 40821).
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow
  Services.Bootstrap.Acc.Handlers.Results Services.Bootstrap.Acc.Handlers.KeyEnc
  Services.Bootstrap.Acc.Handlers.RecentSlotWrite Services.Bootstrap.Acc.Handlers.ResultsInit

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `ExhaustsP` is an allowed early ☇ when `Ab` covers the failed allocator calls (ω₇ = 0 there). -/
theorem ExhaustsP.aborts {p : ByteArray} {env : AccEnv} {pb : Nat} {Ab : St Stream → Prop}
    (hAbX : ∀ s : St Stream, (s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0 → Ab s) {s : St Stream}
    (h : ExhaustsP p env pb s.i s.ω s.μ s.c s.q) : Aborts p (KeepCtx (accContractS env)) Ab s s.c := by
  obtain ⟨ω', μ', q', j, N, run, h7, hj, ω'', μ'', q'', fin⟩ := h
  refine ⟨⟨j, ω', μ', s.c, q'⟩, ⟨N, run⟩, hAbX _ ⟨?_, h7⟩, ω'', μ'', q'', fin⟩
  rcases hj with ⟨e, -⟩ | ⟨e, -⟩
  · exact .inl e
  · exact .inr e

/-- **The state after the results store** at the caller's return address t, against the memory μ₀
    and allocator state st at 36170: ω₇ = −1 (`Ok`), ω₁ = sp, ω₅ and ω₆ restored; the allocator's
    context for some st′ keeping every allocated chunk of st with its data; memory kept from sp up, at
    the globals and below 196608 (with its access). -/
def StorePost (code : ByteArray) (pb S0 S1 sp t : Nat) (v5 v6 : UInt64) (st : State) (μ₀ : Memory)
    (s' : St Stream) : Prop :=
  s'.i = t ∧ s'.ω[7] = UInt64.ofNat 18446744073709551615 ∧ s'.ω[1] = UInt64.ofNat sp ∧ s'.ω[5] = v5 ∧
  s'.ω[6] = v6 ∧
  ∃ st', HeapCtxC code pb S0 S1 s'.μ st' ∧
    (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 4294967296 → sp ≤ a → s'.μ.read a = μ₀.read a) ∧
    (∀ a, Glob a → s'.μ.read a = μ₀.read a) ∧ (∀ a, a < 196608 → s'.μ.read a = μ₀.read a) ∧
    (∀ a, a < 196608 → s'.μ.readable a = μ₀.readable a)

/-- **The results store, 36170 → the caller (`RetOK ret t`), implements
    `orPanic (write key (encodeResults rs))`** (GP v0.8.0 Appendix B, Ω_W of ℰ(↕rs)), with the key
    `keyEnc μ (sp + 1568) 2` (the tag-2 key value at sp + 1568), the n results at rp (`LoopHyp`), under
    `accContractS` against `ExtendH` (R8) and `OkEncH` (R9), with abort reasons `Ab` covering the
    allocation-failure traps 36528 and 34070 and the failed allocator calls 40611 and 40821 (heap
    exhaustion). `Ok` ends in `StorePost` at t; FULL reaches t with ω₇ = 3, where the caller ends ☇
    (`herr`). Hypotheses: the key-size word kc for tag 2 at 68696 (35 ≤ kc), `set`'s error table at
    69056 and 69072, 68680 … 69076 readable; the stack frame up to sp + 1632; `StoreFit`. -/
theorem store_core {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (Ab : St Stream → Prop) (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s)
    (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s) (hAbX : ∀ s : St Stream, (s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0 → Ab s)
    (ret t : Nat) (hrt : RetOK ret t)
    (herr : ∀ (c : AccCtx) (q : Stream) (ω : Regs) (μ : Memory), ω[7] = UInt64.ofNat 3 →
      ∃ ω' μ' q', FreeRunH p (KeepCtx (accContractS env)) t ω μ (c, q) .panic ω' μ' (c, q'))
    (s : St Stream) (st : State) (sp rp n kc : Nat) (rs : List Spec.Result)
    (H : HeapCtxC env.code pb S0 S1 s.μ st) (hi : s.i = 36170)
    (h0 : s.ω[0] = UInt64.ofNat ret) (h1 : s.ω[1] = UInt64.ofNat sp) (h7 : s.ω[7] = UInt64.ofNat rp)
    (h8 : s.ω[8] = UInt64.ofNat n) (h9 : s.ω[9] = UInt64.ofNat (sp + 1568))
    (L : LoopHyp pb S0 S1 sp rp n rs st s.μ) (hS1 : sp + 1632 ≤ S1)
    (mt : s.μ.readN (sp + 1568) 2 = Num.encodeLE 2 2)
    (mc : s.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (ht8 : rdN s.μ 69072 4 = 4294900408) (ht4 : rdN s.μ 69056 4 = 4294900402)
    (hro : ∀ a, 68680 ≤ a → a < 69076 → s.μ.readable a = true) (hvals : StoreFit s.c) :
    Impl p (accContractS env) env Ab (orPanic (.write (keyEnc s.μ (sp + 1568) 2) (encodeResults rs)))
      (fun _ => StorePost env.code pb S0 S1 sp t s.ω[5] s.ω[6] st s.μ) s := by
  obtain ⟨i, ω, μ, c0, f⟩ := s
  dsimp only at hi h0 h1 h7 h8 h9 H L mt mc ht8 ht4 hro hvals ⊢
  subst hi
  have L0 := L
  obtain ⟨hsp, hS1', hn, -, -⟩ := L0
  generalize hkey : keyEnc μ (sp + 1568) 2 = key
  have hkl : key.length = 35 := by
    rw [← hkey, keyEnc_length]; simp only [show (2 : Nat) ≠ 1 from by decide, if_false, if_true]
  unfold orPanic
  refine Impl.bind _ _ _ _ ?_
  unfold Prog.op Impl
  rcases res_store (P := P) env hE hO cap hcap1 hcap c0 f ω μ st sp rp n (sp + 1568) kc rs H h1 h7 h8 h9 L
      ⟨by omega, by omega, by omega⟩ mt mc hkc (fun a h1 h2 => hro a (by omega) (by omega)) with
    ⟨ωB, μB, nB, runB⟩ | ⟨ωB, μB, nB, runB⟩ | hx | ⟨ωB, μB, nB, runB, SP, m0, m5, m6⟩
  · exact .inl ⟨⟨36528, ωB, μB, c0, f⟩, ⟨_, runB⟩, hAb1 _ rfl, ωB, μB, f,
      .exit (FreeRun.exit (trap_36528 (P := P) ωB μB)) (by simp)⟩
  · exact .inl ⟨⟨34070, ωB, μB, c0, f⟩, ⟨_, runB⟩, hAb2 _ rfl, ωB, μB, f,
      .exit (FreeRun.exit (RecentCounter.trap_34070 (P := P) ωB μB)) (by simp)⟩
  · exact .inl (ExhaustsP.aborts (s := ⟨36170, ω, μ, c0, f⟩) hAbX hx)
  refine .inr ⟨⟨48104, ωB, μB, c0, f⟩, ⟨_, runB⟩, rfl, ?_⟩
  rw [hkey] at SP
  obtain ⟨vp, kp, vc, dv, s2, HB, hst, hCv, hdu, hda, hCk, hne, hv1, hv2, hk1, hk2, hvc0, hvc, hlv, hvd, b0, b1, b5, b6, b7,
    b8, b9, b10, b11, mkey, mval, mkc, mvc, mvp, frB, glB, roB⟩ := SP
  have hSB := HB.st
  have hret : (UInt64.ofNat ret).toNat = ret := by
    rcases hrt with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  have hSt := H.st
  have kRO : ∀ a, a < 196608 → μB.read a = μ.read a := fun a ha => (roB a ha).1
  have ht8B : rdN μB 69072 4 = 4294900408 := by
    rw [← ht8]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => kRO _ (by omega)
  have ht4B : rdN μB 69056 4 = 4294900402 := by
    rw [← ht4]; unfold rdN; congr 1; exact Memory.readN_congr fun j hj => kRO _ (by omega)
  have hkr : μB.rangeReadable kp 35 = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => Memory.readable_of_writable (HeapKeep.writableData HB hCk rfl
      (by unfold HeapKeep.InData; dsimp only; omega))) (by omega)
  have hdi := Services.Bootstrap.Decode.VecU8.chunk_in HB.wf hCv hdu
  generalize hval : encodeResults rs = val at mval b11 hv2 hlv
  have hvr : μB.rangeReadable vp val.length = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => Memory.readable_of_writable (HeapKeep.writableData HB hCv hdu
      (by unfold HeapKeep.InData; omega))) (by omega)
  obtain ⟨e, ωD, μD, he, runD, d0, d1, d5, d6, sO, frD, rdD, wrD⟩ := set_call (P := P) env c0 f ωB μB (sp - 96)
    (sp - 96 + 56) kp 35 vp val.length key val b1 b7 b8 b9 b10 b11 (by decide) (by omega) (by omega)
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun a h1 h2 => hSB a (by omega) (by omega))
    (fun a h1 h2 => hSB a (by omega) (by omega)) (.inr (by omega)) hkr mkey hvr mval rfl (.inl (by omega))
    (.inl (by omega)) ht8B ht4B (fun a h1 h2 => by rw [(roB a (by omega)).2]; exact hro a (by omega) (by omega))
    (by omega) (fun v hv => hvals _ v hv)
  have HD : HeapCtxC env.code pb S0 S1 μD s2 :=
    HeapKeep.keepHi HB (fun a ha => frD a (by omega) (.inl (by omega)) (.inl (by omega))) wrD
  have kD : ∀ b n, b + n ≤ 4294967296 → sp - 96 ≤ b → (b + n ≤ sp - 96 + 56 ∨ sp - 96 + 72 ≤ b) →
      μD.readN b n = μB.readN b n := fun b n h0 h1 h2 =>
    Memory.readN_congr fun j hj => frD _ (by omega) (.inr (by omega)) (by omega)
  -- after `set`, for its result word r and the octet b after it
  have rest : ∀ (x : AccCtx × Stream) r b, r < 2 ^ 64 → b < 256 →
      μD.readN (sp - 96 + 56) 8 = Num.encodeLE 8 r → μD.readN (sp - 96 + 64) 1 = Num.encodeLE 1 b →
      ∃ ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) e ωD μD x t ω' μ' x n ∧
        ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
        ω'[7] = (if r = 18446744073709551615 then UInt64.ofNat b else UInt64.ofNat 18446744073709551615) ∧
        HeapCtxC env.code pb S0 S1 μ' (free (free s2 kp) vp) ∧
        (∀ d ∈ chunks st, d.used = true → d ∈ chunks (free (free s2 kp) vp) ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
        (∀ a, a < 196608 → μ'.readable a = μ.readable a) := by
    intro x r b hr hb mr mb
    obtain ⟨ωG, μG, nG, runG, g1, g5, g6, g7, HG, keepG, stkG, glG, roG, rdG⟩ := res_freeG (P := P)
      (R := KeepCtx (accContractS env)) env.code pb S0 S1 x ωD μD s2 sp vp kp kc r b ω[5].toNat ω[6].toNat e vc
      ret t hrt dv HD hCv hdu hda hCk hne (by omega) hvc (by omega) he (d0.trans b0) d1 (d5.trans b5)
      (d6.trans b6) (by omega) ⟨by omega, by omega⟩ (by omega) (by omega) hr hb (UInt64.toNat_lt _)
      (UInt64.toNat_lt _) (by rw [kD _ _ (by omega) (by omega) (.inl (by omega))]; exact mkc) mr mb
      (by rw [kD _ _ (by omega) (by omega) (.inl (by omega))]; exact mvc)
      (by rw [kD _ _ (by omega) (by omega) (.inl (by omega))]; exact mvp)
      (by rw [kD _ _ (by omega) (by omega) (.inr (by omega)), m0, h0, hret])
      (by rw [kD _ _ (by omega) (by omega) (.inr (by omega))]; exact m5)
      (by rw [kD _ _ (by omega) (by omega) (.inr (by omega))]; exact m6)
    refine ⟨ωG, μG, nG, runG, g1, by rw [g5]; simp, by rw [g6]; simp, g7, HG, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd hu
      obtain ⟨k0, k1, k2, k3⟩ := hst d hd hu
      obtain ⟨k4, k5⟩ := keepG d k0 hu k1 k2
      refine ⟨k4, fun a ha => ?_⟩
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
      have := H.hbT
      have ha' := ha; unfold InData at ha'
      rw [k5 a ha, frD a (by omega) (.inl (by omega)) (.inl (by omega)), k3 a ha]
    · intro a h0 ha
      rw [stkG a h0 (by omega) (by omega), frD a h0 (.inr (by omega)) (.inr (by omega)), frB a h0 ha]
    · intro a ha
      have hg := ha; unfold Glob at hg
      rw [glG a ha, frD a (by omega) (.inl (by omega)) (.inl (by omega)), glB a ha]
    · intro a ha
      rw [roG a (by omega) (HD.ro a ha), frD a (by omega) (.inl (by omega)) (.inl (by omega)), kRO a ha]
    · intro a ha
      rw [rdG, rdD, (roB a ha).2]
  -- Ω_W's outcome
  have hfit : ASem.argBase + key.length + val.length ≤ ASem.outBase := by
    rw [hkl]; unfold ASem.argBase ASem.outBase; omega
  have hold : ∀ v, c0.1.self.storage.get? key = some v → v.length < 2 ^ 63 := fun v hv => hvals _ v hv
  have hsw := ASem.step_write env key val c0 hfit hold
  rw [show ({ i := 36170, ω := ω, μ := μ, c := c0, q := f } : St Stream).c = c0 from rfl, hsw]
  by_cases hF : (ASem.writeAcct c0.1.self key val).minBalance > (ASem.writeAcct c0.1.self key val).balance
  · -- FULL: `Err`, then ☇ from t
    rw [if_pos hF]
    dsimp only
    have hS : writeSelf c0.1.self key val = c0.1.self := by unfold writeSelf; rw [if_pos hF]
    have hRw : writeR7 c0.1.self key val = Result.FULL := by unfold writeR7; rw [if_pos hF]
    rw [hRw] at sO
    unfold SetOut at sO
    rw [if_pos rfl] at sO
    rw [hS] at runD
    obtain ⟨ωG, μG, nG, runG, -, -, -, g7, -⟩ := rest ((c0.1.setSelf c0.1.self, c0.2), f) _ 3 (by decide)
      (by decide) sO.1 (by rw [show sp - 96 + 64 = sp - 96 + 56 + 8 by omega]; exact sO.2)
    refine .inr ⟨⟨e, ωD, μD, (c0.1.setSelf c0.1.self, c0.2), f⟩, ⟨_, runD⟩, rfl, .inr ⟨_, ⟨0, .refl⟩, rfl, ?_⟩⟩
    obtain ⟨ωE, μE, qE, finE⟩ := herr (c0.1.setSelf c0.1.self, c0.2) f ωG μG (by rw [g7]; simp)
    exact ⟨ωE, μE, qE, runG.run finE⟩
  · -- `Ok`: back at t
    rw [if_neg hF]
    dsimp only
    have hRw : writeR7 c0.1.self key val ≠ Result.FULL := by
      unfold writeR7; rw [if_neg hF]
      cases hv : c0.1.self.storage.get? key with
      | none => simp [Result.NONE, Result.FULL]
      | some v => have := hold v hv; simp [Result.FULL]; omega
    have hS : writeSelf c0.1.self key val = ASem.writeAcct c0.1.self key val := by
      unfold writeSelf; rw [if_neg hF]
    unfold SetOut at sO
    rw [if_neg hRw] at sO
    have hrw : ∃ r, r < 2 ^ 64 ∧ r ≠ 18446744073709551615 ∧ μD.readN (sp - 96 + 56) 8 = Num.encodeLE 8 r := by
      by_cases hN : writeR7 c0.1.self key val = Result.NONE
      · rw [if_pos hN] at sO; exact ⟨0, by decide, by decide, sO⟩
      · rw [if_neg hN] at sO; exact ⟨1, by decide, by decide, sO.1⟩
    obtain ⟨r, hr, hr1, mr⟩ := hrw
    rw [hS] at runD
    have mb := readN_enc μD (sp - 96 + 64) 1
    generalize hc1 : (c0.1.setSelf (ASem.writeAcct c0.1.self key val), c0.2) = c1 at runD ⊢
    obtain ⟨ωG, μG, nG, runG, g1, g5, g6, g7, HG, keepG, stkG, glG, roG, rdG⟩ :=
      rest (c1, f) r _ hr (decodeLE_readN_lt μD (sp - 96 + 64) 1) mr mb
    rw [if_neg hr1] at g7
    refine .inr ⟨⟨e, ωD, μD, c1, f⟩, ⟨_, runD⟩, rfl, .inr ⟨_, ⟨0, .refl⟩, rfl, .inr ⟨⟨t, ωG, μG, c1, f⟩, ⟨_, runG⟩,
      rfl, rfl, g7, g1, g5, g6, free (free s2 kp) vp, HG, keepG, stkG, glG, roG, rdG⟩⟩⟩

end Services.Bootstrap.Acc.Handlers.ResStore
