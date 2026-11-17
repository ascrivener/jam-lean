import Services.Bootstrap.Acc.Handlers.RecentCounterGet
import Services.Bootstrap.Acc.Handlers.RecentSlotGet

/-!
# `add_recent_work_item`'s counter read, composed (8013 → 8056)

`counter_get`: from 8013 the run reads the counter (GP v0.8.0 Appendix B, Ω_R of `[0]`) and reaches 8056
with ω₅'s low 32 bits the spec's `((storage [0]).bind (decode (fixedN 4))).getD 0` (quirk Q12: a value
shorter than 4 octets, or none, reads as 0; a longer one is read from its first 4), or reaches an
allocation-failure trap (34070, 47977).
-/

namespace Services.Bootstrap.Acc.Handlers.RecentCounterGet

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc Services.Bootstrap.Decode.DeallocCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem ctrDec_long (w : Bytes) (h : 4 ≤ w.length) :
    decode (Dec.fixedN 4) w = some (Num.decodeLE (w.take 4)) := by
  simp [decode, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure, Option.bind, h]

theorem ctrDec_short (w : Bytes) (h : w.length < 4) : decode (Dec.fixedN 4) w = none := by
  simp [decode, Dec.take, Dec.fixedN, StateT.run, bind, StateT.bind, pure, StateT.pure, Option.bind,
    show ¬ 4 ≤ w.length by omega]

/-- The counter `addRecent` reads from a stored value. -/
def ctrVal (v : Option Bytes) : Nat := (v.bind (decode (Dec.fixedN 4))).getD 0

/-- **The counter's typed get, 8013 → 8056**, under `KeepCtx (accContractS env)`: either the run reaches
    8056 with ω₁ = sp, ω₆ restored, ω₅'s low 32 bits `ctrVal` of the value under `[0]`, the allocator's
    context for some st′ keeping st's chunks and their data, memory kept from sp up off the key value
    (sp + 1568, 2 octets), at the globals and below 196608, and the value (if any) shorter than 2³¹
    octets; or it reaches 34070 or 47977 (an `alloc` failed). Hypotheses: the key-size word kc for tag
    0 at 68680 (1 ≤ kc, kc + 31 < 2³⁶), readable; the frame [sp − 352, sp + 1632) in the stack; the value
    shorter than 2⁶³ octets (`ValuesFit`). -/
theorem counter_get {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (st : State) (sp kc pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ st) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483648 + 352 ≤ sp ∧ sp % 8 = 0) (hS0 : S0 + 352 ≤ sp) (hS1 : sp + 1632 ≤ S1)
    (mc : μ.readN 68680 8 = Num.encodeLE 8 kc) (hkc : 1 ≤ kc ∧ kc + 31 < 68719476736)
    (hrt : ∀ a, 68680 ≤ a → a < 68688 → μ.readable a = true)
    (hfit : ∀ w, c.1.self.storage.get? [0] = some w → w.length < 9223372036854775808) :
    (∃ st' ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) 8013 ω μ (c, f) 8056 ω' μ' (c, f) n ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[6] = ω[6] ∧
      ω'[5].toNat % 4294967296 = ctrVal (c.1.self.storage.get? [0]) ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1568 ∨ sp + 1570 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.readable a = μ.readable a) ∧
      (∀ w, c.1.self.storage.get? [0] = some w → w.length < 2 ^ 31)) ∨
    (∃ e ω' μ' n, (e = 34070 ∨ e = 47977) ∧
      FreeStepsH p (KeepCtx (accContractS env)) 8013 ω μ (c, f) e ω' μ' (c, f) n) := by
  have hSt := H.st
  have hS1' := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  -- A: 8013 → 33843
  obtain ⟨ωA, μA, runA, a0, a1, a5, a6, a7, a8, mA0, mA8, mA16, mA24, frA, rdA, wrA⟩ :=
    cg_pre (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 ⟨by omega, by omega⟩
      (fun a h1 h2 => hSt a (by omega) (by omega)) (fun a h1 h2 => hSt a (by omega) (by omega))
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega)) (.inl (by omega))) wrA
  have mcA : μA.readN (68680 + 8 * 0) 8 = Num.encodeLE 8 kc := by
    rw [← mc]; exact Memory.readN_congr fun j hj => frA _ (by omega) (.inl (by omega)) (.inl (by omega))
  have hk0 : keyEnc μA (sp + 1568) 0 = [0] := by simp [keyEnc]
  -- B: the key encoder
  rcases kb_call (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ωA μA st (sp - 80) (sp + 1568) (sp - 48)
      0 kc 1610 34637 pb S0 S1 HA a0 a1 a7 a8 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) mA0 mcA
      (fun a h1 h2 => by rw [rdA]; exact hrt a (by omega) (by omega))
      ⟨by rw [hk0]; simp only [List.length_cons, List.length_nil]; omega, hkc.2⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_804]) bs_34637 with
    ⟨kptr, s1, ωB, μB, nB, -, runB, HB, keepB, hnewK, hfreshK, oB0, oB8, oB16, oBk, hgB, stkB, b0, b1, b5, b6⟩ |
    ⟨-, ωB, μB, nB, runB⟩
  case inr =>
    obtain ⟨-, runBS⟩ := FreeStepsH.growS f runB
    exact .inr ⟨34070, ωB, μB, _, .inl rfl, runA.trans runBS⟩
  obtain ⟨pgB, roB⟩ := HeapHost.keepRO (env := accHeapHost env) HA.bd runB
  obtain ⟨-, runBS⟩ := FreeStepsH.growS f runB
  rw [hk0] at oB16 oBk
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at oB16 oBk
  have hS1B := HB.hS1
  obtain ⟨nk1, nk2, nk3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in HB.wf hnewK rfl
  dsimp only at nk1 nk2 nk3
  have hb0B := HB.hb0
  have hbTB := HB.hbT
  have hdivK : kc ≤ 32 * ((kc + 31) / 32) := by omega
  -- C: 34637 → 47857
  obtain ⟨ωC, runC, c0, c1, c5, c6, c7, c8, c9⟩ := cg_g (P := P) (R := KeepCtx (accContractS env)) (c, f)
    ωB μB (sp - 80) kptr 1 (b1.trans a1) (by omega) (by omega) (by decide)
    (by rw [show sp - 80 + 40 = sp - 48 + 8 by omega]; exact oB8)
    (by rw [show sp - 80 + 48 = sp - 48 + 16 by omega]; exact oB16)
    (fun a h1 h2 => Memory.readable_of_writable (HB.st a (by omega) (by omega)))
  -- D: `get`
  rcases get_call (P := P) (hb := 0) env cap pb hcap1 hcap c f ωC μB s1 (sp - 80) (sp - 72) kptr 1 S0 S1
      [0] HB c1 (by rw [c7]; congr 1; omega) c8 c9 (by decide) (by omega) (by omega) ⟨by omega, by omega⟩
      (.inr ⟨_, hnewK, rfl, fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩⟩) (by omega)
      oBk hfit with
    ⟨e, s2, ωD, μD, nD, he, runD, d0, d1, d5, d6, gO, HD, keepD, dataD, stkD, glD, loD, rdD⟩ | ⟨ωD, μD, nD, runD⟩
  case inr =>
    exact .inr ⟨47977, ωD, μD, _, .inr rfl, (runA.trans runBS).trans (runC.trans runD)⟩
  have runD' := cg_gret (P := P) (R := KeepCtx (accContractS env)) (c, f) ωD μD e he (d0.trans c0)
  -- E: the key's buffer freed
  obtain ⟨ωE, runE, e0, e1, e5, e6, e7⟩ := cg_dk (P := P) (R := KeepCtx (accContractS env)) (c, f) ωD μD
    (sp - 80) kc d1 (by omega) (by omega) (by omega)
    (by rw [← oB0, show sp - 80 + 32 = sp - 48 by omega]
        exact Memory.readN_congr fun j hj => stkD _ (by omega) (by omega) (.inr (by omega)))
    (fun a h1 h2 => Memory.readable_of_writable (HD.st a (by omega) (by omega)))
  have hKD := keepD _ hnewK rfl
  obtain ⟨ωF, μF, runF, HF, -, pgF, roF, stkF, glF, keepF, f0, f1, f5, f6⟩ :=
    dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ωE μD s2 (sp - 80)
      kptr 1614 34671 _ HD hKD rfl (by dsimp only; omega) e0 e1 (e7.trans (d5.trans c5))
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_806]) bs_34671
      (by omega) ⟨by omega, by omega⟩
  have run0 := (((((runA.trans runBS).trans runC).trans runD).trans runD').trans runE).trans runF
  -- the frame words
  have kF : ∀ o n, sp - 24 ≤ o → o + n ≤ sp → μF.readN o n = μA.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => by
      rw [stkF _ (by omega) (by omega), stkD _ (by omega) (by omega) (.inr (by omega)),
        stkB _ (by omega) (by omega) (.inr (by omega))]
  have m72 : μF.readN (sp - 80 + 72) 8 = Num.encodeLE 8 278 := by
    rw [kF _ _ (by omega) (by omega), show sp - 80 + 72 = sp - 8 by omega]; exact mA8
  have m56 : μF.readN (sp - 80 + 56) 8 = Num.encodeLE 8 ω[6].toNat := by
    rw [kF _ _ (by omega) (by omega), show sp - 80 + 56 = sp - 24 by omega, mA24]
  have kFv : ∀ o n, sp - 80 + 8 ≤ o → o + n ≤ sp - 80 + 32 → μF.readN o n = μD.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => stkF _ (by omega) (by omega)
  have eF1 : ωF[1] = UInt64.ofNat (sp - 80) := f1.trans e1
  have hv6 : ω[6].toNat < 2 ^ 64 := UInt64.toNat_lt _
  have e6F : ωF[6] = ω[6] := f6.trans (e6.trans (d6.trans (c6.trans (b6.trans a6))))
  -- the memory frame so far
  have frF : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1568 ∨ sp + 1570 ≤ a) → μF.read a = μ.read a :=
    fun a h0 ha hb => by
      rw [stkF a h0 (by omega), stkD a h0 (by omega) (.inr (by omega)), stkB a h0 (by omega) (.inr (by omega)),
        frA a h0 (.inr ha) hb]
  have glF0 : ∀ a, Glob a → μF.read a = μ.read a := fun a ha => by
    have ha' := ha; unfold Glob at ha'
    rw [glF a ha, glD a ha, hgB a (RecentSlotWrite.glob_off HB.wf hb0B ha) (.inl (by omega)),
      frA a (by omega) (.inl (by omega)) (.inl (by omega))]
  have loF0 : ∀ a, a < 196608 → μF.read a = μ.read a := fun a ha => by
    rw [roF a (by unfold two32; omega) (HD.ro a ha), loD a ha,
      roB a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (by rw [wrA]; exact H.ro a ha),
      frA a (by omega) (.inl (by omega)) (.inl (by omega))]
  have rdF0 : ∀ a, a < 196608 → μF.readable a = μ.readable a := fun a ha => by
    rw [show μF.readable a = μD.readable a by unfold Memory.readable; rw [pgF], rdD a ha,
      show μB.readable a = μA.readable a by
        unfold Memory.readable; rw [pgB (a / pageSize) (.inl (by unfold pageSize; omega))], rdA]
  have keep0 : ∀ d ∈ chunks st, d.used = true → d ∈ chunks (free s2 kptr) ∧ d ∈ chunks s1 ∧
      ∀ a, InData d a → μF.read a = μ.read a := by
    intro d hd hu
    have hd1 := keepB d hd hu
    obtain ⟨k1, k2⟩ := keepF d (keepD d hd1 hu) hu (hfreshK d hd hu)
    refine ⟨k1, hd1, fun a ha => ?_⟩
    have hap := InData.apart HB.wf hd1 hnewK (Ne.symm (hfreshK d hd hu)) ha
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have ha' := ha
    unfold InData at ha' hap
    dsimp only at hap
    rw [k2 a ha, dataD d hd1 hu a ⟨ha'.1, ha'.2⟩,
      hgB a (RecentSlotWrite.data_off HB.wf hb0B hbTB hd1 ha) (by omega),
      frA a (by omega) (.inl (by omega)) (.inl (by omega))]
  -- F: by `get`'s value
  cases hv : c.1.self.storage.get? [0] with
  | none =>
    rw [hv] at gO
    simp only [GetOut] at gO
    obtain ⟨ωG, runG, g1, g5, g6⟩ := cg_none (P := P) (R := KeepCtx (accContractS env)) (c, f) ωF μF (sp - 80)
      ω[6].toNat eF1 (by omega) hv6
      (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 8 = sp - 72 by omega]; exact gO) m72 m56
      (fun a h1 h2 => Memory.readable_of_writable (HF.st a (by omega) (by omega)))
    refine .inl ⟨free s2 kptr, ωG, μF, _, run0.trans runG, by rw [g1]; congr 1; omega,
      g6.trans UInt64.ofNat_toNat, by rw [g5]; simp [ctrVal], HF, fun d hd hu => ⟨(keep0 d hd hu).1, (keep0 d hd hu).2.2⟩,
      frF, glF0, loF0, rdF0, fun w hw => by simp at hw⟩
  | some w =>
    rw [hv] at gO
    -- the reads: `Some(Vec { cap, ptr, len })`, the slice reader, `read_exact` of 4 octets
    have hT := hsp.1
    have common : ∀ (cp vptr L : Nat), cp < 2 ^ 64 → cp ≠ 18446744073709551615 → vptr < 2 ^ 31 → L < 2 ^ 31 →
        μF.readN (sp - 80 + 8) 8 = Num.encodeLE 8 cp → μF.readN (sp - 80 + 16) 8 = Num.encodeLE 8 vptr →
        μF.readN (sp - 80 + 24) 8 = Num.encodeLE 8 L →
        (4 ≤ L → 65536 ≤ vptr ∧ (∀ a, vptr ≤ a → a < vptr + 4 → μF.readable a = true)) →
        ∃ ωH μH ok v n, FreeStepsH p (KeepCtx (accContractS env)) 34671 ωF μF (c, f) 34711 ωH μH (c, f) n ∧
          ωH[1] = UInt64.ofNat (sp - 80) ∧ ωH[5] = UInt64.ofNat cp ∧ ωH[6] = ωF[6] ∧ ωH[7] = UInt64.ofNat ok ∧
          (ok = 0 ∨ ok = 1) ∧ μH.readN (sp - 80 + 8) 4 = Num.encodeLE 4 v ∧ v < 2 ^ 32 ∧
          (ok = 0 → 4 ≤ L ∧ μH.readN (sp - 80 + 8) 4 = μF.readN vptr 4) ∧ (ok = 1 → L < 4) ∧
          μH.readN (sp - 80) 8 = Num.encodeLE 8 vptr ∧
          (∀ a, a < 4294967296 → (a < sp - 80 - 88 ∨ sp - 80 + 48 ≤ a) → μH.read a = μF.read a) ∧
          (∀ a, μH.readable a = μF.readable a) ∧ (∀ a, μH.writable a = μF.writable a) := by
      intro cp vptr L hcp hc1 hvp hL g8 g16 g24 hrv
      obtain ⟨ωG, μG, runG, g0, g1, g5, g6, g7, g8', g9, mT, mR, mL, frG, rdG, wrG⟩ :=
        cg_some (P := P) (R := KeepCtx (accContractS env)) (c, f) ωF μF (sp - 80) cp vptr L eF1 (by omega) hcp hc1
          (by omega) (by omega) g8 g16 g24 (fun a h1 h2 => HF.st a (by omega) (by omega))
      by_cases hL4 : 4 ≤ L
      · obtain ⟨hv0, hrv⟩ := hrv hL4
        obtain ⟨ωH, μH, runH, h0, h1', h5, h6, h7, hdat, -, -, frH, rdH, wrH⟩ :=
          Services.Bootstrap.Acc.Handlers.RecentSlot.read_exact_text (P := P) (R := KeepCtx (accContractS env)) (c, f) ωG μG (sp - 80) (sp - 80 + 32)
            (sp - 80 + 8) 4 vptr L 1616 34711 ⟨by omega, by omega, by omega⟩ g0 g1 g7 g8' g9
            ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_807]) bs_34711
            (Handlers.DesignateAlloc.rd8 (by omega) mR) (Handlers.DesignateAlloc.rd8 (by omega) mL) hL4
            (.inr (by omega)) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega))
            (.inl (by omega)) (.inr (by omega)) (.inr (by omega))
            (fun a h1 h2 => by rw [rdG]; exact hrv a h1 h2)
            (fun a h1 h2 => by rw [wrG]; exact HF.st a (by omega) (by omega))
            (fun a h1 h2 => by rw [wrG]; exact HF.st a (by omega) (by omega))
            (fun a h1 h2 => by rw [wrG]; exact HF.st a (by omega) (by omega))
        refine ⟨ωH, μH, 0, Num.decodeLE (μH.readN (sp - 80 + 8) 4), _, runG.trans runH, h1'.trans g1,
          h5.trans g5, h6.trans g6, h7, .inl rfl, readN_enc μH _ 4, decodeLE_readN_lt μH _ 4,
          fun _ => ⟨hL4, hdat.trans (Memory.readN_congr fun j hj => frG _ (by omega) (.inl (by omega)))⟩,
          fun h => absurd h (by decide), ?_, ?_, fun a => by rw [rdH, rdG], fun a => by rw [wrH, wrG]⟩
        · rw [← mT]; exact Memory.readN_congr fun j hj => frH _ (by omega) (.inl (by omega)) (.inr (by omega))
            (.inl (by omega))
        · intro a h0 ha
          rw [frH a h0 (by omega) (by omega) (by omega), frG a h0 (by omega)]
      · obtain ⟨ωH, μH, runH, h0, h1', h5, h6, h7, frH, rdH, wrH⟩ :=
          RecentSlot.re_short (P := P) (R := KeepCtx (accContractS env)) (c, f) ωG μG (sp - 80) (sp - 80 + 32) 4 L
            1616 34711 ⟨by omega, by omega⟩ g0 g1 g7 g9 (by decide) ⟨by decide, by decide, by decide⟩
            (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_807]) bs_34711
            (Handlers.DesignateAlloc.rd8 (by omega) mL) (by omega) (by omega) (.inr (by omega))
            (fun a h1 h2 => by rw [rdG]; exact Memory.readable_of_writable (HF.st a (by omega) (by omega)))
            (fun a h1 h2 => by rw [wrG]; exact HF.st a (by omega) (by omega))
        refine ⟨ωH, μH, 1, Num.decodeLE (μH.readN (sp - 80 + 8) 4), _, runG.trans runH, h1'.trans g1,
          h5.trans g5, h6.trans g6, h7, .inr rfl, readN_enc μH _ 4, decodeLE_readN_lt μH _ 4,
          fun h => absurd h (by decide), fun _ => by omega, ?_, ?_, fun a => by rw [rdH, rdG],
          fun a => by rw [wrH, wrG]⟩
        · rw [← mT]; exact Memory.readN_congr fun j hj => frH _ (by omega) (.inr (by omega))
        · intro a h0 ha
          rw [frH a h0 (by omega), frG a h0 (by omega)]
    have m72' : ∀ μH : Memory, (∀ a, a < 4294967296 → (a < sp - 80 - 88 ∨ sp - 80 + 48 ≤ a) → μH.read a = μF.read a) →
        μH.readN (sp - 80 + 72) 8 = Num.encodeLE 8 278 ∧ μH.readN (sp - 80 + 56) 8 = Num.encodeLE 8 ω[6].toNat :=
      fun μH fr => ⟨by rw [← m72]; exact Memory.readN_congr fun j hj => fr _ (by omega) (.inr (by omega)),
        by rw [← m56]; exact Memory.readN_congr fun j hj => fr _ (by omega) (.inr (by omega))⟩
    cases w with
    | nil =>
      simp only [GetOut] at gO
      obtain ⟨g8, g16, g24⟩ := gO
      obtain ⟨ωH, μH, ok, v, nH, runH, h1', h5', h6', h7', hok, mv, hv32, hok0, -, -, frH, rdH, wrH⟩ :=
        common 0 1 0 (by decide) (by decide) (by decide) (by decide)
          (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 8 = sp - 72 by omega]; exact g8)
          (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 16 = sp - 72 + 8 by omega]; exact g16)
          (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 24 = sp - 72 + 16 by omega]; exact g24)
          (fun h => absurd h (by decide))
      have hok1 : ok = 1 := by
        rcases hok with h | h
        · exact absurd (hok0 h).1 (by decide)
        · exact h
      subst hok1
      obtain ⟨n0, n6⟩ := m72' μH frH
      obtain ⟨ωI, runI, i1, i6, i5⟩ := cg_fin0 (P := P) (R := KeepCtx (accContractS env)) (c, f) ωH μH (sp - 80)
        v 1 ω[6].toNat h1' h5' h7' (.inr rfl) (by omega) hv6 mv hv32 n0 n6
        (fun a h1 h2 => by rw [rdH]; exact Memory.readable_of_writable (HF.st a (by omega) (by omega)))
      refine .inl ⟨free s2 kptr, ωI, μH, _, (run0.trans runH).trans runI, by rw [i1]; congr 1; omega,
        i6.trans UInt64.ofNat_toNat, by rw [i5]; simp [ctrVal, ctrDec_short [] (by simp)],
        HeapKeep.keepHi HF (fun a ha => frH a (by omega) (.inl (by omega))) wrH,
        fun d hd hu => ⟨(keep0 d hd hu).1, fun a ha => ?_⟩, fun a h0 ha hb => ?_, fun a ha => ?_, fun a ha => ?_,
        fun a ha => by rw [rdH, rdF0 a ha], fun w hw => by cases hw; simp⟩
      · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
        have ha' := ha; unfold InData at ha'
        rw [frH a (by omega) (.inl (by omega)), (keep0 d hd hu).2.2 a ha]
      · rw [frH a h0 (.inr (by omega)), frF a h0 ha hb]
      · have ha' := ha; unfold Glob at ha'; rw [frH a (by omega) (.inl (by omega)), glF0 a ha]
      · rw [frH a (by omega) (.inl (by omega)), loF0 a ha]
    | cons b bs =>
      simp only [GetOut] at gO
      obtain ⟨vptr, g8, g16, g24, gw, hnewV, hvp, hfreshV⟩ := gO
      have hVK : (⟨vptr - 32, ((b :: bs).length + 31) / 32 + 1, true⟩ : Chunk) ≠ ⟨kptr - 32, (kc + 31) / 32 + 1, true⟩ :=
        fun h => hfreshV _ hnewK rfl h.symm
      obtain ⟨hV1, hV2⟩ := keepF _ hnewV rfl hVK
      obtain ⟨nv1, nv2, nv3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in HD.wf hnewV rfl
      dsimp only at nv1 nv2 nv3
      have hb0D := HD.hb0
      have hbTD := HD.hbT
      generalize hL : (b :: bs).length = L at hV1 hV2 hVK g8 g24 gw nv1 nv2 nv3
      have hL0 : 0 < L := by rw [← hL]; simp
      have hdivV : L ≤ 32 * ((L + 31) / 32) := by omega
      have hwF : μF.readN vptr L = b :: bs := by
        refine Eq.trans (Memory.readN_congr fun j hj => hV2 _ ?_) gw
        simp only [InData]; omega
      have HFst := HF.st
      obtain ⟨ωH, μH, ok, v, nH, runH, h1', h5', h6', h7', hok, mv, hv32, hok0, hok1, mT, frH, rdH, wrH⟩ :=
        common L vptr L (by omega) (by omega) (by omega) (by omega)
          (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 8 = sp - 72 by omega]; exact g8)
          (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 16 = sp - 72 + 8 by omega]; exact g16)
          (by rw [kFv _ _ (by omega) (by omega), show sp - 80 + 24 = sp - 72 + 16 by omega]; exact g24)
          (fun h4 => ⟨by omega, fun a h1 h2 => Memory.readable_of_writable
            (HeapKeep.writableData HF hV1 rfl (by unfold HeapKeep.InData; dsimp only; omega))⟩)
      have HH : HeapCtxC env.code pb S0 S1 μH (free s2 kptr) :=
        HeapKeep.keepHi HF (fun a ha => frH a (by omega) (.inl (by omega))) wrH
      obtain ⟨ωJ, μJ, sv, runJ, j0, j1, j5, j6, j7, hsv, hsvm, mS, frJ, rdJ, wrJ⟩ :=
        cg_finD (P := P) (R := KeepCtx (accContractS env)) (c, f) ωH μH (sp - 80) v ok L vptr h1' h5' h7' hok
          (by omega) (by omega) (by omega) (by omega) mv hv32 mT (fun a h1 h2 => HH.st a (by omega) (by omega))
      have HJ : HeapCtxC env.code pb S0 S1 μJ (free s2 kptr) :=
        HeapKeep.keepHi HH (fun a ha => frJ a (by omega) (.inl (by omega))) wrJ
      obtain ⟨ωK, μK, runK, HK, -, pgK, roK, stkK, glK, keepK, k0, k1, k5, k6⟩ :=
        dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ωJ μJ
          (free s2 kptr) (sp - 80) vptr 1618 34735 _ HJ hV1 rfl (by dsimp only; omega) j0 j1 j7
          ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_808]) bs_34735
          (by omega) ⟨by omega, by omega⟩
      obtain ⟨n0, n6⟩ := m72' μH frH
      have kKH : ∀ o, sp - 80 + 48 ≤ o → o + 8 ≤ sp → μK.readN o 8 = μH.readN o 8 := fun o h1 h2 =>
        Memory.readN_congr fun j hj => (stkK _ (by omega) (by omega)).trans (frJ _ (by omega) (.inr (by omega)))
      have n0' := (kKH _ (by omega) (by omega)).trans n0
      have n6' := (kKH _ (by omega) (by omega)).trans n6
      obtain ⟨ωL, runL, l1, l6, l5⟩ := cg_finR (P := P) (R := KeepCtx (accContractS env)) (c, f) ωK μK (sp - 80)
        sv (if ok = 0 then 1 else 0) ω[6].toNat (k1.trans j1) (k6.trans j6) (by split <;> simp) (by omega) hsv hv6
        (by rw [← mS]; exact Memory.readN_congr fun j hj => stkK _ (by omega) (by omega)) n0' n6'
        (fun a h1 h2 => Memory.readable_of_writable (HK.st a (by omega) (by omega)))
      have hval : ωL[5].toNat % 4294967296 = ctrVal (some (b :: bs)) := by
        rw [l5]
        rcases hok with rfl | rfl
        · obtain ⟨h4, hdat⟩ := hok0 rfl
          simp only [if_true, ctrVal, Option.bind_some]
          rw [ctrDec_long _ (by rw [hL]; exact h4), Option.getD_some, UInt64.toNat_ofNat_of_lt' hsv, hsvm]
          have hv' : v = Num.decodeLE (μH.readN (sp - 80 + 8) 4) := by
            rw [mv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv32]
          rw [hv', hdat, ← readN_take μF vptr L 4 h4, hwF]
        · have h4 := hok1 rfl
          simp only [show ¬ (1 = 0) by decide, if_false, ctrVal, Option.bind_some]
          rw [ctrDec_short _ (by rw [hL]; exact h4)]; rfl
      refine .inl ⟨free (free s2 kptr) vptr, ωL, μK, _, (((run0.trans runH).trans runJ).trans runK).trans runL,
        by rw [l1]; congr 1; omega, l6.trans UInt64.ofNat_toNat, hval, HK, fun d hd hu => ?_, fun a h0 ha hb => ?_,
        fun a ha => ?_, fun a ha => ?_,
        fun a ha => by rw [show μK.readable a = μJ.readable a by unfold Memory.readable; rw [pgK], rdJ, rdH, rdF0 a ha],
        fun w hw => by cases hw; rw [hL]; omega⟩
      · obtain ⟨k0', k1', k2'⟩ := keep0 d hd hu
        obtain ⟨k3, k4⟩ := keepK d k0' hu (by rw [← hL]; exact hfreshV d k1' hu)
        refine ⟨k3, fun a ha => ?_⟩
        have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
        have ha' := ha; unfold InData at ha'
        rw [k4 a ha, frJ a (by omega) (.inl (by omega)), frH a (by omega) (.inl (by omega)), k2' a ha]
      · rw [stkK a h0 (by omega), frJ a h0 (.inr (by omega)), frH a h0 (.inr (by omega)), frF a h0 ha hb]
      · have ha' := ha; unfold Glob at ha'
        rw [glK a ha, frJ a (by omega) (.inl (by omega)), frH a (by omega) (.inl (by omega)), glF0 a ha]
      · rw [roK a (by unfold two32; omega) (HJ.ro a ha), frJ a (by omega) (.inl (by omega)),
          frH a (by omega) (.inl (by omega)), loF0 a ha]

end Services.Bootstrap.Acc.Handlers.RecentCounterGet
