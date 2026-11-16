import Services.Bootstrap.Acc.Handlers.RecentSlotTail
import Services.Bootstrap.Acc.Wrappers.GrowS

/-!
# The ring slot's typed `get` (34377), composed

`slot_get`: 34377 called with out (ω₇) and the tag-1 key value {1, c} at kp (ω₈), under
`accContractS` (KeepCtx: the context is kept). Either the run returns to the caller with `SlotOut`
of `(storage(keyEnc μ kp 1)).bind (decode slotDec)` at out (GP v0.8.0 Appendix B's Ω_R, then the
SDK's decode of `(H, u16)`), or it reaches one of the allocation-failure traps 34070 (the key
encoder's `alloc`) or 47977 (`get`'s `alloc`): heap exhaustion.
-/

namespace Services.Bootstrap.Acc.Handlers.RecentSlot

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`get`'s returns** (the `jumpInd` at 47927, 47957 or 48102) with ω₀ = 1600: on to 34417. -/
theorem sg_gret {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : X) (ω : Regs) (μ : Memory) (e : Nat) (he : e = 47927 ∨ e = 47957 ∨ e = 48102)
    (h0 : ω[0] = UInt64.ofNat 1600) :
    FreeStepsH p R e ω μ x 34417 ω μ x 1 := by
  rcases he with rfl | rfl | rfl
  all_goals
    rw [show ω = regsNF ω [] from rfl]
    pvm_go [h0]

theorem keyEnc_frame {μ μ' : Memory} {kp : Nat} (h : ∀ j, j < 4 → μ'.read (kp + 4 + j) = μ.read (kp + 4 + j)) :
    keyEnc μ' kp 1 = keyEnc μ kp 1 := by
  unfold keyEnc; simp only [if_true]; rw [Memory.readN_congr h]

open Services.Bootstrap.Decode.DeallocCall in
/-- **The ring slot's typed `get` (34377), one call**, under `accContractS` from the allocator's
    context for st: out in ω₇, the tag-1 key value {1, c} at kp (ω₈; the key `keyEnc μ kp 1` =
    1 ‖ the 4 octets at kp + 4), return address ret (ω₀, resolving to t), the caller's frame at
    SP (ω₁). Either the run returns to t with ω₀, ω₁, ω₅, ω₆ as they were and `SlotOut` at out of the
    slot's value, decoded (`slotDec`), the allocator's context for some st′ keeping st's allocated
    chunks and their data, memory kept from SP on off out … out + 36, at the globals (`Glob`) and below 196608, and the value (if any) shorter than 2³¹ octets; or it reaches the trap at
    34070 or 47977 (an `alloc` failed). Hypotheses: the key-size word kc for tag 1 at 68688
    (5 ≤ kc, kc + 31 < 2³⁶), readable; the frame [SP − 352, SP) in the stack; the slot's value
    shorter than 2⁶³ octets (`ValuesFit`). -/
theorem slot_get {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (st : State) (SP out kp kc ret t pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ st)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat SP) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat kp)
    (hsp : 2147483648 + 352 ≤ SP ∧ SP % 8 = 0) (hS0 : S0 + 352 ≤ SP)
    (hout : SP ≤ out ∧ out + 36 ≤ S1) (hkp : SP ≤ kp ∧ kp + 64 ≤ S1)
    (mt : μ.readN kp 2 = Num.encodeLE 2 1)
    (mc : μ.readN 68688 8 = Num.encodeLE 8 kc) (hkc : 5 ≤ kc ∧ kc + 31 < 68719476736)
    (hrt : ∀ a, 68688 ≤ a → a < 68696 → μ.readable a = true)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hfit : ∀ w, c.1.self.storage.get? (keyEnc μ kp 1) = some w → w.length < 9223372036854775808) :
    (∃ st' ω' μ' n, FreeStepsH p (KeepCtx (accContractS env)) 34377 ω μ (c, f) t ω' μ' (c, f) n ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      SlotOut μ' out ((c.1.self.storage.get? (keyEnc μ kp 1)).bind (decode slotDec)) ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → SP ≤ a → (a < out ∨ out + 36 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.read a = μ.read a) ∧
      (∀ w, c.1.self.storage.get? (keyEnc μ kp 1) = some w → w.length < 2 ^ 31)) ∨
    (∃ e ω' μ' n, (e = 34070 ∨ e = 47977) ∧
      FreeStepsH p (KeepCtx (accContractS env)) 34377 ω μ (c, f) e ω' μ' (c, f) n) := by
  have hSt := H.st
  have hS1' := H.hS1
  have hb0 := H.hb0
  have hbT := H.hbT
  obtain ⟨S, hSdef⟩ : ∃ S, SP = S + 112 := ⟨SP - 112, by omega⟩
  subst hSdef
  -- 34377 → 33843
  obtain ⟨ωA, μA, runA, a0, a1, a5, a7, a8, mA104, mA96, mA88, frA, rdA, wrA⟩ :=
    sg_pre (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ (S + 112) out h1 h7 (by omega)
      ⟨by omega, by omega⟩ (fun a h1 h2 => hSt a (by omega) (by omega))
  simp only [show S + 112 - 112 = S by omega, show S + 112 - 56 = S + 56 by omega,
    show S + 112 - 8 = S + 104 by omega, show S + 112 - 16 = S + 96 by omega,
    show S + 112 - 24 = S + 88 by omega] at a1 a7 mA104 mA96 mA88 frA
  have HA : HeapCtxC env.code pb S0 S1 μA st :=
    HeapKeep.keepHi H (fun a ha => frA a (by omega) (.inl (by omega))) wrA
  have mtA : μA.readN kp 2 = Num.encodeLE 2 1 := by
    rw [← mt]; exact Memory.readN_congr fun j hj => frA _ (by omega) (.inr (by omega))
  have mcA : μA.readN (68680 + 8 * 1) 8 = Num.encodeLE 8 kc := by
    rw [← mc]; exact Memory.readN_congr fun j hj => frA _ (by omega) (.inl (by omega))
  have hkA : keyEnc μA kp 1 = keyEnc μ kp 1 := keyEnc_frame fun j hj => frA _ (by omega) (.inr (by omega))
  have hkl : (keyEnc μ kp 1).length = 5 := by rw [keyEnc_length]; rfl
  -- the key encoder
  rcases kb_call (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ωA μA st S kp (S + 56) 1 kc
      1598 34400 pb S0 S1 HA a0 a1 a7 (a8.trans h8) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) mtA mcA
      (fun a h1 h2 => by rw [rdA]; exact hrt a (by omega) (by omega))
      ⟨by rw [hkA, hkl]; omega, hkc.2⟩ ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_798]) bs_34400 with
    ⟨kptr, s1, ωB, μB, nB, -, runB, HB, keepB, hnewK, hfreshK, oB0, oB8, oB16, oBk, hgB, stkB, b0, b1, b5, b6⟩ |
    ⟨-, ωB, μB, nB, runB⟩
  case inr =>
    obtain ⟨-, runBS⟩ := FreeStepsH.growS f runB
    exact .inr ⟨34070, ωB, μB, _, .inl rfl, runA.trans runBS⟩
  obtain ⟨-, roB⟩ := HeapHost.keepRO (env := accHeapHost env) HA.bd runB
  obtain ⟨-, runBS⟩ := FreeStepsH.growS f runB
  rw [hkA, hkl] at oB16 oBk
  have hS1B := HB.hS1
  obtain ⟨nk1, nk2, nk3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in HB.wf hnewK rfl
  dsimp only at nk1 nk2 nk3
  have hb0B := HB.hb0
  have hbTB := HB.hbT
  have hdivK : kc ≤ 32 * ((kc + 31) / 32) := by omega
  -- 34400 → 47857
  obtain ⟨ωC, runC, c0, c1, c5, c6, c7, c8, c9⟩ := sg_get (P := P) (R := KeepCtx (accContractS env)) (c, f)
    ωB μB S kptr 5 (b1.trans a1) (by omega) (by omega) (by decide)
    (by rw [show S + 64 = S + 56 + 8 by omega]; exact oB8) (by rw [show S + 72 = S + 56 + 16 by omega]; exact oB16)
    (fun a h1 h2 => Memory.readable_of_writable (HB.st a (by omega) (by omega)))
  -- `get`
  rcases get_call (P := P) (hb := 0) env cap pb hcap1 hcap c f ωC μB s1 S (S + 24) kptr 5 S0 S1
      (keyEnc μ kp 1) HB c1 c7 c8 c9 (by decide) (by omega) (by omega) ⟨by omega, by omega⟩
      (.inr ⟨_, hnewK, rfl, fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩⟩) (by omega)
      (by rw [← hkl]; exact oBk) hfit with
    ⟨e, s2, ωD, μD, nD, he, runD, d0, d1, d5, d6, gO, HD, keepD, dataD, stkD, glD, loD, rdD⟩ | ⟨ωD, μD, nD, runD⟩
  case inr =>
    exact .inr ⟨47977, ωD, μD, _, .inr rfl, (runA.trans runBS).trans (runC.trans runD)⟩
  have runD' := sg_gret (P := P) (R := KeepCtx (accContractS env)) (c, f) ωD μD e he (d0.trans c0)
  -- 34417 → 40613: the key's buffer freed
  have kD : ∀ o n, S + 48 ≤ o → o + n ≤ 4294967296 → μD.readN o n = μB.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => stkD _ (by omega) (by omega) (.inr (by omega))
  obtain ⟨ωE, runE, e0, e1, e5, e6, e7⟩ := sg_dl (P := P) (R := KeepCtx (accContractS env)) (c, f) ωD μD S kc
    d1 (by omega) (by omega) (by omega) (by rw [kD _ _ (by omega) (by omega)]; exact oB0)
    (fun a h1 h2 => Memory.readable_of_writable (HD.st a (by omega) (by omega)))
  have hKD := keepD _ hnewK rfl
  obtain ⟨ωF, μF, runF, HF, -, -, roF, stkF, glF, keepF, f0, f1, f5, f6⟩ :=
    dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ωE μD s2 S kptr
      1602 34434 _ HD hKD rfl (by dsimp only; omega) e0 e1 (e7.trans (d6.trans c6)) ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_800]) bs_34434 (by omega) ⟨by omega, by omega⟩
  have run0 := (((((runA.trans runBS).trans runC).trans runD).trans runD').trans runE).trans runF
  -- the frame words, kept since sg_pre
  have kF : ∀ o n, S + 88 ≤ o → o + n ≤ S + 112 → μF.readN o n = μA.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => by
      rw [stkF _ (by omega) (by omega), stkD _ (by omega) (by omega) (.inr (by omega)),
        stkB _ (by omega) (by omega) (.inr (by omega))]
  have m104 := (kF _ _ (by omega) (by omega)).trans mA104
  have m96 := (kF _ _ (by omega) (by omega)).trans mA96
  have m88 := (kF _ _ (by omega) (by omega)).trans mA88
  have kFv : ∀ o n, S + 24 ≤ o → o + n ≤ S + 48 → μF.readN o n = μD.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => stkF _ (by omega) (by omega)
  have eF1 : ωF[1] = UInt64.ofNat S := f1.trans (e1)
  have eF5 : ωF[5] = UInt64.ofNat out := f5.trans (e5.trans (d5.trans (c5.trans (b5.trans a5))))
  have hr0 : ω[0].toNat < 18446744073709551616 := UInt64.toNat_lt _
  have hv5 : ω[5].toNat < 18446744073709551616 := UInt64.toNat_lt _
  have hv6 : ω[6].toNat < 18446744073709551616 := UInt64.toNat_lt _
  have eret : ω[0].toNat = ret := by rw [h0]; exact UInt64.toNat_ofNat_of_lt' (show ret < 18446744073709551616 by omega)
  -- the memory frame of the steps so far, for the final claims
  have frF : ∀ a, a < 4294967296 → S + 112 ≤ a → μF.read a = μ.read a := fun a h0 ha => by
    rw [stkF a h0 (by omega), stkD a h0 (by omega) (.inr (by omega)), stkB a h0 (by omega) (.inr (by omega)),
      frA a h0 (.inr ha)]
  -- the globals and the read-only data, up to μF
  have glF0 : ∀ a, Glob a → μF.read a = μ.read a := fun a ha => by
    have ha' := ha; unfold Glob at ha'
    rw [glF a ha, glD a ha, hgB a ⟨.inl ha, by omega, fun b ⟨d, hd, hdb⟩ => .inl (by
        have ht := HB.wf.2.2.2.1; unfold TilesOk at ht; have := (ht.mem_lt _ hd).1; omega)⟩ (.inl (by omega)),
      frA a (by omega) (.inl (by omega))]
  have loF0 : ∀ a, a < 196608 → μF.read a = μ.read a := fun a ha => by
    rw [roF a (by unfold two32; omega) (HD.ro a ha), loD a ha,
      roB a (by unfold two32; omega) (.inl (by unfold pageSize; omega)) (by rw [wrA]; exact H.ro a ha),
      frA a (by omega) (.inl (by omega))]
  -- st's chunks: kept, and their data, up to μF
  have keep0 : ∀ d ∈ chunks st, d.used = true → d ∈ chunks (free s2 kptr) ∧ d ∈ chunks s1 ∧
      ∀ a, InData d a → μF.read a = μ.read a := by
    intro d hd hu
    have hd1 := keepB d hd hu
    obtain ⟨k1, k2⟩ := keepF d (keepD d hd1 hu) hu (hfreshK d hd hu)
    refine ⟨k1, hd1, fun a ha => ?_⟩
    have hap := InData.apart HB.wf hd1 hnewK (Ne.symm (hfreshK d hd hu)) ha
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
    have hoff := Services.Bootstrap.Alloc.off_hdr_data HB.wf HB.hb0 HB.hbT hd1 ha.1 ha.2
    unfold InData at ha hap
    dsimp only at hap
    rw [k2 a ⟨ha.1, ha.2⟩, dataD d hd1 hu a ⟨ha.1, ha.2⟩,
      hgB a ⟨.inr hoff.1, hoff.2.1, hoff.2.2⟩ (by omega), frA a (by omega) (.inl (by omega))]
  -- 34434 on, by `get`'s value
  cases hv : c.1.self.storage.get? (keyEnc μ kp 1) with
  | none =>
    rw [hv] at gO
    unfold GetOut at gO
    obtain ⟨ωG, runG, g0, g1, g5, g6⟩ := sg_none (P := P) (R := KeepCtx (accContractS env)) (c, f) ωF μF S out
      ω[0].toNat ω[5].toNat ω[6].toNat t eF1 eF5 ⟨by omega, by omega⟩ (by omega) (.inr (by omega))
      (by rw [kFv _ _ (by omega) (by omega)]; exact gO) m104 m96 m88 hr0 hv5 hv6 (by rw [eret]; exact hret)
      (by rw [eret]; exact hjt) hbt (fun a h1 h2 => Memory.readable_of_writable (HF.st a (by omega) (by omega)))
      (fun a h1 h2 => HF.st a (by omega) (by omega))
    have l2 : (Num.encodeLE 2 0).length = 2 := Num.length_encodeLE ..
    have frG : ∀ a, a < 4294967296 → (a < out ∨ out + 2 ≤ a) → (μF.writeN out (Num.encodeLE 2 0)).read a = μF.read a :=
      fun a h0 ha => rd_wr _ _ _ _ 2 l2 (by omega) (by omega) h0
    refine .inl ⟨free s2 kptr, ωG, _, _, run0.trans runG, g0.trans UInt64.ofNat_toNat, g1.trans h1.symm,
      g5.trans UInt64.ofNat_toNat, g6.trans UInt64.ofNat_toNat, ?_,
      HeapKeep.keepHi HF (fun a ha => frG a (by omega) (.inl (by omega))) (fun a => Memory.writable_writeN _ _ _ _),
      fun d hd hu => ⟨(keep0 d hd hu).1, fun a ha => ?_⟩, fun a h0 ha hb => ?_,
      fun a ha => ?_, fun a ha => ?_, fun w hw => by simp at hw⟩
    rotate_left 3
    · have ha' := ha; unfold Glob at ha'; rw [frG a (by omega) (.inl (by omega)), glF0 a ha]
    · rw [frG a (by omega) (.inl (by omega)), loF0 a ha]
    · unfold SlotOut; exact Memory.readN_writeN_same _ _ _ _ l2 (by unfold two32; omega)
    · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
      unfold InData at ha
      rw [frG a (by omega) (.inl (by omega)), (keep0 d hd hu).2.2 a ha]
    · rw [frG a h0 (by omega), frF a h0 ha]
  | some w =>
    rw [hv] at gO
    cases w with
    | nil =>
      unfold GetOut at gO
      obtain ⟨g24, g32, g40⟩ := gO
      obtain ⟨ωG, μG, nG, runG, g0, g1, g5, g6, slG, frG, wrG⟩ := sg_tailE (P := P)
        (R := KeepCtx (accContractS env)) (c, f) ωF μF S out ω[0].toNat ω[5].toNat ω[6].toNat t eF1 eF5
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by rw [kFv _ _ (by omega) (by omega)]; exact g24)
        (by rw [kFv _ _ (by omega) (by omega), show S + 32 = S + 24 + 8 by omega]; exact g32)
        (by rw [kFv _ _ (by omega) (by omega), show S + 40 = S + 24 + 16 by omega]; exact g40)
        m104 m96 m88 hr0 hv5 hv6 (by rw [eret]; exact hret) (by rw [eret]; exact hjt) hbt
        (fun a h1 h2 => HF.st a (by omega) (by omega)) (fun a h1 h2 => HF.st a (by omega) (by omega))
      refine .inl ⟨free s2 kptr, ωG, μG, _, run0.trans runG, g0.trans UInt64.ofNat_toNat, g1.trans h1.symm,
        g5.trans UInt64.ofNat_toNat, g6.trans UInt64.ofNat_toNat, slG,
        HeapKeep.keepHi HF (fun a ha => frG a (by omega) (.inl (by omega)) (.inl (by omega))) wrG,
        fun d hd hu => ⟨(keep0 d hd hu).1, fun a ha => ?_⟩, fun a h0 ha hb => ?_,
        fun a ha => ?_, fun a ha => ?_, fun w hw => by cases hw; simp⟩
      rotate_left 2
      · have ha' := ha; unfold Glob at ha'
        rw [frG a (by omega) (.inl (by omega)) (.inl (by omega)), glF0 a ha]
      · rw [frG a (by omega) (.inl (by omega)) (.inl (by omega)), loF0 a ha]
      · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
        unfold InData at ha
        rw [frG a (by omega) (.inl (by omega)) (.inl (by omega)), (keep0 d hd hu).2.2 a ha]
      · rw [frG a h0 (.inr (by omega)) (by omega), frF a h0 ha]
    | cons b bs =>
      unfold GetOut at gO
      obtain ⟨vptr, g24, g32, g40, gw, hnewV, hvp, hfreshV⟩ := gO
      have hVK : (⟨vptr - 32, ((b :: bs).length + 31) / 32 + 1, true⟩ : Chunk) ≠ ⟨kptr - 32, (kc + 31) / 32 + 1, true⟩ :=
        fun h => hfreshV _ hnewK rfl h.symm
      obtain ⟨hV1, hV2⟩ := keepF _ hnewV rfl hVK
      have hwF : μF.readN vptr (b :: bs).length = b :: bs := by
        refine Eq.trans (Memory.readN_congr fun j hj => hV2 _ ?_) gw
        have hdivV : bs.length + 1 ≤ 32 * ((bs.length + 1 + 31) / 32) := by omega
        simp only [InData, List.length_cons] at hj ⊢
        omega
      obtain ⟨ωG, μG, nG, runG, g0, g1, g5, g6, slG, HG, frG, glG, loG, keepG⟩ := sg_tailW (P := P)
        (R := KeepCtx (accContractS env)) env.code pb S0 S1 (c, f) ωF μF (free s2 kptr) S out vptr ω[0].toNat
        ω[5].toNat ω[6].toNat t (b :: bs) HF hV1 hvp (List.cons_ne_nil b bs) eF1 eF5 ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by rw [kFv _ _ (by omega) (by omega)]; exact g24)
        (by rw [kFv _ _ (by omega) (by omega), show S + 32 = S + 24 + 8 by omega]; exact g32)
        (by rw [kFv _ _ (by omega) (by omega), show S + 40 = S + 24 + 16 by omega]; exact g40) hwF
        m104 m96 m88 hr0 hv5 hv6 (by rw [eret]; exact hret) (by rw [eret]; exact hjt) hbt
      refine .inl ⟨free (free s2 kptr) vptr, ωG, μG, _, run0.trans runG, g0.trans UInt64.ofNat_toNat,
        g1.trans h1.symm, g5.trans UInt64.ofNat_toNat, g6.trans UInt64.ofNat_toNat, slG, HG,
        fun d hd hu => ?_, fun a h0 ha hb => ?_, fun a ha => by rw [glG a ha, glF0 a ha],
        fun a ha => by rw [loG a ha, loF0 a ha], fun w' hw' => ?_⟩
      rotate_left 2
      · cases hw'
        have := Services.Bootstrap.Decode.VecU8.chunk_in HD.wf hnewV rfl
        dsimp only at this
        omega
      · obtain ⟨k0, k1, k2⟩ := keep0 d hd hu
        obtain ⟨k3, k4⟩ := keepG d k0 hu (hfreshV d k1 hu)
        exact ⟨k3, fun a ha => by rw [k4 a ha, k2 a ha]⟩
      · rw [frG a h0 ha hb, frF a h0 ha]

end Services.Bootstrap.Acc.Handlers.RecentSlot
