import Services.Bootstrap.Acc.Transfer.W2a

/-!
# `on_transfer`'s log line, composed (7454 → 7763), frame-only

- `lg_part1`, 7454 → 7631: `lg_ok` / `lg_err`, `alloc(3, 1)` (null: the trap at 15362), `lg_pick_ok` /
  `lg_pick_err` and `dealloc_callG` of the block not shown. The shown `String` (cap ≠ 0, q, len) is at
  sp + 512, its buffer a live chunk.
- `lg_part2`, 7631 → 7763: `lg_fmt_pre`, `LogFmt` (a named hypothesis; its allocation failure is
  `ExhaustsP`), `lg_sfree` and `dealloc_callG` of the shown buffer, `lg_log_a`, `log` (`logS`), and
  `lg_log_b` with `dealloc_callG` of the message, or `lg_log_b0` (capacity 0).
- `tr_w2b`: both.

The message's text is not stated (logging is frame-only, Adam's decision).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Two distinct chunks of a well-formed state: d's data lies outside c's. -/
theorem apartA {s : State} (hwf : WF s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s)
    (hne : d ≠ c) {a : Nat} (ha : InDataA d a) : a < c.addr + 32 ∨ c.addr + 32 * c.size ≤ a := by
  have h := Services.Bootstrap.Decode.LoopA.InData.apart hwf hd hc (Ne.symm hne) ha
  unfold Services.Bootstrap.Decode.LoopA.InData at h
  omega

theorem setR7_ne (ω : Regs) (r : Nat) (j : Nat) (hj : j < 13) (h : j ≠ 7) : (setR7 ω r)[j] = ω[j] := by
  unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]

/-- The scratch words the log line writes from sp up. -/
def LgW (sp a : Nat) : Prop :=
  (sp + 240 ≤ a ∧ a < sp + 256) ∨ (sp + 512 ≤ a ∧ a < sp + 536) ∨ (sp + 744 ≤ a ∧ a < sp + 768) ∨
  (sp + 1568 ≤ a ∧ a < sp + 1616)

/-- **7454 → 7631**: the shown `String` { cap ≠ 0, q, len } at sp + 512, its len octets the data of a
    live chunk chq (the memo's block ch for `Ok`, a fresh 3-octet block for `Err`), the other block
    freed; every allocated chunk of s₀ but ch kept, apart from chq, with its data; from sp up only
    the log line's scratch words changed. Or `alloc` returned null (15362). -/
theorem lg_part1 (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {Ab : St Stream → Prop} {S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp ptr : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s₀) (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat ptr)
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1)
    (hp : 65536 ≤ ptr ∧ ptr + 128 ≤ 2147483648)
    (hch : (⟨ptr - 32, (128 + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s₀)
    (tag : (rdN μ (sp + 744) 8 = 0 ∧ rdN μ (sp + 752) 8 = ptr ∧ rdN μ (sp + 760) 8 = 128) ∨
      rdN μ (sp + 744) 8 = 1) :
    (∃ s' ω' μ' N (chq : Chunk) cp q len, FreeStepsH p (KeepCtx (accContractS env)) 7454 ω μ (c, f) 7631 ω' μ' (c, f) N ∧
      ω'[1] = UInt64.ofNat sp ∧ HeapCtxC env.code pb S0 S1 μ' s' ∧
      chq ∈ chunks s' ∧ chq.used = true ∧ chq.addr + 32 = q ∧
      rdN μ' (sp + 512) 8 = cp ∧ cp ≠ 0 ∧ rdN μ' (sp + 520) 8 = q ∧ rdN μ' (sp + 528) 8 = len ∧
      (∀ a, q ≤ a → a < q + len → InDataA chq a) ∧
      (∀ d ∈ chunks s₀, d.used = true → d ≠ ⟨ptr - 32, (128 + 31) / 32 + 1, true⟩ →
        d ≠ chq ∧ d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → ¬ LgW sp a → μ'.read a = μ.read a)) ∨
    Aborts p (KeepCtx (accContractS env)) Ab ⟨7454, ω, μ, c, f⟩ c := by
  have hst := H.st
  have hS1 := H.hS1
  have hwS : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hb00 := H.hb0
  obtain ⟨Nc1, Nc2, Nc3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hch rfl
  dsimp only at Nc1 Nc2 Nc3
  -- the common tail: alloc(3), then the pick, from a state at 40494
  rcases tag with ⟨t0, t1, t2⟩ | t0
  · -- `Ok`: the memo's block is shown, the 3-octet block freed
    obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a5, a6, r248, r240, r1576, r1584, r1592, fr1, rd1, wr1⟩ :=
      lg_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp ptr h1 h6 (by omega)
        ⟨by omega, by omega⟩ hwS t0
    have H1 : HeapCtxC env.code pb S0 S1 μ1 s₀ :=
      HeapCtxC.keep_hi H (fun a ha => fr1 a (by omega) (.inl (by omega)) (.inl (by omega))) wr1
    rcases alloc_callG (p := p) (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ω1 μ1 s₀ sp 3 1 pb S0 S1 H1
        a1 a7 a8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
      ⟨p3, s2, ω2, μ2, -, run2, H2, keep2, hnew, hfresh, hkg, e7, stk2, f0, f1, f5, f6⟩ |
      ⟨-, ω2, μ2, run2, e7, stk2, f0, f1, f5, f6⟩
    rotate_left
    · obtain ⟨-, run2S⟩ := FreeStepsH.growS f run2
      obtain ⟨ω3, run3⟩ := lg_null (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 e7
      exact .inr (aborts_of_trap (P := P) (fun s h => hAb s (.inl h)) ⟨7454, ω, μ, c, f⟩
        (.inr (.inr (.inr (.inl rfl))))
        ((run1.trans (run2S.trans (lg_j258 (p := p) (P := P) _ ω2 μ2 (f0.trans a0)))).trans run3))
    obtain ⟨-, run2S⟩ := FreeStepsH.growS f run2
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0 := H2.hb0
    have hbT := H2.hbT
    have hst2 := H2.st
    have k21 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → rdN μ2 o n = rdN μ1 o n := fun o n h1 h2 =>
      rdN_frame fun j hj => stk2 _ (by omega) (by omega)
    obtain ⟨ω3, μ3, run3, g0, g1, g7, g8, r512, r520, r528, r744, r752, r760, fr3, rd3, wr3⟩ :=
      lg_pick_ok (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 sp p3 128 ptr 128 (f1.trans a1) e7
        (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (fun a h1 h2 => hst2 a (by omega) (by omega))
        (fun a h1 h2 => heapC_writable_data H2 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)
        (by rw [k21 _ _ (by omega) (by omega)]; exact r248) (by rw [k21 _ _ (by omega) (by omega)]; exact r240)
        (by rw [k21 _ _ (by omega) (by omega)]; exact r1576) (by rw [k21 _ _ (by omega) (by omega)]; exact r1584)
        (by rw [k21 _ _ (by omega) (by omega)]; exact r1592)
    have H3 : HeapCtxC env.code pb S0 S1 μ3 s2 :=
      HeapCtxC.keep_data H2 hnew (fun a ha hc => fr3 a (by omega) (by dsimp only at hc; omega) (.inl (by omega))
        (.inl (by omega))) wr3
    obtain ⟨ω4, μ4, run4, H4, -, -, -, stk4, -, oth4, e0, e1, -, -⟩ :=
      dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ω3 μ3 s2 sp p3
        260 7631 _ H3 hnew rfl (by dsimp only; omega) g0 g1 g7 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_129]) bs_7631 (by omega) ⟨by omega, by omega⟩
    have hchs2 := keep2 _ hch rfl
    have hne3 : (⟨ptr - 32, (128 + 31) / 32 + 1, true⟩ : Chunk) ≠ ⟨p3 - 32, (3 + 31) / 32 + 1, true⟩ :=
      hfresh _ hch rfl
    have k43 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → rdN μ4 o n = rdN μ3 o n := fun o n h1 h2 =>
      rdN_frame fun j hj => stk4 _ (by omega) (by omega)
    refine .inl ⟨free s2 p3, ω4, μ4, _, ⟨ptr - 32, (128 + 31) / 32 + 1, true⟩, 128, ptr, 128,
      ((run1.trans (run2S.trans (lg_j258 (p := p) (P := P) _ ω2 μ2 (f0.trans a0)))).trans run3).trans run4,
      e1.trans g1, H4, (oth4 _ hchs2 rfl hne3).1, rfl, by dsimp only; omega,
      by rw [k43 _ _ (by omega) (by omega)]; exact r512, by decide,
      by rw [k43 _ _ (by omega) (by omega)]; exact r520, by rw [k43 _ _ (by omega) (by omega)]; exact r528,
      fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩, fun d hd hu hne => ?_, fun a h0 ha hW => ?_⟩
    · have hd2 := keep2 d hd hu
      have hne' := hfresh d hd hu
      refine ⟨hne, (oth4 d hd2 hu hne').1, fun a ha => ?_⟩
      have hap := apartA H2.wf hnew hd2 hne' ha
      dsimp only at hap
      have hlt := heapC_data_lt H hd ha
      rw [(oth4 d hd2 hu hne').2 a ha, fr3 a (by omega) (by omega) (.inl (by omega)) (.inl (by omega)),
        HKeepG.data H2.wf H2.hb0 H2.hbT hkg hd2 ha, fr1 a (by omega) (.inl (by omega)) (.inl (by omega))]
    · unfold LgW at hW
      rw [stk4 a h0 ha, fr3 a h0 (.inr (by omega)) (by omega) (by omega), stk2 a h0 ha,
        fr1 a h0 (by omega) (by omega)]
  · -- `Err`: a 3-octet `String` is shown, the memo's block freed
    obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a5, r248, r240, fr1, rd1, wr1⟩ :=
      lg_err (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp ptr h1 h6 (by omega)
        ⟨by omega, by omega⟩ hwS t0
    have H1 : HeapCtxC env.code pb S0 S1 μ1 s₀ :=
      HeapCtxC.keep_hi H (fun a ha => fr1 a (by omega) (.inl (by omega)) (.inl (by omega))) wr1
    rcases alloc_callG (p := p) (P := P) (hb := 0) (accHeapHost env) cap hcap1 hcap c ω1 μ1 s₀ sp 3 1 pb S0 S1 H1
        a1 a7 a8 (by decide) (by decide) (by decide) (by omega) ⟨by omega, by omega⟩ with
      ⟨p3, s2, ω2, μ2, -, run2, H2, keep2, hnew, hfresh, hkg, e7, stk2, f0, f1, f5, f6⟩ |
      ⟨-, ω2, μ2, run2, e7, stk2, f0, f1, f5, f6⟩
    rotate_left
    · obtain ⟨-, run2S⟩ := FreeStepsH.growS f run2
      obtain ⟨ω3, run3⟩ := lg_null (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 e7
      exact .inr (aborts_of_trap (P := P) (fun s h => hAb s (.inl h)) ⟨7454, ω, μ, c, f⟩
        (.inr (.inr (.inr (.inl rfl))))
        ((run1.trans (run2S.trans (lg_j258 (p := p) (P := P) _ ω2 μ2 (f0.trans a0)))).trans run3))
    obtain ⟨-, run2S⟩ := FreeStepsH.growS f run2
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0 := H2.hb0
    have hbT := H2.hbT
    have hst2 := H2.st
    have k21 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → rdN μ2 o n = rdN μ1 o n := fun o n h1 h2 =>
      rdN_frame fun j hj => stk2 _ (by omega) (by omega)
    obtain ⟨ω3, μ3, run3, g0, g1, g7, g8, r512, r520, r528, r744, r752, r760, fr3, rd3, wr3⟩ :=
      lg_pick_err (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 sp p3 ptr (f1.trans a1) e7
        (f5.trans a5) (by omega) ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩
        (fun a h1 h2 => hst2 a (by omega) (by omega))
        (fun a h1 h2 => heapC_writable_data H2 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩)
        (by rw [k21 _ _ (by omega) (by omega)]; exact r248) (by rw [k21 _ _ (by omega) (by omega)]; exact r240)
    have H3 : HeapCtxC env.code pb S0 S1 μ3 s2 :=
      HeapCtxC.keep_data H2 hnew (fun a ha hc => fr3 a (by omega) (by dsimp only at hc; omega) (.inl (by omega))
        (.inl (by omega))) wr3
    have hchs2 := keep2 _ hch rfl
    have hne3 : (⟨ptr - 32, (128 + 31) / 32 + 1, true⟩ : Chunk) ≠ ⟨p3 - 32, (3 + 31) / 32 + 1, true⟩ :=
      hfresh _ hch rfl
    obtain ⟨ω4, μ4, run4, H4, -, -, -, stk4, -, oth4, e0, e1, -, -⟩ :=
      dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ω3 μ3 s2 sp ptr
        260 7631 _ H3 hchs2 rfl (by dsimp only; omega) g0 g1 g7 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_129]) bs_7631 (by omega) ⟨by omega, by omega⟩
    have k43 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → rdN μ4 o n = rdN μ3 o n := fun o n h1 h2 =>
      rdN_frame fun j hj => stk4 _ (by omega) (by omega)
    refine .inl ⟨free s2 ptr, ω4, μ4, _, ⟨p3 - 32, (3 + 31) / 32 + 1, true⟩, 3, p3, 3,
      ((run1.trans (run2S.trans (lg_j258 (p := p) (P := P) _ ω2 μ2 (f0.trans a0)))).trans run3).trans run4,
      e1.trans g1, H4, (oth4 _ hnew rfl (Ne.symm hne3)).1, rfl, by dsimp only; omega,
      by rw [k43 _ _ (by omega) (by omega)]; exact r512, by decide,
      by rw [k43 _ _ (by omega) (by omega)]; exact r520, by rw [k43 _ _ (by omega) (by omega)]; exact r528,
      fun a h1 h2 => ⟨by dsimp only; omega, by dsimp only; omega⟩, fun d hd hu hne => ?_, fun a h0 ha hW => ?_⟩
    · have hd2 := keep2 d hd hu
      have hne' := hfresh d hd hu
      refine ⟨hne', (oth4 d hd2 hu hne).1, fun a ha => ?_⟩
      have hap := apartA H2.wf hnew hd2 hne' ha
      dsimp only at hap
      have hlt := heapC_data_lt H hd ha
      rw [(oth4 d hd2 hu hne).2 a ha, fr3 a (by omega) (by omega) (.inl (by omega)) (.inl (by omega)),
        HKeepG.data H2.wf H2.hb0 H2.hbT hkg hd2 ha, fr1 a (by omega) (.inl (by omega)) (.inl (by omega))]
    · unfold LgW at hW
      rw [stk4 a h0 ha, fr3 a h0 (.inr (by omega)) (by omega) (by omega), stk2 a h0 ha,
        fr1 a h0 (by omega) (by omega)]

/-- **7631 → 7763**: the log line formatted (`LogFmt`), the shown buffer and the message freed, `log`
    called. Every allocated chunk of s₀ but chq kept, with its data; from sp up only sp + 744 … sp + 768
    and sp + 1568 … sp + 1616 changed. Or a formatting allocation failed (`ExhaustsP`). -/
theorem lg_part2 (env : AccEnv) {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    {Ab : St Stream → Prop} {pb S0 S1 : Nat}
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s) (hL : LogFmt p env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat) (chq : Chunk) (cp q len : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s₀) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483800 + 128 + 64 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 4096 ≤ sp ∧ sp + 1856 ≤ S1)
    (hq : chq ∈ chunks s₀) (hqu : chq.used = true) (hqa : chq.addr + 32 = q)
    (m512 : rdN μ (sp + 512) 8 = cp) (hcp : cp ≠ 0) (m520 : rdN μ (sp + 520) 8 = q)
    (m528 : rdN μ (sp + 528) 8 = len) (hql : ∀ a, q ≤ a → a < q + len → InDataA chq a)
    (m208 : rdN μ (sp + 208) 8 = 2800) (m136 : rdN μ (sp + 136) 8 = 2804) (m200 : rdN μ (sp + 200) 8 = 678) :
    (∃ s' ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 7631 ω μ (c, f) 7763 ω' μ' (c, f) N ∧
      ω'[1] = UInt64.ofNat sp ∧ HeapCtxC env.code pb S0 S1 μ' s' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ≠ chq → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 744 ∨ sp + 768 ≤ a) → (a < sp + 1568 ∨ sp + 1616 ≤ a) →
        μ'.read a = μ.read a)) ∨
    Aborts p (KeepCtx (accContractS env)) Ab ⟨7631, ω, μ, c, f⟩ c := by
  have hst := H.st
  have hS1 := H.hS1
  have hwS : ∀ a, sp ≤ a → a < sp + 1856 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  obtain ⟨Nq1, Nq2, Nq3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hq hqu
  -- 7631 → 59375
  obtain ⟨ω1, μ1, run1, a0, a1, a7, a8, a9, a5, a6, r1568, r1576, r1584, r1592, r1600, r1608, fr1, rd1, wr1⟩ :=
    lg_fmt_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 ⟨by omega, by omega⟩ hwS
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s₀ :=
    HeapCtxC.keep_hi H (fun a ha => fr1 a (by omega) (.inl (by omega))) wr1
  have k10 : ∀ o n, o + n ≤ sp + 1568 → rdN μ1 o n = rdN μ o n := fun o n h =>
    rdN_frame fun j hj => fr1 _ (by omega) (.inl (by omega))
  rcases hL c f ω1 μ1 s₀ sp H1 a0 a1 a7 a8 a9 (by omega) (by omega) (by omega) r1568 (r1576.trans m208) r1584
      (r1592.trans m136) r1600 (r1608.trans m200)
      (fun a h1 h2 => by
        rw [k10 _ _ (by omega), m520] at h1
        rw [k10 _ _ (by omega), m520, k10 _ _ (by omega), m528] at h2
        rw [rd1]; exact Memory.readable_of_writable (heapC_writable_data H hq hqu (hql a h1 h2))) with
    ⟨s2, ω2, μ2, N2, kc, kp, run2, H2, k1, k5, k6, mkc, mkp, hkc, keep2, fr2⟩ | hx
  rotate_left
  · exact .inr (Aborts.prepend ⟨16, run1⟩ (aborts_of_exhaustsP hAb ⟨59375, ω1, μ1, c, f⟩ hx))
  have hst2 := H2.st
  have k20 : ∀ o n, sp ≤ o → o + n ≤ sp + 744 → rdN μ2 o n = rdN μ o n := fun o n h1 h2 =>
    (rdN_frame fun j hj => fr2 _ (by omega) (by omega) (.inl (by omega))).trans (k10 _ _ (by omega))
  have hq2 := (keep2 chq hq hqu).1
  -- 7699 → 40613 → 7720: the shown buffer freed
  obtain ⟨ω3, run3, b0, b1, b7, b8, -, -⟩ := lg_sfree (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f)
    ω2 μ2 sp cp q (k1.trans a1) ⟨by omega, by omega⟩
    (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
    (by rw [k20 _ _ (by omega) (by omega)]; exact m512) hcp (by rw [k20 _ _ (by omega) (by omega)]; exact m520)
  obtain ⟨ω4, μ4, run4, H4, -, -, -, stk4, -, oth4, e0, e1, -, -⟩ :=
    dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ω3 μ2 s2 sp q
      264 7720 chq H2 hq2 hqu hqa b0 b1 b7 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_131]) bs_7720 (by omega) ⟨by omega, by omega⟩
  have hst4 := H4.st
  have hrf4 : ∀ a, sp ≤ a → a < sp + 1856 → μ4.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst4 a (by omega) (by omega))
  -- 7720 → 7741, log, 7743
  obtain ⟨ω5, run5, c1, c5, -⟩ := lg_log_a (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 sp
    (e1.trans b1) ⟨by omega, by omega⟩ hrf4
  have k42 : ∀ o n, sp ≤ o → o + n ≤ 4294967296 → rdN μ4 o n = rdN μ2 o n := fun o n h1 h2 =>
    rdN_frame fun j hj => stk4 _ (by omega) (by omega)
  have w1 : (setR7 ω5 Result.WHAT)[1] = UInt64.ofNat sp := (setR7_ne ω5 _ 1 (by decide) (by decide)).trans c1
  have w5 : (setR7 ω5 Result.WHAT)[5] = UInt64.ofNat kp := by
    rw [setR7_ne ω5 _ 5 (by decide) (by decide), c5, k42 _ _ (by omega) (by omega), mkp]
  have mkc4 : rdN μ4 (sp + 744) 8 = kc := by rw [k42 _ _ (by omega) (by omega), mkc]
  -- the run so far, and the rest from 7743
  have runA := (run1.trans run2).trans (run3.trans (run4.trans run5))
  have keepA : ∀ d ∈ chunks s₀, d.used = true → d ≠ chq →
      d ∈ chunks (free s2 q) ∧ ∀ a, InDataA d a → μ4.read a = μ.read a := fun d hd hu hne => by
    have hd2 := (keep2 d hd hu).1
    refine ⟨(oth4 d hd2 hu hne).1, fun a ha => ?_⟩
    have hlt := heapC_data_lt H hd ha
    rw [(oth4 d hd2 hu hne).2 a ha, (keep2 d hd hu).2 a ha, fr1 a (by omega) (.inl (by omega))]
  have frA : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 744 ∨ sp + 768 ≤ a) → (a < sp + 1568 ∨ sp + 1616 ≤ a) →
      μ4.read a = μ.read a := fun a h0 ha hb hc => by
    rw [stk4 a h0 ha, fr2 a h0 ha hb, fr1 a h0 hc]
  by_cases hk0 : kc = 0
  · obtain ⟨ω6, run6, j6⟩ := lg_log_b0 (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f)
      (setR7 ω5 Result.WHAT) μ4 sp w1 ⟨by omega, by omega⟩ hrf4 (by rw [mkc4, hk0])
    have runL := FreeStepsH.logS env (d_7741 (p := p) (P := P)) run6
    exact .inl ⟨free s2 q, ω6, μ4, _, runA.trans runL, (j6 1 (by decide)).trans w1, H4, keepA, frA⟩
  · rcases hkc with h | ⟨chk, hck, hcku, hcka, hckf⟩
    · exact absurd h hk0
    have hkq : chq ≠ chk := hckf chq hq hqu
    have hk4 : chk ∈ chunks (free s2 q) := (oth4 chk hck hcku (Ne.symm hkq)).1
    obtain ⟨ω6, run6, d0, d1, d7, d8, -⟩ := lg_log_b (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f)
      (setR7 ω5 Result.WHAT) μ4 sp kc kp w1 w5 (by rw [← mkp]; exact rdN_lt64 _ _) ⟨by omega, by omega⟩ hrf4
      mkc4 hk0
    obtain ⟨ω7, μ7, run7, H7, -, -, -, stk7, -, oth7, -, g1, -, -⟩ :=
      dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (c, f) ω6 μ4 (free s2 q)
        sp kp 266 7763 chk H4 hk4 hcku hcka d0 d1 d7 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_132]) bs_7763 (by omega) ⟨by omega, by omega⟩
    have runL := FreeStepsH.logS env (d_7741 (p := p) (P := P)) (run6.trans run7)
    refine .inl ⟨free (free s2 q) kp, ω7, μ7, _, runA.trans runL, g1.trans (d1.trans w1), H7,
      fun d hd hu hne => ?_, fun a h0 ha hb hc => by rw [stk7 a h0 ha]; exact frA a h0 ha hb hc⟩
    obtain ⟨hd4, hda⟩ := keepA d hd hu hne
    have hne' : d ≠ chk := hckf d hd hu
    exact ⟨(oth7 d hd4 hu hne').1, fun a ha => by rw [(oth7 d hd4 hu hne').2 a ha]; exact hda a ha⟩

end Services.Bootstrap.Acc
