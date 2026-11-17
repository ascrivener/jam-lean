import Services.Bootstrap.Acc.ItemsLoop.Loop
import Services.Bootstrap.Acc.ItemsLoop.ErrSeg
import Services.Bootstrap.Acc.Items.Operand
import Services.Bootstrap.Acc.Transfer.CopyVal

/-!
# The items loop's work-error arm (R1)

An operand whose work result is an error (`Spec.Item.work p none`): the spec does nothing
(`pure (yield ())`). The binary: 6766 → 6782 (`il_step`), the dispatch to the operand arm 6827
(`il_disp_op`), the slot's words saved and its octets 8 … 136 copied to sp + 272 (`op_pre`, `memcpy`),
the item's log line set up (`op_mid`) and run (6955 → 7009, the named hypothesis `ItemLogFmt`), then
the skip to the drop 15191 (the result word −1), which frees the trace's buffer and goes round at
6766 (`err_skip_free` / `err_skip_nofree`, `dealloc`).

**`ItemLogFmt`** (decided 2026-11-16, a log site under the standing decision; G4): the item's log line
"Accumulating work item from {}" (template 66266, the operand's first hash at sp + 312 with the
formatter 2502) at 6955 … 7009, including the `log` call and the String's free, is frame-only: it
reaches 7009 keeping the context, ω₁, the allocator's context (for some state keeping every allocated
chunk and its data), the memory from sp up but the String's slot sp + 1568 … 1592, and the statics; or
it reaches a failed allocator call and ends ☇ (`ExhaustsP`). The text is not stated.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc

/-- **The item's log line, frame-only** (named hypothesis; see the module docstring). -/
def ItemLogFmt (p : ByteArray) (env : AccEnv) (pb S0 S1 : Nat) : Prop :=
  ∀ (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s₀ : State) (sp : Nat),
    HeapCtxC env.code pb S0 S1 μ s₀ →
    ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat (sp + 1568) → ω[8] = UInt64.ofNat 66266 →
    ω[9] = UInt64.ofNat (sp + 1144) →
    S0 + 4096 ≤ sp → sp + 1856 ≤ S1 → 2147483648 ≤ sp →
    rdN μ (sp + 1144) 8 = sp + 312 → rdN μ (sp + 1152) 8 = 2502 →
    (∃ (s' : State) (ω' : Regs) (μ' : Memory) (N : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 6955 ω μ (c, f) 7009 ω' μ' (c, f) N ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ ω'[1] = ω[1] ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 6955 ω μ c f

/-- A word inside a copied block. -/
theorem rdN_of_copy {μ ν : Memory} {d s n k : Nat} (h : μ.readN d n = ν.readN s n) (hk : k + 8 ≤ n) :
    rdN μ (d + k) 8 = rdN ν (s + k) 8 := by
  unfold rdN
  rw [← readN_drop_take μ d n k 8 hk, ← readN_drop_take ν s n k 8 hk, h]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The items loop's work-error arm**: from the loop head with an operand with a work error next,
    the run returns to the loop head with `ItemsInv` for the rest, keeping the context; or an early
    ☇ in the item's log line for a failed allocation. Named hypothesis: `ItemLogFmt`. -/
theorem err_arm {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    {Ab : St Stream → Prop} {pb S0 S1 : Nat} (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (hIL : ItemLogFmt p env pb S0 S1) {sp q nc e : Nat} {μ₀ : Memory} :
    ErrArm p env Ab pb S0 S1 sp q nc e μ₀ := by
  intro o er rest s Q hr hQ hI
  obtain ⟨st, H, hbuf, hslots, hown⟩ := hI.heap
  have hS1 := H.hS1
  have hsp := hI.hsp
  have hstk := hI.hstk
  have hl := hI.cur
  simp only [List.length_cons] at hl
  generalize hc : curAt sp s = cur at hl hbuf hslots hown
  have hnc : nc ≠ 0 := by have := hI.hcap; simp only [List.length_cons] at this; omega
  obtain ⟨db, hdb, hdbu, hdbq, hdata⟩ := hbuf hnc
  have hin : ∀ a, cur ≤ a → a < cur + 184 → InDataA db a := fun a h1 h2 => hdata a h1 (by omega)
  have hlo := heapC_data_lt H hdb (hin cur (Nat.le_refl _) (by omega))
  have hhi := heapC_data_lt H hdb (hin (cur + 183) (by omega) (by omega))
  have hrq : ∀ a, cur ≤ a → a < cur + 184 → s.μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heapC_writable_data H hdb hdbu (hin a h1 h2))
  have hwf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.writable a = true := fun a h1 h2 =>
    H.st a (by omega) (by omega)
  have hrf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwf a h1 h2)
  -- the slot
  have hslot := hslots 0 (.operand o) rfl
  simp only [itemOf, hr, Nat.mul_zero, Nat.add_zero] at hslot
  obtain ⟨⟨b0, b16, b8, -, -⟩, b24, -⟩ := hslot
  have hsz := hI.sized (.operand o) (by simp)
  simp only [InputSized] at hsz
  have htl : o.authTrace.toList.length ≤ 16384 := by
    rw [ByteArray.length_toList']; exact hsz.2.2.2.2.2.1
  have e0 : rdN s.μ cur 8 = o.authTrace.toList.length := by
    rw [← b0, wd_slot s.μ cur 0 (by omega), Nat.add_zero]
  have e8 : rdN s.μ (cur + 8) 8 = wd (s.μ.readN cur 184) 8 := (wd_slot s.μ cur 8 (by omega)).symm
  have e24 : rdN s.μ (cur + 24) 8 = 18446744073709551615 := by
    rw [← wd_slot s.μ cur 24 (by omega)]; exact b24
  -- 6766 → 6782 → 6827
  obtain ⟨ω1, N1, r1, g1', e5⟩ := hI.to6782 (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q)
    (by omega) hrf
  rw [hc] at e5
  obtain ⟨ω2, μa, r2, a1, a5, -, a8, -, a7, n168, n200, fra, rda, wra, fa⟩ :=
    il_disp_op (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q) ω1 s.μ sp cur g1' e5
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by rw [e0]; omega) (by rw [e0]; omega) hwf hrq
  have wfa : ∀ a, sp ≤ a → a < sp + 1856 → μa.writable a = true := fun a h1 h2 => by
    rw [wra]; exact hwf a h1 h2
  have rqa : ∀ a, cur ≤ a → a < cur + 184 → μa.readable a = true := fun a h1 h2 => by
    rw [rda]; exact hrq a h1 h2
  -- 6827 → 68729
  obtain ⟨ω3, μb, r3, c0, c7, c9, -, -, -, m264b, frb, rdb, wrb, fb⟩ :=
    op_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q) ω2 μa sp cur a1 a5
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ wfa rqa
  have c8 : ω3[8] = UInt64.ofNat (cur + 8) := (fb 8 (by decide)).trans a8
  have c1 : ω3[1] = UInt64.ofNat sp := (fb 1 (by decide)).trans a1
  have c5 : ω3[5] = UInt64.ofNat cur := (fb 5 (by decide)).trans a5
  -- the memcpy, 68729 → 6866
  obtain ⟨ω4, μc, r4, -, d1, d5, -, cpc, frc, rdc, wrc⟩ :=
    memcpy_val (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q) ω3 μb 230 6866 sp
      (sp + 272) (cur + 8) 128 c0 c1 c7 c8 c9 ⟨by omega, by omega, by omega⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_114]) bs_6866 ⟨by omega, by omega, hsp.2⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) (Or.inl (by omega))
      (Or.inr (by omega)) (fun a h1 h2 => by rw [rdb]; exact rqa a (by omega) (by omega))
      (fun a h1 h2 => by rw [wrb]; exact wfa a (by omega) (by omega))
      (fun a h1 h2 => by rw [wrb, wra]; exact H.st a (by omega) (by omega))
  -- 6866 → 6955
  obtain ⟨ω5, μd, r5, g7, g8, g9, g1, g5, m1144, m1152, -, -, -, -, -, -, -, -, frd, rdd, wrd, fd⟩ :=
    op_mid (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q) ω4 μc sp cur (d1.trans c1)
      (d5.trans c5) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [wrc, wrb]; exact wfa a h1 h2)
      (fun a h1 h2 => by rw [rdc, rdb]; exact rqa a h1 h2)
  -- the memory below sp − 48 (heap, statics, read-only data) is unchanged up to 6955
  have lod : ∀ a, a < sp - 48 → μd.read a = s.μ.read a := fun a ha => by
    rw [frd a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      frc a (by omega) (Or.inl (by omega)) (Or.inl ha),
      frb a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      fra a (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  have wrall : ∀ a, μd.writable a = s.μ.writable a := fun a => by rw [wrd, wrc, wrb, wra]
  have Hd : HeapCtxC env.code pb S0 S1 μd st := HeapCtxC.keep_hi H (fun a ha => lod a (by omega)) wrall
  -- the stack words at 6955
  have std : ∀ k, sp ≤ k → k + 8 ≤ sp + 1856 →
      (k + 8 ≤ sp + 168 ∨ sp + 176 ≤ k) → (k + 8 ≤ sp + 192 ∨ sp + 208 ≤ k) →
      (k + 8 ≤ sp + 232 ∨ sp + 448 ≤ k) → (k + 8 ≤ sp + 1144 ∨ sp + 1160 ≤ k) →
      rdN μd k 8 = rdN s.μ k 8 := fun k h0 h1 h2 h3 h4 h5 => rdN_frame fun j hj => by
    rw [frd _ (by omega) (by omega) (by omega) (by omega), frc _ (by omega) (by omega) (Or.inr (by omega)),
      frb _ (by omega) (by omega) (by omega), fra _ (by omega) (by omega) (by omega)]
  have d168 : rdN μd (sp + 168) 8 = cur + 184 := by
    rw [rdN_frame fun j hj => frd _ (by omega) (by omega) (by omega) (by omega),
      rdN_frame fun j hj => frc _ (by omega) (by omega) (Or.inr (by omega)),
      rdN_frame fun j hj => frb _ (by omega) (by omega) (by omega), n168]
  have d200 : rdN μd (sp + 200) 8 = 678 := by
    rw [rdN_frame fun j hj => frd _ (by omega) (by omega) (by omega) (by omega),
      rdN_frame fun j hj => frc _ (by omega) (by omega) (Or.inr (by omega)),
      rdN_frame fun j hj => frb _ (by omega) (by omega) (by omega), n200]
  have d264 : rdN μd (sp + 264) 8 = o.authTrace.toList.length := by
    rw [rdN_frame fun j hj => frd _ (by omega) (by omega) (by omega) (by omega),
      rdN_frame fun j hj => frc _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)), m264b, a7,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (rdN_lt64 _ _), e0]
  have cpw : ∀ k, k + 8 ≤ 128 → rdN μd (sp + 272 + k) 8 = rdN s.μ (cur + 8 + k) 8 := fun k hk => by
    rw [rdN_frame fun j hj => frd _ (by omega) (by omega) (by omega) (by omega), rdN_of_copy cpc hk,
      rdN_frame fun j hj => frb _ (by omega) (by omega) (by omega),
      rdN_frame fun j hj => fra _ (by omega) (by omega) (by omega)]
  have d288 : rdN μd (sp + 288) 8 = 18446744073709551615 := by
    have := cpw 16 (by omega); rw [show sp + 272 + 16 = sp + 288 by omega,
      show cur + 8 + 16 = cur + 24 by omega, e24] at this; exact this
  have d272 : rdN μd (sp + 272) 8 = wd (s.μ.readN cur 184) 8 := by
    have := cpw 0 (by omega); rw [Nat.add_zero, Nat.add_zero, e8] at this; exact this
  have run6955 := ((((r1.trans r2).trans r3).trans r4).trans r5)
  -- the item's log line
  rcases hIL s.c s.q ω5 μd st sp Hd g1 g7 g8 g9 (by omega) hstk.2 (by omega) m1144 m1152 with
    ⟨st', ω6, μe, N6, r6, He, h1e, keepe, fre, gle⟩ | hx
  rotate_left
  · refine .inl (Aborts.prepend (s' := ⟨6955, ω5, μd, s.c, s.q⟩) ⟨_, run6955⟩ ?_)
    exact aborts_of_exhaustsP hAb ⟨6955, ω5, μd, s.c, s.q⟩ hx
  have ste : ∀ k, sp ≤ k → k + 8 ≤ sp + 1856 → (k + 8 ≤ sp + 1568 ∨ sp + 1592 ≤ k) →
      rdN μe k 8 = rdN μd k 8 := fun k h0 h1 h2 => rdN_frame fun j hj => fre _ (by omega) (by omega) (by omega)
  have e288 : rdN μe (sp + 288) 8 = 18446744073709551615 := by
    rw [ste _ (by omega) (by omega) (by omega)]; exact d288
  have e264 : rdN μe (sp + 264) 8 = o.authTrace.toList.length := by
    rw [ste _ (by omega) (by omega) (by omega)]; exact d264
  have e272 : rdN μe (sp + 272) 8 = wd (s.μ.readN cur 184) 8 := by
    rw [ste _ (by omega) (by omega) (by omega)]; exact d272
  have rfe : ∀ a, sp ≤ a → a < sp + 1856 → μe.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (He.st a (by omega) (by omega))
  -- the heap data kept to 7009, relative to s.μ
  have date : ∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InDataA d a → μe.read a = s.μ.read a :=
    fun d hd hu => ⟨(keepe d hd hu).1, fun a ha => by
      rw [(keepe d hd hu).2 a ha, lod a (by have := heapC_data_lt H hd ha; omega)]⟩
  -- the frame of the whole arm, from sp up: what the loop invariant reads
  have kw : ∀ μf : Memory, (∀ a, a < 4294967296 → sp ≤ a → μf.read a = μe.read a) → ∀ k,
      (k = 16 ∨ k = 32 ∨ k = 136 ∨ k = 144 ∨ k = 184 ∨ k = 208 ∨ k = 216 ∨ k = 1848) →
      rdN μf (sp + k) 8 = rdN s.μ (sp + k) 8 := fun μf hf k hk => by
    rw [rdN_frame fun j hj => hf _ (by omega) (by omega), ste _ (by omega) (by omega) (by omega),
      std _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  -- the end state at 6766, from a final run 7009 → 6766
  have fin : ∀ (stf : State) (ωf : Regs) (μf : Memory) (Nf : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 7009 ω6 μe (s.c, s.q) 6766 ωf μf (s.c, s.q) Nf →
      HeapCtxC env.code pb S0 S1 μf stf → ωf[1] = UInt64.ofNat sp →
      (∀ a, a < 4294967296 → sp ≤ a → μf.read a = μe.read a) →
      (∀ a, Glob a → μf.read a = μe.read a) →
      (∀ d ∈ chunks st, d.used = true →
        (d.addr + 32 ∈ (footL rest (cur + 184) s.μ).map Prod.fst ∨ d = db) →
        d ∈ chunks stf ∧ ∀ a, InDataA d a → μf.read a = μe.read a) →
      Impl p (accContractS env) env Ab (pure (ForInStep.yield PUnit.unit)) Q s := by
    intro stf ωf μf Nf rf Hf h1f frf glf keepf
    have runAll := (run6955.trans r6).trans rf
    have roAll := ro_keep (keepCtx_keepsRO env H.bd) runAll H.ro
    refine .inr ⟨⟨6766, ωf, μf, s.c, s.q⟩, ⟨_, runAll⟩, rfl, hQ _ ?_⟩
    have hcur' : curAt sp ⟨6766, ωf, μf, s.c, s.q⟩ = cur + 184 := by
      rw [curAt_6766 rfl, rdN_frame fun j hj => frf _ (by omega) (by omega), ste _ (by omega) (by omega) (by omega), d168]
    have datf : ∀ d ∈ chunks st, d.used = true →
        (d.addr + 32 ∈ (footL rest (cur + 184) s.μ).map Prod.fst ∨ d = db) →
        d ∈ chunks stf ∧ ∀ a, InDataA d a → μf.read a = s.μ.read a := fun d hd hu hm =>
      ⟨(keepf d hd hu hm).1, fun a ha => by rw [(keepf d hd hu hm).2 a ha, (date d hd hu).2 a ha]⟩
    obtain ⟨sl', own'⟩ := rest_keep (st' := stf) (μ' := μf) (db := db) hslots hown
      (fun a h1 h2 => hdata a h1 (by omega)) (fun a ha => (datf db hdb hdbu (.inr rfl)).2 a ha)
      (fun d0 h0 hu hm => datf d0 h0 hu (.inl hm))
    refine ⟨.inl rfl, h1f, hsp, hstk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.fit, ?_⟩
    · rw [hcur']; omega
    · rw [kw μf frf 144 (by omega)]; exact hI.m144
    · rw [kw μf frf 16 (by omega)]; exact hI.m16
    · rw [kw μf frf 32 (by omega)]; exact hI.m32
    · rw [kw μf frf 208 (by omega)]; exact hI.m208
    · rw [kw μf frf 136 (by omega)]; exact hI.m136
    · rw [kw μf frf 184 (by omega)]; exact hI.m184
    · rw [kw μf frf 216 (by omega)]; exact hI.m216
    · rw [kw μf frf 1848 (by omega)]; exact hI.m1848
    · have := hI.hcap; simp only [List.length_cons] at this; omega
    · refine ⟨stf, Hf, fun _ => ⟨db, (datf db hdb hdbu (.inr rfl)).1, hdbu, hdbq, fun a h1 h2 => ?_⟩, ?_, ?_⟩
      · rw [hcur'] at h1; exact hdata a (by omega) h2
      · rw [hcur']; exact sl'
      · rw [hcur']; exact own'
    · exact hI.ro.keep fun a ha => ⟨(roAll a ha).1, (roAll a ha).2.1⟩
    · exact hI.ro2.keep fun a ha => ⟨(roAll a ha).1, (roAll a ha).2.1⟩
    · intro a ha
      have hg : a < 196792 := by unfold Glob at ha; omega
      rw [glf a ha, gle a ha, lod a (by omega)]; exact hI.glob a ha
    · intro i hi; exact hI.sized i (by simp [hi])
  -- the skip: free the trace's buffer, or not
  by_cases ht0 : o.authTrace.toList.length = 0
  · obtain ⟨ω7, r7, h17⟩ := err_skip_nofree (p := p) (P := P) (R := KeepCtx (accContractS env))
      (s.c, s.q) ω6 μe sp (h1e.trans g1) ⟨by omega, by omega⟩ e288 (by rw [e264, ht0]) rfe
    exact fin st' ω7 μe _ r7 He h17 (fun _ _ _ => rfl) (fun _ _ => rfl)
      (fun d hd hu _ => ⟨(date d hd hu).1, fun _ _ => rfl⟩)
  · -- the trace's buffer is an owned chunk
    have hw0 : wd (s.μ.readN cur 184) 0 ≠ 0 := by rw [b0]; exact ht0
    obtain ⟨hnd, hq, hch⟩ := hown
    have hpl : (wd (s.μ.readN cur 184) 8, wd (s.μ.readN cur 184) 16) ∈ footL (.operand o :: rest) cur s.μ := by
      simp [footL, slotFoot, hr, hw0]
    obtain ⟨dt, hdt, hdtu, hdta, -⟩ := hch _ hpl
    obtain ⟨ω7, r7, h07, h17, h77⟩ := err_skip_free (p := p) (P := P) (R := KeepCtx (accContractS env))
      (s.c, s.q) ω6 μe sp _ _ (h1e.trans g1) ⟨by omega, by omega⟩ e288 e264 ht0 e272 rfe
    obtain ⟨ω8, μf, r8, Hf, -, -, -, stkf, glf, keepf, -, h18, -, -⟩ :=
      Services.Bootstrap.Decode.DeallocCall.dealloc_callG (R := KeepCtx (accContractS env)) (p := p) (P := P) env.code pb S0 S1 (s.c, s.q)
        ω7 μe st' sp _ 228 6766 dt He (keepe dt hdt hdtu).1 hdtu hdta h07 h17 h77 (by decide)
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_113]) bs_6766 (by omega) ⟨by omega, by omega⟩
    simp only [footL, List.map_append] at hnd hq
    have hmem : wd (s.μ.readN cur 184) 8 ∈ (slotFoot (.operand o) (s.μ.readN cur 184)).map Prod.fst := by
      simp [slotFoot, hr, hw0]
    exact fin _ ω8 μf _ (r7.trans r8) Hf (h18.trans h17) stkf glf (fun d hd hu hm => by
      have hne : d ≠ dt := by
        intro hdd
        subst hdd
        have hdta' : d.addr + 32 = wd (s.μ.readN cur 184) 8 := hdta
        rw [hdta'] at hm
        rcases hm with hm | rfl
        · exact (List.nodup_append.1 hnd).2.2 _ hmem _ hm rfl
        · exact hq (List.mem_append_left _ (by rw [← hdbq, hdta']; exact hmem))
      exact ⟨(keepf d (keepe d hd hu).1 hu hne).1, fun a ha => (keepf d (keepe d hd hu).1 hu hne).2 a ha⟩)

end Services.Bootstrap.Acc
