import Services.Bootstrap.Acc.ItemsLoop.Err

/-!
# The operand arms' common head, 6766 → 7009 (R2)

For an operand at the loop head (any work result), the run goes 6766 → 6782 → 6827 (`il_step`,
`il_disp_op`), saves the slot's words and copies its octets 8 … 136 to sp + 272 (`op_pre`, `memcpy`),
sets up the item's log line (`op_mid`) and runs it (`ItemLogFmt`, 6955 → 7009). `op_head` states the
state at 7009 against the loop head's: the context and stream kept, ω₁ = sp, the allocator's context
for a state keeping every allocated chunk with its data, the copy, the cursor advanced, the frame
words the loop invariant reads kept, the statics and the octets below 196608 with their access kept;
or an early ☇ in the log line (`ExhaustsP`). It is the prefix `err_arm` runs inline.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Picoalloc

/-- **The state at 7009** after an operand's head, against the loop head's state s (slot at cur,
    allocator state st). -/
structure OpHeadPost (env : AccEnv) (pb S0 S1 sp cur : Nat) (st : State) (s s₁ : St Stream) : Prop where
  pc : s₁.i = 7009
  c : s₁.c = s.c
  r1 : s₁.ω[1] = UInt64.ofNat sp
  heap : ∃ st', HeapCtxC env.code pb S0 S1 s₁.μ st' ∧
    ∀ d ∈ chunks st, d.used = true → d ∈ chunks st' ∧ ∀ a, InDataA d a → s₁.μ.read a = s.μ.read a
  cpy : s₁.μ.readN (sp + 272) 128 = s.μ.readN (cur + 8) 128
  m168 : rdN s₁.μ (sp + 168) 8 = cur + 184
  m200 : rdN s₁.μ (sp + 200) 8 = 678
  m264 : rdN s₁.μ (sp + 264) 8 = rdN s.μ cur 8
  keep : ∀ k, (k = 16 ∨ k = 32 ∨ k = 136 ∨ k = 144 ∨ k = 184 ∨ k = 208 ∨ k = 216 ∨ k = 1848) →
    rdN s₁.μ (sp + k) 8 = rdN s.μ (sp + k) 8
  glob : ∀ a, Glob a → s₁.μ.read a = s.μ.read a
  lo : ∀ a, a < 196608 → s₁.μ.read a = s.μ.read a ∧ s₁.μ.readable a = s.μ.readable a

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The operand arms' head, 6766 → 7009** (see the module doc). Named hypothesis: `ItemLogFmt`. -/
theorem opArm_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    {Ab : St Stream → Prop} {pb S0 S1 : Nat} (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (hIL : ItemLogFmt p env pb S0 S1) {sp q nc e : Nat} {μ₀ : Memory}
    (o : OperandTuple) (rest : List AccumulateInput) (s : St Stream)
    (hI : ItemsInv env pb S0 S1 sp q nc e μ₀ (.operand o :: rest) s) (st : State)
    (H : HeapCtxC env.code pb S0 S1 s.μ st) (cur : Nat) (hc : rdN s.μ (sp + 168) 8 = cur)
    (db : Chunk) (hdb : db ∈ chunks st) (hdbu : db.used = true)
    (hin : ∀ a, cur ≤ a → a < cur + 184 → InDataA db a)
    (htl : rdN s.μ cur 8 ≤ 16384) :
    Aborts p (KeepCtx (accContractS env)) Ab s s.c ∨
      ∃ s₁, Reaches p (KeepCtx (accContractS env)) s s₁ ∧ OpHeadPost env pb S0 S1 sp cur st s s₁ := by
  have hS1 := H.hS1
  have hsp := hI.hsp
  have hstk := hI.hstk
  have hl := hI.cur
  simp only [List.length_cons] at hl
  rw [hc] at hl
  have hlo := heapC_data_lt H hdb (hin cur (Nat.le_refl _) (by omega))
  have hhi := heapC_data_lt H hdb (hin (cur + 183) (by omega) (by omega))
  have hrq : ∀ a, cur ≤ a → a < cur + 184 → s.μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heapC_writable_data H hdb hdbu (hin a h1 h2))
  have hwf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.writable a = true := fun a h1 h2 =>
    H.st a (by omega) (by omega)
  have hrf : ∀ a, sp ≤ a → a < sp + 1856 → s.μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hwf a h1 h2)
  -- 6766 → 6782 → 6827
  obtain ⟨ω1, r1, e5, f1⟩ := il_step (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q)
    s.ω s.μ sp cur e hI.r1 ⟨by omega, by omega⟩ hc hI.m144 (by omega) hrf
  have g1' : ω1[1] = UInt64.ofNat sp := (f1 1 (by decide)).trans hI.r1
  obtain ⟨ω2, μa, r2, a1, a5, -, a8, -, a7, n168, n200, fra, rda, wra, fa⟩ :=
    il_disp_op (p := p) (P := P) (R := KeepCtx (accContractS env)) (s.c, s.q) ω1 s.μ sp cur g1' e5
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hwf hrq
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
  have lod : ∀ a, a < sp - 48 → μd.read a = s.μ.read a := fun a ha => by
    rw [frd a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)),
      frc a (by omega) (Or.inl (by omega)) (Or.inl ha),
      frb a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      fra a (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  have wrall : ∀ a, μd.writable a = s.μ.writable a := fun a => by rw [wrd, wrc, wrb, wra]
  have Hd : HeapCtxC env.code pb S0 S1 μd st := HeapCtxC.keep_hi H (fun a ha => lod a (by omega)) wrall
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
  have d264 : rdN μd (sp + 264) 8 = rdN s.μ cur 8 := by
    rw [rdN_frame fun j hj => frd _ (by omega) (by omega) (by omega) (by omega),
      rdN_frame fun j hj => frc _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)), m264b, a7,
      UInt64.toNat_ofNat', Nat.mod_eq_of_lt (rdN_lt64 _ _)]
  have dcp : μd.readN (sp + 272) 128 = s.μ.readN (cur + 8) 128 := by
    rw [Memory.readN_congr fun j hj => frd _ (by omega) (by omega) (by omega) (by omega), cpc,
      Memory.readN_congr fun j hj => frb _ (by omega) (by omega) (by omega),
      Memory.readN_congr fun j hj => fra _ (by omega) (by omega) (by omega)]
  have run6955 := ((((r1.trans r2).trans r3).trans r4).trans r5)
  rcases hIL s.c s.q ω5 μd st sp Hd g1 g7 g8 g9 (by omega) hstk.2 (by omega) m1144 m1152 with
    ⟨st', ω6, μe, N6, r6, He, h1e, keepe, fre, gle⟩ | hx
  rotate_left
  · refine .inl (Aborts.prepend (s' := ⟨6955, ω5, μd, s.c, s.q⟩) ⟨_, by rw [hI.pc]; exact run6955⟩ ?_)
    exact aborts_of_exhaustsP hAb ⟨6955, ω5, μd, s.c, s.q⟩ hx
  have ste : ∀ k, sp ≤ k → k + 8 ≤ sp + 1856 → (k + 8 ≤ sp + 1568 ∨ sp + 1592 ≤ k) →
      rdN μe k 8 = rdN μd k 8 := fun k h0 h1 h2 => rdN_frame fun j hj => fre _ (by omega) (by omega) (by omega)
  have runAll := run6955.trans r6
  have roAll := ro_keep (keepCtx_keepsRO env H.bd) runAll H.ro
  refine .inr ⟨⟨7009, ω6, μe, s.c, s.q⟩, ⟨_, by rw [hI.pc]; exact runAll⟩, rfl, rfl, h1e.trans g1, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, fun a ha => ⟨(roAll a ha).1, (roAll a ha).2.1⟩⟩
  · exact ⟨st', He, fun d hd hu => ⟨(keepe d hd hu).1, fun a ha => by
      rw [(keepe d hd hu).2 a ha, lod a (by have := heapC_data_lt H hd ha; omega)]⟩⟩
  · show μe.readN (sp + 272) 128 = _
    rw [Memory.readN_congr fun j hj => fre _ (by omega) (by omega) (by omega)]; exact dcp
  · show rdN μe (sp + 168) 8 = _
    rw [ste _ (by omega) (by omega) (by omega)]; exact d168
  · show rdN μe (sp + 200) 8 = _
    rw [ste _ (by omega) (by omega) (by omega)]; exact d200
  · show rdN μe (sp + 264) 8 = _
    rw [ste _ (by omega) (by omega) (by omega)]; exact d264
  · intro k hk
    show rdN μe (sp + k) 8 = _
    rw [ste _ (by omega) (by omega) (by omega),
      std _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · intro a ha
    have hg : a < 196792 := by unfold Glob at ha; omega
    show μe.read a = _
    rw [gle a ha, lod a (by omega)]

end Services.Bootstrap.Acc
