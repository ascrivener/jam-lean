import Services.Bootstrap.Acc.Final.Hyps
import Services.Bootstrap.Acc.Final.StartCtx
import Services.Bootstrap.Acc.Final.Head
import Services.Bootstrap.Acc.Final.FetchSpec
import Services.Bootstrap.StartMemZ

/-!
# T2's run: accumulate from instruction 5 implements `Spec.accumulate`

`acc_impl`: from Y's state at instruction 5 (registers for the arguments ℰ(t, s, |**i**|), a memory with
the facts `Prefix.StartMem` and `StartMemZ` list, the stack zero, the read-only slices `AccRO`), with
context (x₀, x₀) and any answer stream, the run implements `Spec.accumulate C t` and halts, early ☇ only
for heap exhaustion (`AccAbort`). The chain:

- `Spec.accumulate`'s first operation is `fetchItems` (`step_fetchItems`: it replies ℰ(↕**i**) and keeps
  the context). Its wrapper section runs from instruction 5 to the items loop, all keeping y:
  - 5 → 6501 (`start_ctx`: the statics, the allocator's start state);
  - 6501 → 6630, the first log line (`acc_log_lineK`; its failure tail is `AccLogFail`);
  - 6630 → 6674, the inputs decoded (`inputs_decode`; its traps are heap exhaustion);
  - no inputs: 6674 halts (`items_none_halt`);
  - otherwise 6674 → 6782 (`il_head2`), where `ItemsInv` holds.
- From 6782, `items_loop_full`: the loop over `ins.map specItem` (the spec's decode of ℰ(↕**i**),
  `decode_items`), then the halt.
-/

namespace Services.Bootstrap.Acc.Final

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.CodeF Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Picoalloc
  Services.Bootstrap.Acc Services.Bootstrap.Fmt Services.Bootstrap.Spec
  Services.Bootstrap.Acc.Handlers.InstrRep Services.Bootstrap.Acc.Handlers.InstrLoop
  Services.Bootstrap.Alloc.AfterStart

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-! ## The inputs -/

/-- A sized input's encoding is at most 32925 octets. -/
theorem encode_length_le (i : AccumulateInput) (hi : InputSized i) : i.encode.length ≤ 32925 := by
  cases i with
  | operand o =>
    obtain ⟨h1, h2, h3, h4, -, ht, ho⟩ := hi
    have hg := encodeNat_length_le o.gasLimit
    have h0 : (Blob.encodeNat 0).length = 1 := by decide
    have hta := encodeNat_length_le o.authTrace.size
    have hr : o.result.encode.length ≤ 1 + 9 + 16384 := by
      cases hres : o.result with
      | ok b =>
        have := encodeNat_length_le b.size
        have hb := ho b hres
        simp only [WorkResult.encode, Codec.var, Codec.nat, List.length_cons, List.length_append,
          ByteArray.length_toList']
        omega
      | err e => cases e <;> simp [WorkResult.encode]
    simp only [AccumulateInput.encode, OperandTuple.encode, Codec.blob, Codec.var, Codec.nat, List.length_append,
      ByteArray.length_toList', h1, h2, h3, h4]
    omega
  | transfer x =>
    obtain ⟨-, -, -, -, hm⟩ := hi
    have h1 := encodeNat_length_le 1
    simp only [AccumulateInput.encode, DeferredTransfer.encode, Codec.blob, Codec.fixed, Codec.nat,
      List.length_append, ByteArray.length_toList', hm, Num.length_encodeLE]
    omega

/-- **ℰ(↕**i**) for at most 89 sized inputs** is at most 9 + 89 · 32925 octets. -/
theorem inputsEnc_length_le (env : AccEnv) (hn : env.inputs.length ≤ 89)
    (hsz : ∀ i ∈ env.inputs, InputSized i) : (inputsEnc env).length ≤ 9 + 89 * 32925 := by
  have hf : ∀ (l : List AccumulateInput), (∀ i ∈ l, InputSized i) →
      ((l.map AccumulateInput.encode).flatten).length ≤ l.length * 32925 := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons i r ih =>
      intro h
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      have := encode_length_le i (h i (by simp))
      have := ih (fun j hj => h j (by simp [hj]))
      rw [Nat.add_mul, Nat.one_mul]; omega
  have := hf env.inputs hsz
  have := encodeNat_length_le env.inputs.length
  simp only [inputsEnc, Codec.varSeq, Codec.nat, List.length_append]
  have : env.inputs.length * 32925 ≤ 89 * 32925 := Nat.mul_le_mul_right _ hn
  omega

/-- A sized input is well-sized for the spec's decode (`InputWF`). -/
theorem inputWF_of_sized (i : AccumulateInput) (hi : InputSized i) : InputWF i := by
  cases i with
  | operand o =>
    obtain ⟨h1, h2, h3, h4, hg, ht, ho⟩ := hi
    exact ⟨h1, h2, h3, h4, hg, by omega, fun b hb => by have := ho b hb; omega⟩
  | transfer x => exact hi

/-! ## The read-only data at Y -/

/-- The read-only facts accumulate's proofs read, in a memory. -/
structure AccRO (μ : Memory) : Prop where
  tmpl : μ.readN 66464 42 = accTmplBytes
  row : RoW μ
  tr : TrRO μ
  op : OpRO μ

theorem AccRO.keep {μ μ' : Memory} (h : AccRO μ)
    (hk : ∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) : AccRO μ' :=
  ⟨by rw [Memory.readN_congr fun j hj => (hk _ (by omega)).1]; exact h.tmpl,
   h.row.congr fun a _ h2 => hk a h2, h.tr.keep hk, h.op.keep hk⟩

/-! ## The run -/

/-- The refine host `acc_log_line` is stated for: any, with accumulate's code. -/
def envHOf (env : AccEnv) : RefineHost.Env :=
  ⟨Params.full, 0, ∅, 0, env.code, 0, ⟨Params.full, none, none, none, none, none, none, none⟩⟩

/-- The gas cap the summaries are stated at (≥ 2²⁷ for the allocator, ≥ every host call's cost). -/
abbrev gcap : Nat := 1099511627776

/-- `Spec.accumulate`, unfolded: `fetchItems`, then the decode, then the loop over the items with the
    body `accBody` (definitionally the spec's). -/
theorem accumulate_unfold (C : Spec.Consts) (now : Nat) : Spec.accumulate C now = Prog.call AOp.fetchItems (fun r =>
    match r.bind (decode (Dec.vec Dec.item)) with
    | none => Prog.panic
    | some items => Prog.bind (forIn items PUnit.unit (accBody C now)) (fun _ => pure PUnit.unit)) := by
  unfold Spec.accumulate
  show Prog.call AOp.fetchItems _ = _
  congr 1

/-- **T2's run** (see the module docstring): from Y's state at instruction 5 with context (x₀, x₀) and any
    answer stream, the run implements `Spec.accumulate C t` (t = the environment's timeslot) and halts,
    early ☇ only for heap exhaustion (`AccAbort`). Premises: the code facts, bootstrap's heap bounds and
    the full parameters; the named hypotheses `AccHypsAt`; Y's memory facts and the read-only slices
    (`AccRO`); the arguments ℰ(t, s, |**i**|); the service's own account a in x₀ with an `info` record
    shorter than 2⁶⁴ − 9 octets; at most 89 sized inputs (G3); `ValuesFit`; the ring constant
    maxRecent = 2·𝖢·𝖨 for the full parameters. -/
theorem acc_impl {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] [HasCodeF p P]
    (B : InstrRep) (C : Spec.Consts) (hmax : C.maxRecent = 2 * 341 * 16)
    (env : AccEnv) (henv : heapBounds env.code = (48, 1044430)) (hpar : env.params = Params.full)
    (hH : AccHypsAt B C env.slot p P env)
    (μ : Memory) (hμ : Prefix.StartMem μ) (hZ : Prefix.StartMemZ μ)
    (hz : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.read a = 0) (hro : AccRO μ)
    (S N LA : Nat) (hT : env.slot < 4294967296) (hS : S < 4294967296) (hN : N = env.inputs.length)
    (hLA : (Blob.encodeNat env.slot).length + (Blob.encodeNat S).length + (Blob.encodeNat N).length = LA)
    (hmem : μ.readN 4278124544 LA = Blob.encodeNat env.slot ++ Blob.encodeNat S ++ Blob.encodeNat N)
    (hrd : ∀ a, 4278124544 ≤ a → a < 4278124544 + LA → μ.readable a = true)
    (x₀ : Implications) (a : ServiceAccount) (ha : x₀.state.accounts.get? x₀.id = some a)
    (hlen : (infoValue a).length < 18446744073709551607)
    (hn : env.inputs.length ≤ 89) (hsz : ∀ i ∈ env.inputs, InputSized i) (hfit : ValuesFit env x₀)
    (f : Stream) :
    Impl p (accContractS env) env AccAbort (Spec.accumulate C env.slot) (Halts p (accContractS env))
      ⟨5, Prefix.initRegs LA, μ, (x₀, x₀), f⟩ := by
  have hL := inputsEnc_length_le env hn hsz
  have hstep := ASem.step_fetchItems env (x₀, x₀) (by omega)
  have hdec : (some (inputsEnc env)).bind (decode (Dec.vec Dec.item)) = some (env.inputs.map specItem) :=
    decode_items env.inputs (by omega) (fun i hi => inputWF_of_sized i (hsz i hi))
  rw [accumulate_unfold]
  unfold Impl
  refine .inr ⟨⟨5, Prefix.initRegs LA, μ, (x₀, x₀), f⟩, ⟨0, .refl⟩, rfl, ?_⟩
  simp only [hstep]
  -- (1) 5 → 6501
  obtain ⟨ω1, μ1, run1, r1, r7, hra, hcC, hcI, H1, -, -⟩ :=
    start_ctx p P env henv hpar μ hμ hZ hz env.slot S N LA hT hS (by omega) hLA hmem hrd (x₀, x₀)
  obtain ⟨-, run1Y⟩ := FreeStepsH.yinK x₀ x₀ f run1 rfl
  have lk1 := ro_keep (yIn_keepsRO env henv x₀ x₀) run1Y hZ.lowRO
  have ro1 : AccRO μ1 := hro.keep fun b hb => ⟨(lk1 b hb).1, (lk1 b hb).2.1⟩
  have hrt1 : ∀ b, 66464 ≤ b → b < 66506 → μ1.readable b = true := fun b h1 h2 => ro1.row.vrd b (by omega) (by omega)
  have r7' : ω1[7] = UInt64.ofNat (4278057152 + 1568) := by rw [r7]
  -- (2) 6501 → 6630, the first log line
  rcases acc_log_lineK (p := p) (P := P) gcap ⟨by decide, by decide⟩ env (envHOf env) 1044430 4278050816 4278059008
      (allocOk_keepK (P := P) env (envHOf env) rfl gcap 1044430 4278050816 4278059008 (by decide) (by decide))
      (reallocOk_keepK (P := P) env (envHOf env) rfl gcap 1044430 4278050816 4278059008 (by decide) (by decide))
      (x₀, x₀) a ha hlen ω1 μ1 sStart H1 (by rw [sStart_base]) r1 r7' (by decide)
      ro1.row ro1.tmpl hrt1 with
    ⟨ω2, μ2, x2, s2, run2, H2, -, K2, r21, m136, m208⟩ | hx
  rotate_left
  · -- the log line's failure tail (`AccLogFail`)
    left
    obtain ⟨ωe, μe, xe, je, rune, e7, hje⟩ := hx
    obtain ⟨hxe, runeK⟩ := FreeStepsH.keepS f rune
    subst hxe
    have hE : ExhaustsP p env 1044430 6501 ω1 μ1 (x₀, x₀) f :=
      hH.logFail (x₀, x₀) f ω1 μ1 sStart _ H1 (by rw [sStart_base]) r1 r7' ro1.row ro1.tmpl hrt1
        ⟨ωe, μe, ((x₀, x₀), f), je, runeK, e7, hje⟩
    refine ⟨(x₀, x₀), .inl rfl, ?_⟩
    have hab := aborts_of_exhaustsP (p := p) (Ab := AccAbort) (fun s h => accAbort_of_heapFailT h)
      ⟨6501, ω1, μ1, (x₀, x₀), f⟩ hE
    exact Aborts.prepend ⟨_, run1Y⟩ (Aborts.keepYIn x₀ x₀ hab rfl)
  obtain ⟨hx2, run2K⟩ := FreeStepsH.keepS f run2
  subst hx2
  have run2Y := FreeStepsH.keepYIn x₀ x₀ run2K rfl
  -- (3) 6630 → 6674, the inputs
  have hcost : 287 + memGas 400 (inputsEnc env).length ≤ gcap := by unfold memGas gcap; omega
  rcases inputs_decode env gcap 1044430 (by decide) (by decide) hcost (P := P) (hb := 0) (x₀, x₀) ω2 μ2 s2
      4278057152 4278050816 4278059008 H2 (r21.trans r1) hn hsz (by omega) (by decide) (by decide) (by decide) with
    ⟨q, st', ω3, μ3, run3, z1, -, -, o0, o8, o16, H3, -, reps, sown, fr3⟩ | ⟨j, ω3, μ3, hj, run3⟩
  rotate_left
  · -- an allocation-failure trap
    left
    refine ⟨(x₀, x₀), .inl rfl, ?_⟩
    obtain ⟨-, run3Y⟩ := FreeStepsH.yinK x₀ x₀ f run3 rfl
    refine ⟨⟨j, ω3, μ3, (x₀, x₀), f⟩, ⟨_, (run1Y.trans run2Y).trans run3Y⟩, .inl ?_, ω3, μ3, f, ?_⟩
    · show HeapTrapPc j
      rcases hj with rfl | rfl | rfl <;> decide
    · show FreeRunH p _ j ω3 μ3 ((x₀, x₀), f) .panic ω3 μ3 ((x₀, x₀), f)
      rcases hj with rfl | rfl | rfl
      · exact trap_run _ ⟨(d_47554 (p := p) (P := P)).1, (d_47554 (p := p) (P := P)).2.1⟩ _ ω3 μ3
      · exact trap_run _ ⟨(d_45975 (p := p) (P := P)).1, (d_45975 (p := p) (P := P)).2.1⟩ _ ω3 μ3
      · exact trap_run _ ⟨(d_45642 (p := p) (P := P)).1, (d_45642 (p := p) (P := P)).2.1⟩ _ ω3 μ3
  obtain ⟨-, run3Y⟩ := FreeStepsH.yinK x₀ x₀ f run3 rfl
  have runA := (run1Y.trans run2Y).trans run3Y
  -- the frame words at 6674
  have k3 : ∀ o, 4278057152 ≤ o → o + 8 ≤ 4278057152 + 1568 → rdN μ3 o 8 = rdN μ2 o 8 := fun o h1 h2 =>
    rdN_frame fun j hj => fr3 _ (by omega) (by omega) (.inl (by omega))
  have w1848 : rdN μ3 (4278057152 + 1848) 8 = 4294901760 := by
    rw [rdN_frame fun j hj => fr3 _ (by omega) (by omega) (.inr (by omega)),
      rdN_frame fun j hj => K2.hi _ (by omega) (by omega) (by unfold logE; omega)]
    unfold rdN; rw [show (4278057152 + 1848 : Nat) = 4278059000 from rfl, hra]; rfl
  have g3 : ∀ b, Glob b → μ3.read b = μ1.read b := fun b hb =>
    (hH.inGlob gcap (x₀, x₀) ω2 μ2 s2 4278057152 _ ω3 μ3 (x₀, x₀) H2 (r21.trans r1) (by decide) (by decide)
      (by decide) run3 b hb).trans (K2.glob b hb)
  have hpr : ∀ (prog : Prog AOp Unit), prog = Prog.bind (forIn (env.inputs.map specItem) PUnit.unit (accBody C env.slot))
      (fun _ => pure PUnit.unit) → ∀ s', Impl p (accContractS env) env AccAbort prog (Halts p (accContractS env)) s' →
      Impl p (accContractS env) env AccAbort
        (match (some (inputsEnc env)).bind (decode (Dec.vec Dec.item)) with
          | none => Prog.panic
          | some items => Prog.bind (forIn items PUnit.unit (accBody C env.slot)) (fun _ => pure PUnit.unit))
        (Halts p (accContractS env)) s' := by
    intro prog hp s' h
    rw [hdec]; rw [hp] at h; exact h
  by_cases hn0 : env.inputs = []
  · -- no inputs: 6674 halts
    right
    refine ⟨⟨6674, ω3, μ3, (x₀, x₀), f⟩, ⟨_, runA⟩, rfl, ?_⟩
    have hl0 : env.inputs.length = 0 := by rw [hn0]; rfl
    obtain ⟨ωh, μh, runh, h8⟩ := items_none_halt (p := p) (P := P) (R := KeepCtx (accContractS env))
      ((x₀, x₀), f) ω3 μ3 4278057152 q z1 (by decide) (by rw [o0, hl0])
      (by rw [show (4278057152 + 1576 : Nat) = 4278057152 + 1568 + 8 from rfl]; exact o8)
      (by rw [show (4278057152 + 1584 : Nat) = 4278057152 + 1568 + 16 from rfl, o16, hl0]) w1848
      (fun b h1 h2 => H3.st b (by omega) (by omega))
    refine hpr (Prog.pure PUnit.unit) (by rw [hn0]; rfl) _ ?_
    show _ ∨ _
    exact .inr ⟨_, ⟨0, .refl⟩, rfl, ωh, μh, f, runh, h8⟩
  · -- inputs: 6674 → 6782, then the items loop
    have hpos : 0 < env.inputs.length := by
      cases h : env.inputs with
      | nil => exact absurd h hn0
      | cons _ _ => simp
    obtain ⟨d, hd, hdu, hda, hdq⟩ := sown.1 (by omega)
    obtain ⟨hcb1, hcb2, hcb3⟩ := chunk_bounds H3.wf hd
    have hbT := H3.hbT
    have hq31 : q + 184 * env.inputs.length < 2147483648 := by omega
    obtain ⟨ω4, μ4, run4, a1, a5, -, a144, a16, a32, a184, a216, fr4, rd4, wr4⟩ :=
      il_head2 (p := p) (P := P) (R := YIn (accContractS env) x₀ x₀) ((x₀, x₀), f) ω3 μ3 4278057152
        env.inputs.length q env.inputs.length z1 (by decide) o0
        (by rw [show (4278057152 + 1576 : Nat) = 4278057152 + 1568 + 8 from rfl]; exact o8)
        (by rw [show (4278057152 + 1584 : Nat) = 4278057152 + 1568 + 16 from rfl]; exact o16)
        ⟨hpos, hn⟩ (by omega) (fun b h1 h2 => H3.st b (by omega) (by omega))
    have runB := runA.trans run4
    have lk4 := ro_keep (yIn_keepsRO env henv x₀ x₀) runB hZ.lowRO
    have ro4 : AccRO μ4 := hro.keep fun b hb => ⟨(lk4 b hb).1, (lk4 b hb).2.1⟩
    have lo4 : ∀ b, b < 4278057152 + 16 → μ4.read b = μ3.read b := fun b hb =>
      fr4 b (by omega) (.inl hb) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
    have H4 : HeapCtxC env.code 1044430 4278050816 4278059008 μ4 st' :=
      HeapCtxC.keep_hi H3 (fun b hb => lo4 b (by omega)) wr4
    have k43 : ∀ o, (o = 4278057152 + 136 ∨ o = 4278057152 + 208 ∨ o = 4278057152 + 1848) →
        rdN μ4 o 8 = rdN μ3 o 8 := fun o ho =>
      rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    -- the chunks' data is below the stack: kept by il_head2
    have kch : ∀ c ∈ chunks st', c.used = true → ∀ b, InDataA c b → μ4.read b = μ3.read b := fun c hc _ b hb => by
      have := chunk_bounds H3.wf hc
      unfold InDataA at hb
      exact lo4 b (by omega)
    have hslots : ∀ (j : Nat) (i : AccumulateInput), env.inputs[j]? = some i →
        (itemOf i).2 (μ4.readN (q + 184 * j) 184) μ4 := fun j i hj => reps j i hj μ4 kch
    have hown : ItemsOwn st' μ4 q q env.inputs := by
      have h3 := itemsOwn_of_slots (fun j i hj => reps j i hj μ3 (fun _ _ _ _ _ => rfl)) hsz sown
      unfold ItemsOwn at h3 ⊢
      rw [footL_congr env.inputs q fun b h1 h2 => lo4 b (by omega)]
      exact h3
    have hPS : Handlers.RecentSlotWrite.ParamStatics μ4 341 16 := by
      refine ⟨?_, by decide, ?_, by decide⟩
      · rw [Memory.readN_congr fun j hj => (lo4 _ (by omega)).trans (g3 _ (by unfold Glob; omega))]; exact hcC
      · rw [Memory.readN_congr fun j hj => (lo4 _ (by omega)).trans (g3 _ (by unfold Glob; omega))]; exact hcI
    have he5 : curAt 4278057152 ⟨6782, ω4, μ4, (x₀, x₀), f⟩ = q := by
      rw [curAt_6782 rfl]
      show ω4[5].toNat = q
      rw [a5]; exact UInt64.toNat_ofNat_of_lt' (show q < 2 ^ 64 by omega)
    have hInv : ItemsInv env 1044430 4278050816 4278059008 4278057152 q env.inputs.length
        (q + 184 * env.inputs.length) μ4 env.inputs ⟨6782, ω4, μ4, (x₀, x₀), f⟩ :=
      { pc := .inr ⟨rfl, hn0⟩
        r1 := a1
        hsp := by decide
        hstk := by decide
        cur := by rw [he5]
        m144 := a144
        m16 := a16
        m32 := a32
        m208 := by rw [k43 _ (.inr (.inl rfl)), k3 _ (by omega) (by omega)]; exact m208
        m136 := by rw [k43 _ (.inl rfl), k3 _ (by omega) (by omega)]; exact m136
        m184 := a184
        m216 := a216
        m1848 := by rw [k43 _ (.inr (.inr rfl))]; exact w1848
        hcap := Nat.le_refl _
        heap := ⟨st', H4, fun _ => ⟨d, hd, hdu, hda, fun b h1 h2 => by
            rw [he5] at h1
            unfold InDataA; omega⟩,
          by rw [he5]; exact hslots,
          by rw [he5]; exact hown⟩
        ro := ro4.tr
        ro2 := ro4.op
        glob := fun _ _ => rfl
        fit := hfit
        sized := hsz }
    have himpl := items_loop_full (P := P) env B C env.slot gcap (by decide) (by decide)
      (fun s h => accAbort_of_heapFailT h)
      (fun s h => .inl (by rcases h with h | h | h | h | h <;> rw [h] <;> decide))
      (fun s h => .inr h)
      hH.utf8 hH.logFmt hH.keyFmt hH.itemLog hH.outDec hH.instrLog hH.resultLog hH.handler hH.push
      hH.extend hH.okEnc hH.drop (Cp := 341) (I := 16) (by unfold Handlers.RecentSlotWrite.RingFits; decide) hmax hPS env.inputs _ hInv
    right
    exact ⟨⟨6782, ω4, μ4, (x₀, x₀), f⟩, ⟨_, runB⟩, rfl, hpr _ rfl _ himpl⟩

end Services.Bootstrap.Acc.Final
