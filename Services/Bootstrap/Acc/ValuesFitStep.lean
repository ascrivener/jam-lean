import Services.Bootstrap.Acc.Abort
import Services.Bootstrap.ASem

/-!
# `ValuesFit` is kept by every host call (R12)

T2's premise `ValuesFit` (`Acc/Abort.lean`) bounds this service's storage values, every service's
preimages and the encoded inputs below 2⁶³ octets. It is stated on the regular dimension x of the
accumulation context at the start; this module shows that every host call of the model,
`JAM.AccHost.dispatch` (GP v0.8.0 Appendix B, F of eq. `accinvocation`), keeps it, whatever the
registers, memory and gas. Hence every operation of `ASem.step` keeps it (`ValuesFit.step`), and so
does every prefix of an `ASem.run`.

Why it holds: the only octet strings a host call stores into these places are read from memory
(`write`'s value, B.7), and a readable range lies below 2³² (`PVM.Memory.rangeReadable`); `new`
creates an account with no preimages; `forget` and `eject` only remove entries; every other call
leaves storage and preimages alone. The inputs are part of the environment, which no call changes.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap

/-- An account's storage values and preimages are shorter than 2⁶³ octets. -/
def AcctFit (a : ServiceAccount) : Prop :=
  (∀ k w, a.storage.get? k = some w → w.length < 2 ^ 63) ∧
  (∀ h q, a.preimages.get? h = some q → q.length < 2 ^ 63)

/-- Every account's preimages are shorter than 2⁶³ octets. -/
def PreFit (d : Accounts) : Prop :=
  ∀ s a h q, d.get? s = some a → a.preimages.get? h = some q → q.length < 2 ^ 63

/-- The part of `ValuesFit` a host call can change: self's storage and every account's preimages. -/
def ImpFit (x : Implications) : Prop :=
  (∀ k w, x.self.storage.get? k = some w → w.length < 2 ^ 63) ∧ PreFit x.state.accounts

theorem valuesFit_iff (env : AccEnv) (x : Implications) :
    ValuesFit env x ↔
      ImpFit x ∧ (Codec.varSeq AccumulateInput.encode env.inputs).length < 2 ^ 63 := by
  unfold ValuesFit ImpFit PreFit; exact and_assoc.symm

theorem vf_self_setSelf (x : Implications) (a : ServiceAccount) : (x.setSelf a).self = a := by
  simp [Implications.self, Implications.setSelf]

theorem preFit_insert {d : Accounts} (hd : PreFit d) {i : Nat} {a : ServiceAccount}
    (ha : ∀ h q, a.preimages.get? h = some q → q.length < 2 ^ 63) : PreFit (d.insert i a) := by
  intro s b h q hs hq
  rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at hs
  split at hs
  · cases hs; exact ha h q hq
  · exact hd s b h q hs hq

theorem preFit_erase {d : Accounts} (hd : PreFit d) (i : Nat) : PreFit (d.erase i) := by
  intro s b h q hs hq
  rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase] at hs
  split at hs
  · cases hs
  · exact hd s b h q hs hq

/-- Self's preimages fit when every account's do. -/
theorem preFit_self {x : Implications} (hd : PreFit x.state.accounts) :
    ∀ h q, x.self.preimages.get? h = some q → q.length < 2 ^ 63 := by
  intro h q hq
  unfold Implications.self at hq
  rw [Std.ExtTreeMap.getD_eq_getD_getElem?] at hq
  cases hs : x.state.accounts[x.id]? with
  | none =>
    rw [hs] at hq
    simp [default] at hq
  | some a =>
    rw [hs] at hq
    exact hd x.id a h q (by rw [Std.ExtTreeMap.get?_eq_getElem?]; exact hs) hq

/-- `ImpFit` of x with self replaced by an account whose storage and preimages fit. -/
theorem impFit_setSelf {x : Implications} (hx : ImpFit x) {a : ServiceAccount} (ha : AcctFit a) :
    ImpFit (x.setSelf a) := by
  refine ⟨?_, ?_⟩
  · rw [vf_self_setSelf]; exact ha.1
  · exact preFit_insert hx.2 ha.2

/-- Self's account fits when x does. -/
theorem acctFit_self {x : Implications} (hx : ImpFit x) : AcctFit x.self :=
  ⟨hx.1, preFit_self hx.2⟩

/-- A readable range is at most 2³² octets long. -/
theorem lt_of_rangeReadable {μ : Memory} {o n : Nat} (h : μ.rangeReadable o n = true) :
    (μ.readN o n).length < 2 ^ 63 := by
  simp only [Memory.readN, List.length_map, List.length_range]
  unfold Memory.rangeReadable at h
  by_cases hn : n = 0
  · omega
  · simp only [Bool.or_eq_true, beq_iff_eq, hn, false_or, Bool.and_eq_true,
      decide_eq_true_eq] at h
    omega

/-! ## Host outputs and their context -/

theorem charged_ctx_of {X : Type} (P : X → Prop) {g gas : Nat} {ω : Regs} {μ : Memory} {x : X}
    {body : HostOut X → HostOut X} (hx : P x) (hb : ∀ out : HostOut X, out.ctx = x → P (body out).ctx) :
    P (charged g gas ω μ x body).ctx := by
  unfold charged; split
  · exact hx
  · exact hb _ rfl

@[simp] theorem writeValue_ctx {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f z : Nat) : (writeValue out v o f z).ctx = out.ctx := by
  unfold writeValue
  rcases v with _ | _ | _ <;> dsimp only <;> (try split) <;> rfl

@[simp] theorem vf_r7_ctx (out : HostOut AccCtx) (v : Nat) : (AccHost.r7 out v).ctx = out.ctx := rfl
@[simp] theorem vf_panic_ctx (out : HostOut AccCtx) : (AccHost.panic out).ctx = out.ctx := rfl
@[simp] theorem vf_updX_ctx (out : HostOut AccCtx) (x : Implications) :
    (AccHost.updX out x).ctx.1 = x := rfl

/-- `write`'s candidate account (B.7) fits. -/
theorem write_cand_fit {μ : Memory} {a a' : ServiceAccount} (ha : AcctFit a) {k : List UInt8}
    {vO vZ : Nat}
    (heq : (if vZ = 0 then some { a with storage := a.storage.erase k }
      else if μ.rangeReadable vO vZ = true then some { a with storage := a.storage.insert k (μ.readN vO vZ) }
      else none) = some a') : AcctFit a' := by
  split at heq
  · cases heq
    refine ⟨?_, ha.2⟩
    intro k' w hk
    rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase] at hk
    split at hk
    · cases hk
    · exact ha.1 k' w hk
  · split at heq
    · cases heq
      refine ⟨?_, ha.2⟩
      intro k' w hk
      rw [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert] at hk
      split at hk
      · cases hk; exact lt_of_rangeReadable (by assumption)
      · exact ha.1 k' w hk
    · cases heq

/-- `write` (B.7) keeps an account's fit. -/
theorem hostWrite_keeps {gas : Nat} {ω : Regs} {μ : Memory} {a : ServiceAccount} (ha : AcctFit a) :
    AcctFit (hostWrite gas ω μ a).ctx := by
  unfold hostWrite
  refine charged_ctx_of AcctFit ha ?_
  intro out hout
  dsimp only
  repeat' split
  all_goals first
    | (simp only [hout]; exact ha)
    | exact ha
    | exact write_cand_fit ha ‹_›

/-- `ImpFit x` from x's accounts being d with self inserted. -/
theorem impFit_mk {x : Implications} {d : Accounts} {s : ServiceAccount}
    (hid : x.state.accounts = d.insert x.id s) (hd : PreFit d) (hs : AcctFit s) : ImpFit x := by
  have hself : x.self = s := by
    unfold Implications.self; rw [hid]; exact Std.ExtTreeMap.getD_insert_self
  refine ⟨?_, ?_⟩
  · rw [hself]; exact hs.1
  · rw [hid]; exact preFit_insert hd hs.2

/-- An account with no preimages. -/
theorem preimages_empty_fit {a : ServiceAccount} (ha : a.preimages = ∅) :
    ∀ h q, a.preimages.get? h = some q → q.length < 2 ^ 63 := by
  intro h q hq
  rw [ha, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_empty] at hq
  cases hq

/-- An account with self's storage and preimages, or with a preimage removed. -/
theorem acctFit_with {a b : ServiceAccount} (ha : AcctFit a) (hs : b.storage = a.storage)
    (hp : b.preimages = a.preimages ∨ ∃ k, b.preimages = a.preimages.erase k) : AcctFit b := by
  refine ⟨?_, ?_⟩
  · rw [hs]; exact ha.1
  · rcases hp with hp | ⟨k, hp⟩
    · rw [hp]; exact ha.2
    · intro h q hq
      rw [hp, Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_erase] at hq
      split at hq
      · cases hq
      · exact ha.2 h q hq

/-! ## Every host call keeps `ImpFit` -/

/-- **Every host call of the model keeps `ImpFit`** of the regular dimension x (GP v0.8.0 Appendix B,
    F of eq. `accinvocation`), whatever the id, gas, registers and memory. -/
theorem dispatch_keeps (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (h : ImpFit c.1) : ImpFit (AccHost.dispatch env n gas ω μ c).ctx.1 := by
  unfold AccHost.dispatch
  split
  · -- gas
    unfold hostGas
    exact charged_ctx_of (fun c : AccCtx => ImpFit c.1) h (fun out hout => by simp [hout, h])
  · -- grow_heap
    unfold hostGrowHeap; exact h
  · -- fetch
    unfold hostFetch
    exact charged_ctx_of (fun c : AccCtx => ImpFit c.1) h (fun out hout => by simp [hout, h])
  · exact h
  · exact h
  · -- write
    exact impFit_setSelf h (hostWrite_keeps (acctFit_self h))
  · exact h
  · -- bless
    unfold AccHost.bless AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h) | exact ⟨h.1, h.2⟩
  · -- assign
    unfold AccHost.assign AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h) | exact ⟨h.1, h.2⟩
  · -- designate
    unfold AccHost.designate AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h) | exact ⟨h.1, h.2⟩
  · -- checkpoint
    unfold AccHost.checkpoint AccHost.charge
    exact charged_ctx_of (fun c : AccCtx => ImpFit c.1) h (fun out hout => h)
  · -- new
    unfold AccHost.new AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first
      | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_insert h.2 (preimages_empty_fit rfl)) (acctFit_self h))
  · -- upgrade
    unfold AccHost.upgrade AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first
      | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
      | (simp only [vf_r7_ctx, vf_updX_ctx]; exact impFit_setSelf h (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_erase h.2 _) (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_insert h.2 (preimages_empty_fit rfl)) (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         refine impFit_setSelf h ?_
         rename_i heq _
         revert heq
         split <;> (try split) <;> intro heq <;> cases heq <;>
           exact acctFit_with (acctFit_self h) rfl (by first | exact .inl rfl | exact .inr ⟨_, rfl⟩))
  · -- transfer
    unfold AccHost.transfer AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first
      | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
      | (simp only [vf_r7_ctx, vf_updX_ctx]; exact impFit_setSelf h (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_erase h.2 _) (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_insert h.2 (preimages_empty_fit rfl)) (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         refine impFit_setSelf h ?_
         rename_i heq _
         revert heq
         split <;> (try split) <;> intro heq <;> cases heq <;>
           exact acctFit_with (acctFit_self h) rfl (by first | exact .inl rfl | exact .inr ⟨_, rfl⟩))
  · -- eject
    unfold AccHost.eject AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first
      | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_erase h.2 _) (acctFit_self h))
  · -- query
    unfold AccHost.query AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
  · -- solicit
    unfold AccHost.solicit AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first
      | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
      | (simp only [vf_r7_ctx, vf_updX_ctx]; exact impFit_setSelf h (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_erase h.2 _) (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         exact impFit_mk rfl (preFit_insert h.2 (preimages_empty_fit rfl)) (acctFit_self h))
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         refine impFit_setSelf h ?_
         rename_i heq _
         revert heq
         split <;> (try split) <;> intro heq <;> cases heq <;>
           exact acctFit_with (acctFit_self h) rfl (by first | exact .inl rfl | exact .inr ⟨_, rfl⟩))
  · -- forget
    unfold AccHost.forget AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first
      | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h)
      | (simp only [vf_r7_ctx, vf_updX_ctx]
         refine impFit_setSelf h ?_
         rename_i heq
         revert heq
         split <;> (try split) <;> intro heq <;> cases heq <;>
           exact acctFit_with (acctFit_self h) rfl (by first | exact .inl rfl | exact .inr ⟨_, rfl⟩))
  · -- yield
    unfold AccHost.yield AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h) | exact ⟨h.1, h.2⟩
  · -- provide
    unfold AccHost.provide AccHost.charge
    refine charged_ctx_of (fun c : AccCtx => ImpFit c.1) h ?_
    intro out hout; dsimp only
    repeat' split
    all_goals first | (simp only [vf_r7_ctx, vf_panic_ctx, hout]; exact h) | exact ⟨h.1, h.2⟩
  · exact h

/-- A host call that continues keeps `ImpFit`. -/
theorem call_keeps {env : AccEnv} {n : Nat} {args : List Spec.Bytes} {vals : List Nat} {c : AccCtx}
    {o : HostOut AccCtx} (h : ImpFit c.1) (hc : ASem.call env n args vals c = some o) :
    ImpFit o.ctx.1 := by
  unfold ASem.call at hc
  dsimp only at hc
  split at hc
  · cases hc; exact dispatch_keeps _ _ _ _ _ _ h
  · cases hc

/-- A bind on a host call keeps a property of the context. -/
theorem bind_keeps {α : Type} {P : AccCtx → Prop} {r : Option (HostOut AccCtx)}
    {f : HostOut AccCtx → Option (α × AccCtx)} {b : α} {c' : AccCtx}
    (hr : ∀ o, r = some o → P o.ctx)
    (hf : ∀ o, P o.ctx → f o = some (b, c') → P c') (hs : (r >>= f) = some (b, c')) : P c' := by
  cases hro : r with
  | none => rw [hro] at hs; cases hs
  | some o => rw [hro] at hs; exact hf o (hr o hro) hs

/-- `pure (b, c₀) = some (b', c')` gives c' = c₀. -/
theorem pure_ctx {α : Type} {b b' : α} {c₀ c' : AccCtx}
    (h : (pure (b, c₀) : Option (α × AccCtx)) = some (b', c')) : c' = c₀ := by
  cases h; rfl

/-- `twoPhase` keeps `ImpFit`. -/
theorem twoPhase_keeps {env : AccEnv} {n : Nat} {args : List Spec.Bytes} {pre post : List Nat}
    {c c' : AccCtx} {v : Option Spec.Bytes} (h : ImpFit c.1)
    (hs : ASem.twoPhase env n args pre post c = some (v, c')) : ImpFit c'.1 := by
  unfold ASem.twoPhase at hs
  refine bind_keeps (P := fun c => ImpFit c.1) (fun o ho => call_keeps h ho) ?_ hs
  intro o ho hf
  try dsimp only at hf
  split at hf
  · rw [pure_ctx hf]; exact ho
  · exact bind_keeps (P := fun c => ImpFit c.1) (fun o' ho' => call_keeps ho ho')
      (fun o' ho' hf' => by rw [pure_ctx hf']; exact ho') hf

/-- **R12: every operation of `ASem.step` keeps `ImpFit`.** -/
theorem impFit_step {env : AccEnv} {β : Type} (op : Spec.AOp β) {c c' : AccCtx} {b : β}
    (h : ImpFit c.1) (hs : ASem.step env op c = some (b, c')) : ImpFit c'.1 := by
  cases op
  case read => exact twoPhase_keeps h hs
  case lookup => exact twoPhase_keeps h hs
  case fetchItems =>
    refine bind_keeps (P := fun c => ImpFit c.1) (fun o ho => call_keeps h ho) ?_ hs
    intro o ho hf
    try dsimp only at hf
    split at hf
    · rw [pure_ctx hf]; exact ho
    · exact bind_keeps (P := fun c => ImpFit c.1) (fun o' ho' => call_keeps ho ho')
        (fun o' ho' hf' => by rw [pure_ctx hf']; exact ho') hf
  case remove =>
    refine bind_keeps (P := fun c => ImpFit c.1) (fun o ho => call_keeps h ho) ?_ hs
    intro o ho hf
    try dsimp only at hf
    split at hf
    · cases hf
    · rw [pure_ctx hf]; exact ho
  all_goals
    refine bind_keeps (P := fun c => ImpFit c.1) (fun o ho => call_keeps h ho) ?_ hs
    intro o ho hf
    rw [pure_ctx hf]; exact ho

/-- **R12: `ValuesFit` is kept by every operation of `ASem.step`** (T2's premise on lengths holds
    at every point of a run once it holds at the start). -/
theorem ValuesFit.step {env : AccEnv} {β : Type} (op : Spec.AOp β) {c c' : AccCtx} {b : β}
    (h : ValuesFit env c.1) (hs : ASem.step env op c = some (b, c')) : ValuesFit env c'.1 := by
  rw [valuesFit_iff] at h ⊢
  exact ⟨impFit_step op h.1 hs, h.2⟩

/-- `ValuesFit` holds for the regular dimension at the end of every run (`ASem.run`). -/
theorem ValuesFit.run {env : AccEnv} : ∀ (n : Nat) (p : Spec.Prog Spec.AOp Unit) {c : AccCtx},
    ValuesFit env c.1 → ValuesFit env (ASem.run n p env c).2.1
  | n, .pure _, _, h => by cases n <;> exact h
  | n, .panic, _, h => by cases n <;> exact h
  | 0, .call _ _, _, h => h
  | n + 1, .call o k, c, h => by
    simp only [ASem.run]
    split
    · next b c' hs => exact ValuesFit.run n (k b) (ValuesFit.step o h hs)
    · exact h

end Services.Bootstrap.Acc
