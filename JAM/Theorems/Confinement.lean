import JAM.Accumulate
import JAM.Refine
import PVM.Theorems.HostIds

/-!
# Confinement: what a service's host calls can reach

Which host calls a service can make is fixed by its code: Ψ only ever stops for the ids of its
own `ecalli` instructions (`PVM.psi_hostId_mem`), and Ψ_M's final context satisfies any invariant
that those calls preserve (`PVM.psiM_ctx_inv`). From the host functions of GP v0.8.0 Appendix B:

* **Accumulate** (`psiA_confined`). If a service's code names none of `bless`, `assign`,
  `designate`, `new`, `eject` and `provide` (ids 15, 16, 17, 19, 22, 27), then Ψ_A for it changes
  only its own account: every other account, the staging set, the authorizer queue and the
  privileged services are as they were, and it provides nothing. Its only effects on other
  services are the deferred transfers it returns.
* **Refine** (`psiR_noExports`). If a service's code does not name `export` (id 8), Ψ_R returns no
  exported segments.

Both depend only on the set of host-call ids in the blob, which is read off the code without
running it.
-/

namespace JAM

open PVM

/-! ## Accumulate -/

/-- The ids of the accumulate host functions that can reach beyond the caller's own account:
    `bless`, `assign`, `designate`, `new`, `eject`, `provide`. -/
def reachingIds : List Nat := [15, 16, 17, 19, 22, 27]

/-- Inserting at s leaves every other key alone. -/
theorem get?_insert_ne {α : Type} (m : Std.ExtTreeMap Nat α) {s k : Nat} (a : α) (h : k ≠ s) :
    (m.insert s a).get? k = m.get? k := by
  have hne : ¬ compare s k = .eq := fun hc => h (Nat.compare_eq_eq.1 hc).symm
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, ↓reduceIte]

theorem get?_insert_same {α : Type} (m : Std.ExtTreeMap Nat α) (s : Nat) (a : α) :
    (m.insert s a).get? s = some a := by
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]

/-- Implications x of service s that leave everything outside s's own account as in **e**. -/
def Confined (e : PartialState) (s : Nat) (x : Implications) : Prop :=
  x.id = s ∧ (∀ k, k ≠ s → x.state.accounts.get? k = e.accounts.get? k) ∧
    x.state.staging = e.staging ∧ x.state.authQueue = e.authQueue ∧ x.state.manager = e.manager ∧
    x.state.assigners = e.assigners ∧ x.state.delegator = e.delegator ∧
    x.state.registrar = e.registrar ∧ x.state.alwaysAcc = e.alwaysAcc ∧ x.provisions = ∅

/-- Both dimensions of the accumulation context are confined. -/
def ConfinedCtx (e : PartialState) (s : Nat) (c : AccCtx) : Prop :=
  Confined e s c.1 ∧ Confined e s c.2

theorem Confined.setSelf {e : PartialState} {s : Nat} {x : Implications} (h : Confined e s x)
    (a : ServiceAccount) : Confined e s (x.setSelf a) := by
  obtain ⟨hid, hk, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨hid, fun k hks => ?_, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp only [Implications.setSelf, hid, get?_insert_ne _ _ hks]
  exact hk k hks

/-- The common rules and their body: if the body keeps a confined context confined, so does the
    charged function (on ∞ the context is unchanged). -/
theorem charged_ctx {X : Type} (P : X → Prop) (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) (hx : P x)
    (hb : P (body ⟨.cont, (gas : Int) - g, ω, μ, x⟩).ctx) :
    P (charged g gas ω μ x body).ctx := by
  unfold charged
  split
  · exact hx
  · exact hb

/-- `writeValue` leaves the context alone. -/
theorem writeValue_ctx {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f z : Nat) : (writeValue out v o f z).ctx = out.ctx := by
  unfold writeValue
  dsimp only
  repeat' split
  all_goals rfl

namespace AccHost

/-- Close a goal `ConfinedCtx e s (…)` for a host function's result by splitting every case. -/
macro "confined_tac" hc:term : tactic =>
  `(tactic| (
    apply charged_ctx _ _ _ _ _ _ _ $hc
    dsimp only
    (repeat' split) <;>
      (simp only [r7, panic, updX, ConfinedCtx] at *
       first
        | exact $hc
        | exact ⟨($hc).1.setSelf _, ($hc).2⟩
        | (refine ⟨?_, ($hc).2⟩
           have h := ($hc).1
           unfold Confined at h ⊢
           simp only [Implications.setSelf] at h ⊢
           first
            | exact h
            | (obtain ⟨hid, hk, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
               refine ⟨hid, fun k hks => ?_, h1, h2, h3, h4, h5, h6, h7, h8⟩
               simp only [hid, get?_insert_ne _ _ hks]
               exact hk k hks)))))

variable {e : PartialState} {s : Nat}

theorem checkpoint_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (checkpoint gas ω μ c).ctx := by
  unfold checkpoint charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  exact ⟨hc.1, hc.1⟩

theorem upgrade_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (upgrade gas ω μ c).ctx := by
  unfold upgrade charge; confined_tac hc

theorem transfer_confined (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (transfer env gas ω μ c).ctx := by
  unfold transfer charge; confined_tac hc

theorem query_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (query gas ω μ c).ctx := by
  unfold query charge; confined_tac hc

theorem solicit_confined (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (solicit env gas ω μ c).ctx := by
  unfold solicit charge; confined_tac hc

theorem forget_confined (env : AccEnv) (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (forget env gas ω μ c).ctx := by
  unfold forget charge; confined_tac hc

theorem yield_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (yield gas ω μ c).ctx := by
  unfold yield charge; confined_tac hc

/-- **The accumulate dispatcher keeps a service confined**, for every id outside `reachingIds`. -/
theorem dispatch_confined (env : AccEnv) (n gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hn : n ∉ reachingIds) (hc : ConfinedCtx e s c) :
    ConfinedCtx e s (dispatch env n gas ω μ c).ctx := by
  unfold dispatch
  split
  · exact charged_ctx _ _ _ _ _ _ _ hc hc
  · unfold hostGrowHeap; exact hc
  · exact charged_ctx _ _ _ _ _ _ _ hc (by rw [writeValue_ctx]; exact hc)
  · exact hc
  · exact hc
  · unfold onSelf
    have hs := hc.1.1
    exact ⟨hc.1.setSelf _, hc.2⟩
  · exact hc
  · simp [reachingIds] at hn
  · simp [reachingIds] at hn
  · simp [reachingIds] at hn
  · exact checkpoint_confined gas ω μ c hc
  · simp [reachingIds] at hn
  · exact upgrade_confined gas ω μ c hc
  · exact transfer_confined env gas ω μ c hc
  · simp [reachingIds] at hn
  · exact query_confined gas ω μ c hc
  · exact solicit_confined env gas ω μ c hc
  · exact forget_confined env gas ω μ c hc
  · exact yield_confined gas ω μ c hc
  · simp [reachingIds] at hn
  · exact hc

end AccHost

/-- A partial state that agrees with **e** everywhere except possibly s's own account. -/
def Outside (e : PartialState) (s : Nat) (st : PartialState) : Prop :=
  (∀ k, k ≠ s → st.accounts.get? k = e.accounts.get? k) ∧ st.staging = e.staging ∧
    st.authQueue = e.authQueue ∧ st.manager = e.manager ∧ st.assigners = e.assigners ∧
    st.delegator = e.delegator ∧ st.registrar = e.registrar ∧ st.alwaysAcc = e.alwaysAcc

theorem Confined.outside {e st : PartialState} {s : Nat} {x : Implications}
    (hst : Outside e s st) (hx : Confined st s x) : Outside e s x.state ∧ x.provisions = ∅ := by
  obtain ⟨hk0, g1, g2, g3, g4, g5, g6, g7⟩ := hst
  obtain ⟨_, hk, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  exact ⟨⟨fun k hks => (hk k hks).trans (hk0 k hks), h1.trans g1, h2.trans g2, h3.trans g3,
    h4.trans g4, h5.trans g5, h6.trans g6, h7.trans g7⟩, h8⟩

/-- Ψ_A's run, from a starting state that differs from **e** at most in s's account. -/
theorem psiARun_confined (params : Params) (entropy : List UInt8) (e st : PartialState)
    (t s g : Nat) (inputs : List AccumulateInput) (code : ByteArray) (hst : Outside e s st)
    (hcode : (st.accounts.get? s).bind (·.code) = some code)
    (hids : ∀ h ∈ jamHostCallIdsOf code, h ∉ reachingIds) :
    Outside e s (psiARun params entropy st t s g inputs).state ∧
      (psiARun params entropy st t s g inputs).provisions = ∅ := by
  unfold psiARun
  dsimp only
  rw [hcode]
  dsimp only
  split
  · exact ⟨hst, rfl⟩
  · have conf_init : Confined st s (initImplications st s t entropy) :=
      ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have hinv := psiM_ctx_inv code 5 (UInt64.ofNat g)
      ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
      (initImplications st s t entropy, initImplications st s t entropy) (ConfinedCtx st s)
      (accHostFn { params, slot := t, entropy, inputs, code })
      (fun h hh _ _ _ x hx => by
        simp only [accHostFn]
        exact AccHost.dispatch_confined _ h _ _ _ x (hids h hh) hx)
      ⟨conf_init, conf_init⟩
    generalize psiM code 5 _ _ _ _ = r at hinv ⊢
    obtain ⟨u, o, x, y⟩ := r
    dsimp only at hinv ⊢
    split
    · exact Confined.outside hst hinv.2
    · exact Confined.outside hst hinv.2
    · split
      · exact Confined.outside hst hinv.1
      · exact Confined.outside hst hinv.1

/-- **Accumulate confinement.** If service s's code names none of `bless`, `assign`, `designate`,
    `new`, `eject`, `provide`, then Ψ_A for s leaves every other account, the staging set, the
    authorizer queue and the privileged services as they were in **e**, and provides nothing. -/
theorem psiA_confined (params : Params) (entropy : List UInt8) (e : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) (a : ServiceAccount) (code : ByteArray)
    (ha : e.accounts.get? s = some a) (hcode : a.code = some code)
    (hids : ∀ h ∈ jamHostCallIdsOf code, h ∉ reachingIds) :
    Outside e s (psiA params entropy e t s g inputs).state ∧
      (psiA params entropy e t s g inputs).provisions = ∅ := by
  simp only [psiA, ha]
  apply psiARun_confined (code := code) _ _ _ _ _ _ _ _ _ _ hids
  · exact ⟨fun k hks => get?_insert_ne _ _ hks, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [get?_insert_same, Option.bind_some]
    exact hcode

/-! ## Refine -/

namespace RefineHost

/-- Close `(f …).ctx.2 = c.2` by splitting every case of a refine host function. -/
macro "exports_tac" c:term : tactic =>
  `(tactic| (
    dsimp only
    apply charged_ctx (fun c' : RefineCtx => c'.2 = ($c).2) _ _ _ _ _ _ rfl
    dsimp only
    (repeat' split) <;> (simp only [r7, panic]) <;> rfl))

theorem invoke_exports (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (invoke gas ω μ c).ctx.2 = c.2 := by
  unfold invoke
  dsimp only
  generalize (if μ.rangeWritable (reg ω 8) 112 = true then
          some (Num.decodeLE (List.take 8 (μ.readN (reg ω 8) 112)),
            decodeRegs (List.drop 8 (μ.readN (reg ω 8) 112)))
        else none) = w?
  unfold charged
  rcases w? with _ | ⟨gR, w⟩
  · dsimp only
    split <;> rfl
  · dsimp only
    split
    · rfl
    · split
      · rfl
      · rename_i vm _
        generalize psi vm.code vm.pc (UInt64.ofNat gR) vm.charged w vm.ram = r
        rcases r with ⟨st, pc, g', ch', regs, mem⟩
        cases st <;> rfl

theorem dispatch_exports (env : Env) (n gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx)
    (hn : n ≠ 8) (hc : c.2 = []) : (dispatch env n gas ω μ c).ctx.2 = [] := by
  rw [← hc]
  unfold dispatch
  split
  · exact charged_ctx (fun c' : RefineCtx => c'.2 = c.2) _ _ _ _ _ _ rfl rfl
  · unfold hostGrowHeap; rfl
  · exact charged_ctx (fun c' : RefineCtx => c'.2 = c.2) _ _ _ _ _ _ rfl (by rw [writeValue_ctx])
  · unfold historicalLookup
    exact charged_ctx (fun c' : RefineCtx => c'.2 = c.2) _ _ _ _ _ _ rfl (by rw [writeValue_ctx])
  · exact absurd rfl hn
  · unfold machine; exports_tac c
  · unfold peek; exports_tac c
  · unfold poke; exports_tac c
  · unfold pages; exports_tac c
  · exact invoke_exports gas ω μ c
  · unfold expunge; exports_tac c
  · rfl

end RefineHost

/-- Ψ_M under the refine dispatcher, for code that does not name `export`, exports nothing. -/
theorem refine_psiM_noExports (env : RefineHost.Env) (code : ByteArray) (gas : UInt64)
    (a : ByteArray) (h8 : 8 ∉ jamHostCallIdsOf code) :
    (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, []) : RefineCtx)).2.2.2 = [] :=
  psiM_ctx_inv code 0 gas a ((∅, []) : RefineCtx) (fun c => c.2 = [])
    (toHostFn (RefineHost.dispatch env))
    (fun h hh g ω μ x hx => by
      have hne : h ≠ 8 := fun he => h8 (he ▸ hh)
      simp only [toHostFn]
      exact RefineHost.dispatch_exports _ h g.toNat ω μ x hne hx) rfl

/-- **Refine exports nothing without `export`.** If the code of the service a work item names does
    not name `export`, Ψ_R returns no exported segments. -/
theorem psiR_noExports (params : Params) (d : Accounts) (c i : Nat) (p : WorkPackage)
    (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (hids : ∀ w ∈ p.items[i]?, ∀ a ∈ d.get? w.service, ∀ l ∈ a.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList,
      ∀ code ∈ splitMetadata l, 8 ∉ jamHostCallIdsOf code) :
    (psiR params d c i p r imports extrinsics off).exports = [] := by
  unfold psiR
  split
  · rfl
  · rename_i w hw
    dsimp only
    split
    · rfl
    · rename_i l hl
      split
      · rfl
      · split
        · rfl
        · rename_i code hcode
          obtain ⟨a, ha, hla⟩ := Option.bind_eq_some_iff.1 hl
          have h8 := hids w hw a ha l hla code hcode
          generalize hres : psiM code 0 _ _ _ _ = res
          have hinv : res.2.2.2 = [] := by
            rw [← hres]; exact refine_psiM_noExports _ _ _ _ h8
          obtain ⟨u, o, m, ex⟩ := res
          simp only at hinv ⊢
          split <;> simp [hinv]

end JAM
