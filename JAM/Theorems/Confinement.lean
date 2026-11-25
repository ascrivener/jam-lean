import JAM.Accumulate
import JAM.Refine
import PVM.Theorems.HostIds

/-!
# Confinement: what a service's host calls can reach

Which host calls a service can make is fixed by its code: Ψ only ever stops for the ids of its
own `ecalli` instructions (`PVM.psi_hostId_mem`), and Ψ_M's final context satisfies any invariant
that those calls preserve (`PVM.psiM_ctx_inv`). From the host functions of GP v0.8.0 Appendix B:

* **Accumulate** (`psiA_confined`, in `JAM/Theorems/ConfinementAcc.lean`, which is excluded from the
  build while GP v0.8.1's supervisors make it false as stated; see that file). If a service's code names none of `bless`, `assign`,
  `designate`, `new`, `eject` and `provide` (ids 15, 16, 17, 19, 22, 27), then Ψ_A for it changes
  only its own account: every other account, the staging set, the authorizer queue and the
  privileged services are as they were, and it provides nothing. Its only effects on other
  services are the deferred transfers it returns.
* **Refine** (`psiR_noExports`). If a service's code does not name `export` (id 8), Ψ_R returns no
  exported segments. Since GP v0.8.1 (#582) the code is the whole preimage and Y skips its
  metadata, so the hypothesis names `jamHostCallIdsOf` of the preimage itself.

Both depend only on the set of host-call ids in the blob, which is read off the code without
running it.
-/

namespace JAM

open PVM

/-! ## Shared lemmas -/


/-- Inserting at s leaves every other key alone. -/
theorem get?_insert_ne {α : Type} (m : Std.ExtTreeMap Nat α) {s k : Nat} (a : α) (h : k ≠ s) :
    (m.insert s a).get? k = m.get? k := by
  have hne : ¬ compare s k = .eq := fun hc => h (Nat.compare_eq_eq.1 hc).symm
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, ↓reduceIte]

theorem get?_insert_same {α : Type} (m : Std.ExtTreeMap Nat α) (s : Nat) (a : α) :
    (m.insert s a).get? s = some a := by
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]

/-- The common rules and their body: if the body keeps a confined context confined, so does the
    charged function (on ∞ the context is unchanged). -/
theorem charged_ctx {X : Type} (P : X → Prop) (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) (hx : P x)
    (hb : P (body ⟨.cont, ((gas - g : Nat) : Int), ω, μ, x⟩).ctx) :
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
  · unfold hostGrowHeap; exact charged_ctx (fun c' : RefineCtx => c'.2 = c.2) _ _ _ _ _ _ rfl rfl
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
  · unfold unknown; split <;> rfl

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
      8 ∉ jamHostCallIdsOf ⟨l.toArray⟩) :
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
      · obtain ⟨a, ha, hla⟩ := Option.bind_eq_some_iff.1 hl
        have h8 := hids w hw a ha l hla
        generalize hres : psiM _ 0 _ _ _ _ = res
        have hinv : res.2.2.2 = [] := by
          rw [← hres]; exact refine_psiM_noExports _ _ _ _ h8
        obtain ⟨u, o, m, ex⟩ := res
        simp only at hinv ⊢
        split <;> simp [hinv]

end JAM
