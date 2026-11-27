import JAM.Accumulate
import JAM.Refine
import PVM.Theorems.HostIds

/-!
# Confinement: what a service's host calls can reach

Which host calls a service can make is fixed by its code: $\Psi$ only ever stops for the ids of its
own `ecalli` instructions (`PVM.psi_hostId_mem`), and $\Psi_M$'s final context satisfies any invariant
that those calls preserve (`PVM.psiM_ctx_inv`). From the host functions of GP v0.8.1 Appendix B:

* **Accumulate** (`psiA_confined`). If a service's code names none of `bless`, `assign`,
  `designate`, `new`, `eject` and `provide` (ids 16, 17, 18, 20, 23, 28), and no other service has
  it as effective supervisor (`NoSupervisee`, new with GP v0.8.1's supervisors), then $\Psi_A$ for it
  changes only its own account: every other account, the staging set, the authorizer queue and the
  privileged services are as they were, and it provides nothing. Its only effects on other
  services are the deferred transfers it returns.
* **Refine** (`psiR_noExports`). If a service's code does not name `export` (id 8), $\Psi_R$ returns no
  exported segments. Since GP v0.8.1 (#582) the code is the whole preimage and $Y$ skips its
  metadata, so the hypothesis names `jamHostCallIdsOf` of the preimage itself.

Both depend only on the set of host-call ids in the blob, which is read off the code without
running it.
-/

namespace JAM

open PVM

/-! ## Shared lemmas -/


/-- Inserting at $s$ leaves every other key alone. -/
theorem get?_insert_ne {α : Type} (m : Std.ExtTreeMap Nat α) {s k : Nat} (a : α) (h : k ≠ s) :
    (m.insert s a).get? k = m.get? k := by
  have hne : ¬ compare s k = .eq := fun hc => h (Nat.compare_eq_eq.1 hc).symm
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert, hne, ↓reduceIte]

theorem get?_insert_same {α : Type} (m : Std.ExtTreeMap Nat α) (s : Nat) (a : α) :
    (m.insert s a).get? s = some a := by
  simp only [Std.ExtTreeMap.get?_eq_getElem?, Std.ExtTreeMap.getElem?_insert_self]

/-- The common rules and their body: if the body keeps a confined context confined, so does the
    charged function (on $\infty$ the context is unchanged). -/
theorem charged_ctx {X : Type} (P : X → Prop) (g gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) (hx : P x)
    (hb : P (body ⟨.cont, gas - g, ω, μ, x⟩).ctx) :
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

/-! ## Accumulate -/

/-- The ids of the accumulate host functions that can reach beyond the caller's own account
    regardless of supervision (GP v0.8.1 numbering): `bless`, `assign`, `designate`, `new`,
    `eject`, `provide`. -/
def reachingIds : List Nat := [16, 17, 18, 20, 23, 28]

/-- No service other than $s$ has $s$ as its effective supervisor in $\mathbf{d}$ (GP v0.8.1
    eq. `effectivesupervisor`). -/
def NoSupervisee (d : Accounts) (s : Nat) : Prop := ∀ k, k ≠ s → effectiveSupervisor d k ≠ s

/-- Implications $x$ of service $s$ that leave everything outside $s$'s own account as in $\mathbf{e}$, and
    keep $s$'s creation slot (so that $E(\cdot, k)$ for $k \ne s$ is as in $\mathbf{e}$). -/
def Confined (e : PartialState) (s : Nat) (x : Implications) : Prop :=
  x.id = s ∧ (∀ k, k ≠ s → x.state.accounts.get? k = e.accounts.get? k) ∧
    x.state.staging = e.staging ∧ x.state.authQueue = e.authQueue ∧ x.state.manager = e.manager ∧
    x.state.assigners = e.assigners ∧ x.state.delegator = e.delegator ∧
    x.state.registrar = e.registrar ∧ x.state.alwaysAcc = e.alwaysAcc ∧ x.provisions = ∅ ∧
    ∀ a, x.state.accounts.get? s = some a → ∃ b, e.accounts.get? s = some b ∧ b.created = a.created

/-- Both dimensions of the accumulation context are confined. -/
def ConfinedCtx (e : PartialState) (s : Nat) (c : AccCtx) : Prop :=
  Confined e s c.1 ∧ Confined e s c.2

/-- If $k$'s effective supervisor is $s \ne k$, $k$ names $s$ as supervisor, recorded with $s$'s creation slot. -/
theorem effectiveSupervisor_eq {d : Accounts} {k s : Nat} (h : effectiveSupervisor d k = s)
    (hks : k ≠ s) : ∃ a b, d.get? k = some a ∧ a.supervisor = s ∧ d.get? s = some b ∧
      b.created = a.supervisorCreated := by
  unfold effectiveSupervisor at h
  split at h
  · exact absurd h hks
  · rename_i a ha
    split at h
    · rename_i b hb
      split at h
      · exact ⟨a, b, ha, h, h ▸ hb, by assumption⟩
      · exact absurd h hks
    · exact absurd h hks

/-- A confined context keeps every other service from having $s$ as its effective supervisor. -/
theorem Confined.noSupervisee {e : PartialState} {s : Nat} {x : Implications}
    (hx : Confined e s x) (hn : NoSupervisee e.accounts s) : NoSupervisee x.state.accounts s := by
  intro k hks hk
  obtain ⟨a, b, ha, hsup, hb, hcr⟩ := effectiveSupervisor_eq hk hks
  obtain ⟨_, hko, -, -, -, -, -, -, -, -, hcs⟩ := hx
  obtain ⟨b', hb', hcr'⟩ := hcs b hb
  apply hn k hks
  rw [hko k hks] at ha
  unfold effectiveSupervisor
  rw [ha]
  dsimp only
  rw [hsup, hb']
  dsimp only
  rw [if_pos (by rw [hcr', hcr])]

/-- In a confined context, the accumulating service may modify only its own account. -/
theorem Confined.mayModify_eq {e : PartialState} {s : Nat} {x : Implications}
    (hx : Confined e s x) (hn : NoSupervisee e.accounts s) {d : Nat}
    (hm : AccHost.mayModify x d = true) : d = s := by
  have hid := hx.1
  unfold AccHost.mayModify at hm
  simp only [Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with h | h
  · exact h ▸ hid
  · by_cases hds : d = s
    · exact hds
    · exact absurd (h ▸ hid) (hx.noSupervisee hn d hds)

/-- Replacing $s$'s account by one with the same creation slot keeps a context confined. -/
theorem Confined.insertSelf {e : PartialState} {s : Nat} {x : Implications}
    (hx : Confined e s x) (a b : ServiceAccount) (hb : x.state.accounts.get? s = some b)
    (hc : a.created = b.created) :
    Confined e s { x with state := { x.state with accounts := x.state.accounts.insert s a } } := by
  obtain ⟨hid, hk, h1, h2, h3, h4, h5, h6, h7, h8, hcs⟩ := hx
  refine ⟨hid, fun k hks => ?_, h1, h2, h3, h4, h5, h6, h7, h8, fun a' ha' => ?_⟩
  · simp only [get?_insert_ne _ _ hks]; exact hk k hks
  · simp only [get?_insert_same, Option.some.injEq] at ha'
    obtain ⟨b', hb', hcr⟩ := hcs b hb
    exact ⟨b', hb', by rw [hcr, ← ha', hc]⟩

/-- `putAcct` on $s$ with the same creation slot keeps a context confined. -/
theorem Confined.putSelf {e : PartialState} {s : Nat} {x : Implications}
    (hx : Confined e s x) (a b : ServiceAccount) (hb : x.state.accounts.get? s = some b)
    (hc : a.created = b.created) : Confined e s (AccHost.putAcct x s a) :=
  hx.insertSelf a b hb hc

namespace AccHost

variable {e : PartialState} {s : Nat}

/-- Close a goal `ConfinedCtx e s (…)` for a host function that leaves the context alone in
    every branch, or only writes registers. -/
macro "confined_tac" hc:term : tactic =>
  `(tactic| (
    apply charged_ctx _ _ _ _ _ _ _ $hc
    dsimp only
    (repeat' split) <;> (simp only [r7, panic, updX, ConfinedCtx] at *; first | exact $hc | skip)))

theorem checkpoint_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (checkpoint gas ω μ c).ctx := by
  unfold checkpoint charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  exact ⟨hc.1, hc.1⟩

theorem query_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (query gas ω μ c).ctx := by
  unfold query charge; confined_tac hc

theorem yield_confined (gas : Nat) (ω : Regs) (μ : Memory) (c : AccCtx)
    (hc : ConfinedCtx e s c) : ConfinedCtx e s (yield gas ω μ c).ctx := by
  unfold yield charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  dsimp only
  split
  · exact hc
  · obtain ⟨⟨hid, hk, h1, h2, h3, h4, h5, h6, h7, h8, hcs⟩, h2'⟩ := hc
    exact ⟨⟨hid, hk, h1, h2, h3, h4, h5, h6, h7, h8, hcs⟩, h2'⟩

/-- The common shape of `write`, `upgrade`, `solicit`, `forget`: the account of $d$ is replaced,
    with its creation slot, only when $x_s$ may modify $d$. -/
theorem put_of_mayModify (hn : NoSupervisee e.accounts s) {c : AccCtx} (hc : ConfinedCtx e s c)
    {d : Nat} {a a' : ServiceAccount} (hm : mayModify c.1 d = true)
    (ha : c.1.state.accounts.get? d = some a) (hcr : a'.created = a.created) :
    ConfinedCtx e s (putAcct c.1 d a', c.2) := by
  have hd := hc.1.mayModify_eq hn hm
  subst hd
  exact ⟨hc.1.putSelf a' a ha hcr, hc.2⟩

/-- Close a goal `ConfinedCtx e s (f … c).ctx` for `write`, `upgrade`, `solicit`, `forget`: every
    branch leaves the context alone or replaces $d$'s account under `mayModify`. -/
macro "put_tac" hn:term "," hc:term : tactic =>
  `(tactic| (
    apply charged_ctx _ _ _ _ _ _ _ $hc
    dsimp only
    (repeat' split) <;> (try simp only [r7, panic, updX, Bool.not_eq_true', Bool.not_eq_false] at *) <;>
      first | exact $hc | exact put_of_mayModify $hn $hc ‹_› ‹_› (by first | simp | (subst_vars; simp) | simp_all)))

theorem write_confined (hn : NoSupervisee e.accounts s) (gas : Nat) (ω : Regs) (μ : Memory)
    (c : AccCtx) (hc : ConfinedCtx e s c) : ConfinedCtx e s (write gas ω μ c).ctx := by
  unfold write charge; put_tac hn, hc

theorem upgrade_confined (hn : NoSupervisee e.accounts s) (gas : Nat) (ω : Regs) (μ : Memory)
    (c : AccCtx) (hc : ConfinedCtx e s c) : ConfinedCtx e s (upgrade gas ω μ c).ctx := by
  unfold upgrade charge; put_tac hn, hc

theorem solicit_confined (hn : NoSupervisee e.accounts s) (env : AccEnv) (gas : Nat) (ω : Regs)
    (μ : Memory) (c : AccCtx) (hc : ConfinedCtx e s c) :
    ConfinedCtx e s (solicit env gas ω μ c).ctx := by
  unfold solicit charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  dsimp only
  (repeat' split) <;> (try simp only [r7, panic, updX, Bool.not_eq_true', Bool.not_eq_false] at *) <;>
    first
    | exact hc
    | (rename_i heq _ hm
       exact put_of_mayModify hn hc hm ‹_› (by
         revert heq; split <;> intro heq <;> (try split at heq) <;>
           (try simp only [Option.some.injEq] at heq) <;> (first | (rw [← heq]; simp) | simp at heq)))

theorem forget_confined (hn : NoSupervisee e.accounts s) (env : AccEnv) (gas : Nat) (ω : Regs)
    (μ : Memory) (c : AccCtx) (hc : ConfinedCtx e s c) :
    ConfinedCtx e s (forget env gas ω μ c).ctx := by
  unfold forget charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  dsimp only
  (repeat' split) <;> (try simp only [r7, panic, updX, Bool.not_eq_true', Bool.not_eq_false] at *) <;>
    first
    | exact hc
    | (rename_i heq hm
       exact put_of_mayModify hn hc hm ‹_› (by
         revert heq; split <;> intro heq <;> (try split at heq) <;>
           (try simp only [Option.some.injEq] at heq) <;> (first | (rw [← heq]; simp) | simp at heq)))

theorem supervisor_confined (hn : NoSupervisee e.accounts s) (gas : Nat) (ω : Regs) (μ : Memory)
    (c : AccCtx) (hc : ConfinedCtx e s c) : ConfinedCtx e s (supervisor gas ω μ c).ctx := by
  unfold supervisor charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  dsimp only
  split
  · rename_i a ua ha hua
    split
    · exact hc
    · rename_i hsup
      have hm : mayModify c.1 (tgt (reg ω 7) c.1.id) = true := by
        unfold mayModify; simp only [Bool.or_eq_true, beq_iff_eq]; right
        exact Classical.not_not.mp hsup
      exact put_of_mayModify hn hc hm ha rfl
  · exact hc

/-- An OK from `transferCode` means both permissions held. -/
theorem transferCode_ok {x : Implications} {src dst mode amount l o : Nat}
    (h : transferCode x src dst mode amount l o = Result.OK) :
    transferPs x src mode = true ∧ transferPd x src dst mode o = true := by
  unfold transferCode at h
  dsimp only at h
  split at h
  · simp [Result.WHO, Result.OK] at h
  · split at h
    · simp [Result.HUH, Result.OK] at h
    · rename_i hh
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or] at hh
      exact ⟨by simpa using hh.1.2, by simpa using hh.2⟩

/-- The debit changes only src's account, keeping its creation slot. -/
theorem transferDebit_get?_ne (d : Accounts) (src mode amount k : Nat) (hk : k ≠ src) :
    (transferDebit d src mode amount).get? k = d.get? k := by
  unfold transferDebit; split
  · exact get?_insert_ne _ _ hk
  · rfl

theorem transferCredit_get?_ne (d : Accounts) (dst mode amount o k : Nat) (hk : k ≠ dst) :
    (transferCredit d dst mode amount o).get? k = d.get? k := by
  unfold transferCredit; split
  · rfl
  · split
    · exact get?_insert_ne _ _ hk
    · rfl

theorem transferDebit_created (d : Accounts) (src mode amount : Nat) (a : ServiceAccount)
    (ha : (transferDebit d src mode amount).get? src = some a) :
    ∃ b, d.get? src = some b ∧ b.created = a.created := by
  unfold transferDebit at ha; split at ha
  · rename_i sa hsa
    simp only [get?_insert_same, Option.some.injEq] at ha
    refine ⟨sa, hsa, ?_⟩
    rw [← ha]; split <;> rfl
  · exact ⟨a, by assumption, rfl⟩

theorem transferCredit_created (d : Accounts) (dst mode amount o : Nat) (a : ServiceAccount)
    (ha : (transferCredit d dst mode amount o).get? dst = some a) :
    ∃ b, d.get? dst = some b ∧ b.created = a.created := by
  unfold transferCredit at ha; split at ha
  · exact ⟨a, ha, rfl⟩
  · split at ha
    · rename_i da hda
      simp only [get?_insert_same, Option.some.injEq] at ha
      refine ⟨da, hda, ?_⟩
      rw [← ha]; split <;> rfl
    · exact ⟨a, ha, rfl⟩

theorem transfer_confined (hn : NoSupervisee e.accounts s) (env : AccEnv) (gas : Nat) (ω : Regs)
    (μ : Memory) (c : AccCtx) (hc : ConfinedCtx e s c) :
    ConfinedCtx e s (transfer env gas ω μ c).ctx := by
  unfold transfer charge
  apply charged_ctx _ _ _ _ _ _ _ hc
  dsimp only
  split
  · exact hc
  · rename_i c' t' hcode ht
    split
    · exact hc
    · rename_i hok
      have hc' : c' = Result.OK := Classical.not_not.mp hok
      simp only [Option.map_eq_some_iff] at hcode
      obtain ⟨_, -, hcode⟩ := hcode
      obtain ⟨hps, hpd⟩ := transferCode_ok (hcode.trans hc')
      have hid := hc.1.1
      -- the source is s
      have hsrc : tgt (reg ω 7) c.1.id = s := by
        unfold transferPs at hps
        split at hps
        · exact hc.1.mayModify_eq hn hps
        · simp only [beq_iff_eq] at hps
          by_cases h : tgt (reg ω 7) c.1.id = s
          · exact h
          · exact absurd (hps ▸ hid) (hc.1.noSupervisee hn _ h)
      -- with o = 0 the destination is s too
      have hdst : reg ω 12 = 0 → tgt (reg ω 8) c.1.id = s := by
        intro h0
        unfold transferPd at hpd
        simp only [h0, ne_eq, not_true_eq_false, decide_false, Bool.false_or, Bool.and_eq_true]
          at hpd
        exact hc.1.mayModify_eq hn hpd.1
      simp only [r7, updX]
      refine ⟨?_, hc.2⟩
      obtain ⟨_, hk, h1, h2, h3, h4, h5, h6, h7, h8, hcs⟩ := hc.1
      refine ⟨hid, fun k hks => ?_, h1, h2, h3, h4, h5, h6, h7, h8, fun a ha => ?_⟩
      · by_cases h0 : reg ω 12 = 0
        · rw [transferCredit_get?_ne _ _ _ _ _ _ (by rw [hdst h0]; exact hks),
            transferDebit_get?_ne _ _ _ _ _ (by rw [hsrc]; exact hks)]
          exact hk k hks
        · simp only [transferCredit, ne_eq, h0, not_false_eq_true, ↓reduceIte]
          rw [transferDebit_get?_ne _ _ _ _ _ (by rw [hsrc]; exact hks)]
          exact hk k hks
      · by_cases h0 : reg ω 12 = 0
        · rw [← hdst h0] at ha
          obtain ⟨b, hb, hbc⟩ := transferCredit_created _ _ _ _ _ a ha
          rw [hdst h0, ← hsrc] at hb
          obtain ⟨b', hb', hbc'⟩ := transferDebit_created _ _ _ _ b hb
          rw [hsrc] at hb'
          obtain ⟨b'', hb'', hbc''⟩ := hcs b' hb'
          exact ⟨b'', hb'', by rw [hbc'', hbc', hbc]⟩
        · simp only [transferCredit, ne_eq, h0, not_false_eq_true, ↓reduceIte] at ha
          rw [← hsrc] at ha
          obtain ⟨b, hb, hbc⟩ := transferDebit_created _ _ _ _ a ha
          rw [hsrc] at hb
          obtain ⟨b', hb', hbc'⟩ := hcs b hb
          exact ⟨b', hb', by rw [hbc', hbc]⟩
  · exact hc

/-- **The accumulate dispatcher keeps a service confined**, for every id outside `reachingIds`,
    while no other service has it as effective supervisor. -/
theorem dispatch_confined (hn : NoSupervisee e.accounts s) (env : AccEnv) (n gas : Nat)
    (ω : Regs) (μ : Memory) (c : AccCtx) (hnr : n ∉ reachingIds) (hc : ConfinedCtx e s c) :
    ConfinedCtx e s (dispatch env n gas ω μ c).ctx := by
  unfold dispatch
  split
  · exact charged_ctx _ _ _ _ _ _ _ hc hc
  · unfold hostGrowHeap; exact charged_ctx _ _ _ _ _ _ _ hc hc
  · exact charged_ctx _ _ _ _ _ _ _ hc (by rw [writeValue_ctx]; exact hc)
  · exact charged_ctx _ _ _ _ _ _ _ hc (by rw [writeValue_ctx]; exact hc)
  · exact charged_ctx _ _ _ _ _ _ _ hc (by rw [writeValue_ctx]; exact hc)
  · exact write_confined hn gas ω μ c hc
  · exact charged_ctx _ _ _ _ _ _ _ hc (by rw [writeValue_ctx]; exact hc)
  · simp [reachingIds] at hnr
  · simp [reachingIds] at hnr
  · simp [reachingIds] at hnr
  · exact checkpoint_confined gas ω μ c hc
  · simp [reachingIds] at hnr
  · exact upgrade_confined hn gas ω μ c hc
  · exact transfer_confined hn env gas ω μ c hc
  · simp [reachingIds] at hnr
  · exact query_confined gas ω μ c hc
  · exact solicit_confined hn env gas ω μ c hc
  · exact forget_confined hn env gas ω μ c hc
  · exact yield_confined gas ω μ c hc
  · simp [reachingIds] at hnr
  · exact supervisor_confined hn gas ω μ c hc
  · split <;> exact hc

end AccHost

/-- A partial state that agrees with $\mathbf{e}$ everywhere except possibly $s$'s own account. -/
def Outside (e : PartialState) (s : Nat) (st : PartialState) : Prop :=
  (∀ k, k ≠ s → st.accounts.get? k = e.accounts.get? k) ∧ st.staging = e.staging ∧
    st.authQueue = e.authQueue ∧ st.manager = e.manager ∧ st.assigners = e.assigners ∧
    st.delegator = e.delegator ∧ st.registrar = e.registrar ∧ st.alwaysAcc = e.alwaysAcc

theorem Confined.outside {e st : PartialState} {s : Nat} {x : Implications}
    (hst : Outside e s st) (hx : Confined st s x) : Outside e s x.state ∧ x.provisions = ∅ := by
  obtain ⟨hk0, g1, g2, g3, g4, g5, g6, g7⟩ := hst
  obtain ⟨_, hk, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hx
  exact ⟨⟨fun k hks => (hk k hks).trans (hk0 k hks), h1.trans g1, h2.trans g2, h3.trans g3,
    h4.trans g4, h5.trans g5, h6.trans g6, h7.trans g7⟩, h8⟩

/-- $\Psi_A$'s run, from a starting state that differs from $\mathbf{e}$ at most in $s$'s account, in which no
    other service has $s$ as effective supervisor. -/
theorem psiARun_confined (params : Params) (entropy : List UInt8) (e st : PartialState)
    (t s g : Nat) (inputs : List AccumulateInput) (m : Std.ExtTreeSet Nat) (code : ByteArray)
    (hst : Outside e s st) (hn : NoSupervisee st.accounts s)
    (hcode : (st.accounts.get? s).bind (·.code) = some code)
    (hids : ∀ h ∈ jamHostCallIdsOf code, h ∉ reachingIds) :
    Outside e s (psiARun params entropy st t s g inputs m).state ∧
      (psiARun params entropy st t s g inputs m).provisions = ∅ := by
  unfold psiARun
  dsimp only
  rw [hcode]
  dsimp only
  split
  · exact ⟨hst, rfl⟩
  · have conf_init : Confined st s (initImplications st s t entropy m) :=
      ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        fun a ha => ⟨a, ha, rfl⟩⟩
    have hinv := psiM_ctx_inv code 5 (UInt64.ofNat g)
      ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
      (initImplications st s t entropy m, initImplications st s t entropy m) (ConfinedCtx st s)
      (accHostFn { params, slot := t, entropy, inputs, code })
      (fun h hh _ _ _ x hx => by
        simp only [accHostFn]
        exact AccHost.dispatch_confined hn _ h _ _ _ x (hids h hh) hx)
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

/-- **Accumulate confinement** (GP v0.8.1). If service $s$'s code names none of `bless`, `assign`,
    `designate`, `new`, `eject`, `provide`, and in $\mathbf{e}$ no other service has $s$ as its effective
    supervisor (`NoSupervisee`, GP v0.8.1 eq. `effectivesupervisor`), then $\Psi_A$ for $s$ leaves every
    other account, the staging set, the authorizer queue and the privileged services as they were
    in $\mathbf{e}$, and provides nothing.

    The `NoSupervisee` hypothesis is new with GP v0.8.1 (Adam, 2026-11-25): a service may change
    any service it effectively supervises through `write`, `upgrade`, `solicit`, `forget`,
    `transfer` and `supervisor`. -/
theorem psiA_confined (params : Params) (entropy : List UInt8) (e : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) (a : ServiceAccount) (code : ByteArray)
    (ha : e.accounts.get? s = some a) (hcode : a.code = some code)
    (hn : NoSupervisee e.accounts s)
    (hids : ∀ h ∈ jamHostCallIdsOf code, h ∉ reachingIds) :
    Outside e s (psiA params entropy e t s g inputs).state ∧
      (psiA params entropy e t s g inputs).provisions = ∅ := by
  simp only [psiA, ha]
  refine psiARun_confined params entropy e _ t s g inputs _ code ?_ ?_ ?_ hids
  · exact ⟨fun k hks => get?_insert_ne _ _ hks, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro k hks hk
    obtain ⟨a', b, ha', hsup, hb, hcr⟩ := effectiveSupervisor_eq hk hks
    simp only [get?_insert_ne _ _ hks] at ha'
    simp only [get?_insert_same, Option.some.injEq] at hb
    apply hn k hks
    unfold effectiveSupervisor
    rw [ha']; dsimp only; rw [hsup, ha]; dsimp only
    rw [if_pos (by rw [← hcr, ← hb])]
  · simp only [get?_insert_same, Option.bind_some]
    exact hcode


/-! ## Refine -/

namespace RefineHost

/-- Close `(f …).ctx.2.2 = c.2.2` (the exports) by splitting every case of a refine host function. -/
macro "exports_tac" c:term : tactic =>
  `(tactic| (
    dsimp only
    apply charged_ctx (fun c' : RefineCtx => c'.2.2 = ($c).2.2) _ _ _ _ _ _ rfl
    dsimp only
    (repeat' split) <;> (simp only [r7, panic]) <;> rfl))

theorem invoke_exports (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) :
    (invoke gas ω μ c).ctx.2.2 = c.2.2 := by
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
    (hn : n ≠ 8) (hc : c.2.2 = []) : (dispatch env n gas ω μ c).ctx.2.2 = [] := by
  rw [← hc]
  unfold dispatch
  split
  · exact charged_ctx (fun c' : RefineCtx => c'.2.2 = c.2.2) _ _ _ _ _ _ rfl rfl
  · unfold hostGrowHeap; exact charged_ctx (fun c' : RefineCtx => c'.2.2 = c.2.2) _ _ _ _ _ _ rfl rfl
  · exact charged_ctx (fun c' : RefineCtx => c'.2.2 = c.2.2) _ _ _ _ _ _ rfl (by rw [writeValue_ctx])
  · unfold historicalLookup
    exact charged_ctx (fun c' : RefineCtx => c'.2.2 = c.2.2) _ _ _ _ _ _ rfl (by rw [writeValue_ctx])
  · exact absurd rfl hn
  · unfold compile; exports_tac c
  · unfold machine; exports_tac c
  · unfold peek; exports_tac c
  · unfold poke; exports_tac c
  · unfold pages; exports_tac c
  · exact invoke_exports gas ω μ c
  · unfold expunge; exports_tac c
  · unfold unknown; split <;> rfl

end RefineHost

/-- $\Psi_M$ under the refine dispatcher, for code that does not name `export`, exports nothing. -/
theorem refine_psiM_noExports (env : RefineHost.Env) (code : ByteArray) (gas : UInt64)
    (a : ByteArray) (h8 : 8 ∉ jamHostCallIdsOf code) :
    (psiM code 0 gas a (toHostFn (RefineHost.dispatch env)) ((∅, ∅, []) : RefineCtx)).2.2.2.2 = [] :=
  psiM_ctx_inv code 0 gas a ((∅, ∅, []) : RefineCtx) (fun c => c.2.2 = [])
    (toHostFn (RefineHost.dispatch env))
    (fun h hh g ω μ x hx => by
      have hne : h ≠ 8 := fun he => h8 (he ▸ hh)
      simp only [toHostFn]
      exact RefineHost.dispatch_exports _ h g.toNat ω μ x hne hx) rfl

/-- **Refine exports nothing without `export`.** If the code of the service a work item names does
    not name `export`, $\Psi_R$ returns no exported segments. -/
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
        have hinv : res.2.2.2.2 = [] := by
          rw [← hres]; exact refine_psiM_noExports _ _ _ _ h8
        obtain ⟨u, o, m, P, ex⟩ := res
        simp only at hinv ⊢
        split <;> simp [hinv]

end JAM
