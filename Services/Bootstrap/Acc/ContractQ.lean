import Services.Bootstrap.Acc.Contract

/-!
# The accumulate contract with an answer queue for `gas` and `checkpoint`

Two of Ψ_A's host functions put the gas left in ω₇ (GP v0.8.0 eq. `accinvocation`): Ω_G (`gas`, id
0) and Ω_C (`checkpoint`, id 18). The gas left is not known to a gas-free run, and bootstrap reads
the value after `gas` (it is printed, `format!`), so the contract cannot fix it. Instead the
context carries a queue of answers: `AccCtxQ = AccCtx × List Nat`.

`accContractQ env`:
* at a gas-independent id (`AccGasFreeId`): the model's outcome at some gas g, not ∞, with the
  queue kept. All such outcomes agree (`dispatch_sameButGas`), so the contract is deterministic;
* at id 0 or 18: the call continues, memory kept, ω₇ := the queue's head v (the queue drops it),
  y := x at 18 (Ω_C), context kept at 0.

Given its queue a run is determined, and `psiM_of_freeRunH_accQ` lifts it: the real Ψ_M run is a
run under `accContractQ` for the queue of gas values actually left at its `gas` and `checkpoint`
calls. A statement proved for every queue therefore holds of Ψ_M, and the queue does not appear in
it.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- The accumulate context with a queue of answers for `gas` and `checkpoint`. -/
abbrev AccCtxQ := AccCtx × List Nat

/-- **The accumulate contract with an answer queue** (see the module docstring). -/
def accContractQ (env : AccEnv) : HostRel AccCtxQ :=
  fun h ω μ xq s ω' μ' xq' =>
    (AccGasFreeId h ∧ s ≠ .oog ∧ xq'.2 = xq.2 ∧
      ∃ g, accHostFn env h g ω μ xq.1 = ⟨s, (accHostFn env h g ω μ xq.1).gas, ω', μ', xq'.1⟩) ∨
    ((h = 0 ∨ h = 18) ∧ s = .cont ∧ μ' = μ ∧
      xq'.1 = (if h = 18 then (xq.1.1, xq.1.1) else xq.1) ∧
      ∃ v, xq.2 = v :: xq'.2 ∧ ω' = setR7 ω v)

/-- The handler's outcomes, at any gas. -/
def accGraph (env : AccEnv) : HostRel AccCtx :=
  fun h ω μ x s ω' μ' x' => ∃ g, accHostFn env h g ω μ x = ⟨s, (accHostFn env h g ω μ x).gas, ω', μ', x'⟩

/-- Ω_G and Ω_C continue only with ω₇ := the gas left, memory kept, and the context kept (Ω_G) or
    y := x (Ω_C); otherwise they end in ∞. -/
theorem gasCk_outcome (env : AccEnv) {h : Nat} (hh : h = 0 ∨ h = 18) (g : UInt64) (ω : Regs) (μ : Memory)
    (x : AccCtx) :
    (accHostFn env h g ω μ x).status = .oog ∨
      ((accHostFn env h g ω μ x).status = .cont ∧ (accHostFn env h g ω μ x).mem = μ ∧
        (accHostFn env h g ω μ x).ctx = (if h = 18 then (x.1, x.1) else x) ∧
        ∃ v, (accHostFn env h g ω μ x).regs = setR7 ω v) := by
  rcases hh with rfl | rfl
  · simp only [accHostFn, AccHost.dispatch, hostGas, charged]
    split <;> simp; exact ⟨_, rfl⟩
  · simp only [accHostFn, AccHost.dispatch, AccHost.checkpoint, AccHost.charge, charged]
    split <;> simp; exact ⟨_, rfl⟩

theorem toStatus_ne_oog {s : PVM.HostStatus} (h : s.toStatus ≠ Status.oog) : s ≠ PVM.HostStatus.oog := by
  rintro rfl; exact h rfl

/-- **A run of the handler's outcomes is a run under `accContractQ`**, for the queue of the values
    its `gas` and `checkpoint` calls put in ω₇, when it does not end in ∞. -/
theorem FreeRunH.toQ (env : AccEnv) {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {x : AccCtx}
    {ε : Status} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    (hrun : FreeRunH p (accGraph env) i ω μ x ε ω' μ' x') (hε : ε ≠ .oog) :
    ∃ qs, FreeRunH p (accContractQ env) i ω μ (x, qs) ε ω' μ' (x', []) := by
  induction hrun with
  | exit hr hh => exact ⟨[], .exit hr hh⟩
  | @host i ω μ x h e ω₁ μ₁ ω₂ μ₂ x₂ ε ω₃ μ₃ x₃ hr hR _ ih =>
    obtain ⟨qs, hq⟩ := ih hε
    obtain ⟨g, hg⟩ := hR
    by_cases hgf : AccGasFreeId h.toNat
    · exact ⟨qs, .host (x'' := (x₂, qs)) hr (.inl ⟨hgf, by simp, rfl, g, by simpa using hg⟩) hq⟩
    · have h018 : h.toNat = 0 ∨ h.toNat = 18 := by unfold AccGasFreeId at hgf; omega
      rcases gasCk_outcome env h018 g ω₁ μ₁ x with ho | ⟨hs, hm, hx, v, hv⟩
      · rw [hg] at ho; simp at ho
      · rw [hg] at hs hm hx hv
        simp only at hs hm hx hv
        exact ⟨v :: qs, .host (x'' := (x₂, qs)) hr (.inr ⟨h018, rfl, hm, hx, v, rfl, hv⟩) hq⟩
  | @hostStop i ω μ x h e ω₁ μ₁ s ω₂ μ₂ x₂ hr hR hs =>
    obtain ⟨g, hg⟩ := hR
    by_cases hgf : AccGasFreeId h.toNat
    · exact ⟨[], .hostStop (x'' := (x₂, [])) hr (.inl ⟨hgf, toStatus_ne_oog hε, rfl, g, by simpa using hg⟩) hs⟩
    · have h018 : h.toNat = 0 ∨ h.toNat = 18 := by unfold AccGasFreeId at hgf; omega
      rcases gasCk_outcome env h018 g ω₁ μ₁ x with ho | ⟨hs', -⟩
      · rw [hg] at ho; simp only at ho; subst ho; exact absurd rfl hε
      · rw [hg] at hs'; exact absurd hs' hs

/-- **Ψ_M from a run under `accContractQ`.** If Ψ_M (with Ψ_A's handler `accHostFn env`) does not
    end in ∞ and Y succeeds, its output and context are those of a gas-free run under
    `accContractQ env` from Y's initial state, for some queue of answers. A statement proved for
    runs under `accContractQ env` for every queue (the handler summaries are) therefore holds of
    Ψ_M without mentioning the queue: it is the queue of gas values left at the `gas` and
    `checkpoint` calls, which no statement needs to name. -/
theorem psiM_of_freeRunH_accQ (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray)
    (x : AccCtx) (env : AccEnv) {p : ByteArray} {ω : Regs} {μ : Memory}
    (hY : standardInit b a = some (p, ω, μ)) :
    (psiM b i gas a (accHostFn env) x).2.1.isOog = true ∨
      ∃ qs ε ω' μ' x', FreeRunH p (accContractQ env) i ω μ (x, qs) ε ω' μ' (x', []) ∧
        (psiM b i gas a (accHostFn env) x).2 = (freeOutput ε ω' μ', x') := by
  cases hno : (psiM b i gas a (accHostFn env) x).2.1.isOog
  · right
    have hresp : (accHostFn env).Respects (accGraph env) := fun h g ω μ x => ⟨g, rfl⟩
    rcases psiM_free b i gas a x (accGraph env) (accHostFn env) (accHostFn_gasNonIncreasing env)
      hresp hno with ⟨hY', _⟩ | ⟨p', ω₀, μ₀, ε, ω', μ', x', hY', hrun, hout⟩
    · rw [hY] at hY'; cases hY'
    · rw [hY] at hY'; cases hY'
      have hε : ε ≠ .oog := by
        intro he; rw [hout] at hno; simp [freeOutput, he, InvOutput.isOog] at hno
      obtain ⟨qs, hq⟩ := FreeRunH.toQ env hrun hε
      exact ⟨qs, ε, ω', μ', x', hq, hout⟩
  · left; rfl

/-- **`accContractQ` is deterministic**: two steps it allows from the same state (and queue) are
    the same. At a gas-independent id the model's non-∞ outcomes agree at every gas
    (`dispatch_sameButGas`); at 0 and 18 the answer is the queue's head. So `FreeRunH.det` applies to
    runs under it. -/
theorem accContractQ_pins (env : AccEnv) : (accContractQ env).Pins (accContractQ env) := by
  intro h ω μ xq s₁ ω₁ μ₁ xq₁ s₂ ω₂ μ₂ xq₂ h₁ h₂
  rcases h₁ with ⟨hh, hs₁, hq₁, g₁, he₁⟩ | ⟨h018, rfl, rfl, hx₁, v₁, hv₁, rfl⟩ <;>
    rcases h₂ with ⟨hh', hs₂, hq₂, g₂, he₂⟩ | ⟨h018', rfl, rfl, hx₂, v₂, hv₂, rfl⟩
  · simp only [accHostFn, HostResult.mk.injEq] at he₁ he₂
    obtain ⟨e1s, -, e1r, e1m, e1c⟩ := he₁
    obtain ⟨e2s, -, e2r, e2m, e2c⟩ := he₂
    have n₁ : (AccHost.dispatch env h g₁.toNat ω μ xq.1).status ≠ .oog := by
      intro hc; apply hs₁; rw [← e1s, hc]
    have n₂ : (AccHost.dispatch env h g₂.toNat ω μ xq.1).status ≠ .oog := by
      intro hc; apply hs₂; rw [← e2s, hc]
    obtain ⟨a, b, c, d⟩ := AccHost.dispatch_sameButGas env hh ω μ xq.1 n₁ n₂
    refine ⟨e1s ▸ e2s ▸ a, e1r ▸ e2r ▸ b, e1m ▸ e2m ▸ c, Prod.ext (e1c ▸ e2c ▸ d) (hq₁.trans hq₂.symm)⟩
  · exfalso; unfold AccGasFreeId at hh; omega
  · exfalso; unfold AccGasFreeId at hh'; omega
  · rw [hv₁] at hv₂
    obtain ⟨rfl, hq⟩ := List.cons.inj hv₂
    exact ⟨rfl, rfl, rfl, Prod.ext (hx₁.trans hx₂.symm) hq⟩

/-- Chains under one contract are chains under another with a mapped context, when each
    continuing step maps to an allowed one. -/
theorem FreeStepsH.mapCtx {X Y : Type} {p : ByteArray} {R : HostRel X} {R' : HostRel Y} (f : X → Y)
    (hR : ∀ h ω μ x ω' μ' x', R h ω μ x .cont ω' μ' x' → R' h ω μ (f x) .cont ω' μ' (f x'))
    {i ω μ x i' ω' μ' x' n} (hs : FreeStepsH p R i ω μ x i' ω' μ' x' n) :
    FreeStepsH p R' i ω μ (f x) i' ω' μ' (f x') n := by
  induction hs with
  | refl => exact .refl
  | pad _ ih => exact .pad ih
  | next hn hc _ ih => exact .next hn hc ih
  | host hP hc hs hr _ ih => exact .host hP hc hs (hR _ _ _ _ _ _ _ hr) ih

/-- A step `accContractK cap` allows is one `accContractQ` allows, the queue kept. -/
theorem accContractK_toQ (cap : Nat) (env : AccEnv) (q : List Nat) {h : Nat} {ω : Regs} {μ : Memory}
    {x : AccCtx} {s : PVM.HostStatus} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    (hk : accContractK cap env h ω μ x s ω' μ' x') : accContractQ env h ω μ (x, q) s ω' μ' (x', q) :=
  .inl ⟨hk.1, hk.2.1, rfl, UInt64.ofNat cap, hk.2.2⟩

/-- **A chain under `accContractK cap` is one under `accContractQ`** for every queue, kept: the
    summaries that make no `gas` or `checkpoint` call carry over unchanged. -/
theorem FreeStepsH.toQ (cap : Nat) (env : AccEnv) (q : List Nat) {p : ByteArray}
    {i : Nat} {ω : Regs} {μ : Memory} {x : AccCtx} {i' : Nat} {ω' : Regs} {μ' : Memory} {x' : AccCtx}
    {n : Nat} (hs : FreeStepsH p (accContractK cap env) i ω μ x i' ω' μ' x' n) :
    FreeStepsH p (accContractQ env) i ω μ (x, q) i' ω' μ' (x', q) n :=
  FreeStepsH.mapCtx (R := accContractK cap env) (fun x => (x, q))
    (fun _ _ _ _ _ _ _ hk => accContractK_toQ cap env q hk) hs

/-- **A `checkpoint` step** under `accContractQ`: at an `ecalli 18`, ω₇ := the queue's head v, which
    the queue drops, memory kept, y := x. -/
theorem FreeStepsH.checkpointQ (env : AccEnv) {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs}
    {μ : Memory} {x : AccCtx} (v : Nat) (qs : List Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtxQ} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 18) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accContractQ env) n (setR7 ω v) μ ((x.1, x.1), qs) i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractQ env) i ω μ (x, v :: qs) i'' ω'' μ'' x'' (k + 1) :=
  FreeStepsH.host_decode hd (.inr ⟨Or.inr rfl, rfl, rfl, by simp, v, rfl, rfl⟩) rest

/-- **A `gas` step** under `accContractQ`: at an `ecalli 0`, ω₇ := the queue's head v, which the
    queue drops, memory and context kept. -/
theorem FreeStepsH.gasQ (env : AccEnv) {p : ByteArray} {P : Program} {i n : Nat} {ω : Regs}
    {μ : Memory} {x : AccCtx} (v : Nat) (qs : List Nat)
    {i'' : Nat} {ω'' : Regs} {μ'' : Memory} {x'' : AccCtxQ} {k : Nat}
    (hd : deblob p i = some P ∧ P.decode i = some (.oneImm .ecalli 0) ∧ P.next i = n ∧
      P.blockCost (P.blockStartOf i) ≤ stepCostCap)
    (rest : FreeStepsH p (accContractQ env) n (setR7 ω v) μ (x, qs) i'' ω'' μ'' x'' k) :
    FreeStepsH p (accContractQ env) i ω μ (x, v :: qs) i'' ω'' μ'' x'' (k + 1) :=
  FreeStepsH.host_decode hd (.inr ⟨Or.inl rfl, rfl, rfl, by simp, v, rfl, rfl⟩) rest

end Services.Bootstrap.Acc
