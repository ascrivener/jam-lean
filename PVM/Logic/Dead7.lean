import PVM.Logic.Det
import PVM.Theorems.Host
import PVM.Theorems.HostIds
import PVM.Logic.FastCheck

/-!
# Host calls whose ω₇ the program ignores

`psiM_of_freeRunH` lifts a gas-free run to Ψ_M (GP §A.8) when the run's contract *pins down* the
real handler: every non-∞ outcome the handler can produce is the one the contract allows. A host
call that reports the gas left in ω₇ cannot be pinned down that way. Examples are Ψ_A's
`checkpoint` (Ω_C, GP v0.8.0 eq. `accinvocation`) and `gas` (Ω_G). A program that overwrites ω₇
before reading it does not see the difference.

This file lifts such runs.
- `Dead7 p i`: whatever ω₇ holds at index i, the run from i ends the same way, up to Ψ_M's output.
  The step at i either does not depend on ω₇ (`kill`, e.g. `load_imm ω₇`), or passes it along
  untouched to an index where it is dead (`pass`).
- `HostRel.PinsExcept7 K R₁ R₂`: `R₁` pins down `R₂`, except that at the ids in `K` a continuing
  outcome may differ in ω₇.
- `FreeRunH.det7`: two runs, one under each contract, from the same state, end with the same
  status, context and Ψ_M output. This needs ω₇ to be dead after every `ecalli k`, k ∈ `K`, in the
  program (`Program.ecalliSites`, a syntactic scan as `Program.hostCallIds`).
- `psiM_of_freeRunH7`: the lift to Ψ_M.
-/

namespace PVM

variable {X : Type}

/-- ω and ω' agree except perhaps at ω₇. -/
def Agree7 (ω ω' : Regs) : Prop := ω.set 7 0 = ω'.set 7 0

theorem Agree7.symm {ω ω' : Regs} (h : Agree7 ω ω') : Agree7 ω' ω := Eq.symm h

/-- The exits whose Ψ_M output is ☇ whatever the registers and memory (`freeOutput`): ☇ and F. -/
def Status.Quiet : Status → Prop
  | .panic => True
  | .fault _ => True
  | _ => False

theorem freeOutput_quiet {ε : Status} (h : ε.Quiet) (ω ω' : Regs) (μ μ' : Memory) :
    freeOutput ε ω μ = freeOutput ε ω' μ' := by
  cases ε <;> simp_all [Status.Quiet, freeOutput]

/-- **ω₇ is dead at index i** of the blob `p`: the run from i does not depend on ω₇, except
    through an exit whose output is ☇ anyway.
    - `kill`: the gas-free step at i gives the same result whatever ω₇ is (as `load_imm ω₇`, or a
      load into ω₇), except for the registers of a ☇ or F exit (Ψ_M's output is ☇ whatever they
      are); and it is not a host call.
    - `pass`: the step at i gives results that agree except at ω₇. It continues to an index where
      ω₇ is dead (which may depend on the state, as after a branch), or exits with ☇ or F. -/
inductive Dead7 (p : ByteArray) : Nat → Prop where
  | kill {i : Nat} {P : Program} : deblob p i = some P →
      (∀ ω ω' μ, Agree7 ω ω' →
        (P.freeStep i ω μ).1 = (P.freeStep i ω' μ).1 ∧
        (P.freeStep i ω μ).2.1 = (P.freeStep i ω' μ).2.1 ∧
        (P.freeStep i ω μ).2.2.2 = (P.freeStep i ω' μ).2.2.2 ∧
        ((P.freeStep i ω μ).1 = .cont ∨ (P.freeStep i ω μ).1 = .halt →
          (P.freeStep i ω μ).2.2.1 = (P.freeStep i ω' μ).2.2.1)) →
      (∀ ω μ, (∀ h, (P.freeStep i ω μ).1 ≠ .host h) ∧ (P.freeStep i ω μ).1 ≠ .oog) → Dead7 p i
  | pass {i : Nat} {P : Program} : deblob p i = some P →
      (∀ ω ω' μ, Agree7 ω ω' →
        (P.freeStep i ω μ).1 = (P.freeStep i ω' μ).1 ∧
        (P.freeStep i ω μ).2.1 = (P.freeStep i ω' μ).2.1 ∧
        Agree7 (P.freeStep i ω μ).2.2.1 (P.freeStep i ω' μ).2.2.1 ∧
        (P.freeStep i ω μ).2.2.2 = (P.freeStep i ω' μ).2.2.2) →
      (∀ ω μ, (P.freeStep i ω μ).1 = .cont ∨ (P.freeStep i ω μ).1.Quiet) →
      (∀ ω μ, (P.freeStep i ω μ).1 = .cont → Dead7 p (P.freeStep i ω μ).2.1) → Dead7 p i

/-- Registers that agree except at ω₇ are the first with ω₇ set to the second's. -/
theorem Agree7.eq_set {ω ω' : Regs} (h : Agree7 ω ω') : ω' = ω.set 7 ω'[7] := by
  apply Vector.ext
  intro j hj
  by_cases hj7 : j = 7
  · subst hj7; simp
  · have := congrArg (fun v : Regs => v[j]) h
    simp only [Vector.getElem_set, Ne.symm hj7, ↓reduceIte] at this
    simp [Ne.symm hj7, this]

theorem agree7_set (ω : Regs) (v : UInt64) : Agree7 ω (ω.set 7 v) := by
  unfold Agree7; rw [Vector.set_set]

/-- `Dead7.kill` from the step at ω with ω₇ set to anything. -/
theorem Dead7.kill_of {p : ByteArray} {i : Nat} {P : Program} (hP : deblob p i = some P)
    (hk : ∀ ω μ v, P.freeStep i (ω.set 7 v) μ = P.freeStep i ω μ)
    (hnh : ∀ ω μ, (∀ h, (P.freeStep i ω μ).1 ≠ .host h) ∧ (P.freeStep i ω μ).1 ≠ .oog) :
    Dead7 p i :=
  .kill hP (fun ω ω' μ ha => by rw [ha.eq_set, hk]; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩) hnh

/-- `Dead7.kill` from the step at ω with ω₇ set to anything: the same status, index and memory,
    and the same registers unless the step exits with ☇ or F (which may keep the registers from
    before). -/
theorem Dead7.kill_of' {p : ByteArray} {i : Nat} {P : Program} (hP : deblob p i = some P)
    (hk : ∀ ω μ v, (P.freeStep i (ω.set 7 v) μ).1 = (P.freeStep i ω μ).1 ∧
      (P.freeStep i (ω.set 7 v) μ).2.1 = (P.freeStep i ω μ).2.1 ∧
      (P.freeStep i (ω.set 7 v) μ).2.2.2 = (P.freeStep i ω μ).2.2.2 ∧
      ((P.freeStep i ω μ).1 = .cont ∨ (P.freeStep i ω μ).1 = .halt →
        (P.freeStep i (ω.set 7 v) μ).2.2.1 = (P.freeStep i ω μ).2.2.1))
    (hnh : ∀ ω μ, (∀ h, (P.freeStep i ω μ).1 ≠ .host h) ∧ (P.freeStep i ω μ).1 ≠ .oog) :
    Dead7 p i :=
  .kill hP (fun ω ω' μ ha => by
    rw [ha.eq_set]
    obtain ⟨a, b, c, d⟩ := hk ω μ ω'[7]
    exact ⟨a.symm, b.symm, c.symm, fun h => (d h).symm⟩) hnh

/-- `Dead7.pass` from the step at ω with ω₇ set to anything: the same result, with ω₇ set. -/
theorem Dead7.pass_of {p : ByteArray} {i : Nat} {P : Program} (hP : deblob p i = some P)
    (hp : ∀ ω μ v, P.freeStep i (ω.set 7 v) μ =
      ((P.freeStep i ω μ).1, (P.freeStep i ω μ).2.1, (P.freeStep i ω μ).2.2.1.set 7 v,
        (P.freeStep i ω μ).2.2.2))
    (hc : ∀ ω μ, (P.freeStep i ω μ).1 = .cont ∨ (P.freeStep i ω μ).1.Quiet)
    (hd : ∀ ω μ, (P.freeStep i ω μ).1 = .cont → Dead7 p (P.freeStep i ω μ).2.1) : Dead7 p i :=
  .pass hP (fun ω ω' μ ha => by
    rw [ha.eq_set, hp]; exact ⟨rfl, rfl, agree7_set _ _, rfl⟩) hc hd

/-- `Dead7.pass_of` with the indices the step can continue to listed, each with ω₇ dead. -/
theorem Dead7.pass_to {p : ByteArray} {i : Nat} {P : Program} (js : List Nat)
    (hP : deblob p i = some P)
    (hp : ∀ ω μ v, P.freeStep i (ω.set 7 v) μ =
      ((P.freeStep i ω μ).1, (P.freeStep i ω μ).2.1, (P.freeStep i ω μ).2.2.1.set 7 v,
        (P.freeStep i ω μ).2.2.2))
    (hc : ∀ ω μ, (P.freeStep i ω μ).1 = .cont ∨ (P.freeStep i ω μ).1.Quiet)
    (hn : ∀ ω μ, (P.freeStep i ω μ).1 = .cont → (P.freeStep i ω μ).2.1 ∈ js)
    (hjs : ∀ j ∈ js, Dead7 p j) : Dead7 p i :=
  Dead7.pass_of hP hp hc (fun ω μ h => hjs _ (hn ω μ h))

/-- Two states at index i, as `det7` compares them: equal, or ω₇ dead and the registers equal
    except at ω₇. -/
def Same7 (p : ByteArray) (i : Nat) (ω ω' : Regs) : Prop := ω = ω' ∨ (Dead7 p i ∧ Agree7 ω ω')

/-- **Gas-free runs from states that differ only in a dead ω₇** end with the same status, and
    with the same index, registers and memory unless that status is ☇ or F. -/
theorem FreeRun.det7 {p : ByteArray} {i : Nat} {ω₁ ω₂ : Regs} {μ : Memory} {ε₁ ε₂ : Status}
    {e₁ e₂ : Nat} {ω₁' ω₂' : Regs} {μ₁' μ₂' : Memory} (hs : Same7 p i ω₁ ω₂)
    (h₁ : FreeRun p i ω₁ μ ε₁ e₁ ω₁' μ₁') (h₂ : FreeRun p i ω₂ μ ε₂ e₂ ω₂' μ₂') :
    ε₁ = ε₂ ∧ ((e₁ = e₂ ∧ ω₁' = ω₂' ∧ μ₁' = μ₂') ∨ ε₁.Quiet) := by
  induction h₁ generalizing ω₂ with
  | @exit i ω₁ μ ε₁ ω₁' μ₁' he =>
    rcases hs with rfl | ⟨hd, ha⟩
    · obtain ⟨a, b, c, d⟩ := (FreeRun.exit he).det h₂
      exact ⟨a, Or.inl ⟨b, c, d⟩⟩
    · cases he with
      | invalid hn =>
        cases hd with
        | kill hP _ _ => rw [hP] at hn; cases hn
        | pass hP _ _ _ => rw [hP] at hn; cases hn
      | @step P ε j ω' μ' hP hst hne =>
        cases hd with
        | @kill _ P' hP' hk hnh =>
          rw [hP] at hP'; cases hP'
          obtain ⟨e1, e2, e4, e3⟩ := hk _ _ μ ha
          rw [hst] at e1 e2 e3 e4
          cases h₂ with
          | exit he₂ =>
            cases he₂ with
            | invalid hn => rw [hP] at hn; cases hn
            | step hP₂ hst₂ _ =>
              rw [hP] at hP₂; cases hP₂
              rw [hst₂] at e1 e2 e3 e4
              simp only at e1 e2 e3 e4
              subst e1 e4
              refine ⟨rfl, ?_⟩
              by_cases hhp : ε₁ = .halt
              · have e3 := e3 (Or.inr hhp); subst e3
                exact Or.inl ⟨rfl, by simp [hhp], by simp [hhp]⟩
              · have := (hnh ω₁ μ); rw [hst] at this
                obtain ⟨h1, h2⟩ := this
                cases ε₁ <;> simp_all [Status.Quiet]
          | next hn _ =>
            obtain ⟨P', hP', hs'⟩ := hn
            rw [hP] at hP'; cases hP'; rw [hs'] at e1; exact absurd e1 hne
        | @pass _ P' hP' hp hcont _ =>
          rw [hP] at hP'; cases hP'
          obtain ⟨e1, e2, e3, e4⟩ := hp _ _ μ ha
          rw [hst] at e1 e2 e3 e4
          have hq : ε₁.Quiet := by
            rcases hcont ω₁ μ with hc | hq
            · rw [hst] at hc; exact absurd hc hne
            · rw [hst] at hq; exact hq
          cases h₂ with
          | exit he₂ =>
            cases he₂ with
            | invalid hn => rw [hP] at hn; cases hn
            | step hP₂ hst₂ _ =>
              rw [hP] at hP₂; cases hP₂
              rw [hst₂] at e1; exact ⟨e1, Or.inr hq⟩
          | next hn _ =>
            obtain ⟨P', hP', hs'⟩ := hn
            rw [hP] at hP'; cases hP'; rw [hs'] at e1; exact absurd e1 hne
  | @next i ω₁ μ i' ω₁'' μ'' ε₁ e₁ ω₁' μ₁' hn hr ih =>
    rcases hs with rfl | ⟨hd, ha⟩
    · obtain ⟨a, b, c, d⟩ := (FreeRun.next hn hr).det h₂
      exact ⟨a, Or.inl ⟨b, c, d⟩⟩
    · obtain ⟨P, hP, hst⟩ := hn
      cases hd with
      | @kill _ P' hP' hk _ =>
        rw [hP] at hP'; cases hP'
        obtain ⟨e1, e2, e4, e3⟩ := hk _ _ μ ha
        rw [hst] at e1 e2 e3 e4
        cases h₂ with
        | exit he₂ =>
          cases he₂ with
          | invalid hn => rw [hP] at hn; cases hn
          | step hP₂ hst' hne =>
            rw [hP] at hP₂; cases hP₂; rw [hst'] at e1; exact absurd e1.symm hne
        | next hn₂ hr₂ =>
          obtain ⟨P', hP', hs'⟩ := hn₂
          rw [hP] at hP'; cases hP'
          rw [hs'] at e2 e3 e4
          simp only at e2 e3 e4
          have e3 := e3 (by simp)
          subst e2 e3 e4
          obtain ⟨a, b, c, d⟩ := hr.det hr₂
          exact ⟨a, Or.inl ⟨b, c, d⟩⟩
      | @pass _ P' hP' hp _ hdead =>
        rw [hP] at hP'; cases hP'
        obtain ⟨e1, e2, e3, e4⟩ := hp _ _ μ ha
        have hdj : Dead7 p i' := by
          have := hdead ω₁ μ (by rw [hst]); rwa [hst] at this
        rw [hst] at e1 e2 e3 e4
        cases h₂ with
        | exit he₂ =>
          cases he₂ with
          | invalid hn => rw [hP] at hn; cases hn
          | step hP₂ hst' hne =>
            rw [hP] at hP₂; cases hP₂; rw [hst'] at e1; exact absurd e1.symm hne
        | next hn₂ hr₂ =>
          obtain ⟨P', hP', hs'⟩ := hn₂
          rw [hP] at hP'; cases hP'
          rw [hs'] at e2 e3 e4
          simp only at e2 e3 e4
          subst e2 e4
          exact ih (Or.inr ⟨hdj, e3⟩) hr₂

/-- Contract `R₁` pins down `R₂` except in ω₇ at the ids in `K`: wherever `R₁` allows an
    outcome, `R₂` allows only one with the same status, memory and context, and the same
    registers, unless the id is in `K` and the outcome continues, when ω₇ may differ. -/
def HostRel.PinsExcept7 (K : Nat → Prop) (R₁ R₂ : HostRel X) : Prop :=
  ∀ h ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂, R₁ h ω μ x s₁ ω₁ μ₁ x₁ → R₂ h ω μ x s₂ ω₂ μ₂ x₂ →
    s₁ = s₂ ∧ μ₁ = μ₂ ∧ x₁ = x₂ ∧ (ω₁ = ω₂ ∨ (K h ∧ s₁ = .cont ∧ Agree7 ω₁ ω₂))

theorem HostRel.Pins.except7 {R₁ R₂ : HostRel X} (K : Nat → Prop) (h : R₁.Pins R₂) :
    R₁.PinsExcept7 K R₂ := by
  intro h' ω μ x s₁ ω₁ μ₁ x₁ s₂ ω₂ μ₂ x₂ h₁ h₂
  obtain ⟨a, b, c, d⟩ := h _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂
  exact ⟨a, c, d, Or.inl b⟩

/-- The indices of `ecalli k` in a program, where 𝔳_inst holds (as `Program.hostCallIds`). -/
def Program.ecalliSites (P : Program) (k : Nat) : List Nat :=
  (List.range P.code.size).filter fun i =>
    P.vInst i && match P.decode i with
      | some (.oneImm .ecalli x) => x.toNat == k
      | _ => false

/-- **The `ecalli k` sites of a program**, from what its code view says at opcode positions (as
    `Program.hostCallIds_sub`): a chunked scan (`CodeView.hostScan` with the ids other than k)
    shows that no other index holds `ecalli k`. -/
theorem Program.ecalliSites_sub (P : Program) (k : Nat) (sites : List Nat)
    (h : ∀ i, i < P.code.size → P.view.maskAt i = true → ∀ x,
      P.view.decode i = some (.oneImm .ecalli x) → x.toNat = k → i ∈ sites) :
    ∀ e ∈ P.ecalliSites k, e ∈ sites := by
  intro e he
  simp only [Program.ecalliSites, List.mem_filter, List.mem_range, Bool.and_eq_true] at he
  obtain ⟨hlt, hv, hd⟩ := he
  have hm : P.view.maskAt e = true := by
    simp only [Program.vInst, Bool.and_eq_true] at hv
    exact hv.1.2
  split at hd
  · rename_i x hdx
    exact h e hlt hm x hdx (by simpa using hd)
  · cases hd

/-- A gas-free step that makes host call h is at an `ecalli h` of the program. -/
theorem freeStep_host {P : Program} {i : Nat} {ω : Regs} {μ : Memory} {h : UInt64} {j : Nat}
    {ω' : Regs} {μ' : Memory} (hs : P.freeStep i ω μ = (.host h, j, ω', μ')) :
    P.decode i = some (.oneImm .ecalli h) := by
  simp only [Program.freeStep] at hs
  generalize hm : P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ = m at hs
  generalize memoryException μ m.reads m.writes = e at hs
  cases e with
  | some e' => cases e' <;> simp [Program.finalState] at hs
  | none =>
    simp only [Program.finalState, ne_eq, not_true_eq_false, ↓reduceIte, Prod.mk.injEq] at hs
    cases hdec : P.decode i with
    | none => rw [hdec] at hm; subst hm; simp [Program.exec] at hs
    | some ins =>
      rw [hdec] at hm; subst hm
      rw [(Program.exec_status_eq_host_iff P i ins ω μ h).1 hs.1]

/-- A host-call exit of a gas-free run is at one of the program's `ecalli h`. -/
theorem FreeExit.host_site {p : ByteArray} {e : Nat} {ω : Regs} {μ : Memory} {h : UInt64}
    {ω' : Regs} {μ' : Memory} (he : FreeExit p e ω μ (.host h) ω' μ') :
    ∃ P, Blob.parse? p = some P ∧ deblob p e = some P ∧ e ∈ P.ecalliSites h.toNat := by
  cases he with
  | step hP hst _ =>
    obtain ⟨hparse, hlt⟩ := deblob_some hP
    have hv := deblob_vInst hP
    refine ⟨_, hparse, hP, ?_⟩
    simp only [Program.ecalliSites, List.mem_filter, List.mem_range]
    exact ⟨hlt, by simp [hv, freeStep_host hst]⟩

theorem FreeRun.host_site {p : ByteArray} {i : Nat} {ω : Regs} {μ : Memory} {h : UInt64} {e : Nat}
    {ω' : Regs} {μ' : Memory} (hr : FreeRun p i ω μ (.host h) e ω' μ') :
    ∃ P, Blob.parse? p = some P ∧ deblob p e = some P ∧ e ∈ P.ecalliSites h.toNat := by
  generalize hε : Status.host h = ε at hr
  induction hr with
  | exit he => subst hε; exact he.host_site
  | next _ _ ih => exact ih hε

/-- ω₇ is dead after every `ecalli k` with k ∈ `K` in the blob `p`. -/
def DeadAfter (p : ByteArray) (K : Nat → Prop) : Prop :=
  ∀ P, Blob.parse? p = some P → ∀ k, K k → ∀ e ∈ P.ecalliSites k, Dead7 p (P.next e)

theorem blobNext_eq {p : ByteArray} {e : Nat} {P : Program} (h : deblob p e = some P) :
    blobNext p e = P.next e := by
  unfold blobNext; rw [(deblob_some h).1]

/-- **Gas-free runs with host calls are deterministic up to a dead ω₇**: a run under `R₁` and a run
    under `R₂` from the same state end with the same status, context and Ψ_M output, if `R₁`
    pins down `R₂` except in ω₇ at the ids `K`, and ω₇ is dead after every `ecalli k`, k ∈ `K`. -/
theorem FreeRunH.det7 {p : ByteArray} {K : Nat → Prop} {R₁ R₂ : HostRel X}
    (hR : R₁.PinsExcept7 K R₂) (hK : DeadAfter p K) {i : Nat} {ω₁ ω₂ : Regs} {μ : Memory} {x : X}
    {ε₁ ε₂ : Status} {ω₁' ω₂' : Regs} {μ₁' μ₂' : Memory} {x₁ x₂ : X} (hs : Same7 p i ω₁ ω₂)
    (h₁ : FreeRunH p R₁ i ω₁ μ x ε₁ ω₁' μ₁' x₁) (h₂ : FreeRunH p R₂ i ω₂ μ x ε₂ ω₂' μ₂' x₂) :
    ε₁ = ε₂ ∧ x₁ = x₂ ∧ freeOutput ε₁ ω₁' μ₁' = freeOutput ε₂ ω₂' μ₂' := by
  induction h₁ generalizing ω₂ ε₂ ω₂' μ₂' x₂ with
  | exit hr hne =>
    cases h₂ with
    | exit hr' _ =>
      obtain ⟨a, b⟩ := FreeRun.det7 hs hr hr'
      subst a
      refine ⟨rfl, rfl, ?_⟩
      rcases b with ⟨_, rfl, rfl⟩ | hq
      · rfl
      · exact freeOutput_quiet hq _ _ _ _
    | host hr' _ _ => obtain ⟨a, _⟩ := FreeRun.det7 hs hr hr'; exact absurd a (hne _)
    | hostStop hr' _ _ => obtain ⟨a, _⟩ := FreeRun.det7 hs hr hr'; exact absurd a (hne _)
  | host hr hR1 _ ih =>
    cases h₂ with
    | exit hr' hne' => obtain ⟨a, _⟩ := FreeRun.det7 hs hr hr'; exact absurd a.symm (hne' _)
    | host hr' hR2 hrest =>
      obtain ⟨a, b⟩ := FreeRun.det7 hs hr hr'
      cases a
      rcases b with ⟨rfl, rfl, rfl⟩ | hq
      · obtain ⟨_, rfl, rfl, hω⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
        refine ih ?_ hrest
        rcases hω with rfl | ⟨hk, _, ha⟩
        · exact Or.inl rfl
        · obtain ⟨P, hparse, hP, hsite⟩ := hr.host_site
          rw [blobNext_eq hP]
          exact Or.inr ⟨hK P hparse _ hk _ hsite, ha⟩
      · exact hq.elim
    | hostStop hr' hR2 hs' =>
      obtain ⟨a, b⟩ := FreeRun.det7 hs hr hr'
      cases a
      rcases b with ⟨rfl, rfl, rfl⟩ | hq
      · obtain ⟨hc, _⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
        exact absurd hc.symm hs'
      · exact hq.elim
  | hostStop hr hR1 hs' =>
    cases h₂ with
    | exit hr' hne' => obtain ⟨a, _⟩ := FreeRun.det7 hs hr hr'; exact absurd a.symm (hne' _)
    | host hr' hR2 _ =>
      obtain ⟨a, b⟩ := FreeRun.det7 hs hr hr'
      cases a
      rcases b with ⟨rfl, rfl, rfl⟩ | hq
      · obtain ⟨hc, _⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
        exact absurd hc hs'
      · exact hq.elim
    | hostStop hr' hR2 _ =>
      obtain ⟨a, b⟩ := FreeRun.det7 hs hr hr'
      cases a
      rcases b with ⟨rfl, rfl, rfl⟩ | hq
      · obtain ⟨rfl, rfl, rfl, hω⟩ := hR _ _ _ _ _ _ _ _ _ _ _ _ hR1 hR2
        rcases hω with rfl | ⟨_, hc, _⟩
        · exact ⟨rfl, rfl, rfl⟩
        · exact absurd hc hs'
      · exact hq.elim

/-- **Ψ_M is determined by one gas-free run, up to a dead ω₇.** As `psiM_of_freeRunH`, for a
    contract that pins down the handler except in ω₇ at the ids `K`, in a program where ω₇ is
    dead after every `ecalli k`, k ∈ `K`. -/
theorem psiM_of_freeRunH7 (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (x : X)
    (f : HostFn X) (hf : f.GasNonIncreasing) (K : Nat → Prop) (R : HostRel X)
    (hR : R.PinsExcept7 K f.graph) {p : ByteArray} {ω : Regs} {μ : Memory}
    (hY : standardInit b a = some (p, ω, μ)) (hK : DeadAfter p K)
    {ε : Status} {ω' : Regs} {μ' : Memory} {x' : X} (hrun : FreeRunH p R i ω μ x ε ω' μ' x') :
    (psiM b i gas a f x).2.1.isOog = true ∨ (psiM b i gas a f x).2 = (freeOutput ε ω' μ', x') := by
  cases hno : (psiM b i gas a f x).2.1.isOog
  · right
    let G : HostRel X := fun h ω μ x s ω' μ' x' =>
      ∃ g, f h g ω μ x = ⟨s, (f h g ω μ x).gas, ω', μ', x'⟩
    have hresp : f.Respects G := fun h g ω μ x => ⟨g, rfl⟩
    rcases psiM_free b i gas a x G f hf hresp hno with ⟨hY', _⟩ | ⟨p', ω₀, μ₀, ε', ω'', μ'', x'', hY', hrun', hout⟩
    · rw [hY] at hY'; cases hY'
    · rw [hY] at hY'; cases hY'
      have hε' : ε' ≠ .oog := by
        intro he; rw [hout] at hno; simp [freeOutput, he, InvOutput.isOog] at hno
      obtain ⟨_, rfl, hout'⟩ := hrun.det7 hR hK (Or.inl rfl) (hrun'.to_graph hε')
      rw [hout, hout']
  · left; rfl

end PVM
