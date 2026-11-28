import PVM.Invocation
import PVM.Theorems.Host
import PVM.Theorems.Termination

/-!
# $\Psi_H$ terminates for gas-non-increasing handlers, and satisfies the paper's equation

A host call happens at an `ecalli`, which is not in $T$, so after it $\tilde\varrho$ stays $\top$
and $\Psi_H$ resumes at $\imath + 1 + \text{skip}(\imath) > \imath$ without recharging; either way
`runMeasure` drops below its value at the start of the $\Psi$ run (`psi_host_measure`). If the
handler does not add gas, the next $\Psi_H$ iteration starts
lower still, so `runMeasure + 1` iterations suffice (`psiHFuel_stable`), and `psiHStar` satisfies
GP §A.6's recursive definition of $\Psi_H^{\ast}$ (`psiHStar_eq`).
-/

namespace PVM

theorem runMeasure_mono_gas (p : ByteArray) (i : Nat) {g g' : UInt64} (ch : Bool)
    (h : g'.toNat ≤ g.toNat) : runMeasure p i g' ch ≤ runMeasure p i g ch := by
  unfold runMeasure
  split
  · exact Nat.le_refl _
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

namespace Program

/-- A step that exits with $\hbar$ has charged its block ($\tilde\varrho^{\ast} = \top$), costing at
    least one gas when $\tilde\varrho = \bot$ and nothing when $\tilde\varrho = \top$. -/
theorem step_host_facts {P : Program} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs}
    {μ : Memory} {h : UInt64} (hs : (P.step i gas ch ω μ).status = .host h) :
    (P.step i gas ch ω μ).charged = true ∧
    (ch = false → (P.step i gas ch ω μ).gas.toNat < gas.toNat) ∧
    (ch = true → (P.step i gas ch ω μ).gas = gas) := by
  have hdec := step_host hs
  have hT : isTerminator (P.zeta i) = false := by
    rw [← decode_opcode hdec]; simp only [Instr.opcode]; decide
  have hcg := P.chargeGas_cases i gas ch
  simp only [step] at hs ⊢
  generalize P.chargeGas i gas ch = g at hs ⊢ hcg
  generalize memoryException μ _ _ = e at hs ⊢
  obtain ⟨εg, gas', ch'⟩ := g
  have hεg' : εg = .cont ∨ εg = .oog := by
    cases ch
    · rcases hcg.1 rfl with ⟨_, h1, _⟩ | h1 <;> cases h1 <;> simp
    · cases hcg.2 rfl; simp
  by_cases hεg : εg = .cont
  · subst hεg
    refine ⟨?_, fun hc => ?_, fun hc => ?_⟩
    · have : ch' = true := by
        cases ch
        · rcases hcg.1 rfl with ⟨_, h1, _⟩ | h1 <;> cases h1; rfl
        · cases hcg.2 rfl; rfl
      simp [this, hT]
    · subst hc
      rcases hcg.1 rfl with ⟨g', h1, hlt⟩ | h1
      · cases h1; exact hlt
      · cases h1
    · subst hc; cases hcg.2 rfl; rfl
  · rcases hεg' with h1 | h1
    · exact absurd h1 hεg
    · subst h1; simp [finalState] at hs

end Program

/-- When $\Psi$ (with fuel) exits with $\hbar$, resuming at $\imath + 1 + \text{skip}(\imath)$ with
    the returned gas and flag
    is strictly lower in `runMeasure` than where the run started. -/
theorem runFuel_host_measure {p : ByteArray} :
    ∀ (n i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) (r : Result) (h : UInt64),
      runFuel p n i gas ch ω μ = some r → r.status = .host h →
      runMeasure p (blobNext p r.pc) r.gas r.charged < runMeasure p i gas ch := by
  intro n
  induction n with
  | zero => intros; simp_all [runFuel]
  | succ n ih =>
    intro i gas ch ω μ r h hr hs
    unfold runFuel at hr
    cases hP : deblob p i with
    | none => rw [hP] at hr; cases hr; simp at hs
    | some P =>
      rw [hP] at hr
      dsimp only at hr
      split at hr
      · rename_i hc
        exact Nat.lt_trans (ih _ _ _ _ _ _ _ hr hs) (step_measure_lt hP hc)
      · cases hr; simp_all
      · cases hr; simp_all
      · cases hr
        rename_i hst _ _
        simp only at hs
        obtain ⟨hparse, hi⟩ := deblob_some hP
        obtain ⟨hch, hlt, heq⟩ := Program.step_host_facts hs
        have hnx := P.next_gt i
        simp only [blobNext, hparse, runMeasure, hch]
        generalize hn : P.code.size + 1 = n'
        cases ch
        · have h1 : 2 * n' * (P.step i gas false ω μ).gas.toNat + 2 * n' ≤ 2 * n' * gas.toNat := by
            rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (hlt rfl)
          simp only [↓reduceIte, Bool.false_eq_true]
          omega
        · rw [heq rfl]; simp only [↓reduceIte]; omega

theorem psi_host_measure {p : ByteArray} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs}
    {μ : Memory} {h : UInt64} (hs : (psi p i gas ch ω μ).status = .host h) :
    runMeasure p (blobNext p (psi p i gas ch ω μ).pc) (psi p i gas ch ω μ).gas
      (psi p i gas ch ω μ).charged < runMeasure p i gas ch :=
  runFuel_host_measure _ i gas ch ω μ _ h
    (psi_eq_runFuel p (runMeasure p i gas ch + 1) i gas ch ω μ (by omega)) hs

variable {X : Type}

/-- Extra fuel does not change `psiHFuel`, which never runs out, when the handler does not add gas. -/
theorem psiHFuel_stable (p : ByteArray) (f : HostFn X) (hf : f.GasNonIncreasing) :
    ∀ (n i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) (x : X),
      runMeasure p i gas ch < n →
      (psiHFuel p f n i gas ch ω μ x).isSome ∧
        ∀ k, psiHFuel p f (n + k) i gas ch ω μ x = psiHFuel p f n i gas ch ω μ x := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro i gas ch ω μ x hm
    have e : ∀ k, n + 1 + k = (n + k) + 1 := fun k => by omega
    generalize hr : psi p i gas ch ω μ = r
    cases hst : r.status
    case host h =>
      generalize hy : f h.toNat r.gas r.regs r.mem x = y
      have hlt : runMeasure p (blobNext p r.pc) y.gas r.charged < n := by
        have h1 := psi_host_measure (hr ▸ hst : (psi p i gas ch ω μ).status = .host h)
        rw [hr] at h1
        have h2 := runMeasure_mono_gas p (blobNext p r.pc) r.charged (hy ▸ hf h.toNat r.gas r.regs r.mem x)
        omega
      cases hys : y.status
      all_goals
        refine ⟨?_, fun k => ?_⟩ <;> (try rw [e k]) <;> simp only [psiHFuel, hr, hst, hy, hys]
      all_goals first
        | exact (ih _ _ _ _ _ _ hlt).1
        | exact (ih _ _ _ _ _ _ hlt).2 k
        | rfl
    all_goals
      refine ⟨?_, fun k => ?_⟩ <;> (try rw [e k]) <;> simp [psiHFuel, hr, hst]

/-- **$\Psi_H^{\ast}$'s defining equation** (GP §A.6), for any handler that does not add gas: run
    $\Psi$; on $\hbar \times h$ call $f$, then either continue at $\imath' + 1 + \text{skip}(\imath')$
    or stop with $f$'s exit reason; on any other
    exit reason stop. -/
theorem psiHStar_eq (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory)
    (f : HostFn X) (hf : f.GasNonIncreasing) (x : X) :
    psiHStar p i gas ch ω μ f x =
      let r := psi p i gas ch ω μ
      match r.status with
      | .host h =>
        let y := f h.toNat r.gas r.regs r.mem x
        match y.status with
        | .cont => psiHStar p (blobNext p r.pc) y.gas r.charged y.regs y.mem f y.ctx
        | s => { status := s.toStatus, pc := r.pc, gas := y.gas,
                 charged := r.charged, regs := y.regs, mem := y.mem, ctx := y.ctx }
      | _ => { status := r.status, pc := r.pc, gas := r.gas,
               charged := r.charged, regs := r.regs, mem := r.mem, ctx := x } := by
  -- `psiHFuel` with any fuel above the measure agrees with `psiHStar`.
  have agree : ∀ n i gas ch ω μ x, runMeasure p i gas ch < n →
      psiHFuel p f n i gas ch ω μ x = some (psiHStar p i gas ch ω μ f x) := by
    intro n i gas ch ω μ x hn
    have h1 := psiHFuel_stable p f hf (runMeasure p i gas ch + 1) i gas ch ω μ x (by omega)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show runMeasure p i gas ch + 1 ≤ n by omega)
    rw [hk, h1.2 k]
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h1.1
    simp [psiHStar, hv]
  have h0 := agree (runMeasure p i gas ch + 1) i gas ch ω μ x (by omega)
  rw [psiHFuel] at h0
  dsimp only at h0 ⊢
  generalize hr : psi p i gas ch ω μ = r at h0 ⊢
  cases hst : r.status
  case host h =>
    simp only [hst] at h0 ⊢
    generalize hy : f h.toNat r.gas r.regs r.mem x = y at h0 ⊢
    have hlt : runMeasure p (blobNext p r.pc) y.gas r.charged < runMeasure p i gas ch := by
      have h1 := psi_host_measure (hr ▸ hst : (psi p i gas ch ω μ).status = .host h)
      rw [hr] at h1
      have h2 := runMeasure_mono_gas p (blobNext p r.pc) r.charged (hy ▸ hf h.toNat r.gas r.regs r.mem x)
      omega
    cases hys : y.status <;> simp only [hys] at h0 ⊢
    · rw [agree _ _ _ _ _ _ _ hlt] at h0; exact (Option.some.inj h0).symm
    all_goals exact (Option.some.inj h0).symm
  all_goals (simp only [hst] at h0 ⊢; exact (Option.some.inj h0).symm)

/-! ## $\mathbb{N}_{a \dots+n} \subseteq \mathbb{V}_\mu$ -/

/-- Indices on the same page are readable alike. -/
theorem Memory.readable_of_div_eq (μ : Memory) {i j : Nat} (h : i / pageSize = j / pageSize) :
    μ.readable i = μ.readable j := by
  simp [Memory.readable, h]

/-- `rangeReadable` is the paper's $\mathbb{N}_{a \dots+n} \subseteq \mathbb{V}_\mu$ (GP §A.8, eq. `psimdef`
    and the host functions that read a range): every index of the range is below $2^{32}$ and
    readable. The page-by-page check is only how it is computed. -/
theorem Memory.rangeReadable_iff (μ : Memory) (a n : Nat) :
    μ.rangeReadable a n = true ↔
      ∀ j, a ≤ j → j < a + n → j < 2 ^ 32 ∧ μ.readable j = true := by
  have hps : 0 < pageSize := by decide
  unfold Memory.rangeReadable
  by_cases hn : n = 0
  · subst hn
    simp only [beq_self_eq_true, Bool.true_or, true_iff]
    intro j h1 h2; omega
  · have hn' : (n == 0) = false := by simpa using hn
    simp only [hn', Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_range]
    constructor
    · rintro ⟨hle, hall⟩ j h1 h2
      refine ⟨by omega, ?_⟩
      have hf : a / pageSize ≤ j / pageSize := Nat.div_le_div_right h1
      have hl : j / pageSize ≤ (a + n - 1) / pageSize := Nat.div_le_div_right (by omega)
      have := hall (j / pageSize - a / pageSize) (by omega)
      rw [show a / pageSize + (j / pageSize - a / pageSize) = j / pageSize by omega] at this
      rw [μ.readable_of_div_eq (j := j / pageSize * pageSize) (by rw [Nat.mul_div_cancel _ hps])]
      exact this
    · intro h
      refine ⟨by have := (h (a + n - 1) (by omega) (by omega)).1; omega, ?_⟩
      intro k hk
      have hlast : (a / pageSize + k) * pageSize ≤ a + n - 1 :=
        Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) (Nat.div_mul_le_self _ _)
      by_cases hc : a ≤ (a / pageSize + k) * pageSize
      · exact (h _ hc (by omega)).2
      · have hk0 : a / pageSize + k ≤ a / pageSize :=
          (Nat.le_div_iff_mul_le hps).2 (by omega)
        rw [show k = 0 by omega, Nat.add_zero,
          μ.readable_of_div_eq (j := a) (by rw [Nat.mul_div_cancel _ hps])]
        exact (h a (Nat.le_refl _) (by omega)).2

end PVM
