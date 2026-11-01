import PVM.Machine
import PVM.Theorems.Decode

/-!
# Ψ terminates, and `psi` satisfies the paper's equation for Ψ

`psi` runs Ψ with fuel `stepBound`. We show that this fuel never runs out
(`runFuel_stepBound_isSome`) and that `psi` satisfies the recursive definition of Ψ in GP
v0.8.0 §A.1 verbatim (`psi_eq`), so the fuel is an implementation device only.

The argument: a continuing step either charges a block (ϱ̃ = ⊥ before the step), which costs at
least one unit of gas; or executes a terminator, which clears ϱ̃; or executes a non-terminator,
which moves ı forward to ı + 1 + skip(ı) inside **c**. The measure `runMeasure` decreases in
each case.
-/

namespace PVM

namespace Program

/-- Every instruction outside T continues at ı + 1 + skip(ı) (the default of GP §A.4). -/
theorem exec_pc_of_not_terminator (P : Program) (i : Nat) (ins : Instr) (ω : Regs) (μ : Memory)
    (h : isTerminator ins.opcode = false) : (P.exec i ins ω μ).pc = P.next i := by
  cases ins with
  | noArgs op => cases op <;> first | rfl | (exfalso; simp only [Instr.opcode] at h; revert h; decide)
  | oneImm op => cases op <;> rfl
  | regExtImm op => cases op <;> rfl
  | twoImm op => cases op <;> rfl
  | oneOffset op => cases op; exfalso; simp only [Instr.opcode] at h; revert h; decide
  | regImm op => cases op <;> first | rfl | (exfalso; simp only [Instr.opcode] at h; revert h; decide)
  | regTwoImm op => cases op <;> rfl
  | regImmOffset op => cases op <;> (exfalso; simp only [Instr.opcode] at h; revert h; decide)
  | twoReg op => cases op <;> rfl
  | twoRegImm op => cases op <;> rfl
  | twoRegOffset op => cases op <;> (exfalso; simp only [Instr.opcode] at h; revert h; decide)
  | twoRegTwoImm op => cases op; exfalso; simp only [Instr.opcode] at h; revert h; decide
  | threeReg op => cases op <;> rfl

theorem blockCost_pos (P : Program) (i : Nat) : 1 ≤ P.blockCost i := by
  unfold blockCost blockCost?
  cases Sim.run P (Sim.fuel P i) (Sim.init i) <;> simp only [Option.map_some, Option.map_none,
    Option.getD_some, Option.getD_none] <;> omega

theorem next_gt (P : Program) (i : Nat) : i < P.next i := by unfold next; omega

/-- The gas stage either continues having charged (ϱ̃ = ⊥: at least one unit of gas; ϱ̃ = ⊤:
    nothing), or reports ∞. -/
theorem chargeGas_cases (P : Program) (i : Nat) (gas : UInt64) (ch : Bool) :
    (ch = false → (∃ g', P.chargeGas i gas ch = (.cont, g', true) ∧ g'.toNat < gas.toNat) ∨
        P.chargeGas i gas ch = (.oog, gas, false)) ∧
    (ch = true → P.chargeGas i gas ch = (.cont, gas, true)) := by
  unfold chargeGas
  cases ch
  · simp only [Bool.false_eq_true, ↓reduceIte, forall_const, false_implies, and_true]
    split
    · left
      refine ⟨_, rfl, ?_⟩
      have := P.blockCost_pos (P.blockStartOf i)
      have hsz : UInt64.size = 2 ^ 64 := rfl
      rw [UInt64.toNat_ofNat_of_lt' (by have := gas.toNat_lt; omega)]
      omega
    · right; rfl
  · simp

/-- What a continuing step of Ψ₁ does to (ı, ϱ, ϱ̃): with ϱ̃ = ⊥ it charges at least one unit of
    gas; with ϱ̃ = ⊤ it leaves ϱ unchanged and either clears ϱ̃ or moves to ı + 1 + skip(ı). -/
theorem step_cont {P : Program} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs} {μ : Memory}
    (hs : (P.step i gas ch ω μ).status = .cont) :
    (ch = false → (P.step i gas ch ω μ).gas.toNat < gas.toNat) ∧
    (ch = true → (P.step i gas ch ω μ).gas = gas ∧
      ((P.step i gas ch ω μ).charged = false ∨ (P.step i gas ch ω μ).pc = P.next i)) := by
  have hcg := P.chargeGas_cases i gas ch
  simp only [step] at hs ⊢
  generalize P.chargeGas i gas ch = g at hs ⊢ hcg
  generalize hm : P.exec i ((P.decode i).getD (.noArgs .trap)) ω μ = m at hs ⊢
  generalize memoryException μ m.reads m.writes = e at hs ⊢
  obtain ⟨εg, gas', ch'⟩ := g
  by_cases hεg : εg = .cont
  · subst hεg
    cases e with
    | some e' => cases e' <;> simp [finalState] at hs
    | none =>
      simp only [finalState, ne_eq, not_true_eq_false, ↓reduceIte] at hs ⊢
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · subst hc
        rcases hcg.1 rfl with ⟨g', hg', hlt⟩ | h
        · cases hg'; exact hlt
        · cases h
      · subst hc
        cases hcg.2 rfl
        refine ⟨rfl, ?_⟩
        cases hT : isTerminator (P.zeta i)
        · right
          cases hdec : P.decode i with
          | none =>
            -- an undecodable octet is read as `trap`, which panics
            rw [hdec] at hm; subst hm; simp [exec] at hs
          | some ins =>
            rw [hdec] at hm; subst hm
            simp only [Option.getD_some]
            apply exec_pc_of_not_terminator
            rw [decode_opcode hdec, hT]
        · left; simp [hs, Status.continuesOrHost]
  · simp [finalState, hεg] at hs

end Program

theorem deblob_some {p : ByteArray} {i : Nat} {P : Program} (h : deblob p i = some P) :
    Blob.parse? p = some P ∧ i < P.code.size := by
  unfold deblob at h
  cases hp : Blob.parse? p with
  | none => simp [hp] at h
  | some P' =>
    simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · cases h
      rename_i hv
      simp only [Bool.and_eq_true, Program.vInst, beq_iff_eq, decide_eq_true_eq] at hv
      exact ⟨rfl, by omega⟩
    · cases h

/-- `runMeasure` strictly decreases on every continuing step of Ψ. -/
theorem step_measure_lt {p : ByteArray} {i : Nat} {gas : UInt64} {ch : Bool} {ω : Regs}
    {μ : Memory} {P : Program} (hP : deblob p i = some P)
    (hs : (P.step i gas ch ω μ).status = .cont) :
    runMeasure p (P.step i gas ch ω μ).pc (P.step i gas ch ω μ).gas (P.step i gas ch ω μ).charged <
      runMeasure p i gas ch := by
  obtain ⟨hparse, hi⟩ := deblob_some hP
  have hc := Program.step_cont hs
  generalize P.step i gas ch ω μ = r at hc ⊢
  unfold runMeasure
  rw [hparse]
  dsimp only
  generalize hn : P.code.size + 1 = n
  have hn1 : P.code.size < n := by omega
  cases ch
  · have hlt := hc.1 rfl
    have h1 : 2 * n * r.gas.toNat + 2 * n ≤ 2 * n * gas.toNat := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    have h2 : (if r.charged = true then n + P.code.size - r.pc else 0) ≤ n + P.code.size := by
      split <;> omega
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    omega
  · obtain ⟨hg, hpc⟩ := hc.2 rfl
    rw [hg]
    simp only [↓reduceIte]
    rcases hpc with hch | hpc
    · simp only [hch, Bool.false_eq_true, ↓reduceIte]; omega
    · have := P.next_gt i
      split <;> omega

/-- Extra fuel beyond the measure does not change `runFuel`'s result, which is never `none`. -/
theorem runFuel_stable (p : ByteArray) :
    ∀ (n : Nat) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory),
      runMeasure p i gas ch < n →
      (runFuel p n i gas ch ω μ).isSome ∧ ∀ k, runFuel p (n + k) i gas ch ω μ = runFuel p n i gas ch ω μ := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro i gas ch ω μ hm
    have e : ∀ k, n + 1 + k = (n + k) + 1 := fun k => by omega
    cases hP : deblob p i with
    | none => exact ⟨by simp [runFuel, hP], fun k => by rw [e k]; simp [runFuel, hP]⟩
    | some P =>
      by_cases hs : (P.step i gas ch ω μ).status = .cont
      · have hlt := step_measure_lt hP hs
        have := ih (P.step i gas ch ω μ).pc (P.step i gas ch ω μ).gas (P.step i gas ch ω μ).charged
          (P.step i gas ch ω μ).regs (P.step i gas ch ω μ).mem (by omega)
        refine ⟨?_, fun k => ?_⟩
        · simp only [runFuel, hP, hs]; exact this.1
        · rw [e k]; simp only [runFuel, hP, hs]; exact this.2 k
      · refine ⟨?_, fun k => ?_⟩
        · simp only [runFuel, hP]; split <;> simp_all
        · rw [e k]; simp only [runFuel, hP]; split <;> simp_all

/-- `psi`'s fuel never runs out. -/
theorem runFuel_stepBound_isSome (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) : (runFuel p (stepBound p i gas ch) i gas ch ω μ).isSome :=
  (runFuel_stable p _ i gas ch ω μ (by unfold stepBound; omega)).1

/-- `psi` agrees with `runFuel` for any fuel larger than the measure. -/
theorem psi_eq_runFuel (p : ByteArray) (n i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) (hn : runMeasure p i gas ch < n) :
    runFuel p n i gas ch ω μ = some (psi p i gas ch ω μ) := by
  have h1 := runFuel_stable p _ i gas ch ω μ (show runMeasure p i gas ch < stepBound p i gas ch by
    unfold stepBound; omega)
  have h2 := runFuel_stable p n i gas ch ω μ hn
  unfold psi
  have hb : stepBound p i gas ch ≤ n := by unfold stepBound; omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hb
  rw [hk, h1.2 k]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h1.1
  simp [hr]

/-- **Ψ's defining equation** (GP §A.1): `psi` satisfies the paper's recursive definition of Ψ,
    with deblob, Ψ₁ and the case split on ε, exactly. -/
theorem psi_eq (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) :
    psi p i gas ch ω μ =
      match deblob p i with
      | none => { status := .panic, pc := 0, gas, charged := ch, regs := ω, mem := μ }
      | some P =>
        let r := P.step i gas ch ω μ
        match r.status with
        | .cont => psi p r.pc r.gas r.charged r.regs r.mem
        | .halt | .panic =>
          { status := r.status, pc := 0, gas := r.gas, charged := r.charged,
            regs := r.regs, mem := r.mem }
        | _ =>
          { status := r.status, pc := i, gas := r.gas, charged := r.charged,
            regs := ω, mem := μ } := by
  have h := psi_eq_runFuel p (runMeasure p i gas ch + 1) i gas ch ω μ (by omega)
  rw [runFuel] at h
  cases hP : deblob p i with
  | none => simp [hP] at h; exact h.symm
  | some P =>
    rw [hP] at h
    dsimp only at h ⊢
    by_cases hs : (P.step i gas ch ω μ).status = .cont
    · rw [hs] at h ⊢
      dsimp only at h ⊢
      rw [psi_eq_runFuel p _ _ _ _ _ _ (step_measure_lt hP hs)] at h
      exact (Option.some.inj h).symm
    · split at h
      · contradiction
      all_goals (rename_i heq; simp only [heq] at h ⊢; exact (Option.some.inj h).symm)

/-- Ψ never returns ▸. -/
theorem psi_status_ne_cont (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) : (psi p i gas ch ω μ).status ≠ .cont := by
  have key : ∀ n i gas ch ω μ r, runFuel p n i gas ch ω μ = some r → r.status ≠ .cont := by
    intro n
    induction n with
    | zero => intros; simp_all [runFuel]
    | succ n ih =>
      intro i gas ch ω μ r hr
      unfold runFuel at hr
      split at hr
      · cases hr; simp
      · dsimp only at hr
        split at hr
        · exact ih _ _ _ _ _ _ hr
        all_goals (cases hr; simp_all)
  exact key _ i gas ch ω μ _ (psi_eq_runFuel p (runMeasure p i gas ch + 1) i gas ch ω μ (by omega))

end PVM
