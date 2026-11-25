import PVM.SymExec.Fork

/-!
# Loop induction (symexec)

A loop is given by a header cut `H` at pc `hpc` with facts `asm`, a Lean predicate `I` on the named
naturals (what the executor does not track, e.g. a property of the octets read so far), and a
measure. One forking check (`forkCheck`) runs the body from the header to leaves at `hpc` (back
edges) or at the exit `xpc`. Each leaf comes with a Lean obligation (`LoopObl`): on a back edge, the
next named naturals satisfy `I`, the bounds and `asm`, and the measure drops; at the exit, the
leaf's target cut implies the postcondition `Q`.

`loop_sound` is the induction itself, over any invariant; `loop_fork_sound` instantiates it with a
forking check. Both are about `FreeStepsH` (GP v0.8.1 §A.4–A.5) only.
-/

namespace PVM.SymExec

open Num Exec

/-- **Loop induction.** If from every state satisfying `Inv vals` the machine reaches either the
    header again in a state satisfying `Inv vals'` with a smaller measure, or the exit in a state
    satisfying `Q`, then from every such state it reaches the exit in a state satisfying `Q`. -/
theorem loop_sound {X : Type} {p : ByteArray} {R : HostRel X} {hpc xpc : Nat} {x : X}
    (Inv : List Nat → Regs → Memory → Prop) (Q : Regs → Memory → Prop) (meas : List Nat → Nat)
    (hbody : ∀ vals ω μ, Inv vals ω μ → ∃ k ω' μ',
      (FreeStepsH p R hpc ω μ x hpc ω' μ' x k ∧ ∃ vals', meas vals' < meas vals ∧ Inv vals' ω' μ') ∨
      (FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q ω' μ')) :
    ∀ vals ω μ, Inv vals ω μ → ∃ k ω' μ', FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q ω' μ' := by
  suffices H : ∀ n vals ω μ, meas vals = n → Inv vals ω μ →
      ∃ k ω' μ', FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q ω' μ' from
    fun vals ω μ h => H _ vals ω μ rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro vals ω μ hn hinv
    obtain ⟨k, ω₁, μ₁, hb⟩ := hbody vals ω μ hinv
    rcases hb with ⟨hrun, vals', hlt, hinv'⟩ | ⟨hrun, hq⟩
    · obtain ⟨k', ω', μ', hrun', hq⟩ := ih (meas vals') (hn ▸ hlt) vals' ω₁ μ₁ rfl hinv'
      exact ⟨k + k', ω', μ', FreeStepsH.trans hrun hrun', hq⟩
    · exact ⟨k, ω₁, μ₁, hrun, hq⟩

/-- A fact that depends only on the named naturals and the page map. -/
def Fact.closed : Fact → Bool
  | .lt v _ | .ge v _ | .ne v _ => v.closed
  | .le _ _ | .rd _ _ | .wr _ _ | .sum _ _ _ | .neA _ _ => true

theorem Fact.holds_env {vals : List Nat} {ω ω' : Regs} {μ μ' : Memory} (hp : μ.pages = μ'.pages) :
    ∀ {f : Fact}, f.closed = true → f.Holds (env vals ω μ) → f.Holds (env vals ω' μ')
  | .lt v c, hc, h => by
    simp only [Fact.closed] at hc; simp only [Fact.Holds, env] at h ⊢; rwa [← SVal.eval_closed v hc]
  | .ge v c, hc, h => by
    simp only [Fact.closed] at hc; simp only [Fact.Holds, env] at h ⊢; rwa [← SVal.eval_closed v hc]
  | .ne v c, hc, h => by
    simp only [Fact.closed] at hc; simp only [Fact.Holds, env] at h ⊢; rwa [← SVal.eval_closed v hc]
  | .le a b, _, h => h
  | .sum _ _ _, _, h => h
  | .neA _ _, _, h => h
  | .rd lo hi, _, h => fun t h1 h2 => by
    simp only [env] at h ⊢; rw [← readable_pages hp]; exact h t h1 h2
  | .wr lo hi, _, h => fun t h1 h2 => by
    simp only [env] at h ⊢; rw [← writable_pages hp]; exact h t h1 h2

theorem factsHold_env {vals : List Nat} {ω ω' : Regs} {μ μ' : Memory} (hp : μ.pages = μ'.pages) :
    ∀ {l : List Fact}, l.all Fact.closed = true → FactsHold (env vals ω μ) l → FactsHold (env vals ω' μ') l
  | [], _, _ => trivial
  | _ :: _, hc, ⟨h, hs⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    exact ⟨Fact.holds_env hp hc.1 h, factsHold_env hp hc.2 hs⟩

/-- The obligation of one leaf of a loop body: a back edge to the header `H` at `hpc` keeps the
    invariant and lowers the measure; a leaf at the exit `xpc` implies the postcondition `Q`. -/
def LoopObl (ub lb : List Nat) (H : Cut) (asm : List Fact) (μ₀ : Memory) (I : List Nat → Prop)
    (meas : List Nat → Nat) (hpc xpc : Nat) (Q : Regs → Memory → Prop) (ℓ : Leaf) : Prop :=
  ∀ vals ω μ, I vals → BHold vals ub → LBHold vals lb → FactsHold (env vals ω μ) asm →
    H.Holds vals μ₀ ω μ → FactsHold (env vals ω μ) ℓ.facts →
    (ℓ.pc = hpc ∧ ℓ.B = H ∧ I (svals (env vals ω μ) ℓ.sub) ∧ BHold (svals (env vals ω μ) ℓ.sub) ub ∧
      LBHold (svals (env vals ω μ) ℓ.sub) lb ∧ FactsHold (env (svals (env vals ω μ) ℓ.sub) ω μ) asm ∧
      meas (svals (env vals ω μ) ℓ.sub) < meas vals) ∨
    (ℓ.pc = xpc ∧ ∀ ω' μ', ℓ.B.Holds (svals (env vals ω μ) ℓ.sub) μ₀ ω' μ' → Q ω' μ')

/-- **A loop, from one forking check of its body and one obligation per leaf.** -/
theorem loop_fork_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {G : Prog}
    {ub lb : List Nat} {sep : List ((Aff × Nat) × (Aff × Nat))} {H : Cut} {asm : List Fact}
    {leaves : List Leaf} {hpc xpc fuel : Nat} {μ₀ : Memory} {I : List Nat → Prop}
    {meas : List Nat → Nat} {Q : Regs → Memory → Prop}
    (hchk : forkCheck G ub lb sep H asm leaves hpc fuel = true)
    (hasm : asm.all Fact.closed = true)
    (hG : ProgHyp p P G) (hH : HostOk R G.hosts)
    (hsep : ∀ vals, I vals → ∀ ω μ, SepHold (env vals ω μ) sep)
    (hobl : ∀ ℓ ∈ leaves, LoopObl ub lb H asm μ₀ I meas hpc xpc Q ℓ) (x : X) :
    ∀ vals ω μ, I vals → BHold vals ub → LBHold vals lb → FactsHold (env vals ω μ) asm →
      H.Holds vals μ₀ ω μ →
      ∃ k ω' μ', FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q ω' μ' := by
  intro vals ω μ hI hB hLB hF hH0
  refine loop_sound (fun vals ω μ => I vals ∧ BHold vals ub ∧ LBHold vals lb ∧
      FactsHold (env vals ω μ) asm ∧ H.Holds vals μ₀ ω μ) Q meas ?_ vals ω μ ⟨hI, hB, hLB, hF, hH0⟩
  rintro vals ω μ ⟨hI, hB, hLB, hF, hH0⟩
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, hfs, hBℓ⟩ :=
    fork_sound hchk hG hH hB hLB (hsep vals hI) hH0 hF x
  have hpg : μ'.pages = μ.pages := by
    have h1 := hBℓ.2.2.2.2.2; have h2 := hH0.2.2.2.2.2; rw [h1, h2]
  refine ⟨k, ω', μ', ?_⟩
  rcases hobl ℓ hℓ vals ω μ hI hB hLB hF hH0 hfs with
    ⟨hpc', hBH, hI', hB', hLB', hF', hlt⟩ | ⟨hx, hq⟩
  · left
    refine ⟨hpc' ▸ hrun, _, hlt, hI', hB', hLB', factsHold_env hpg.symm hasm hF', hBH ▸ hBℓ⟩
  · right
    exact ⟨hx ▸ hrun, hq ω' μ' hBℓ⟩

end PVM.SymExec

/-! ## Loops with several exits -/

namespace PVM.SymExec

open Num Exec

/-- **Loop induction, several exits.** As `loop_sound`, with the exit pc part of the postcondition:
    from every state satisfying `Inv vals` the machine reaches the header again (smaller measure)
    or some pc `x'` in a state satisfying `Q x'`. -/
theorem loop_soundX {X : Type} {p : ByteArray} {R : HostRel X} {hpc : Nat} {x : X}
    (Inv : List Nat → Regs → Memory → Prop) (Q : Nat → Regs → Memory → Prop) (meas : List Nat → Nat)
    (hbody : ∀ vals ω μ, Inv vals ω μ → ∃ k ω' μ',
      (FreeStepsH p R hpc ω μ x hpc ω' μ' x k ∧ ∃ vals', meas vals' < meas vals ∧ Inv vals' ω' μ') ∨
      (∃ xpc, FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q xpc ω' μ')) :
    ∀ vals ω μ, Inv vals ω μ →
      ∃ xpc k ω' μ', FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q xpc ω' μ' := by
  suffices H : ∀ n vals ω μ, meas vals = n → Inv vals ω μ →
      ∃ xpc k ω' μ', FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q xpc ω' μ' from
    fun vals ω μ h => H _ vals ω μ rfl h
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro vals ω μ hn hinv
    obtain ⟨k, ω₁, μ₁, hb⟩ := hbody vals ω μ hinv
    rcases hb with ⟨hrun, vals', hlt, hinv'⟩ | ⟨xpc, hrun, hq⟩
    · obtain ⟨xpc, k', ω', μ', hrun', hq⟩ := ih (meas vals') (hn ▸ hlt) vals' ω₁ μ₁ rfl hinv'
      exact ⟨xpc, k + k', ω', μ', FreeStepsH.trans hrun hrun', hq⟩
    · exact ⟨xpc, k, ω₁, μ₁, hrun, hq⟩

/-- The obligation of one leaf of a loop body with several exits: a back edge to the header `H` at
    `hpc` keeps the invariant and lowers the measure; any other leaf implies the postcondition
    `Q` at its pc. -/
def LoopOblX (ub lb : List Nat) (H : Cut) (asm : List Fact) (μ₀ : Memory) (I : List Nat → Prop)
    (meas : List Nat → Nat) (hpc : Nat) (Q : Nat → Regs → Memory → Prop) (ℓ : Leaf) : Prop :=
  ∀ vals ω μ, I vals → BHold vals ub → LBHold vals lb → FactsHold (env vals ω μ) asm →
    H.Holds vals μ₀ ω μ → FactsHold (env vals ω μ) ℓ.facts →
    (ℓ.pc = hpc ∧ ℓ.B = H ∧ I (svals (env vals ω μ) ℓ.sub) ∧ BHold (svals (env vals ω μ) ℓ.sub) ub ∧
      LBHold (svals (env vals ω μ) ℓ.sub) lb ∧ FactsHold (env (svals (env vals ω μ) ℓ.sub) ω μ) asm ∧
      meas (svals (env vals ω μ) ℓ.sub) < meas vals) ∨
    (∀ ω' μ', ℓ.B.Holds (svals (env vals ω μ) ℓ.sub) μ₀ ω' μ' → Q ℓ.pc ω' μ')

/-- **A loop with several exits, from one forking check of its body and one obligation per
    leaf.** -/
theorem loop_fork_soundX {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {G : Prog}
    {ub lb : List Nat} {sep : List ((Aff × Nat) × (Aff × Nat))} {H : Cut} {asm : List Fact}
    {leaves : List Leaf} {hpc fuel : Nat} {μ₀ : Memory} {I : List Nat → Prop}
    {meas : List Nat → Nat} {Q : Nat → Regs → Memory → Prop}
    (hchk : forkCheck G ub lb sep H asm leaves hpc fuel = true)
    (hasm : asm.all Fact.closed = true)
    (hG : ProgHyp p P G) (hH : HostOk R G.hosts)
    (hsep : ∀ vals, I vals → ∀ ω μ, SepHold (env vals ω μ) sep)
    (hobl : ∀ ℓ ∈ leaves, LoopOblX ub lb H asm μ₀ I meas hpc Q ℓ) (x : X) :
    ∀ vals ω μ, I vals → BHold vals ub → LBHold vals lb → FactsHold (env vals ω μ) asm →
      H.Holds vals μ₀ ω μ →
      ∃ xpc k ω' μ', FreeStepsH p R hpc ω μ x xpc ω' μ' x k ∧ Q xpc ω' μ' := by
  intro vals ω μ hI hB hLB hF hH0
  refine loop_soundX (fun vals ω μ => I vals ∧ BHold vals ub ∧ LBHold vals lb ∧
      FactsHold (env vals ω μ) asm ∧ H.Holds vals μ₀ ω μ) Q meas ?_ vals ω μ ⟨hI, hB, hLB, hF, hH0⟩
  rintro vals ω μ ⟨hI, hB, hLB, hF, hH0⟩
  obtain ⟨ℓ, hℓ, k, ω', μ', hrun, hfs, hBℓ⟩ :=
    fork_sound hchk hG hH hB hLB (hsep vals hI) hH0 hF x
  have hpg : μ'.pages = μ.pages := by
    have h1 := hBℓ.2.2.2.2.2; have h2 := hH0.2.2.2.2.2; rw [h1, h2]
  refine ⟨k, ω', μ', ?_⟩
  rcases hobl ℓ hℓ vals ω μ hI hB hLB hF hH0 hfs with
    ⟨hpc', hBH, hI', hB', hLB', hF', hlt⟩ | hq
  · left
    refine ⟨hpc' ▸ hrun, _, hlt, hI', hB', hLB', factsHold_env hpg.symm hasm hF', hBH ▸ hBℓ⟩
  · right
    exact ⟨ℓ.pc, hrun, hq ω' μ' hBℓ⟩

end PVM.SymExec
