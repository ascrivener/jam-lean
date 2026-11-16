import PVM.SymExec.Check

/-!
# Cut states as data (symexec)

EXPERIMENTAL (see `docs/symexec-spike.md`). A chain of stretches is cut at points where a `Cut`
says what holds of the machine state: registers, memory cells, readable and writable regions, and
the regions written since the chain's start (everything else reads as in the start memory μ₀, and
the page map is μ₀'s). `seg_sound` turns one Boolean check per segment, evaluated by the kernel,
into `Cut.Holds A → ∃ …, FreeStepsH … ∧ Cut.Holds B`, with no per-segment proof: a generator only
emits the data of each cut.
-/

namespace PVM.SymExec

open Num Exec

/-- A cut state. Its values are closed (`SVal.closed`): named naturals and literals only. -/
structure Cut where
  regs : List (Nat × SVal)
  cells : List (Aff × Nat × SVal)
  rd : List (Aff × Nat)
  wr : List (Aff × Nat)
  frame : List (Aff × Nat)

/-- The environment of the named naturals `vals` and a machine state. -/
def env (vals : List Nat) (ω : Regs) (μ : Memory) : Env := ⟨fun k => vals.getD k 0, ω, μ⟩

/-- What a cut asserts of (ω, μ), given the named naturals and the chain's start memory μ₀. -/
def Cut.Holds (vals : List Nat) (μ₀ : Memory) (c : Cut) (ω : Regs) (μ : Memory) : Prop :=
  RegsHold (env vals ω μ) ω c.regs ∧ CellsHold (env vals ω μ) μ c.cells ∧
  RdHold (env vals ω μ) μ c.rd ∧ WrHold (env vals ω μ) μ c.wr ∧
  (∀ t, t < two32 → (∀ f ∈ c.frame, ¬ InReg (env vals ω μ) f t) → μ.read t = μ₀.read t) ∧
  μ.pages = μ₀.pages

/-- A value that depends only on the named naturals. -/
def SVal.closed : SVal → Bool
  | .const _ | .var _ | .addr _ => true
  | .mod v _ => v.closed
  | .sx _ v => v.closed
  | .tbl _ i => i.closed
  | .alu2 _ a => a.closed
  | .alu2i _ a b _ => a.closed && b.closed
  | .alu3 _ a b d => a.closed && b.closed && d.closed
  | .reg0 _ | .mem0 _ _ => false

theorem SVal.eval_closed {ρ : Nat → Nat} {ω ω' : Regs} {μ μ' : Memory} :
    ∀ v : SVal, v.closed = true → v.eval ⟨ρ, ω, μ⟩ = v.eval ⟨ρ, ω', μ'⟩
  | .const _, _ | .var _, _ | .addr _, _ => rfl
  | .mod v _, h => by simp only [SVal.closed] at h; simp only [SVal.eval, eval_closed (ω' := ω') (μ' := μ') v h]
  | .sx _ v, h => by simp only [SVal.closed] at h; simp only [SVal.eval, eval_closed (ω' := ω') (μ' := μ') v h]
  | .tbl _ i, h => by simp only [SVal.closed] at h; simp only [SVal.eval, eval_closed (ω' := ω') (μ' := μ') i h]
  | .alu2 _ a, h => by simp only [SVal.closed] at h; simp only [SVal.eval, eval_closed (ω' := ω') (μ' := μ') a h]
  | .alu2i _ a b _, h => by
    simp only [SVal.closed, Bool.and_eq_true] at h
    simp only [SVal.eval, eval_closed (ω' := ω') (μ' := μ') a h.1, eval_closed (ω' := ω') (μ' := μ') b h.2]
  | .alu3 _ a b d, h => by
    simp only [SVal.closed, Bool.and_eq_true] at h
    simp only [SVal.eval, eval_closed (ω' := ω') (μ' := μ') a h.1.1, eval_closed (ω' := ω') (μ' := μ') b h.1.2, eval_closed (ω' := ω') (μ' := μ') d h.2]
  | .reg0 _, h | .mem0 _ _, h => by simp [SVal.closed] at h

def Cut.closed (c : Cut) : Bool :=
  c.regs.all (fun r => r.2.closed) && c.cells.all (fun x => x.2.2.closed)

theorem regsHold_env {vals : List Nat} {ω₁ ω₂ ω : Regs} {μ₁ μ₂ : Memory} :
    ∀ {l : List (Nat × SVal)}, l.all (fun r => r.2.closed) = true →
      RegsHold (env vals ω₁ μ₁) ω l → RegsHold (env vals ω₂ μ₂) ω l
  | [], _, _ => trivial
  | r :: rs, hc, ⟨h, hs⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    refine ⟨?_, regsHold_env hc.2 hs⟩
    rw [h]; unfold env; rw [SVal.eval_closed _ hc.1]

theorem cellsHold_env {vals : List Nat} {ω₁ ω₂ : Regs} {μ₁ μ₂ μ : Memory} :
    ∀ {l : List (Aff × Nat × SVal)}, l.all (fun x => x.2.2.closed) = true →
      CellsHold (env vals ω₁ μ₁) μ l → CellsHold (env vals ω₂ μ₂) μ l
  | [], _, _ => trivial
  | c :: cs, hc, ⟨h, hs⟩ => by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    refine ⟨?_, cellsHold_env hc.2 hs⟩
    rw [show Aff.eval (env vals ω₂ μ₂) c.1 = Aff.eval (env vals ω₁ μ₁) c.1 from rfl, h]
    unfold env; rw [SVal.eval_closed _ hc.1]

theorem rdHold_env {vals : List Nat} {ω₁ ω₂ : Regs} {μ₁ μ₂ μ : Memory} :
    ∀ {l : List (Aff × Nat)}, RdHold (env vals ω₁ μ₁) μ l → RdHold (env vals ω₂ μ₂) μ l
  | [], _ => trivial
  | _ :: _, ⟨h, hs⟩ => ⟨h, rdHold_env hs⟩

theorem wrHold_env {vals : List Nat} {ω₁ ω₂ : Regs} {μ₁ μ₂ μ : Memory} :
    ∀ {l : List (Aff × Nat)}, WrHold (env vals ω₁ μ₁) μ l → WrHold (env vals ω₂ μ₂) μ l
  | [], _ => trivial
  | _ :: _, ⟨h, hs⟩ => ⟨h, wrHold_env hs⟩

/-- The static part a segment runs under: the bounds and separations of the chain, the regions of
    the cut it starts from. -/
def segStatic (ub lb : List Nat) (sep : List ((Aff × Nat) × (Aff × Nat))) (A : Cut) : Static :=
  ⟨ub, lb, A.rd, A.wr, sep, []⟩

/-- **The check of one segment** from cut `A` at `start` to cut `B` at `tgt`, `k` steps: both cuts
    closed, the run entails `B` within `B.frame`, `B`'s regions lie within `A`'s, and `B.frame`
    covers `A.frame`. -/
def segCheck (G : Prog) (ub lb : List Nat) (sep : List ((Aff × Nat) × (Aff × Nat)))
    (A B : Cut) (start tgt k : Nat) : Bool :=
  let st := segStatic ub lb sep A
  A.closed && B.closed &&
  check st G ⟨A.regs, A.cells⟩ ⟨B.regs, B.cells⟩ B.frame start tgt k &&
  B.rd.all (fun r => (A.rd ++ A.wr).any (within st r.1 r.2)) &&
  B.wr.all (fun r => A.wr.any (within st r.1 r.2)) &&
  A.frame.all (fun f => B.frame.any (within st f.1 f.2))

theorem rdHold_of_any {E : Env} {μ : Memory} {L : List (Aff × Nat)} (hL : ∀ r ∈ L, ∀ t, InReg E r t → μ.readable t = true)
    {st : Static} (hpre : Pre E st) :
    ∀ {l : List (Aff × Nat)}, l.all (fun r => L.any (within st r.1 r.2)) = true → RdHold E μ l
  | [], _ => trivial
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨q, hq, hw⟩, hs⟩ := h
    exact ⟨fun t ht => hL q hq t (within_sound hpre hw t ht), rdHold_of_any hL hpre hs⟩

theorem wrHold_of_any {E : Env} {μ : Memory} {L : List (Aff × Nat)} (hL : ∀ r ∈ L, ∀ t, InReg E r t → μ.writable t = true)
    {st : Static} (hpre : Pre E st) :
    ∀ {l : List (Aff × Nat)}, l.all (fun r => L.any (within st r.1 r.2)) = true → WrHold E μ l
  | [], _ => trivial
  | r :: rs, h => by
    simp only [List.all_cons, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨q, hq, hw⟩, hs⟩ := h
    exact ⟨fun t ht => hL q hq t (within_sound hpre hw t ht), wrHold_of_any hL hpre hs⟩

/-- **A segment between two cuts**, from its check. -/
theorem seg_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {G : Prog}
    {ub lb : List Nat} {sep : List ((Aff × Nat) × (Aff × Nat))} {A B : Cut} {start tgt k : Nat}
    (h : segCheck G ub lb sep A B start tgt k = true) (hG : ProgHyp p P G)
    {vals : List Nat} (hB : BHold vals ub) (hLB : LBHold vals lb)
    (hsep : ∀ ω μ, SepHold (env vals ω μ) sep)
    {μ₀ : Memory} {ω : Regs} {μ : Memory} (hA : A.Holds vals μ₀ ω μ) (x : X)
    (hH : HostOk R G.hosts := by exact trivial) :
    ∃ ω' μ', FreeStepsH p R start ω μ x tgt ω' μ' x k ∧ B.Holds vals μ₀ ω' μ' := by
  simp only [segCheck, Cut.closed, Bool.and_eq_true, and_assoc] at h
  obtain ⟨-, -, hcb1, hcb2, hck, hrd, hwr, hfr⟩ := h
  obtain ⟨hr, hc, hrdA, hwrA, hfA, hpA⟩ := hA
  obtain ⟨ω', μ', hrun, hr', hc', hfr', hp'⟩ := check_sound (R := R) hck hG vals hB hLB ω μ
    hrdA hwrA (hsep ω μ) hr hc x hH
  have hpre : Pre (env vals ω μ) (segStatic ub lb sep A) :=
    ⟨bHold_get hB, lbHold_get hLB, rdHold_mem hrdA, wrHold_mem hwrA, sepHold_mem (hsep ω μ),
      fun q hq => by simp [segStatic] at hq⟩
  refine ⟨ω', μ', hrun, regsHold_env hcb1 hr', cellsHold_env hcb2 hc', ?_, ?_, ?_, ?_⟩
  · -- B's readable regions: within A's, whose pages μ' keeps
    have : RdHold (env vals ω μ) μ' B.rd := rdHold_of_any (L := A.rd ++ A.wr) (fun r hr t ht => by
      rw [readable_pages hp' t]
      rcases List.mem_append.1 hr with hr | hr
      · exact rdHold_mem hrdA r hr t ht
      · exact Memory.readable_of_writable (wrHold_mem hwrA r hr t ht)) hpre hrd
    exact rdHold_env this
  · exact wrHold_env (wrHold_of_any (fun r hr t ht => by
      rw [writable_pages hp' t]; exact wrHold_mem hwrA r hr t ht) hpre hwr)
  · intro t ht hout
    rw [hfr' t ht hout]
    apply hfA t ht
    intro f hf hin
    obtain ⟨g, hg, hw⟩ := List.any_eq_true.1 (List.all_eq_true.1 hfr f hf)
    exact hout g hg (within_sound hpre hw t hin)
  · rw [hp', hpA]

end PVM.SymExec
