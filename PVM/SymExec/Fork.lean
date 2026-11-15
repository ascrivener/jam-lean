import PVM.SymExec.Cut

/-!
# Forking runs (symexec)

`srun` follows one path and gives up at a branch whose condition it cannot decide. `srunF` splits
there instead: it runs on twice, once with the facts saying the condition holds and once with the
facts saying it fails (`splitB`). Every branch condition is true or false, so one of the two runs
describes the machine (`split_sound`). Each run stops at the first pc of a given stop list (loop
headers, exits) and yields a leaf: the pc, the facts taken on the way (the path condition) and the
symbolic state.

`srunF_sound`: if the start state is described, some leaf's path condition holds, and the machine
reaches that leaf's pc in a state the leaf's symbolic state describes (GP v0.8.0 §A.4–A.5, through
`sstep_sound` and `srun_sound`).
-/

namespace PVM.SymExec

open Num Exec

/-- The static part with the path facts `path` added. -/
def addF (st : Static) (path : List Fact) : Static := { st with facts := path ++ st.facts }

theorem pre_addF {E : Env} {st : Static} {path : List Fact} (hp : Pre E st)
    (hf : ∀ f ∈ path, f.Holds E) : Pre E (addF st path) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hp
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro f hm
  rcases List.mem_append.1 hm with hm | hm
  · exact hf f hm
  · exact h7 f hm

theorem pre_addF_append {E : Env} {st : Static} {fs path : List Fact} (hp : Pre E (addF st path))
    (hf : ∀ f ∈ fs, f.Holds E) : Pre E (addF st (fs ++ path)) := by
  have := pre_addF (path := fs) hp hf
  simpa [addF, List.append_assoc] using this

theorem pre_of_addF {E : Env} {st : Static} {path : List Fact} (hp : Pre E (addF st path)) :
    (∀ f ∈ path, f.Holds E) := fun f hf => hp.2.2.2.2.2.2 f (List.mem_append_left _ hf)

/-! ## Splits -/

/-- The facts that an unsigned or equality comparison of `v` with the immediate `x` holds, and that
    it fails (§A.5.8). -/
def splitU (op : RegImmOffsetOp) (v : SVal) (x : Nat) : Option (List Fact × List Fact) :=
  match op with
  | .branchEqImm => some ([.ge v x, .lt v (x + 1)], [.ne v x])
  | .branchNeImm => some ([.ne v x], [.ge v x, .lt v (x + 1)])
  | .branchLtUImm => some ([.lt v x], [.ge v x])
  | .branchGeUImm => some ([.ge v x], [.lt v x])
  | .branchLeUImm => some ([.lt v (x + 1)], [.ge v (x + 1)])
  | .branchGtUImm => some ([.ge v (x + 1)], [.lt v (x + 1)])
  | _ => none

/-- A split for a comparison with an immediate: a signed one first on the sign of `v`
    (v < 2^63 or not), then as the unsigned comparison it equals on that side. -/
def splitImm (st : Static) (op : RegImmOffsetOp) (v : SVal) (x : Nat) : Option (List Fact × List Fact) :=
  match toU op with
  | some u =>
    if (v.bnd st).any (· ≤ 2 ^ 63) || decide (2 ^ 63 ≤ v.lob st) then splitU u v x
    else some ([.lt v (2 ^ 63)], [.ge v (2 ^ 63)])
  | none => splitU op v x

/-- The facts that an unsigned comparison of two addresses holds and fails (§A.5.11). -/
def splitAddr (st : Static) (op : TwoRegOffsetOp) (v w : SVal) : Option (List Fact × List Fact) :=
  match v, w with
  | .addr a, .addr b =>
    if decide (0 ≤ a.lo st) && decide (0 ≤ b.lo st) then
      match op with
      | .branchLtU => some ([.le ⟨a.base, a.off + 1⟩ b], [.le b a])
      | .branchGeU => some ([.le b a], [.le ⟨a.base, a.off + 1⟩ b])
      | _ => none
    else none
  | _, _ => none

/-- A comparison of two registers with a literal operand, split as one with an immediate. -/
def splitVia (st : Static) (op : TwoRegOffsetOp) (v w : SVal) : Option (List Fact × List Fact) :=
  match imm2 op v w with
  | some (op', u, c) => splitImm st op' u c
  | none => none

/-- The facts that a comparison of two registers holds and fails. -/
def split2 (st : Static) (op : TwoRegOffsetOp) (v w : SVal) : Option (List Fact × List Fact) :=
  match splitAddr st op v w with
  | some r => some r
  | none => splitVia st op v w

/-- A split at the branch at `pc`: two lists of facts, one of which holds. -/
def splitB (st : Static) (G : Prog) (pc : Nat) (σ : SState) : Option (List Fact × List Fact) :=
  match G.code.find pc with
  | some (.regImmOffset op a x _, _) =>
    if op = .loadImmJump then none else splitImm st op (rdv st σ a.val) x.toNat
  | some (.twoRegOffset op a b _, _) => split2 st op (rdv st σ a.val) (rdv st σ b.val)
  | _ => none

theorem splitU_sound {E : Env} {op : RegImmOffsetOp} {v : SVal} {x : Nat} {ft ff : List Fact}
    (h : splitU op v x = some (ft, ff)) :
    (∀ f ∈ ft, f.Holds E) ∨ (∀ f ∈ ff, f.Holds E) := by
  cases op <;> simp only [splitU, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Fact.Holds] <;> omega

theorem splitImm_sound {E : Env} {st : Static} {op : RegImmOffsetOp} {v : SVal} {x : Nat}
    {ft ff : List Fact} (h : splitImm st op v x = some (ft, ff)) :
    (∀ f ∈ ft, f.Holds E) ∨ (∀ f ∈ ff, f.Holds E) := by
  unfold splitImm at h
  split at h
  · split at h
    · exact splitU_sound h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Fact.Holds]
      omega
  · exact splitU_sound h

theorem splitAddr_sound {E : Env} {st : Static} {op : TwoRegOffsetOp} {v w : SVal}
    {ft ff : List Fact} (h : splitAddr st op v w = some (ft, ff)) :
    (∀ f ∈ ft, f.Holds E) ∨ (∀ f ∈ ff, f.Holds E) := by
  unfold splitAddr at h
  split at h
  · rename_i a b
    split at h
    · have h1 := aff_shift (E := E) a 1
      cases op <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
        obtain ⟨rfl, rfl⟩ := h <;> simp only [List.mem_cons, List.not_mem_nil, or_false,
          forall_eq, Fact.Holds] <;> omega
    · cases h
  · cases h

theorem split2_sound {E : Env} {st : Static} {op : TwoRegOffsetOp} {v w : SVal}
    {ft ff : List Fact} (h : split2 st op v w = some (ft, ff)) :
    (∀ f ∈ ft, f.Holds E) ∨ (∀ f ∈ ff, f.Holds E) := by
  unfold split2 at h
  split at h
  · rename_i r hr; cases h; exact splitAddr_sound hr
  · unfold splitVia at h
    split at h
    · exact splitImm_sound h
    · cases h

theorem splitB_sound {E : Env} {st : Static} {G : Prog} {pc : Nat} {σ : SState}
    {ft ff : List Fact} (h : splitB st G pc σ = some (ft, ff)) :
    (∀ f ∈ ft, f.Holds E) ∨ (∀ f ∈ ff, f.Holds E) := by
  unfold splitB at h
  split at h
  · split at h
    · cases h
    · exact splitImm_sound h
  · exact split2_sound h
  · cases h

/-! ## The forking run -/

/-- One step, ALU, memory, jump or decided branch (`sstep`), or a listed host call (`hstep`). -/
def step1 (st : Static) (G : Prog) (pc : Nat) (σ : SState) : Option (Nat × SState) :=
  match sstep st G pc σ with
  | some r => some r
  | none => hstep st G pc σ

theorem srun_one {st : Static} {G : Prog} {pc pc' : Nat} {σ σ' : SState}
    (h : step1 st G pc σ = some (pc', σ')) : srun st G pc' 1 pc σ = some σ' := by
  unfold step1 at h
  simp only [srun]
  split at h
  · rename_i r hs; cases h; rw [hs]; simp
  · rename_i hs; rw [hs, h]; simp

/-- A leaf of a forking run: the pc it stops at, its path facts, and its symbolic state. -/
abbrev Leaf0 := Nat × List Fact × SState

/-- **The forking run.** From `pc`, with path facts `path`, step until a pc of `stops` (after at
    least one step), splitting at undecided branches. `fuel` bounds the steps and splits on each
    path. -/
def srunF (st : Static) (G : Prog) (stops : List Nat) : Nat → List Fact → Nat → SState → Option (List Leaf0)
  | 0, _, _, _ => none
  | fuel + 1, path, pc, σ =>
    match step1 (addF st path) G pc σ with
    | some (pc', σ') => if stops.contains pc' then some [(pc', path, σ')] else srunF st G stops fuel path pc' σ'
    | none =>
      match splitB (addF st path) G pc σ with
      | some (ft, ff) =>
        match srunF st G stops fuel (ft ++ path) pc σ, srunF st G stops fuel (ff ++ path) pc σ with
        | some l1, some l2 => some (l1 ++ l2)
        | _, _ => none
      | none => none

/-- **Soundness of the forking run**: some leaf's path facts hold, and the machine reaches the
    leaf's pc in a state that the leaf describes. -/
theorem srunF_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {G : Prog}
    {st : Static} {stops : List Nat} {E : Env}
    (hG : ProgHyp p P G) (hH : HostOk R G.hosts) (x : X) :
    ∀ (fuel : Nat) (path : List Fact) (pc : Nat) (σ : SState) (ω : Regs) (μ : Memory)
      (leaves : List Leaf0),
      Pre E (addF st path) → Inv E σ ω μ → srunF st G stops fuel path pc σ = some leaves →
      ∃ ℓ ∈ leaves, ∃ k ω' μ', FreeStepsH p R pc ω μ x ℓ.1 ω' μ' x k ∧
        Pre E (addF st ℓ.2.1) ∧ Inv E ℓ.2.2 ω' μ' := by
  intro fuel
  induction fuel with
  | zero => intro path pc σ ω μ leaves _ _ h; simp [srunF] at h
  | succ fuel ih =>
    intro path pc σ ω μ leaves hpre hinv h
    simp only [srunF] at h
    split at h
    · rename_i pc' σ' hs
      obtain ⟨ω₁, μ₁, hrun, hi₁⟩ := srun_sound (E := E) hG hH hpre x 1 pc σ ω μ σ' hinv (srun_one hs)
      split at h
      · cases h
        exact ⟨_, List.mem_singleton_self _, 1, ω₁, μ₁, hrun, hpre, hi₁⟩
      · obtain ⟨ℓ, hℓ, k, ω', μ', hr, hp, hi⟩ := ih path pc' σ' ω₁ μ₁ leaves hpre hi₁ h
        exact ⟨ℓ, hℓ, 1 + k, ω', μ', FreeStepsH.trans hrun hr, hp, hi⟩
    · split at h
      · rename_i ft ff hsp
        split at h
        · rename_i l1 l2 h1 h2
          cases h
          rcases splitB_sound hsp with hf | hf
          · obtain ⟨ℓ, hℓ, rest⟩ := ih (ft ++ path) pc σ ω μ l1 (pre_addF_append hpre hf) hinv h1
            exact ⟨ℓ, List.mem_append_left _ hℓ, rest⟩
          · obtain ⟨ℓ, hℓ, rest⟩ := ih (ff ++ path) pc σ ω μ l2 (pre_addF_append hpre hf) hinv h2
            exact ⟨ℓ, List.mem_append_right _ hℓ, rest⟩
        · cases h
      · cases h

/-! ## Leaves as cuts

A leaf's target is a cut `B` whose named naturals are given by values `sub` over the start
environment (for a loop's back edge: the next iteration's named naturals). -/

/-- The values of `sub` in `E`: the named naturals of a target cut. -/
def svals (E : Env) (sub : List SVal) : List Nat := sub.map (SVal.eval E)

theorem getD_svals {E : Env} : ∀ {sub : List SVal} {k : Nat},
    (svals E sub).getD k 0 = (sub.getD k (.const 0)).eval E
  | [], k => by simp [svals, SVal.eval]
  | v :: vs, 0 => by simp [svals]
  | v :: vs, k + 1 => by simpa [svals] using getD_svals (E := E) (sub := vs) (k := k)

/-- An address of a target cut, over the start environment. -/
def substAff (st : Static) (sub : List SVal) (a : Aff) : Option Aff :=
  match a.base with
  | none => some a
  | some k =>
    match asAff (sub.getD k (.const 0)) with
    | some b => if decide (0 ≤ b.lo st) then some ⟨b.base, b.off + a.off⟩ else none
    | none => none

/-- A value of a target cut, over the start environment. -/
def SVal.subst (st : Static) (sub : List SVal) : SVal → Option SVal
  | .const n => some (.const n)
  | .var k => some (sub.getD k (.const 0))
  | .addr a => (substAff st sub a).map .addr
  | .mod v m => (v.subst st sub).map (.mod · m)
  | .sx k v => (v.subst st sub).map (.sx k ·)
  | .tbl vs i => (i.subst st sub).map (.tbl vs ·)
  | .alu2 op a => (a.subst st sub).map (.alu2 op ·)
  | .alu2i op a b x =>
    match a.subst st sub, b.subst st sub with
    | some a', some b' => some (.alu2i op a' b' x)
    | _, _ => none
  | .alu3 op a b d =>
    match a.subst st sub, b.subst st sub, d.subst st sub with
    | some a', some b', some d' => some (.alu3 op a' b' d')
    | _, _, _ => none
  | .reg0 _ | .mem0 _ _ => none

section Subst
variable {E : Env} {st : Static} {sub : List SVal} {ω' : Regs} {μ' : Memory}

theorem substAff_eval (hpre : Pre E st) {a a' : Aff} (h : substAff st sub a = some a') :
    a'.eval E = a.eval ⟨fun k => (svals E sub).getD k 0, ω', μ'⟩ := by
  obtain ⟨base, off⟩ := a
  cases base with
  | none => simp only [substAff, Option.some.injEq] at h; subst h; simp [Aff.eval]
  | some k =>
    simp only [substAff] at h
    split at h
    · rename_i b hb
      split at h
      · rename_i hlo
        cases h
        have := asAff_sound hb (by simpa using hlo) hpre
        rw [aff_shift]
        show b.eval E + off = (((svals E sub).getD k 0 : Nat) : Int) + off
        rw [getD_svals]
        omega
      · cases h
    · cases h

theorem subst_eval (hpre : Pre E st) :
    ∀ (v : SVal) {v' : SVal}, v.subst st sub = some v' →
      v'.eval E = v.eval ⟨fun k => (svals E sub).getD k 0, ω', μ'⟩
  | .const n, v', h => by simp only [SVal.subst, Option.some.injEq] at h; subst h; rfl
  | .var k, v', h => by
    simp only [SVal.subst, Option.some.injEq] at h; subst h
    show _ = (svals E sub).getD k 0
    rw [getD_svals]
  | .addr a, v', h => by
    simp only [SVal.subst] at h
    cases ha : substAff st sub a with
    | none => rw [ha] at h; cases h
    | some a' =>
      rw [ha] at h; cases h
      simp only [SVal.eval]; rw [substAff_eval hpre ha]
  | .mod v m, v', h => by
    simp only [SVal.subst] at h
    cases hv : v.subst st sub with
    | none => rw [hv] at h; cases h
    | some w => rw [hv] at h; cases h; simp only [SVal.eval]; rw [subst_eval hpre v hv]
  | .sx k v, v', h => by
    simp only [SVal.subst] at h
    cases hv : v.subst st sub with
    | none => rw [hv] at h; cases h
    | some w => rw [hv] at h; cases h; simp only [SVal.eval]; rw [subst_eval hpre v hv]
  | .tbl vs i, v', h => by
    simp only [SVal.subst] at h
    cases hv : i.subst st sub with
    | none => rw [hv] at h; cases h
    | some w => rw [hv] at h; cases h; simp only [SVal.eval]; rw [subst_eval hpre i hv]
  | .alu2 op a, v', h => by
    simp only [SVal.subst] at h
    cases hv : a.subst st sub with
    | none => rw [hv] at h; cases h
    | some w => rw [hv] at h; cases h; simp only [SVal.eval]; rw [subst_eval hpre a hv]
  | .alu2i op a b x, v', h => by
    simp only [SVal.subst] at h
    split at h
    · rename_i a' b' ha hb
      cases h; simp only [SVal.eval]; rw [subst_eval hpre a ha, subst_eval hpre b hb]
    · cases h
  | .alu3 op a b d, v', h => by
    simp only [SVal.subst] at h
    split at h
    · rename_i a' b' d' ha hb hd
      cases h; simp only [SVal.eval]; rw [subst_eval hpre a ha, subst_eval hpre b hb, subst_eval hpre d hd]
    · cases h
  | .reg0 _, v', h => by simp [SVal.subst] at h
  | .mem0 _ _, v', h => by simp [SVal.subst] at h

end Subst

/-- `f` on every element, if it succeeds on each. -/
def omap {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | a :: as =>
    match f a, omap f as with
    | some b, some bs => some (b :: bs)
    | _, _ => none

theorem omap_mem {α β : Type} {f : α → Option β} : ∀ {l : List α} {l' : List β}, omap f l = some l' →
    (∀ a ∈ l, ∃ b ∈ l', f a = some b) ∧ (∀ b ∈ l', ∃ a ∈ l, f a = some b)
  | [], l', h => by simp only [omap, Option.some.injEq] at h; subst h; simp
  | a :: as, l', h => by
    simp only [omap] at h
    split at h
    · rename_i b bs hb hbs
      cases h
      obtain ⟨h1, h2⟩ := omap_mem hbs
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨b, List.mem_cons_self .., hb⟩
        · obtain ⟨y, hy, hf⟩ := h1 x hx; exact ⟨y, List.mem_cons_of_mem _ hy, hf⟩
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., hb⟩
        · obtain ⟨x, hx, hf⟩ := h2 y hy; exact ⟨x, List.mem_cons_of_mem _ hx, hf⟩
    · cases h

theorem regsHold_of_mem {E : Env} {ω : Regs} : ∀ {l : List (Nat × SVal)},
    (∀ r ∈ l, ω.get (regIdx r.1) = UInt64.ofNat (r.2.eval E)) → RegsHold E ω l
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (List.mem_cons_self ..), regsHold_of_mem fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem cellsHold_of_mem {E : Env} {μ : Memory} : ∀ {l : List (Aff × Nat × SVal)},
    (∀ c ∈ l, μ.readN (c.1.eval E).toNat c.2.1 = encodeLE c.2.1 (c.2.2.eval E)) → CellsHold E μ l
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (List.mem_cons_self ..), cellsHold_of_mem fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem rdHold_of_mem {E : Env} {μ : Memory} : ∀ {l : List (Aff × Nat)},
    (∀ r ∈ l, ∀ t, InReg E r t → μ.readable t = true) → RdHold E μ l
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (List.mem_cons_self ..), rdHold_of_mem fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem wrHold_of_mem {E : Env} {μ : Memory} : ∀ {l : List (Aff × Nat)},
    (∀ r ∈ l, ∀ t, InReg E r t → μ.writable t = true) → WrHold E μ l
  | [], _ => trivial
  | _ :: _, h => ⟨h _ (List.mem_cons_self ..), wrHold_of_mem fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

/-- A leaf of a forking check: the pc, the path facts, the target cut and its named naturals. -/
structure Leaf where
  pc : Nat
  facts : List Fact
  B : Cut
  sub : List SVal

def substReg (st : Static) (sub : List SVal) (r : Aff × Nat) : Option (Aff × Nat) :=
  (substAff st sub r.1).map (·, r.2)

def substRegs (st : Static) (sub : List SVal) (r : Nat × SVal) : Option (Nat × SVal) :=
  (r.2.subst st sub).map (r.1, ·)

def substCell (st : Static) (sub : List SVal) (c : Aff × Nat × SVal) : Option (Aff × Nat × SVal) :=
  match substAff st sub c.1, c.2.2.subst st sub with
  | some a, some v => some (a, c.2.1, v)
  | _, _ => none

/-- The end state σ of a path from cut `A` meets the leaf's target cut: its registers and cells,
    writes only inside its frame, its regions inside `A`'s, and its frame covers `A`'s. -/
def leafOk (st : Static) (A : Cut) (σ : SState) (ℓ : Leaf) : Bool :=
  match omap (substRegs st ℓ.sub) ℓ.B.regs, omap (substCell st ℓ.sub) ℓ.B.cells,
      omap (substReg st ℓ.sub) ℓ.B.rd, omap (substReg st ℓ.sub) ℓ.B.wr,
      omap (substReg st ℓ.sub) ℓ.B.frame with
  | some regs, some cells, some rd, some wr, some frame =>
    ℓ.B.closed && entails st σ ⟨regs, cells⟩ frame &&
    rd.all (fun r => (A.rd ++ A.wr).any (within st r.1 r.2)) &&
    wr.all (fun r => A.wr.any (within st r.1 r.2)) &&
    A.frame.all (fun f => frame.any (within st f.1 f.2))
  | _, _, _, _, _ => false

/-- The static part a forking check runs under. -/
def forkStatic (ub lb : List Nat) (sep : List ((Aff × Nat) × (Aff × Nat))) (A : Cut)
    (asm : List Fact) : Static :=
  { ub := ub, lb := lb, rd := A.rd, wr := A.wr, sep := sep, facts := asm }

/-- **The check of a forking segment** from cut `A` (with facts `asm`) at `start`: every path of
    `srunF` ends at a listed leaf, with the same path facts, meeting the leaf's target cut. -/
def forkCheck (G : Prog) (ub lb : List Nat) (sep : List ((Aff × Nat) × (Aff × Nat))) (A : Cut)
    (asm : List Fact) (leaves : List Leaf) (start fuel : Nat) : Bool :=
  let st := forkStatic ub lb sep A asm
  A.closed && initOk st ⟨A.regs, A.cells⟩ &&
  match srunF st G (leaves.map (·.pc)) fuel [] start (init ⟨A.regs, A.cells⟩) with
  | some ls => ls.all fun l => leaves.any fun ℓ =>
      ℓ.pc == l.1 && ℓ.facts == l.2.1 && leafOk (addF st l.2.1) A l.2.2 ℓ
  | none => false

theorem inReg_subst {E : Env} {st : Static} {sub : List SVal} {ω' : Regs} {μ' : Memory}
    (hpre : Pre E st) {r r' : Aff × Nat} (h : substReg st sub r = some r') (t : Nat) :
    InReg ⟨fun k => (svals E sub).getD k 0, ω', μ'⟩ r t ↔ InReg E r' t := by
  unfold substReg at h
  cases ha : substAff st sub r.1 with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h; cases h
    simp only [InReg]; rw [substAff_eval (ω' := ω') (μ' := μ') hpre ha]

/-- **Soundness of a forking segment**: some leaf's path facts hold at the start, and the machine
    reaches its pc in a state its target cut describes, with the named naturals `sub`. -/
theorem fork_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {G : Prog}
    {ub lb : List Nat} {sep : List ((Aff × Nat) × (Aff × Nat))} {A : Cut} {asm : List Fact}
    {leaves : List Leaf} {start fuel : Nat}
    (h : forkCheck G ub lb sep A asm leaves start fuel = true) (hG : ProgHyp p P G)
    (hH : HostOk R G.hosts)
    {vals : List Nat} (hB : BHold vals ub) (hLB : LBHold vals lb)
    (hsep : ∀ ω μ, SepHold (env vals ω μ) sep)
    {μ₀ : Memory} {ω : Regs} {μ : Memory} (hA : A.Holds vals μ₀ ω μ)
    (hasm : FactsHold (env vals ω μ) asm) (x : X) :
    ∃ ℓ ∈ leaves, ∃ k ω' μ', FreeStepsH p R start ω μ x ℓ.pc ω' μ' x k ∧
      FactsHold (env vals ω μ) ℓ.facts ∧
      ℓ.B.Holds (svals (env vals ω μ) ℓ.sub) μ₀ ω' μ' := by
  simp only [forkCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hAc, hok⟩, h⟩ := h
  split at h
  · rename_i ls hrun
    let E := env vals ω μ
    let st := forkStatic ub lb sep A asm
    obtain ⟨hr, hc, hrdA, hwrA, hfA, hpA⟩ := hA
    have hpre : Pre E st :=
      ⟨bHold_get hB, lbHold_get hLB, rdHold_mem hrdA, wrHold_mem hwrA, sepHold_mem (hsep ω μ),
        fun q hq => by simp [st, forkStatic] at hq, factsHold_mem hasm⟩
    have hpre0 : Pre E (addF st []) := by simpa [addF] using hpre
    have hinv := init_inv (E := E) hpre hok hr hc
    obtain ⟨l, hl, k, ω', μ', hsteps, hpl, hil⟩ :=
      srunF_sound (E := E) (stops := leaves.map (·.pc)) hG hH x fuel [] start _ ω μ ls hpre0 hinv hrun
    obtain ⟨ℓ, hℓ, hm⟩ := List.any_eq_true.1 (List.all_eq_true.1 h l hl)
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    obtain ⟨⟨hpc, hfs⟩, hok'⟩ := hm
    refine ⟨ℓ, hℓ, k, ω', μ', hpc ▸ hsteps, factsHold_of_mem (hfs ▸ pre_of_addF hpl), ?_⟩
    -- the leaf's target cut
    unfold leafOk at hok'
    split at hok'
    · rename_i regs cells rd wr frame hregs hcells hrd hwr hframe
      simp only [Bool.and_eq_true] at hok'
      obtain ⟨⟨⟨⟨hBc, hent⟩, hrdin⟩, hwrin⟩, hfrin⟩ := hok'
      obtain ⟨hR, hC, hF, hP⟩ := entails_sound hpl hil hent
      have hpre' : Pre E (addF st l.2.1) := hpl
      let E' : Env := ⟨fun k => (svals E ℓ.sub).getD k 0, ω', μ'⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply regsHold_of_mem
        intro r hrm
        obtain ⟨r', hr'm, hsr⟩ := (omap_mem hregs).1 r hrm
        unfold substRegs at hsr
        cases hv : r.2.subst (addF st l.2.1) ℓ.sub with
        | none => rw [hv] at hsr; cases hsr
        | some v' =>
          rw [hv] at hsr; cases hsr
          have := regsHold_mem hR _ hr'm
          simp only at this
          rw [this, subst_eval (ω' := ω') (μ' := μ') hpre' r.2 hv]
          rfl
      · apply cellsHold_of_mem
        intro c hcm
        obtain ⟨c', hc'm, hsc⟩ := (omap_mem hcells).1 c hcm
        unfold substCell at hsc
        split at hsc
        · rename_i a v ha hv
          cases hsc
          have := cellsHold_mem hC _ hc'm
          simp only at this
          rw [substAff_eval (ω' := ω') (μ' := μ') hpre' ha,
            subst_eval (ω' := ω') (μ' := μ') hpre' _ hv] at this
          exact this
        · cases hsc
      · apply rdHold_of_mem
        intro r hrm t ht
        obtain ⟨r', hr'm, hsr⟩ := (omap_mem hrd).1 r hrm
        have ht' := (inReg_subst hpre' hsr t).1 ht
        obtain ⟨q, hq, hw⟩ := List.any_eq_true.1 (List.all_eq_true.1 hrdin r' hr'm)
        have hin := within_sound hpre' hw t ht'
        rw [readable_pages hP t]
        rcases List.mem_append.1 hq with hq | hq
        · exact rdHold_mem hrdA q hq t hin
        · exact Memory.readable_of_writable (wrHold_mem hwrA q hq t hin)
      · apply wrHold_of_mem
        intro r hrm t ht
        obtain ⟨r', hr'm, hsr⟩ := (omap_mem hwr).1 r hrm
        have ht' := (inReg_subst hpre' hsr t).1 ht
        obtain ⟨q, hq, hw⟩ := List.any_eq_true.1 (List.all_eq_true.1 hwrin r' hr'm)
        have hin := within_sound hpre' hw t ht'
        rw [writable_pages hP t]
        exact wrHold_mem hwrA q hq t hin
      · intro t ht hout
        rw [hF t ht ?_]
        · apply hfA t ht
          intro f hf hin
          obtain ⟨g, hg, hw⟩ := List.any_eq_true.1 (List.all_eq_true.1 hfrin f hf)
          have hin' := within_sound hpre' hw t hin
          obtain ⟨g0, hg0, hsg⟩ := (omap_mem hframe).2 g hg
          exact hout g0 hg0 ((inReg_subst hpre' hsg t).2 hin')
        · intro f hf hin
          obtain ⟨g0, hg0, hsg⟩ := (omap_mem hframe).2 f hf
          exact hout g0 hg0 ((inReg_subst hpre' hsg t).2 hin)
      · exact hP.trans hpA
    · cases hok'
  · cases h

end PVM.SymExec
