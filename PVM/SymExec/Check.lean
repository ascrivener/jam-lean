import PVM.SymExec.Sound

/-!
# One Boolean check per stretch (spike)

`check` runs `srun` from the state an assumption `Spec` describes and compares the end state with
a target `Spec` and a frame. `check_sound` turns `check … = true`, evaluated by the kernel, into
the stretch's theorem: a `FreeStepsH` chain of exactly `k` steps whose end state satisfies the
target, leaves every octet outside the frame unchanged, and keeps the page map.
-/

namespace PVM.SymExec

open Num Exec

/-- Facts about registers `(r, v)`: ω_r = v, and memory cells `(a, n, v)`: μ_{a…+n} = ℰ_n(v). -/
structure Spec where
  regs : List (Nat × SVal)
  cells : List (Aff × Nat × SVal)

def RegsHold (E : Env) (ω : Regs) : List (Nat × SVal) → Prop
  | [] => True
  | r :: rs => ω.get (regIdx r.1) = UInt64.ofNat (r.2.eval E) ∧ RegsHold E ω rs

def CellsHold (E : Env) (μ : Memory) : List (Aff × Nat × SVal) → Prop
  | [] => True
  | c :: cs => μ.readN (c.1.eval E).toNat c.2.1 = encodeLE c.2.1 (c.2.2.eval E) ∧ CellsHold E μ cs

/-- The regions of a list are readable. -/
def RdHold (E : Env) (μ : Memory) : List (Aff × Nat) → Prop
  | [] => True
  | r :: rs => (∀ t, InReg E r t → μ.readable t = true) ∧ RdHold E μ rs

/-- The regions of a list are writable. -/
def WrHold (E : Env) (μ : Memory) : List (Aff × Nat) → Prop
  | [] => True
  | r :: rs => (∀ t, InReg E r t → μ.writable t = true) ∧ WrHold E μ rs

/-- Each rewrite (p, q) holds: p and q have the same value. -/
def RwHold (E : Env) : List (SVal × SVal) → Prop
  | [] => True
  | q :: qs => q.1.eval E = q.2.eval E ∧ RwHold E qs

theorem rwHold_mem {E : Env} : ∀ {l : List (SVal × SVal)}, RwHold E l → ∀ q ∈ l, q.1.eval E = q.2.eval E
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, _, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h
    · exact rwHold_mem hs _ hq

/-- The pairs of regions of a list are disjoint. -/
def SepHold (E : Env) : List ((Aff × Nat) × (Aff × Nat)) → Prop
  | [] => True
  | p :: ps => (∀ t, InReg E p.1 t → ¬ InReg E p.2 t) ∧ SepHold E ps

/-- Each named natural is below its bound. -/
def BHold : List Nat → List Nat → Prop
  | v :: vs, b :: bs => v < b ∧ BHold vs bs
  | [], [] => True
  | _, _ => False

/-- Each named natural is at least its lower bound. -/
def LBHold : List Nat → List Nat → Prop
  | v :: vs, b :: bs => b ≤ v ∧ LBHold vs bs
  | [], [] => True
  | _, _ => False

theorem regsHold_mem {E : Env} {ω : Regs} :
    ∀ {l : List (Nat × SVal)}, RegsHold E ω l → ∀ r ∈ l, ω.get (regIdx r.1) = UInt64.ofNat (r.2.eval E)
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, r, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact regsHold_mem hs r hm

theorem cellsHold_mem {E : Env} {μ : Memory} :
    ∀ {l : List (Aff × Nat × SVal)}, CellsHold E μ l → ∀ c ∈ l,
      μ.readN (c.1.eval E).toNat c.2.1 = encodeLE c.2.1 (c.2.2.eval E)
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, c, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact cellsHold_mem hs c hm

theorem rdHold_mem {E : Env} {μ : Memory} : ∀ {l : List (Aff × Nat)}, RdHold E μ l →
    ∀ r ∈ l, ∀ t, InReg E r t → μ.readable t = true
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, r, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact rdHold_mem hs r hm

theorem wrHold_mem {E : Env} {μ : Memory} : ∀ {l : List (Aff × Nat)}, WrHold E μ l →
    ∀ r ∈ l, ∀ t, InReg E r t → μ.writable t = true
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, r, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact wrHold_mem hs r hm

theorem sepHold_mem {E : Env} : ∀ {l : List ((Aff × Nat) × (Aff × Nat))}, SepHold E l →
    ∀ p ∈ l, ∀ t, InReg E p.1 t → ¬ InReg E p.2 t
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, r, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact sepHold_mem hs r hm

theorem bHold_get : ∀ {vs bs : List Nat}, BHold vs bs → ∀ k b, bs[k]? = some b → vs.getD k 0 < b
  | [], [], _, k, b, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | v :: vs, b' :: bs, ⟨h1, h2⟩, k, b, h => by
    cases k with
    | zero => simp at h; subst h; simpa using h1
    | succ k => simpa using bHold_get h2 k b (by simpa using h)

theorem lbHold_get : ∀ {vs bs : List Nat}, LBHold vs bs → ∀ k b, bs[k]? = some b → b ≤ vs.getD k 0
  | [], [], _, k, b, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | v :: vs, b' :: bs, ⟨h1, h2⟩, k, b, h => by
    cases k with
    | zero => simp at h; subst h; simpa using h1
    | succ k => simpa using lbHold_get h2 k b (by simpa using h)

/-- The start state an assumption describes: the listed registers and cells; every other
    register is its own start value. -/
def init (A : Spec) : SState :=
  { regs := (List.range 13).map fun r => (A.regs.lookup r).getD (.reg0 r)
    cells := A.cells
    dirty := [] }

def initOk (st : Static) (A : Spec) : Bool :=
  A.regs.all (fun r => r.1 < 13) && A.cells.all (fun c => valid st c.1 c.2.1)

/-- The end state σ has the target's registers and cells, and writes only inside `frame`. -/
def entails (st : Static) (σ : SState) (T : Spec) (frame : List (Aff × Nat)) : Bool :=
  T.regs.all (fun r => r.1 < 13 &&
    mkMod st (σ.regs.getD r.1 (.const 0)) two64 == mkMod st r.2 two64) &&
  T.cells.all (fun t => (valid st t.1 t.2.1 && σ.cells.any fun c =>
    c.1 == t.1 && c.2.1 == t.2.1 && mkMod st c.2.2 (2 ^ (8 * t.2.1)) == mkMod st t.2.2 (2 ^ (8 * t.2.1))) ||
    (valid st t.1 t.2.1 && match t.2.2, assemble σ.cells t.2.1 t.1 t.2.1 with
    | .const v, some w => w % 256 ^ t.2.1 == v % 256 ^ t.2.1
    | _, _ => false)) &&
  σ.dirty.all (fun d => frame.any (within st d.1 d.2))

/-- The check of one stretch: from `A` at `start`, `srun` runs `k` steps to `tgt`, ending in a state
    that entails `T` within `frame`. -/
def check (st : Static) (G : Prog) (A T : Spec)
    (frame : List (Aff × Nat)) (start tgt k : Nat) : Bool :=
  initOk st A &&
  match srun st G tgt k start (init A) with
  | some σ => entails st σ T frame
  | none => false

theorem ofNat_eq_of_mod {a b : Nat} (h : a % two64 = b % two64) : UInt64.ofNat a = UInt64.ofNat b := by
  apply UInt64.toNat.inj
  simpa using h

theorem mem_of_lookup {l : List (Nat × SVal)} {k : Nat} {v : SVal} (h : l.lookup k = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e es ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.lookup_cons] at h
    by_cases hk : k = a
    · subst hk; simp at h; subst h; exact List.mem_cons_self
    · rw [show (k == a) = false by simpa using hk] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem init_inv {E : Env} {st : Static} {A : Spec} (hpre : Pre E st) (hok : initOk st A = true)
    (hr : RegsHold E E.ω A.regs)
    (hc : CellsHold E E.μ A.cells) : Inv E (init A) E.ω E.μ := by
  simp only [initOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  refine ⟨by simp [init], ?_, ?_, fun _ _ _ => rfl, rfl⟩
  · intro r
    have hgd : (init A).regs.getD r.val (.const 0) = (A.regs.lookup r.val).getD (.reg0 r.val) := by
      simp [init, List.getD_eq_getElem?_getD, r.isLt]
    rw [hgd]
    have hri : regIdx r.val = r := by
      apply Fin.ext; simp [regIdx]; omega
    cases hl : A.regs.lookup r.val with
    | none =>
      simp only [Option.getD_none, SVal.eval, hri]
      simp
    | some v =>
      have hm : (r.val, v) ∈ A.regs := mem_of_lookup hl
      have := regsHold_mem hr _ hm
      simp only [hri] at this
      simpa using this
  · intro c hcm
    obtain ⟨h0, h1, -⟩ := valid_sound hpre (hok.2 c hcm)
    exact ⟨h0, h1, cellsHold_mem hc c hcm⟩

theorem entails_sound {E : Env} {st : Static} (hpre : Pre E st)
    {σ : SState} {ω : Regs} {μ : Memory} {T : Spec} {frame : List (Aff × Nat)}
    (hinv : Inv E σ ω μ) (h : entails st σ T frame = true) :
    RegsHold E ω T.regs ∧ CellsHold E μ T.cells ∧
      (∀ t, t < two32 → (∀ f ∈ frame, ¬ InReg E f t) → μ.read t = E.μ.read t) ∧
      μ.pages = E.μ.pages := by
  obtain ⟨_, hr, hc, hf, hp⟩ := hinv
  simp only [entails, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hR, hC⟩, hD⟩ := h
  refine ⟨?_, ?_, ?_, hp⟩
  · clear hC hD
    generalize T.regs = l at hR
    induction l with
    | nil => trivial
    | cons t ts ih =>
      refine ⟨?_, ih (fun x hx => hR x (List.mem_cons_of_mem _ hx))⟩
      have ht := hR t (List.mem_cons_self ..)
      simp only [decide_eq_true_eq, beq_iff_eq] at ht
      obtain ⟨hlt, heq⟩ := ht
      have hri : regIdx t.1 = ⟨t.1, hlt⟩ := by apply Fin.ext; simp [regIdx]; omega
      rw [hri, hr ⟨t.1, hlt⟩]
      apply ofNat_eq_of_mod
      have := congrArg (SVal.eval E) heq
      rwa [mkMod_eval hpre, mkMod_eval hpre] at this
  · clear hR hD
    generalize T.cells = l at hC
    induction l with
    | nil => trivial
    | cons t ts ih =>
      refine ⟨?_, ih (fun x hx => hC x (List.mem_cons_of_mem _ hx))⟩
      have ht := hC t (List.mem_cons_self ..)
      rw [Bool.or_eq_true] at ht
      rcases ht with ht | ht
      · simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at ht
        obtain ⟨-, c, hcm, ⟨⟨h1, h2⟩, h3⟩⟩ := ht
        have := congrArg (SVal.eval E) h3
        rw [mkMod_eval hpre, mkMod_eval hpre] at this
        rw [← h1, ← h2, (hc c hcm).2.2, ← encodeLE_mod c.2.1 (SVal.eval E c.2.2),
          ← encodeLE_mod c.2.1 (SVal.eval E t.2.2), ← pow8, h2, this]
      · simp only [Bool.and_eq_true] at ht
        obtain ⟨hv0, ht⟩ := ht
        obtain ⟨ha0, -, -⟩ := valid_sound hpre hv0
        split at ht
        · rename_i v w hv hw
          simp only [beq_iff_eq] at ht
          rw [cellsT hc _ _ _ _ hw ha0, hv, SVal.eval,
            ← encodeLE_mod t.2.1 w, ht, encodeLE_mod]
        · cases ht
  · intro t ht hout
    apply hf t ht
    intro d hd hin
    have := hD d hd
    obtain ⟨f, hfm, hw⟩ := List.any_eq_true.1 this
    exact hout f hfm (within_sound hpre hw t hin)

/-- A cell given as a list of octets. -/
theorem cell_of_list {μ : Memory} {a n : Nat} {l : List UInt8} (h : μ.readN a n = l)
    (hn : l.length = n) : μ.readN a n = encodeLE n (decodeLE l) := by
  subst hn; rw [h, encodeLE_decodeLE]

theorem list_of_cell {μ : Memory} {a n : Nat} {l : List UInt8} (hn : l.length = n)
    (h : μ.readN a n = encodeLE n (decodeLE l)) : μ.readN a n = l := by
  subst hn; rw [h, encodeLE_decodeLE]

/-- A literal range `[lo, hi)` of readable octets as a region. -/
theorem rng_rd {E : Env} {μ : Memory} {lo hi : Nat} (h : ∀ a, lo ≤ a → a < hi → μ.readable a = true) :
    ∀ t, InReg E (⟨none, lo⟩, hi - lo) t → μ.readable t = true := by
  intro t ht; simp only [InReg, Aff.eval] at ht; exact h t (by omega) (by omega)

/-- A literal range `[lo, hi)` of writable octets as a region. -/
theorem rng_wr {E : Env} {μ : Memory} {lo hi : Nat} (h : ∀ a, lo ≤ a → a < hi → μ.writable a = true) :
    ∀ t, InReg E (⟨none, lo⟩, hi - lo) t → μ.writable t = true := by
  intro t ht; simp only [InReg, Aff.eval] at ht; exact h t (by omega) (by omega)

/-- An octet outside every literal region of a frame. -/
theorem out_of_bool {E : Env} {frame : List (Aff × Nat)} {t : Nat}
    (h : frame.all (fun f => f.1.base == none && (decide ((t : Int) < f.1.off) ||
      decide (f.1.off + f.2 ≤ t))) = true) : ∀ f ∈ frame, ¬ InReg E f t := by
  intro f hf hin
  have := List.all_eq_true.1 h f hf
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at this
  obtain ⟨hb, h2⟩ := this
  simp only [InReg, Aff.eval, hb] at hin
  omega

/-- A return `jump_ind r, 0` to a symbolic address `ret` (an entry of **j**, GP eq.
    `jumptablealignment`) as the last step of a stretch. -/
theorem ret_step {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {pc n : Nat} {r : RegIdx}
    {ω : Regs} {μ : Memory} {x : X} {ret t : Nat}
    (hd : deblob p pc = some P ∧ P.decode pc = some (.regImm .jumpInd r 0) ∧ P.next pc = n ∧
      P.blockCost (P.blockStartOf pc) ≤ stepCostCap)
    (hr : ω.get r = UInt64.ofNat ret) (h1 : 0 < ret) (h2 : ret ≤ P.jumpTable.size * 2)
    (h3 : ret % 2 = 0) (h4 : ret < 2 ^ 32 - 2 ^ 16)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true) :
    FreeStepsH p R pc ω μ x t ω μ x 1 := by
  apply FreeStepsH.step_decode hd _ FreeStepsH.refl
  have hrn : (ω.get r).toNat = ret := by
    rw [hr]; simp; omega
  have ha : ((ω.get r).toNat + UInt64.toNat 0) % two32 = ret := by
    rw [hrn, show UInt64.toNat 0 = 0 from rfl, Nat.add_zero, Nat.mod_eq_of_lt (by simp only [two32]; omega)]
  have hd1 : ¬ (ret = 2 ^ 32 - 2 ^ 16) := by omega
  have hd2 : ¬ (ret = 0 ∨ ret > P.jumpTable.size * 2 ∨ ret % 2 ≠ 0) := by omega
  simp only [Program.exec, Program.djump, Program.finalState, memoryException, ha, hd1, hd2,
    ↓reduceIte, hjt, hbt]
  rfl

/-- A stretch ending in `trap` (GP §A.5.1): the run exits with ☇ and the state unchanged. -/
theorem trap_exit {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {pc n : Nat}
    {ω : Regs} {μ : Memory} {x : X}
    (hd : deblob p pc = some P ∧ P.decode pc = some (.noArgs .trap) ∧ P.next pc = n ∧
      P.blockCost (P.blockStartOf pc) ≤ stepCostCap) :
    FreeRunH p R pc ω μ x .panic ω μ x := by
  have hs : P.freeStep pc ω μ = (.panic, P.next pc, ω, μ) := by
    rw [Program.freeStep_of_decode ω μ hd.2.1]; rfl
  have := FreeExit.step (p := p) hd.1 hs (by simp)
  simp only [or_true, ite_true] at this
  exact .exit (.exit this) (by simp)

/-- A stretch ending in `jump_ind r, 0` with ω_r = 2^32 − 2^16 (GP eq. `jumptablealignment`): the
    run halts with the state unchanged. -/
theorem halt_exit {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {pc n : Nat} {r : RegIdx}
    {ω : Regs} {μ : Memory} {x : X}
    (hd : deblob p pc = some P ∧ P.decode pc = some (.regImm .jumpInd r 0) ∧ P.next pc = n ∧
      P.blockCost (P.blockStartOf pc) ≤ stepCostCap)
    (hr : ω.get r = UInt64.ofNat (2 ^ 32 - 2 ^ 16)) :
    FreeRunH p R pc ω μ x .halt ω μ x := by
  have hrn : ((ω.get r).toNat + UInt64.toNat 0) % two32 = 2 ^ 32 - 2 ^ 16 := by
    rw [hr]; rfl
  have hs : P.freeStep pc ω μ = (.halt, pc, ω, μ) := by
    rw [Program.freeStep_of_decode ω μ hd.2.1]
    simp only [Program.exec, Program.djump, Program.finalState, memoryException, hrn, ↓reduceIte]
    rfl
  have := FreeExit.step (p := p) hd.1 hs (by simp)
  simp only [true_or, ite_true] at this
  exact .exit (.exit this) (by simp)

/-- **The theorem of a stretch, from its check.** -/
theorem check_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {st : Static}
    {G : Prog} {A T : Spec} {frame : List (Aff × Nat)}
    {start tgt k : Nat} (h : check st G A T frame start tgt k = true)
    (hG : ProgHyp p P G) (vals : List Nat) (hB : BHold vals st.ub)
    (hLB : LBHold vals st.lb) (ω : Regs) (μ : Memory)
    (hrd : RdHold ⟨fun k => vals.getD k 0, ω, μ⟩ μ st.rd)
    (hwr : WrHold ⟨fun k => vals.getD k 0, ω, μ⟩ μ st.wr)
    (hsep : SepHold ⟨fun k => vals.getD k 0, ω, μ⟩ st.sep)
    (hr : RegsHold ⟨fun k => vals.getD k 0, ω, μ⟩ ω A.regs)
    (hc : CellsHold ⟨fun k => vals.getD k 0, ω, μ⟩ μ A.cells) (x : X)
    (hH : HostOk R G.hosts := by exact trivial)
    (hrw : RwHold ⟨fun k => vals.getD k 0, ω, μ⟩ st.rw := by exact trivial) :
    ∃ ω' μ', FreeStepsH p R start ω μ x tgt ω' μ' x k ∧
      RegsHold ⟨fun k => vals.getD k 0, ω, μ⟩ ω' T.regs ∧
      CellsHold ⟨fun k => vals.getD k 0, ω, μ⟩ μ' T.cells ∧
      (∀ t, t < two32 → (∀ f ∈ frame, ¬ InReg ⟨fun k => vals.getD k 0, ω, μ⟩ f t) →
        μ'.read t = μ.read t) ∧ μ'.pages = μ.pages := by
  let E : Env := ⟨fun k => vals.getD k 0, ω, μ⟩
  have hpre : Pre E st :=
    ⟨bHold_get hB, lbHold_get hLB, rdHold_mem hrd, wrHold_mem hwr, sepHold_mem hsep, rwHold_mem hrw⟩
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨hok, h⟩ := h
  split at h
  · rename_i σ' hrun
    obtain ⟨ω', μ', hsteps, hinv⟩ := srun_sound (E := E) hG hH hpre x k start
      (init A) ω μ σ' (init_inv (E := E) hpre hok hr hc) hrun
    exact ⟨ω', μ', hsteps, entails_sound hpre hinv h⟩
  · cases h

end PVM.SymExec
