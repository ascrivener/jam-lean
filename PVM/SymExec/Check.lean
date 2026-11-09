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
  cells : List (Nat × Nat × SVal)

def RegsHold (E : Env) (ω : Regs) : List (Nat × SVal) → Prop
  | [] => True
  | r :: rs => ω.get (regIdx r.1) = UInt64.ofNat (r.2.eval E) ∧ RegsHold E ω rs

def CellsHold (E : Env) (μ : Memory) : List (Nat × Nat × SVal) → Prop
  | [] => True
  | c :: cs => μ.readN c.1 c.2.1 = encodeLE c.2.1 (c.2.2.eval E) ∧ CellsHold E μ cs

/-- The ranges of a list are readable. -/
def RdHold (μ : Memory) : List (Nat × Nat) → Prop
  | [] => True
  | r :: rs => (∀ a, r.1 ≤ a → a < r.2 → μ.readable a = true) ∧ RdHold μ rs

/-- The ranges of a list are writable. -/
def WrHold (μ : Memory) : List (Nat × Nat) → Prop
  | [] => True
  | r :: rs => (∀ a, r.1 ≤ a → a < r.2 → μ.writable a = true) ∧ WrHold μ rs

/-- Each named natural is below its bound. -/
def BHold : List Nat → List Nat → Prop
  | v :: vs, b :: bs => v < b ∧ BHold vs bs
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
    ∀ {l : List (Nat × Nat × SVal)}, CellsHold E μ l → ∀ c ∈ l,
      μ.readN c.1 c.2.1 = encodeLE c.2.1 (c.2.2.eval E)
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, c, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact cellsHold_mem hs c hm

theorem rdHold_mem {μ : Memory} : ∀ {l : List (Nat × Nat)}, RdHold μ l →
    ∀ r ∈ l, ∀ a, r.1 ≤ a → a < r.2 → μ.readable a = true
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, r, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact rdHold_mem hs r hm

theorem wrHold_mem {μ : Memory} : ∀ {l : List (Nat × Nat)}, WrHold μ l →
    ∀ r ∈ l, ∀ a, r.1 ≤ a → a < r.2 → μ.writable a = true
  | [], _, _, h => by cases h
  | _ :: _, ⟨h, hs⟩, r, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h
    · exact wrHold_mem hs r hm

theorem bHold_get : ∀ {vs bs : List Nat}, BHold vs bs → ∀ k b, bs[k]? = some b → vs.getD k 0 < b
  | [], [], _, k, b, h => by simp at h
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | v :: vs, b' :: bs, ⟨h1, h2⟩, k, b, h => by
    cases k with
    | zero => simp at h; subst h; simpa using h1
    | succ k => simpa using bHold_get h2 k b (by simpa using h)

/-- The start state an assumption describes: the listed registers and cells; every other
    register is its own start value. -/
def init (A : Spec) : SState :=
  { regs := (List.range 13).map fun r => (A.regs.lookup r).getD (.reg0 r)
    cells := A.cells
    dirty := [] }

def initOk (A : Spec) : Bool :=
  A.regs.all (fun r => r.1 < 13) && A.cells.all (fun c => c.1 + c.2.1 ≤ two32)

/-- The end state σ has the target's registers and cells, and writes only inside `frame`. -/
def entails (B : List Nat) (σ : SState) (T : Spec) (frame : List (Nat × Nat)) : Bool :=
  T.regs.all (fun r => r.1 < 13 &&
    mkMod B (σ.regs.getD r.1 (.const 0)) two64 == mkMod B r.2 two64) &&
  T.cells.all (fun t => (σ.cells.any fun c =>
    c.1 == t.1 && c.2.1 == t.2.1 && mkMod B c.2.2 (2 ^ (8 * t.2.1)) == mkMod B t.2.2 (2 ^ (8 * t.2.1))) ||
    match t.2.2, assemble σ.cells t.2.1 t.1 t.2.1 with
    | .const v, some w => w % 256 ^ t.2.1 == v % 256 ^ t.2.1
    | _, _ => false) &&
  σ.dirty.all (fun d => frame.any fun f => f.1 ≤ d.1 && d.2 ≤ f.2)

/-- The check of one stretch: from `A` at `start`, `srun` runs `k` steps to `tgt`, ending in a state
    that entails `T` within `frame`. -/
def check (st : Static) (G : Prog) (A T : Spec)
    (frame : List (Nat × Nat)) (start tgt k : Nat) : Bool :=
  initOk A &&
  match srun st G tgt k start (init A) with
  | some σ => entails st.bounds σ T frame
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

theorem init_inv {E : Env} {A : Spec} (hok : initOk A = true) (hr : RegsHold E E.ω A.regs)
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
    exact ⟨hok.2 c hcm, cellsHold_mem hc c hcm⟩

theorem entails_sound {E : Env} {B : List Nat} (hB : ∀ k b, B[k]? = some b → E.ρ k < b)
    {σ : SState} {ω : Regs} {μ : Memory} {T : Spec} {frame : List (Nat × Nat)}
    (hinv : Inv E σ ω μ) (h : entails B σ T frame = true) :
    RegsHold E ω T.regs ∧ CellsHold E μ T.cells ∧
      (∀ a, a < two32 → clear frame a 1 = true → μ.read a = E.μ.read a) ∧ μ.pages = E.μ.pages := by
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
      rwa [mkMod_eval (st := ⟨B, [], []⟩) hB, mkMod_eval (st := ⟨B, [], []⟩) hB] at this
  · clear hR hD
    generalize T.cells = l at hC
    induction l with
    | nil => trivial
    | cons t ts ih =>
      refine ⟨?_, ih (fun x hx => hC x (List.mem_cons_of_mem _ hx))⟩
      have ht := hC t (List.mem_cons_self ..)
      rw [Bool.or_eq_true] at ht
      rcases ht with ht | ht
      · simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at ht
        obtain ⟨c, hcm, ⟨⟨h1, h2⟩, h3⟩⟩ := ht
        have := congrArg (SVal.eval E) h3
        rw [mkMod_eval (st := ⟨B, [], []⟩) hB, mkMod_eval (st := ⟨B, [], []⟩) hB] at this
        rw [← h1, ← h2, (hc c hcm).2, ← encodeLE_mod c.2.1 (SVal.eval E c.2.2),
          ← encodeLE_mod c.2.1 (SVal.eval E t.2.2), ← pow8, h2, this]
      · split at ht
        · rename_i v w hv hw
          simp only [beq_iff_eq] at ht
          rw [assemble_sound (fun c hc' => (hc c hc').2) _ _ _ _ hw, hv, SVal.eval,
            ← encodeLE_mod t.2.1 w, ht, encodeLE_mod]
        · cases ht
  · intro a ha hcl
    apply hf a ha
    simp only [clear, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hcl ⊢
    intro d hd
    have := hD d hd
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨f, hfm, h1, h2⟩ := this
    rcases hcl f hfm with h | h <;> omega

/-- A cell given as a list of octets. -/
theorem cell_of_list {μ : Memory} {a n : Nat} {l : List UInt8} (h : μ.readN a n = l)
    (hn : l.length = n) : μ.readN a n = encodeLE n (decodeLE l) := by
  subst hn; rw [h, encodeLE_decodeLE]

theorem list_of_cell {μ : Memory} {a n : Nat} {l : List UInt8} (hn : l.length = n)
    (h : μ.readN a n = encodeLE n (decodeLE l)) : μ.readN a n = l := by
  subst hn; rw [h, encodeLE_decodeLE]

/-- **The theorem of a stretch, from its check.** -/
theorem check_sound {X : Type} {p : ByteArray} {R : HostRel X} {P : Program} {st : Static}
    {G : Prog} {A T : Spec} {frame : List (Nat × Nat)}
    {start tgt k : Nat} (h : check st G A T frame start tgt k = true)
    (hcode : AllCodeT p P G.code) (hbs : AllBS P G.bs) (hjt : AllJT P G.jt)
    (hjs : P.jumpTable.size = G.jsize) (vals : List Nat) (hB : BHold vals st.bounds)
    (ω : Regs) (μ : Memory) (hrd : RdHold μ st.rd) (hwr : WrHold μ st.wr)
    (hr : RegsHold ⟨fun k => vals.getD k 0, ω, μ⟩ ω A.regs)
    (hc : CellsHold ⟨fun k => vals.getD k 0, ω, μ⟩ μ A.cells) (x : X) :
    ∃ ω' μ', FreeStepsH p R start ω μ x tgt ω' μ' x k ∧
      RegsHold ⟨fun k => vals.getD k 0, ω, μ⟩ ω' T.regs ∧
      CellsHold ⟨fun k => vals.getD k 0, ω, μ⟩ μ' T.cells ∧
      (∀ a, a < two32 → clear frame a 1 = true → μ'.read a = μ.read a) ∧ μ'.pages = μ.pages := by
  let E : Env := ⟨fun k => vals.getD k 0, ω, μ⟩
  have hpre : Pre E st := ⟨bHold_get hB, rdHold_mem hrd, wrHold_mem hwr⟩
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨hok, h⟩ := h
  split at h
  · rename_i σ' hrun
    obtain ⟨ω', μ', hsteps, hinv⟩ := srun_sound (E := E) ⟨hcode, hbs, hjt, hjs⟩ hpre x k start (init A) ω μ
      σ' (init_inv (E := E) hok hr hc) hrun
    exact ⟨ω', μ', hsteps, entails_sound hpre.1 hinv h⟩
  · cases h

end PVM.SymExec
