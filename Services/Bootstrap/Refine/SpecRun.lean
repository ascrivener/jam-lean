import Services.Bootstrap.Refine.RunMixed
import Services.Bootstrap.SpecLemmas.Codec
import Services.Bootstrap.Bridge
import Services.Bootstrap.Encode.PrefixBig

/-!
# `Spec.refine` under the GP refine host functions, for the milestone's instructions

For a payload ℰ(`Instructions { is, salt }`) ⌢ rest whose instructions are all passed through (`Kinds.MFixed`) or
`ExportSegs`, `RSem.run (Spec.refine C i y)` returns ℰ(`BootstrapWorkOutput { outI is, i }`) and the segments
exported in order, each `padSeg`ged while ς + |e| < 𝖶_X (`run_refine`); and `RunMixed.expTo`, the binary's
host context, is that list of exports (`expTo_eq`). GP v0.8.0 Appendix B.4 (Ψ_R), B.7 (export); `Spec.refine`,
`Spec.refineInstr`, `Bridge.RSem`.
-/

namespace Services.Bootstrap.Refine.SpecRun

open JAM Services.Bootstrap Services.Bootstrap.Spec Services.Bootstrap.Bridge Services.Bootstrap.Refine.Kinds
  Services.Bootstrap.Refine.RunMixed Services.Bootstrap.Refine.ExportOkOf

/-- Ω_E's effect on the exports e: `padSeg d` appended while ς + |e| < 𝖶_X (`RSem.reply`). -/
def expE (off : Nat) (d : Bytes) (e : List Bytes) : List Bytes :=
  if off + e.length < Constants.Cmaxpackageexports then e ++ [RSem.padSeg d] else e

/-- The exports after the instruction i. -/
def instrE (off : Nat) (i : Instr) (e : List Bytes) : List Bytes :=
  match segsOf i with
  | some ds => ds.foldl (fun e d => expE off d e) e
  | none => e

/-- The exports after the instructions is. -/
def expsL (off : Nat) (is : List Instr) (e : List Bytes) : List Bytes := is.foldl (fun e i => instrE off i e) e

theorem go_bind_some {α β : Type} {p : Prog ROp α} {env : RSem.Env} {e e' : List Bytes} {a : α}
    (h : RSem.go p env e = some (a, e')) (f : α → Prog ROp β) : RSem.go (p >>= f) env e = RSem.go (f a) env e' := by
  show RSem.go (Prog.bind p f) env e = _
  induction p generalizing e with
  | pure b => simp only [RSem.go, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | call o k ih => exact ih _ h
  | panic => simp [RSem.go] at h

theorem go_forIn (F : Bytes → PUnit → Prog ROp (ForInStep PUnit)) (env : RSem.Env)
    (hF : ∀ d b e, RSem.go (F d b) env e = some (ForInStep.yield PUnit.unit, expE env.exportOffset d e)) :
    ∀ (ds : List Bytes) (e : List Bytes),
      RSem.go (forIn ds PUnit.unit F) env e = some (PUnit.unit, ds.foldl (fun e d => expE env.exportOffset d e) e) := by
  intro ds
  induction ds with
  | nil => intro e; rfl
  | cons d ds ih =>
    intro e
    rw [List.forIn_cons]
    exact (go_bind_some (hF d _ e) _).trans (ih _)

theorem refineInstr_fixed (C : Consts) (x : Instr) (hm : MFixed x) : refineInstr C x = Prog.pure x := by
  cases x <;> simp only [MFixed] at hm <;> try rfl
  case lookup s h e => subst hm; rfl

theorem segsOf_fixed {x : Instr} (hm : MFixed x) : segsOf x = none := by
  cases x <;> simp only [MFixed] at hm <;> rfl

/-- One instruction under `RSem`: its `outI`, the exports `instrE`. -/
theorem go_instr (C : Consts) (x : Instr) (hx : MFixed x ∨ ∃ ds, x = .exportSegs ds) (env : RSem.Env)
    (e : List Bytes) : RSem.go (refineInstr C x) env e = some (outI x, instrE env.exportOffset x e) := by
  rcases hx with hm | ⟨ds, rfl⟩
  · rw [refineInstr_fixed C x hm]
    simp only [RSem.go, outI, instrE, segsOf_fixed hm]
  · simp only [refineInstr]
    rw [go_bind_some (go_forIn _ env (fun d b e => rfl) ds e)]
    rfl

theorem go_mapM_loop (C : Consts) (env : RSem.Env) :
    ∀ (is acc : List Instr) (e : List Bytes), (∀ x ∈ is, MFixed x ∨ ∃ ds, x = .exportSegs ds) →
      RSem.go (List.mapM.loop (refineInstr C) is acc) env e =
        some (acc.reverse ++ is.map outI, expsL env.exportOffset is e) := by
  intro is
  induction is with
  | nil => intro acc e _; simp [List.mapM.loop, expsL]; rfl
  | cons x is ih =>
    intro acc e hx
    simp only [List.mapM.loop]
    rw [go_bind_some (go_instr C x (hx x List.mem_cons_self) env e)]
    rw [ih _ _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))]
    simp [expsL]

/-- **`Spec.refine` on the milestone's payloads**: for well-formed instructions, each passed through
    (`MFixed`) or `ExportSegs`, fewer than 2^32 of them and a 32-octet salt, refine returns
    ℰ(`BootstrapWorkOutput { outI is, item }`) with the segments exported in order (`expsL`). -/
theorem run_refine (C : Consts) (env : RSem.Env) (item : Nat) (is : List Instr) (salt rest : Bytes)
    (hwf : ∀ x ∈ is, x.WF C) (hn : is.length < 2 ^ 32) (hsalt : salt.length = 32)
    (hk : ∀ x ∈ is, MFixed x ∨ ∃ ds, x = .exportSegs ds) :
    RSem.run (refine C item (encodePayload is salt ++ rest)) env =
      some (encodeOutput (is.map outI) item, expsL env.exportOffset is []) := by
  unfold refine RSem.run
  rw [decode_payload C is salt rest hwf hn hsalt]
  dsimp only
  unfold List.mapM
  rw [go_bind_some (go_mapM_loop C env is [] [] hk)]
  rfl

theorem expD_eq (env : RefineHost.Env) (d : List UInt8) (x : RefineCtx) :
    expD env d x = (x.1, expE env.exportOffset d x.2) := by
  unfold expD expE RSem.padSeg
  by_cases h : env.exportOffset + x.2.length ≥ Constants.Cmaxpackageexports
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]
    congr 3
    rcases Nat.le_total d.length Constants.Csegmentsize with h' | h'
    · rw [Nat.min_eq_left h', List.take_of_length_le (Nat.le_refl _), List.take_of_length_le h']
    · rw [Nat.min_eq_right h',
        show Constants.Csegmentsize - Constants.Csegmentsize = Constants.Csegmentsize - d.length by omega]

theorem expDs_eq (env : RefineHost.Env) (ds : List (List UInt8)) :
    ∀ x : RefineCtx, expDs env ds x = (x.1, ds.foldl (fun e d => expE env.exportOffset d e) x.2) := by
  induction ds with
  | nil => intro x; rfl
  | cons d ds ih => intro x; simp only [expDs, List.foldl_cons]; rw [← expDs, ih, expD_eq]

theorem instrCtx_eq (env : RefineHost.Env) (i : Instr) (x : RefineCtx) :
    instrCtx env i x = (x.1, instrE env.exportOffset i x.2) := by
  unfold instrCtx instrE
  split <;> simp_all [expDs_eq]

/-- **The binary's host context is `RSem`'s exports**: `expTo` after the first k instructions. -/
theorem expTo_eq (env : RefineHost.Env) (is : List Instr) (x : RefineCtx) (k : Nat) :
    expTo env is x k = (x.1, expsL env.exportOffset (is.take k) x.2) := by
  unfold expTo expsL
  generalize is.take k = l
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih, instrCtx_eq]

theorem map_range_getD {β : Type} (is : List Instr) (f : Instr → β) :
    (List.range is.length).map (fun j => f (is.getD j .panic)) = is.map f := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- **The binary's output is ℰ(`BootstrapWorkOutput { outI is, item }`)**: for 1 ≤ n < 128 instructions and
    an item index below 2^16, n :: (the encodings of `outI` of each) ⌢ ℰ₂(item mod 2^16). -/
theorem output_eq (is : List Instr) (item : Nat) (hn : 1 ≤ is.length ∧ is.length < 128) (hi : item < 65536) :
    UInt8.ofNat is.length :: (Encode.Loop.out (encOut is) is.length ++ PVM.Num.encodeLE 2 (item % 65536)) =
      encodeOutput (is.map outI) item := by
  unfold encodeOutput vec Encode.Loop.out encOut
  rw [map_range_getD is (fun x => (outI x).encode), List.length_map, Nat.mod_eq_of_lt hi,
    show Codec.nat is.length = [UInt8.ofNat is.length] from
      Services.Bootstrap.Encode.PrefixBig.encodeNat_small _ ⟨by omega, hn.2⟩]
  simp [List.map_map, Codec.nat, Codec.fixed, Function.comp_def]

end Services.Bootstrap.Refine.SpecRun
