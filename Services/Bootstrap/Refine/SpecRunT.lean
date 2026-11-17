import Services.Bootstrap.Refine.SpecRun

/-!
# `Spec.refine` under the GP refine host functions, for T1c's instructions

For a payload ℰ(`Instructions { is, salt }`) ⌢ rest with no `Import` and no `RandomStorageRefine` (`NoImpRsr`),
`RSem.run (Spec.refine C i y)` returns ℰ(`BootstrapWorkOutput { outT lk is, i }`) and the segments exported in order
(`run_refineT`): each instruction passed through (quirk Q3), each `ExportSegs ds` returned as `Exported |ds|`, each
eager `Lookup s h` as `LookedUp (lk s h)` with lk the historical lookup at the anchor (`rsemLk`). GP v0.8.0
Appendix B.4 (Ψ_R), B.6 (historical_lookup), B.7 (export); `Spec.refine`, `Spec.refineInstr`, `Bridge.RSem`.
-/

namespace Services.Bootstrap.Refine.SpecRunT

open JAM Services.Bootstrap Services.Bootstrap.Spec Services.Bootstrap.Bridge Services.Bootstrap.Refine.RunMixed
  Services.Bootstrap.Refine.SpecRun

/-- The instructions T1c covers: all but `Import` (excluded while Adam decides) and `RandomStorageRefine` (`hrsr`). -/
def NoImpRsr : Instr → Prop
  | .importSegs _ | .randomStorageRefine .. => False
  | _ => True

/-- The instruction refine returns for i, given the historical lookup lk: an eager `Lookup s h` becomes
    `LookedUp (lk s h)`, `ExportSegs ds` becomes `Exported |ds|`, every other instruction is returned as it is. -/
def outT (lk : Nat → Bytes → Option Bytes) : Instr → Instr
  | .lookup s h true => .lookedUp (lk s h)
  | .exportSegs ds => .exported ds.length
  | i => i

/-- `RSem`'s historical lookup (Ω_H's 𝐯 at the lookup anchor). -/
def rsemLk (env : RSem.Env) (s : Nat) (h : Bytes) : Option Bytes :=
  (env.accounts.get? s).bind (·.historicalLookup env.lookupSlot h)

/-- One instruction under `RSem`: its `outT`, the exports `instrE`. -/
theorem go_instrT (C : Consts) (x : Instr) (hx : NoImpRsr x) (env : RSem.Env) (e : List Bytes) :
    RSem.go (refineInstr C x) env e = some (outT (rsemLk env) x, instrE env.exportOffset x e) := by
  cases x with
  | importSegs _ => exact absurd hx id
  | randomStorageRefine _ _ => exact absurd hx id
  | exportSegs ds =>
    simp only [refineInstr]
    rw [go_bind_some (go_forIn _ env (fun d b e => rfl) ds e)]
    rfl
  | lookup s h b => cases b <;> rfl
  | _ => rfl

theorem go_mapM_loopT (C : Consts) (env : RSem.Env) :
    ∀ (is acc : List Instr) (e : List Bytes), (∀ x ∈ is, NoImpRsr x) →
      RSem.go (List.mapM.loop (refineInstr C) is acc) env e =
        some (acc.reverse ++ is.map (outT (rsemLk env)), expsL env.exportOffset is e) := by
  intro is
  induction is with
  | nil => intro acc e _; simp [List.mapM.loop, expsL]; rfl
  | cons x is ih =>
    intro acc e hx
    simp only [List.mapM.loop]
    rw [go_bind_some (go_instrT C x (hx x List.mem_cons_self) env e)]
    rw [ih _ _ (fun y hy => hx y (List.mem_cons_of_mem _ hy))]
    simp [expsL]

/-- **`Spec.refine` on T1c's payloads**: for well-formed instructions with no `Import` and no
    `RandomStorageRefine`, fewer than 2^32 of them and a 32-octet salt, refine returns
    ℰ(`BootstrapWorkOutput { outT lk is, item }`) with the segments exported in order (`expsL`). -/
theorem run_refineT (C : Consts) (env : RSem.Env) (item : Nat) (is : List Instr) (salt rest : Bytes)
    (hwf : ∀ x ∈ is, x.WF C) (hn : is.length < 2 ^ 32) (hsalt : salt.length = 32)
    (hk : ∀ x ∈ is, NoImpRsr x) :
    RSem.run (refine C item (encodePayload is salt ++ rest)) env =
      some (encodeOutput (is.map (outT (rsemLk env))) item, expsL env.exportOffset is []) := by
  unfold refine RSem.run
  rw [decode_payload C is salt rest hwf hn hsalt]
  dsimp only
  unfold List.mapM
  rw [go_bind_some (go_mapM_loopT C env is [] [] hk)]
  rfl

end Services.Bootstrap.Refine.SpecRunT
