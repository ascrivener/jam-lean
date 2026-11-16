import Services.Bootstrap.Acc.Handlers.InstrLoopRowEleven

/-!
# Spec `onWorkItem`, unfolded for the operand arm (R2)

`onWorkItem C now package out` (GP v0.8.0 Appendix B, Ω_W) with `decode (Dec.output C) out =
some (is, item)` is `addRecent`, then row 9's `store key (encodeResults [])` and `checkpoint`, then the
loop and the final write that `loop_row11` implements; with `none` it is `panic`.
-/

namespace Services.Bootstrap.Acc

open Services.Bootstrap Services.Bootstrap.Spec Services.Bootstrap.Acc.Handlers.InstrLoop

/-- The loop body of `onWorkItem` for the key k. -/
def wiBody (C : Consts) (now : Nat) (k : Key) (i : Instr) (rs : List Result) :
    Prog AOp (ForInStep (List Result)) := do
  match i with
  | .checkpoint => store k (encodeResults rs)
  | _ => pure ()
  let r ← onInstr C now i
  pure (ForInStep.yield (rs ++ [r]))

theorem wiBody_ck (C : Consts) (now : Nat) (k : Key) (rs : List Result) :
    wiBody C now k .checkpoint rs = Prog.bind (store k (encodeResults rs))
      (fun _ => Prog.bind (onInstr C now .checkpoint) (fun r => Prog.pure (.yield (rs ++ [r])))) := rfl

theorem wiBody_other (C : Consts) (now : Nat) (k : Key) (i : Instr) (rs : List Result)
    (h : i ≠ .checkpoint) :
    wiBody C now k i rs = Prog.bind (onInstr C now i) (fun r => Prog.pure (.yield (rs ++ [r]))) := by
  cases i <;> first | rfl | exact absurd rfl h

theorem onWorkItem_none (C : Consts) (now : Nat) (pkg out : Bytes)
    (h : decode (Dec.output C) out = none) : onWorkItem C now pkg out = Prog.panic := by
  simp only [onWorkItem, h]

theorem onWorkItem_some (C : Consts) (now : Nat) (pkg out : Bytes) (is : List Instr) (item : Nat)
    (h : decode (Dec.output C) out = some (is, item)) :
    onWorkItem C now pkg out =
      Prog.bind (addRecent C pkg item) (fun _ =>
        Prog.bind (store (.results pkg item) (encodeResults [])) (fun _ => Prog.bind (Prog.op AOp.checkpoint)
          (fun _ => Prog.bind (forIn is [] (wiBody C now (.results pkg item))) (fun rs =>
            if is.any isZomb then pure () else store (.results pkg item) (encodeResults rs))))) := by
  simp only [onWorkItem, h]
  refine congrArg (Prog.bind _) (funext fun _ => congrArg (Prog.bind _) (funext fun _ =>
    congrArg (Prog.bind _) (funext fun _ => ?_)))
  refine congr (congrArg Prog.bind ?_) (funext fun rs => ?_)
  · congr 1
  · congr 3

end Services.Bootstrap.Acc
