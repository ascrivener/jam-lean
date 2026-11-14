import PVM.SymExec.Cut

/-!
# Diagnostics for a failing check (symexec)

EXPERIMENTAL (see `docs/symexec-spike.md`). When `decide +kernel` says a check is `false` it says no
more. `#eval traceSeg …` runs the same executor (compiled, so it is fast) and reports the first
step it cannot follow (pc, instruction, registers) or, when the run completes, the target facts
the end state does not entail. Nothing here is used by any proof.
-/

namespace PVM.SymExec

/-- Run `k` steps from `pc`, logging each pc; stop at the first step the executor cannot follow. -/
def traceRun (st : Static) (G : Prog) : Nat → Nat → SState → List String × Option (Nat × SState)
  | 0, pc, σ => ([], some (pc, σ))
  | k + 1, pc, σ =>
    match sstep st G pc σ with
    | some (pc', σ') => let r := traceRun st G k pc' σ'; (s!"{pc}" :: r.1, r.2)
    | none =>
      match hstep st G pc σ with
      | some (pc', σ') => let r := traceRun st G k pc' σ'; (s!"{pc} (host)" :: r.1, r.2)
      | none =>
        ([s!"cannot follow pc {pc}: {repr ((G.code.find pc).map (·.1))}; registers {repr σ.regs}"], none)

/-- What a failing `check st G A T frame start tgt k` trips on: the same tests as `entails`. -/
def traceCheck (st : Static) (G : Prog) (A T : Spec) (frame : List (Aff × Nat))
    (start tgt k : Nat) : List String :=
  if !initOk st A then ["the start spec is not valid (a register ≥ 13, or a cell outside ℕ_{2^32})"] else
  match traceRun st G k start (init A) with
  | (log, none) => log.reverse.take 3
  | (_, some (pc, σ)) =>
    (if pc ≠ tgt then [s!"ends at pc {pc}, not {tgt}"] else []) ++
    (T.regs.filter fun (t : Nat × SVal) =>
      !(t.1 < 13 && mkMod st (σ.regs.getD t.1 (.const 0)) two64 == mkMod st t.2 two64)).map
      (fun t => s!"register {t.1}: wanted {repr t.2}, have {repr (σ.regs.getD t.1 (.const 0))}") ++
    (T.cells.filter fun (t : Aff × Nat × SVal) => !((valid st t.1 t.2.1 && σ.cells.any fun c =>
      c.1 == t.1 && c.2.1 == t.2.1 && mkMod st c.2.2 (2 ^ (8 * t.2.1)) == mkMod st t.2.2 (2 ^ (8 * t.2.1))) ||
      (valid st t.1 t.2.1 && match t.2.2, assemble σ.cells t.2.1 t.1 t.2.1 with
        | .const v, some w => w % 256 ^ t.2.1 == v % 256 ^ t.2.1
        | _, _ => false))).map
      (fun t => s!"cell {repr t.1} ({t.2.1}): wanted {repr t.2.2}, have {repr (σ.cells.filter fun c => c.1 == t.1)}") ++
    (σ.dirty.filter fun (d : Aff × Nat) => !frame.any (within st d.1 d.2)).map
      (fun d => s!"write outside the frame: {repr d}")

/-- `traceCheck` for a segment between two cuts. -/
def traceSeg (G : Prog) (ub lb : List Nat) (sep : List ((Aff × Nat) × (Aff × Nat)))
    (A B : Cut) (start tgt k : Nat) : List String :=
  traceCheck (segStatic ub lb sep A) G ⟨A.regs, A.cells⟩ ⟨B.regs, B.cells⟩ B.frame start tgt k

end PVM.SymExec
