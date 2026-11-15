import PVM.Invocation

/-!
# A fast Ψ_H, proved equal to the paper's

`psiHStar` follows GP §A.6 literally. At every host call it runs Ψ on the raw blob, and it
computes the next instruction with `blobNext`. The fuel comes from `runMeasure`. Each of these
parses the blob afresh. Through `psi_eq_psiFast`, each Ψ also parses it and runs
`Program.prepare`. So every host call costs about three parses and one preparation of the whole
blob. Every block cost is also simulated again, because each Ψ builds a fresh cost table. For a
service blob of ~100 KB that makes a host-call-heavy invocation very slow.

`psiHStarFast` parses and prepares the blob once per Ψ_H, then runs the host-call loop on the
prepared program (`Prepared.hostFuel`). Its block-cost table is shared by all segments. Otherwise
its definition is the same as `psiHFuel`'s.

The equalities `psiHStar_eq_psiHStarFast`, `psiH_eq_psiHFast` and `psiM_eq_psiMFast` are
registered with `@[csimp]`. The compiler then uses the fast versions in compiled code that imports
this module. As with `psi_eq_psiFast`, the kernel and every theorem still see the paper-literal
definitions. `psiH` and `psiM` need their own `@[csimp]` because their compiled code (in
`PVM.Invocation`) predates this module.
-/

namespace PVM

/-- `runMeasure` for a parsed program. -/
def Program.measure (P : Program) (i : Nat) (gas : UInt64) (charged : Bool) : Nat :=
  let n := P.code.size + 1
  2 * n * gas.toNat + (if charged then n + P.code.size - i else 0)

theorem runMeasure_of_parse {p : ByteArray} {P : Program} (h : Blob.parse? p = some P)
    (i : Nat) (gas : UInt64) (ch : Bool) : runMeasure p i gas ch = P.measure i gas ch := by
  simp [runMeasure, h, Program.measure]

theorem blobNext_of_parse {p : ByteArray} {P : Program} (h : Blob.parse? p = some P) (i : Nat) :
    blobNext p i = P.next i := by
  simp [blobNext, h]

namespace Prepared

/-- Ψ on a prepared program (cf. `psiFast`). -/
def psi (Q : Prepared) (i : Nat) (gas : UInt64) (charged : Bool) (ω : Regs) (μ : Memory) :
    Result :=
  (Q.run (Q.prog.measure i gas charged + 1) i gas charged ω μ).getD
    { status := .panic, pc := 0, gas, charged, regs := ω, mem := μ }

/-- Ψ_H* with at most `fuel` host calls, on a prepared program (cf. `psiHFuel`). -/
def hostFuel {X : Type} (Q : Prepared) (f : HostFn X) :
    Nat → Nat → UInt64 → Bool → Regs → Memory → X → Option (HostRunResult X)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, i, gas, ch, ω, μ, x =>
    let r := Q.psi i gas ch ω μ
    match r.status with
    | .host h =>
      let y := f h.toNat r.gas r.regs r.mem x
      match y.status with
      | .cont => Q.hostFuel f fuel (Q.prog.next r.pc) y.gas r.charged y.regs y.mem y.ctx
      | s => some { status := s.toStatus, pc := r.pc, gas := y.gas,
                    charged := r.charged, regs := y.regs, mem := y.mem, ctx := y.ctx }
    | _ => some { status := r.status, pc := r.pc, gas := r.gas,
                  charged := r.charged, regs := r.regs, mem := r.mem, ctx := x }

end Prepared

theorem psi_of_parse {p : ByteArray} {P : Program} (h : Blob.parse? p = some P) (i : Nat)
    (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) :
    psi p i gas ch ω μ = P.prepare.psi i gas ch ω μ := by
  rw [psi_eq_psiFast]
  simp only [psiFast, h, stepBound, runMeasure_of_parse h, Prepared.psi, prepare_prog]

theorem hostFuel_prepare {X : Type} {p : ByteArray} {P : Program} (h : Blob.parse? p = some P)
    (f : HostFn X) :
    ∀ n i gas ch ω μ x, P.prepare.hostFuel f n i gas ch ω μ x = psiHFuel p f n i gas ch ω μ x := by
  intro n
  induction n with
  | zero => intros; rfl
  | succ n ih =>
    intro i gas ch ω μ x
    simp only [Prepared.hostFuel, psiHFuel, ← psi_of_parse h, blobNext_of_parse h, prepare_prog,
      ih]
    rfl

/-- Ψ_H*, parsing and preparing the blob once (cf. `psiHStar`). -/
def psiHStarFast {X : Type} (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) (f : HostFn X) (x : X) : HostRunResult X :=
  match Blob.parse? p with
  | none => { status := .panic, pc := 0, gas, charged := ch, regs := ω, mem := μ, ctx := x }
  | some P =>
    (P.prepare.hostFuel f (P.measure i gas ch + 1) i gas ch ω μ x).getD
      { status := .panic, pc := 0, gas, charged := ch, regs := ω, mem := μ, ctx := x }

/-- **The fast Ψ_H* is the paper's Ψ_H*.** Registered with `@[csimp]`. -/
@[csimp] theorem psiHStar_eq_psiHStarFast : @psiHStar = @psiHStarFast := by
  funext X p i gas ch ω μ f x
  unfold psiHStar psiHStarFast
  cases h : Blob.parse? p with
  | none =>
    have hp : psi p i gas ch ω μ =
        ({ status := .panic, pc := 0, gas, charged := ch, regs := ω, mem := μ } : Result) := by
      rw [psi_eq_psiFast]; simp [psiFast, h]
    simp [psiHFuel, hp]
  | some P => simp only [runMeasure_of_parse h, hostFuel_prepare h]

/-- Ψ_H with the fast Ψ_H* (cf. `psiH`). -/
def psiHFast {X : Type} (p : ByteArray) (i : Nat) (gas : UInt64) (ω : Regs) (μ : Memory)
    (f : HostFn X) (x : X) : HostRunResult X :=
  psiHStarFast p i gas false ω μ f x

/-- **The fast Ψ_H is the paper's Ψ_H.** Registered with `@[csimp]`. -/
@[csimp] theorem psiH_eq_psiHFast : @psiH = @psiHFast := by
  funext X p i gas ω μ f x
  simp only [psiH, psiHFast, psiHStar_eq_psiHStarFast]

/-- Ψ_M with the fast Ψ_H (cf. `psiM`). -/
def psiMFast {X : Type} (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (f : HostFn X)
    (x : X) : Nat × InvOutput × X :=
  match standardInit b a with
  | none => (0, .panic, x)
  | some (p, ω, μ) => invocationResult gas (psiHFast p i gas ω μ f x)

/-- **The fast Ψ_M is the paper's Ψ_M.** Registered with `@[csimp]`. -/
@[csimp] theorem psiM_eq_psiMFast : @psiM = @psiMFast := by
  funext X b i gas a f x
  unfold psiM psiMFast
  rw [psiH_eq_psiHFast]
  rcases standardInit b a with _ | ⟨p, ω, μ⟩ <;> rfl

end PVM
