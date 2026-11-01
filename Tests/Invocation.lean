import PVM

/-!
# Kernel-checked examples of Ψ_H, Y and Ψ_M

Each `example` is proved by `decide +kernel`: the Lean kernel itself evaluates Y, deblob, the
gas model and Ψ/Ψ_H on a small program. No vectors exist for these layers at the pinned commit,
so these hand-assembled programs are the tests; they also show that concrete runs can be checked
by kernel evaluation alone, without trusting compiled code.
-/

namespace PVM.Tests.Invocation

open PVM

/-- A JAM blob (GP eq. `conditions`) with read-only data `ro`, no read-write data, `z` extra heap
    pages and a one-page stack, wrapping the PVM blob `p`. -/
def jam (p : List UInt8) (ro : List UInt8 := []) (z : Nat := 0) : ByteArray :=
  ⟨(Num.encodeLE 3 ro.length ++ Num.encodeLE 3 0 ++ Num.encodeLE 2 z ++ Num.encodeLE 3 4096 ++
    ro ++ Num.encodeLE 4 p.length ++ p).toArray⟩

/-- `jump_ind ω₀ + 0`: since Y sets ω₀ = 2^32 − 2^16, this halts, returning μ[ω₇…+ω₈], which Y
    pointed at the arguments: an echo service. PVM blob: |j| = 0, z = 0, |c| = 2, c, k = 0b01. -/
def echo : ByteArray := jam [0, 0, 2, 50, 0, 1]

/-- `ecalli 7; jump_ind ω₀ + 0`. c = [10, 7, 50, 0], k = 0b0101. -/
def callThenHalt : ByteArray := jam [0, 0, 4, 10, 7, 50, 0, 5]

/-- A single `trap`. -/
def trapOnly : ByteArray := jam [0, 0, 1, 0, 1]

/-- A handler that panics on every call. -/
def noHost : HostFn Nat := fun _ g ω μ x => ⟨.panic, g, ω, μ, x⟩

/-- Host call 7 keeps only the first argument octet (ω₈ := 1), charges 10 gas and counts the
    call in the context; any other call panics. -/
def keepFirst : HostFn Nat := fun h g ω μ x =>
  if h = 7 then ⟨.cont, g - 10, ω.set 8 1, μ, x + 1⟩ else ⟨.panic, g, ω, μ, x⟩

/-- Host call 7 points the output at address 0, which is never readable. -/
def badOutput : HostFn Nat := fun _ g ω μ x => ⟨.cont, g, ω.set 7 0, μ, x⟩

/-- The output of Ψ_M as a list, `none` for ☇ and ∞. -/
def out (r : Nat × InvOutput × Nat) : Option (List UInt8) :=
  match r.2.1 with | .ok b => some b.toList | _ => none

/-- Whether Ψ_M ended in ☇ / ∞. -/
def isPanic (r : Nat × InvOutput × Nat) : Bool := match r.2.1 with | .panic => true | _ => false
def isOog (r : Nat × InvOutput × Nat) : Bool := match r.2.1 with | .oog => true | _ => false

-- Echo returns its arguments.
example : out (psiM echo 0 1000 ⟨#[1, 2, 3]⟩ noHost 0) = some [1, 2, 3] := by decide +kernel
-- Gas used is ϱ^Δ of the single block (č = 22 for `jump_ind`, so 22 + pipeline − 3).
example : (psiM echo 0 1000 ⟨#[1, 2, 3]⟩ noHost 0).1 = (Blob.parse? ⟨#[0, 0, 2, 50, 0, 1]⟩).elim 0
    (·.blockCost 0) := by decide +kernel
-- Out of gas: the block cannot be charged, so nothing is consumed.
example : isOog (psiM echo 0 1 ⟨#[1]⟩ noHost 0) ∧ (psiM echo 0 1 ⟨#[1]⟩ noHost 0).1 = 0 := by
  decide +kernel
-- A trap panics.
example : isPanic (psiM trapOnly 0 1000 ⟨#[]⟩ noHost 0) := by decide +kernel
-- An invalid JAM blob: (0, ☇, x).
example : (psiM (X := Nat) ⟨#[1, 2]⟩ 0 1000 ⟨#[]⟩ noHost 5).1 = 0 := by decide +kernel
example : isPanic (psiM (X := Nat) ⟨#[1, 2]⟩ 0 1000 ⟨#[]⟩ noHost 5) := by decide +kernel
-- The host call resumes after `ecalli`, its register write is seen, the context is threaded,
-- and its 10 gas is counted in the gas used.
example : out (psiM callThenHalt 0 1000 ⟨#[9, 8, 7]⟩ keepFirst 0) = some [9] := by decide +kernel
example : (psiM callThenHalt 0 1000 ⟨#[9, 8, 7]⟩ keepFirst 0).2.2 = 1 := by decide +kernel
example : (psiM callThenHalt 0 1000 ⟨#[9, 8, 7]⟩ keepFirst 0).1 =
    (Blob.parse? ⟨#[0, 0, 4, 10, 7, 50, 0, 5]⟩).elim 0 (·.blockCost 0) + 10 := by decide +kernel
-- A handler's ☇ ends the run.
example : isPanic (psiM callThenHalt 0 1000 ⟨#[1]⟩ noHost 0) := by decide +kernel
-- Halting with an unreadable output range gives the empty blob.
example : out (psiM callThenHalt 0 1000 ⟨#[1]⟩ badOutput 0) = some [] := by decide +kernel

/-! ### Y's memory layout (GP eq. `memlayout`) and registers (eq. `registers`) -/

def initMem (b : ByteArray) (a : ByteArray) : Memory :=
  (standardInit b a).elim Memory.empty (·.2.2)

-- Read-only data at 𝖹_Z, readable but not writable; one zone below it is inaccessible.
example : let μ := initMem (jam [0, 0, 1, 0, 1] [42, 43]) ⟨#[]⟩
    μ.read zoneSize = 42 ∧ μ.read (zoneSize + 1) = 43 ∧ μ.readable zoneSize ∧
      !μ.writable zoneSize ∧ !μ.readable (zoneSize - 1) := by decide +kernel
-- Heap pages (z = 2) right after the read-write section at 2𝖹_Z + Q(|o|) are writable.
example : let μ := initMem (jam [0, 0, 1, 0, 1] [42] 2) ⟨#[]⟩
    μ.writable (2 * zoneSize + zoneSize) ∧ μ.writable (2 * zoneSize + zoneSize + 2 * pageSize - 1) ∧
      !μ.readable (2 * zoneSize + zoneSize + 2 * pageSize) := by decide +kernel
-- The stack page below 2^32 − 2𝖹_Z − 𝖹_I is writable; the arguments are read-only above it.
example : let μ := initMem echo ⟨#[5, 6]⟩
    μ.writable (stackEnd - 1) ∧ !μ.readable stackEnd ∧ μ.read argStart = 5 ∧
      μ.readable argStart ∧ !μ.writable argStart := by decide +kernel
-- Registers.
example : ((standardInit echo ⟨#[5, 6]⟩).map fun r => r.2.1.toList) =
    some [UInt64.ofNat (2 ^ 32 - 2 ^ 16), UInt64.ofNat stackEnd, 0, 0, 0, 0, 0, UInt64.ofNat argStart, 2, 0, 0, 0, 0] := by
  decide +kernel
-- A JAM blob with trailing octets is not a valid encoding.
example : (standardInit (echo.push 0) ⟨#[]⟩).isNone := by decide +kernel

end PVM.Tests.Invocation
