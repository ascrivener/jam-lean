import PVM.Machine

/-!
# Host-call invocation Ψ_H, standard initialization Y and argument invocation Ψ_M

GP v0.8.0 §A.6 (Host Call Definition), §A.7 (`sec:standardprograminit`, eqs. `conditions`,
`memlayout`, `registers`) and §A.8 (Argument Invocation Definition).
-/

namespace PVM

/-! ## Host-call handlers and Ψ_H (GP §A.6) -/

/-- The exit reasons a host-call handler may give: {▸, ∎, ☇, ∞} (GP §A.6, 𝔉_X). -/
inductive HostStatus where
  | cont
  | halt
  | panic
  | oog
  deriving DecidableEq, Repr

/-- The corresponding PVM exit reason. -/
def HostStatus.toStatus : HostStatus → Status
  | .cont => .cont
  | .halt => .halt
  | .panic => .panic
  | .oog => .oog

/-- The result of a host-call handler: (ε, ϱ, ω, μ, x). -/
structure HostResult (X : Type) where
  status : HostStatus
  gas : UInt64
  regs : Regs
  mem : Memory
  ctx : X

/-- 𝔉_X ≡ (ℕ, ℕ_G, ⟦ℕ_R⟧_13, 𝕄, X) → ({▸, ∎, ☇, ∞}, ℕ_G, ⟦ℕ_R⟧_13, 𝕄, X) (GP §A.6).

    We follow this type literally, with gas in ℕ_G. (The paper gives Ψ_H's result gas the type
    ℤ_G, and its host functions compute ϱ − g, which can be negative; Ψ_M clamps with max(ϱ', 0).
    See README.) -/
abbrev HostFn (X : Type) := Nat → UInt64 → Regs → Memory → X → HostResult X

/-- A handler that never returns more gas than it was given. Every host function of the paper
    charges a non-negative amount, so they all have this property; under it Ψ_H terminates. -/
def HostFn.GasNonIncreasing {X : Type} (f : HostFn X) : Prop :=
  ∀ h g ω μ x, (f h g ω μ x).gas.toNat ≤ g.toNat

/-- The result of Ψ_H*: (ε, ı, ϱ, ϱ̃, ω, μ, x) (GP §A.6). -/
structure HostRunResult (X : Type) where
  /-- ε ∈ {☇, ∞, ∎} ∪ {F} × ℕ_R -/
  status : Status
  /-- ı as Ψ returns it (0 on ∎ and ☇ from the machine). -/
  pc : Nat
  gas : UInt64
  charged : Bool
  regs : Regs
  mem : Memory
  ctx : X

/-- ı + 1 + skip(ı) for the program of blob `p` (ı itself if `p` does not parse; Ψ only reports
    h̵ for blobs that do). -/
def blobNext (p : ByteArray) (i : Nat) : Nat :=
  match Blob.parse? p with
  | some P => P.next i
  | none => i

/-- Ψ_H* with at most `fuel` host calls (GP §A.6). -/
def psiHFuel {X : Type} (p : ByteArray) (f : HostFn X) :
    Nat → Nat → UInt64 → Bool → Regs → Memory → X → Option (HostRunResult X)
  | 0, _, _, _, _, _, _ => none
  | fuel + 1, i, gas, ch, ω, μ, x =>
    let r := psi p i gas ch ω μ
    match r.status with
    | .host h =>
      let y := f h.toNat r.gas r.regs r.mem x
      match y.status with
      | .cont => psiHFuel p f fuel (blobNext p r.pc) y.gas r.charged y.regs y.mem y.ctx
      | s => some { status := s.toStatus, pc := r.pc, gas := y.gas,
                    charged := r.charged, regs := y.regs, mem := y.mem, ctx := y.ctx }
    | _ => some { status := r.status, pc := r.pc, gas := r.gas,
                  charged := r.charged, regs := r.regs, mem := r.mem, ctx := x }

/-- Ψ_H*(p, ı, ϱ, ϱ̃, ω, μ, f, x) (GP §A.6). Every host call that continues happens at a lower
    `runMeasure` than the last, so `runMeasure + 1` host calls suffice when `f` does not increase
    gas (`PVM.psiHStar_eq` in `PVM.Theorems.Invocation`). For a handler that does increase gas
    the paper's Ψ_H need not terminate; there we return ☇ after the fuel. -/
def psiHStar {X : Type} (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) (f : HostFn X) (x : X) : HostRunResult X :=
  (psiHFuel p f (runMeasure p i gas ch + 1) i gas ch ω μ x).getD
    { status := .panic, pc := 0, gas, charged := ch, regs := ω, mem := μ, ctx := x }

/-- Ψ_H(p, ı, ϱ, ω, μ, f, x) ≡ Ψ_H*(p, ı, ϱ, ⊥, ω, μ, f, x) (GP §A.6). -/
def psiH {X : Type} (p : ByteArray) (i : Nat) (gas : UInt64) (ω : Regs) (μ : Memory)
    (f : HostFn X) (x : X) : HostRunResult X :=
  psiHStar p i gas false ω μ f x

/-! ## Standard program initialization Y (GP §A.7) -/

/-- 𝖹_Z = 2^16, the major zone size (GP eq. `conditions`). -/
def zoneSize : Nat := 2 ^ 16

/-- 𝖹_I = 2^24, the maximum input size (GP eq. `conditions`). -/
def inputSize : Nat := 2 ^ 24

/-- P(x) = 𝖹_P⌈x / 𝖹_P⌉. -/
def roundPage (x : Nat) : Nat := pageSize * ((x + pageSize - 1) / pageSize)

/-- Q(x) = 𝖹_Z⌈x / 𝖹_Z⌉. -/
def roundZone (x : Nat) : Nat := zoneSize * ((x + zoneSize - 1) / zoneSize)

/-- The components of a standard JAM program blob (GP eq. `conditions`): read-only data **o**,
    read-write data **w**, `z` extra heap pages, stack size `s` and the PVM blob **p**. -/
structure JamBlob where
  ro : ByteArray
  rw : ByteArray
  heapPages : Nat
  stackSize : Nat
  code : ByteArray

/-- The unique (**o**, **w**, z, s, **p**) with
    ℰ_3(|**o**|) ⌢ ℰ_3(|**w**|) ⌢ ℰ_2(z) ⌢ ℰ_3(s) ⌢ **o** ⌢ **w** ⌢ ℰ_4(|**p**|) ⌢ **p** equal to the blob. -/
def JamBlob.parse? (b : ByteArray) : Option JamBlob := do
  let fixed (pos n : Nat) : Option Nat := (Num.decodeLE ·) <$> Blob.slice? b pos n
  let oLen ← fixed 0 3
  let wLen ← fixed 3 3
  let z ← fixed 6 2
  let s ← fixed 8 3
  let pos := 11
  let o ← Blob.slice? b pos oLen
  let pos := pos + oLen
  let w ← Blob.slice? b pos wLen
  let pos := pos + wLen
  let pLen ← fixed pos 4
  let pos := pos + 4
  if pos + pLen ≠ b.size then none
  let p ← Blob.slice? b pos pLen
  some ⟨⟨o.toArray⟩, ⟨w.toArray⟩, z, s, ⟨p.toArray⟩⟩

/-- The address of the read-only section, 𝖹_Z. -/
def roStart : Nat := zoneSize

/-- The address of the read-write section, 2𝖹_Z + Q(|**o**|). -/
def rwStart (jb : JamBlob) : Nat := 2 * zoneSize + roundZone jb.ro.size

/-- The end of the stack, 2^32 − 2𝖹_Z − 𝖹_I. -/
def stackEnd : Nat := 2 ^ 32 - 2 * zoneSize - inputSize

/-- The address of the argument section, 2^32 − 𝖹_Z − 𝖹_I. -/
def argStart : Nat := 2 ^ 32 - zoneSize - inputSize

/-- The RAM of GP eq. `memlayout`. Every section boundary there is a multiple of 𝖹_P, so we
    set page access per page and then write the three data sections. -/
def initialMemory (jb : JamBlob) (a : ByteArray) : Memory :=
  let pg (x : Nat) := x / pageSize
  let μ : Memory := Memory.empty
  -- [𝖹_Z, 𝖹_Z + P(|o|)) : R
  let μ := μ.setPages (pg roStart) (pg (roundPage jb.ro.size)) (some .read)
  -- [2𝖹_Z + Q(|o|), 2𝖹_Z + Q(|o|) + P(|w|) + z𝖹_P) : W
  let μ := μ.setPages (pg (rwStart jb)) (pg (roundPage jb.rw.size) + jb.heapPages) (some .write)
  -- [2^32 − 2𝖹_Z − 𝖹_I − P(s), 2^32 − 2𝖹_Z − 𝖹_I) : W
  let μ := μ.setPages (pg (stackEnd - roundPage jb.stackSize)) (pg (roundPage jb.stackSize)) (some .write)
  -- [2^32 − 𝖹_Z − 𝖹_I, 2^32 − 𝖹_Z − 𝖹_I + P(|a|)) : R
  let μ := μ.setPages (pg argStart) (pg (roundPage a.size)) (some .read)
  let μ := μ.writeN roStart jb.ro.toList
  let μ := μ.writeN (rwStart jb) jb.rw.toList
  μ.writeN argStart a.toList

/-- The registers of GP eq. `registers`: ω₀ = 2^32 − 2^16, ω₁ = 2^32 − 2𝖹_Z − 𝖹_I,
    ω₇ = 2^32 − 𝖹_Z − 𝖹_I, ω₈ = |**a**|, all others 0. -/
def initialRegs (a : ByteArray) : Regs :=
  (Vector.replicate 13 (0 : UInt64))
    |>.set 0 (UInt64.ofNat (2 ^ 32 - 2 ^ 16))
    |>.set 1 (UInt64.ofNat stackEnd)
    |>.set 7 (UInt64.ofNat argStart)
    |>.set 8 (UInt64.ofNat a.size)

/-- The decoded JAM blob, if it is a valid encoding, the sections fit
    (5𝖹_Z + Q(|**o**|) + Q(|**w**| + z𝖹_P) + Q(s) + 𝖹_I ≤ 2^32) and |**a**| ≤ 𝖹_I. -/
def validJamBlob? (b : ByteArray) (a : ByteArray) : Option JamBlob :=
  if a.size > inputSize then none
  else (JamBlob.parse? b).bind fun jb =>
    if 5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32 then none
    else some jb

/-- Y(**p**, **a**) (GP §A.7): the PVM blob, registers and RAM for JAM blob `b` and arguments
    `a`, or ∅ if `b` is not a valid encoding or the sections do not fit.

    The paper types **a** ∈ 𝔹_{:𝖹_I}; we return ∅ for longer arguments. -/
def standardInit (b : ByteArray) (a : ByteArray) : Option (ByteArray × Regs × Memory) :=
  (validJamBlob? b a).map fun jb => (jb.code, initialRegs a, initialMemory jb a)

/-! ## Argument invocation Ψ_M (GP §A.8) -/

/-- The output of Ψ_M: a blob, ☇ or ∞. -/
inductive InvOutput where
  | ok (bytes : ByteArray)
  | panic
  | oog

/-- Whether the octets `a, …, a + n − 1` all lie in 𝕍_μ: ℕ_{a…+n} ⊆ 𝕍_μ. Checked page by page
    (`PVM.Memory.rangeReadable_iff` states it index by index). -/
def Memory.rangeReadable (μ : Memory) (a n : Nat) : Bool :=
  n == 0 ||
    (a + n ≤ 2 ^ 32 &&
      let first := a / pageSize
      let last := (a + n - 1) / pageSize
      (List.range (last + 1 - first)).all fun k => μ.readable ((first + k) * pageSize))

/-- R(ϱ, (ε, ı', ϱ', ω', μ', x')) of Ψ_M (GP §A.8), with u = ϱ − max(ϱ', 0). -/
def invocationResult {X : Type} (gas : UInt64) (r : HostRunResult X) : Nat × InvOutput × X :=
  let u := gas.toNat - r.gas.toNat
  let a := (r.regs.get 7).toNat
  let n := (r.regs.get 8).toNat
  match r.status with
  | .oog => (u, .oog, r.ctx)
  | .halt =>
    if r.mem.rangeReadable a n then (u, .ok ⟨(r.mem.readN a n).toArray⟩, r.ctx)
    else (u, .ok ByteArray.empty, r.ctx)
  | _ => (u, .panic, r.ctx)

/-- Ψ_M(**p**, ı, ϱ, **a**, f, x) (GP §A.8): (gas used, output, final context). -/
def psiM {X : Type} (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (f : HostFn X)
    (x : X) : Nat × InvOutput × X :=
  match standardInit b a with
  | none => (0, .panic, x)
  | some (p, ω, μ) => invocationResult gas (psiH p i gas ω μ f x)

end PVM
