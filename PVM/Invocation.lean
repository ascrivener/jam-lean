import PVM.Machine
import PVM.Fast.Basic

/-!
# Host-call invocation $\Psi_H$, standard initialization $Y$ and argument invocation $\Psi_M$

GP v0.8.1 §A.6 (Host Call Definition), §A.7 (`sec:standardprograminit`, eqs. `jamblobformat`,
`ramlayoutfits`, `memlayout`, `registers`; the metadata prefix $\mathcal{E}(\updownarrow\mathbf{m})$ is #582) and §A.8
(Argument Invocation Definition).
-/

namespace PVM

/-! ## Host-call handlers and $\Psi_H$ (GP §A.6) -/

/-- The exit reasons a host-call handler may give: $\{\blacktriangleright, \text{☇}, \infty\}$ (GP v0.8.1 §A.6, $\contextmutator{X}$). Since
    v0.8.1 (#533) a handler can no longer halt the machine. -/
inductive HostStatus where
  | cont
  | panic
  | oog
  deriving DecidableEq, Repr

/-- The corresponding PVM exit reason. -/
def HostStatus.toStatus : HostStatus → Status
  | .cont => .cont
  | .panic => .panic
  | .oog => .oog

/-- The result of a host-call handler: $(\varepsilon, \varrho, \varphi, \mu, x)$. -/
structure HostResult (X : Type) where
  status : HostStatus
  gas : UInt64
  regs : Regs
  mem : Memory
  ctx : X

/-- $\contextmutator{X} \equiv (\mathbb{N}, \mathbb{N}_G, [\![ \mathbb{N}_R ]\!]_{13}, \mathbb{M}, X) \to$
    $(\{\blacktriangleright, \text{☇}, \infty\}, \mathbb{N}_G, [\![ \mathbb{N}_R ]\!]_{13}, \mathbb{M}, X)$ (GP v0.8.1 §A.6).

    Gas is in $\mathbb{N}_G$ throughout: since v0.8.1 (#533) $\Psi_H$'s result gas is $\mathbb{N}_G$ too, and host functions
    return $\varrho^{\ast} = \max(\varrho - g, 0)$. -/
abbrev HostFn (X : Type) := Nat → UInt64 → Regs → Memory → X → HostResult X

/-- A handler that never returns more gas than it was given. Every host function of the paper
    charges a non-negative amount, so they all have this property; under it $\Psi_H$ terminates. -/
def HostFn.GasNonIncreasing {X : Type} (f : HostFn X) : Prop :=
  ∀ h g ω μ x, (f h g ω μ x).gas.toNat ≤ g.toNat

/-- The result of $\Psi_H^{\ast}$: $(\varepsilon, \imath, \varrho, \tilde\varrho, \varphi, \mu, x)$ (GP v0.8.1 §A.6). -/
structure HostRunResult (X : Type) where
  /-- $\varepsilon \in \{\text{☇}, \infty, \blacksquare\} \cup \{\Finv\} \times \mathbb{N}_R$ -/
  status : Status
  /-- $\imath$ as $\Psi$ returns it (0 on $\blacksquare$ and ☇ from the machine). -/
  pc : Nat
  gas : UInt64
  charged : Bool
  regs : Regs
  mem : Memory
  ctx : X

/-- $\imath + 1 + \text{skip}(\imath)$ for the program of blob `p` ($\imath$ itself if `p` does not parse; $\Psi$ only reports
    $\hbar$ for blobs that do). -/
def blobNext (p : ByteArray) (i : Nat) : Nat :=
  match Blob.parse? p with
  | some P => P.next i
  | none => i

/-- $\Psi_H^{\ast}$ with at most `fuel` host calls (GP v0.8.1 §A.6). A handler result other than $\blacktriangleright$ is ☇ or
    $\infty$, which $\Psi_H^{\ast}$ returns with the handler's state. -/
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

/-- $\Psi_H^{\ast}(p, \imath, \varrho, \tilde\varrho, \varphi, \mu, f, x)$ (GP v0.8.1 §A.6). Every host call that continues happens at a lower
    `runMeasure` than the last, so `runMeasure + 1` host calls suffice when `f` does not increase
    gas (`PVM.psiHStar_eq` in `PVM.Theorems.Invocation`). For a handler that does increase gas
    the paper's $\Psi_H$ need not terminate; there we return ☇ after the fuel. -/
def psiHStar {X : Type} (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs)
    (μ : Memory) (f : HostFn X) (x : X) : HostRunResult X :=
  (psiHFuel p f (runMeasure p i gas ch + 1) i gas ch ω μ x).getD
    { status := .panic, pc := 0, gas, charged := ch, regs := ω, mem := μ, ctx := x }

/-- $\Psi_H(p, \imath, \varrho, \varphi, \mu, f, x) \equiv \Psi_H^{\ast}(p, \imath, \varrho, \bot, \varphi, \mu, f, x)$ (GP v0.8.1 §A.6). -/
def psiH {X : Type} (p : ByteArray) (i : Nat) (gas : UInt64) (ω : Regs) (μ : Memory)
    (f : HostFn X) (x : X) : HostRunResult X :=
  psiHStar p i gas false ω μ f x

/-! ## Standard program initialization $Y$ (GP §A.7) -/

/-- $\mathsf{Z}_Z = 2^{16}$, the major zone size (GP v0.8.1 eq. `jamblobformat`). -/
def zoneSize : Nat := 2 ^ 16

/-- $\mathsf{Z}_I = 2^{24}$, the maximum input size (GP v0.8.1 eq. `jamblobformat`). -/
def inputSize : Nat := 2 ^ 24

/-- $P(x) = \mathsf{Z}_P \lceil x / \mathsf{Z}_P \rceil$. -/
def roundPage (x : Nat) : Nat := pageSize * ((x + pageSize - 1) / pageSize)

/-- $Z(x) = \mathsf{Z}_Z \lceil x / \mathsf{Z}_Z \rceil$. -/
def roundZone (x : Nat) : Nat := zoneSize * ((x + zoneSize - 1) / zoneSize)

/-- The components of a standard JAM program blob (GP v0.8.1 eq. `jamblobformat`): read-only data $\mathbf{o}$,
    read-write data $\mathbf{w}$, `z` extra heap pages, stack size `s` and the PVM blob $\mathbf{p}$. -/
structure JamBlob where
  ro : ByteArray
  rw : ByteArray
  heapPages : Nat
  stackSize : Nat
  code : ByteArray

/-- The unique $(\mathbf{o}, \mathbf{w}, z, s, \mathbf{p})$ with
    $\mathcal{E}_3(|\mathbf{o}|) \frown \mathcal{E}_3(|\mathbf{w}|) \frown \mathcal{E}_2(z) \frown \mathcal{E}_3(s) \frown{}$
    $\mathbf{o} \frown \mathbf{w} \frown \mathcal{E}_4(|\mathbf{p}|) \frown \mathbf{p}$ equal to the blob. -/
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

/-- A standard program blob without its metadata (GP v0.8.1 eq. `jamblobformat`, GP #582): the
    blob is $\mathcal{E}(\updownarrow\mathbf{m}) \frown{}$ (the rest), and the metadata $\mathbf{m}$ is opaque and ignored by $Y$. `none` if
    the blob does not start with a well-formed $\mathcal{E}(\updownarrow\mathbf{m})$. -/
def skipMetadata? (b : ByteArray) : Option ByteArray := do
  let (mLen, pos) ← Blob.decodeNat? b 0
  if pos + mLen > b.size then none
  some (b.extract (pos + mLen) b.size)

/-- The unique $(\mathbf{m}, \mathbf{o}, \mathbf{w}, z, s, \mathbf{p})$ of a standard program blob (GP v0.8.1
    eq. `jamblobformat`): the metadata is skipped (`skipMetadata?`), the rest parsed by
    `JamBlob.parse?`. -/
def JamBlob.parseStd? (b : ByteArray) : Option JamBlob := (skipMetadata? b).bind JamBlob.parse?

/-- The address of the read-only section, $\mathsf{Z}_Z$. -/
def roStart : Nat := zoneSize

/-- The address of the read-write section, $2\mathsf{Z}_Z + Z(|\mathbf{o}|)$. -/
def rwStart (jb : JamBlob) : Nat := 2 * zoneSize + roundZone jb.ro.size

/-- The end of the stack, $2^{32} - 2\mathsf{Z}_Z - \mathsf{Z}_I$. -/
def stackEnd : Nat := 2 ^ 32 - 2 * zoneSize - inputSize

/-- The address of the argument section, $2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I$. -/
def argStart : Nat := 2 ^ 32 - zoneSize - inputSize

/-- The RAM of GP eq. `memlayout`. Every section boundary there is a multiple of $\mathsf{Z}_P$, so we
    set page access per page and then write the three data sections. -/
def initialMemory (jb : JamBlob) (a : ByteArray) : Memory :=
  let pg (x : Nat) := x / pageSize
  let μ : Memory := Memory.empty
  -- [𝖹_Z, 𝖹_Z + P(|o|)) : R
  let μ := μ.setPages (pg roStart) (pg (roundPage jb.ro.size)) (some .read)
  -- [2𝖹_Z + Z(|o|), 2𝖹_Z + Z(|o|) + P(|w|) + z𝖹_P) : W
  let μ := μ.setPages (pg (rwStart jb)) (pg (roundPage jb.rw.size) + jb.heapPages) (some .write)
  -- [2^32 − 2𝖹_Z − 𝖹_I − P(s), 2^32 − 2𝖹_Z − 𝖹_I) : W
  let μ := μ.setPages (pg (stackEnd - roundPage jb.stackSize)) (pg (roundPage jb.stackSize)) (some .write)
  -- [2^32 − 𝖹_Z − 𝖹_I, 2^32 − 𝖹_Z − 𝖹_I + P(|a|)) : R
  let μ := μ.setPages (pg argStart) (pg (roundPage a.size)) (some .read)
  let μ := μ.writeN roStart jb.ro.toList
  let μ := μ.writeN (rwStart jb) jb.rw.toList
  μ.writeN argStart a.toList

/-- The registers of GP eq. `registers`: $\varphi_0 = 2^{32} - 2^{16}$, $\varphi_1 = 2^{32} - 2\mathsf{Z}_Z - \mathsf{Z}_I$,
    $\varphi_7 = 2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I$, $\varphi_8 = |\mathbf{a}|$, all others 0. -/
def initialRegs (a : ByteArray) : Regs :=
  (Vector.replicate 13 (0 : UInt64))
    |>.set 0 (UInt64.ofNat (2 ^ 32 - 2 ^ 16))
    |>.set 1 (UInt64.ofNat stackEnd)
    |>.set 7 (UInt64.ofNat argStart)
    |>.set 8 (UInt64.ofNat a.size)

/-- The decoded JAM blob, if it is a valid encoding, the sections fit
    ($5\mathsf{Z}_Z + Z(|\mathbf{o}|) + Z(|\mathbf{w}| + z\mathsf{Z}_P) + Z(s) + \mathsf{Z}_I \le 2^{32}$) and $|\mathbf{a}| \le \mathsf{Z}_I$. -/
def validJamBlob? (b : ByteArray) (a : ByteArray) : Option JamBlob :=
  if a.size > inputSize then none
  else (JamBlob.parseStd? b).bind fun jb =>
    if 5 * zoneSize + roundZone jb.ro.size + roundZone (jb.rw.size + jb.heapPages * pageSize) +
        roundZone jb.stackSize + inputSize > 2 ^ 32 then none
    else some jb

/-- $Y(\mathbf{p}, \mathbf{a})$ (GP §A.7): the PVM blob, registers and RAM for JAM blob `b` and arguments
    `a`, or $\emptyset$ if `b` is not a valid encoding or the sections do not fit.

    The paper types $\mathbf{a} \in \mathbb{B}_{:\mathsf{Z}_I}$; we return $\emptyset$ for longer arguments. -/
def standardInit (b : ByteArray) (a : ByteArray) : Option (ByteArray × Regs × Memory) :=
  (validJamBlob? b a).map fun jb => (jb.code, initialRegs a, initialMemory jb a)

/-! ## Argument invocation $\Psi_M$ (GP v0.8.1 §A.8) -/

/-- The output of $\Psi_M$: a blob, ☇ or $\infty$. -/
inductive InvOutput where
  | ok (bytes : ByteArray)
  | panic
  | oog

/-- Whether the octets `a, …, a + n − 1` all lie in $\mathbb{V}_\mu$: $\mathbb{N}_{a \dots+n} \subseteq \mathbb{V}_\mu$. Checked page by page. -/
def Memory.rangeReadable (μ : Memory) (a n : Nat) : Bool :=
  n == 0 ||
    (a + n ≤ 2 ^ 32 &&
      let first := a / pageSize
      let last := (a + n - 1) / pageSize
      (List.range (last + 1 - first)).all fun k => μ.readable ((first + k) * pageSize))

/-- $R(\varrho, (\varepsilon, \imath', \varrho', \varphi', \mu', x'))$ of $\Psi_M$ (GP v0.8.1 §A.8), with $u = \varrho - \varrho'$. -/
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

/-- $\Psi_M(\mathbf{p}, \imath, \varrho, \mathbf{a}, f, x)$ (GP v0.8.1 §A.8): (gas used, output, final context). -/
def psiM {X : Type} (b : ByteArray) (i : Nat) (gas : UInt64) (a : ByteArray) (f : HostFn X)
    (x : X) : Nat × InvOutput × X :=
  match standardInit b a with
  | none => (0, .panic, x)
  | some (p, ω, μ) => invocationResult gas (psiH p i gas ω μ f x)

end PVM
