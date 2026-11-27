import PVM.Invocation
import PVM.Fast.Parse
import JAM.Account
import JAM.Params
import JAM.Work

/-!
# General host functions (GP v0.8.1 Appendix B, `sec:generalfunctions`)

`gas` ($\Omega_G$), `grow_heap` ($\Omega_{\text{♊}}$), `fetch` ($\Omega_Y$), `lookup` ($\Omega_L$),
`read` ($\Omega_R$), `write` ($\Omega_W$) and `info` ($\Omega_I$), each transcribed from its row of
the paper's table.

The common rules (GP v0.8.1 Appendix B, `Host Functions`, #533), shared by every host function:
* $\varrho^{\ast} \equiv \max(\varrho - g, 0)$ unless a function defines $\varrho^{\ast}$ itself;
* $(\varepsilon^{\ast}, \varphi^{\ast}, \mu^{\ast}, x^{\ast}) \equiv (\infty, \varphi, \mu, x)$ if
  $\varrho < g$, and otherwise $(\varepsilon', \varphi', \mu', x')$, where by default
  $\varepsilon' = \blacktriangleright$, $\varphi' = \varphi$, $\mu' = \mu$ and $x' = x$ except as
  indicated.

So running out of gas consumes all of it ($\varrho^{\ast} = 0$) and leaves registers, memory and
context as they were. The paper's gas is $\mathbb{N}_G$ throughout (v0.8.0 used $\mathbb{Z}_G$
here), and so is `HostOut.gas`.
-/

namespace JAM

open PVM

/-- $\varepsilon^{\ast}$ of a host function: $\blacktriangleright$, ☇ or $\infty$ (GP v0.8.1). -/
abbrev HostStatus := PVM.HostStatus

/-- The result of a host function: $(\varepsilon^{\ast}, \varrho^{\ast}, \varphi^{\ast}, \mu^{\ast},
    x^{\ast})$, with $\varrho^{\ast} \in \mathbb{N}_G$ (GP v0.8.1). -/
structure HostOut (X : Type) where
  status : HostStatus
  gas : Nat
  regs : Regs
  mem : Memory
  ctx : X

-- The host-call result constants (GP Appendix B "Host-Call Result Constants").
namespace Result
def NONE : Nat := 2 ^ 64 - 1
def WHAT : Nat := 2 ^ 64 - 2
def OOB : Nat := 2 ^ 64 - 3
def WHO : Nat := 2 ^ 64 - 4
def FULL : Nat := 2 ^ 64 - 5
def CORE : Nat := 2 ^ 64 - 6
def CASH : Nat := 2 ^ 64 - 7
def LOW : Nat := 2 ^ 64 - 8
def HUH : Nat := 2 ^ 64 - 9
def OK : Nat := 0
end Result

/-- $\mathcal{G}(L, \ell) = \lceil L \cdot \ell / 1024 \rceil$, memory-sized gas (GP eq. `fnmemgas`). -/
def memGas (L ℓ : Nat) : Nat := (L * ℓ + 1023) / 1024

/-- $\mathbb{N}_{a \dots + n} \subseteq \mathbb{V}^{\ast}_\mu$, checked page by page like
    `Memory.rangeReadable`. -/
def _root_.PVM.Memory.rangeWritable (μ : Memory) (a n : Nat) : Bool :=
  n == 0 ||
    (a + n ≤ 2 ^ 32 &&
      let first := a / pageSize
      let last := (a + n - 1) / pageSize
      (List.range (last + 1 - first)).all fun k => μ.writable ((first + k) * pageSize))

/-- Set $\varphi_7$. -/
def setR7 (ω : Regs) (v : Nat) : Regs := ω.set 7 (UInt64.ofNat v)

/-- Register `k` as a natural. -/
def reg (ω : Regs) (k : Fin 13) : Nat := (ω.get k).toNat

/-- Apply the common rules (GP v0.8.1 Appendix B, #533): if $\varrho < g$,
    $(\infty, 0, \varphi, \mu, x)$, with all gas consumed and the state unchanged; otherwise run
    `body` on the default $(\blacktriangleright, \varrho - g, \varphi, \mu, x)$.
    ($\varrho - g = \max(\varrho - g, 0)$ here, since $\varrho \ge g$.) -/
def charged {X : Type} (g : Nat) (gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) : HostOut X :=
  if gas < g then ⟨.oog, 0, ω, μ, x⟩
  else body ⟨.cont, gas - g, ω, μ, x⟩

/-- The shared tail of `fetch`, `lookup`, `read` and `info`: given the value $\mathbf{v}$
    ($\emptyset$ as `none`, $\nabla$ as `.error`), the offset `f₀` and length `z` registers and the
    output address `o`: ☇ if $\mathbf{v} = \nabla$ or
    $\mathbb{N}_{o \dots + l} \not\subseteq \mathbb{V}^{\ast}_\mu$; NONE if $\mathbf{v} = \emptyset$;
    otherwise $\varphi'_7 = |\mathbf{v}|$ and $\mu'_{o \dots + l} = \mathbf{v}_{f \dots + l}$, where
    $f = \min(f_0, |\mathbf{v}|)$ and $l = \min(z, |\mathbf{v}| - f)$.
    For $\mathbf{v} = \emptyset$ we take $|\mathbf{v}| = 0$, so $l = 0$. -/
def writeValue {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f₀ z : Nat) : HostOut X :=
  let len := match v with | .ok (some v) => v.length | _ => 0
  let f := min f₀ len
  let l := min z (len - f)
  match v with
  | .error () => { out with status := .panic }
  | .ok v =>
    if !out.mem.rangeWritable o l then { out with status := .panic }
    else match v with
      | none => { out with regs := setR7 out.regs Result.NONE }
      | some v =>
        { out with regs := setR7 out.regs v.length, mem := out.mem.writeN o ((v.drop f).take l) }

/-! ## $\Omega_G$, `gas` = 0 -/

/-- $\Omega_G$: $\varphi'_7 \equiv \varrho^{\ast}$, with $g = \mathsf{M}_G$ (GP v0.8.1). -/
def hostGas {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) : HostOut X :=
  charged Constants.CgasG gas ω μ x fun out => { out with regs := setR7 ω out.gas }

/-! ## $\Omega_{\text{♊}}$, `grow_heap` = 1 -/

/-- The heap's page bounds for a standard program (GP v0.8.1 $\Omega_{\text{♊}}$, eq.
    `jamblobformat`): the first heap page $a = (2\mathsf{Z}_Z + Q(|\mathbf{o}|)) / \mathsf{Z}_P$ and
    the bound $b = (2^{32} - 3\mathsf{Z}_Z - \mathsf{Z}_I - Q(s)) / \mathsf{Z}_P$ below the stack,
    with the stack size rounded to a zone ($Q$, not $P$: GP #538). -/
def heapBounds (jam : ByteArray) : Nat × Nat :=
  let (roLen, stack) := match JamBlob.parseStd? jam with
    | some jb => (jb.ro.size, jb.stackSize)
    | none => (0, 0)
  ((2 * zoneSize + roundZone roLen) / pageSize,
   (2 ^ 32 - 3 * zoneSize - inputSize - roundZone stack) / pageSize)

/-- The gas-free part of $\Omega_{\text{♊}}$: the heap bounds $a$ and $b$, the current heap top
    $h = a + c$ ($c$ the writable pages in $\mathbb{N}_{a \dots b}$) and the requested top
    $w = \varphi_7$. -/
def growHeapCore (ω : Regs) (μ : Memory) (jam : ByteArray) : Nat × Nat × Nat × Nat :=
  let (a, b) := heapBounds jam
  -- c = |{p ∈ ℕ_{a…b} | (μ_**a**)[p] = W}|
  let c := (List.range (b - a)).countP fun k => μ.pages.get? (a + k) == some .write
  (a, b, a + c, reg ω 7)


/-- $\Omega_{\text{♊}}(\varrho, \varphi, \mu, x, \mathbf{p})$ (GP v0.8.1): grow the read-write
    region of a standard program (eq. `conditions`) to page $\varphi_7$. $\varphi'_7 = h$ if
    $\varphi_7 \le h$ or $\varphi_7 > b$, otherwise $\varphi_7$; then
    $(\mu'_{\mathbf{a}})_{a \dots \varphi'_7} = [\mathrm{W}, \dots]$;
    $g = \mathsf{M}_{\text{♊},c} + (\varphi'_7 - h) \cdot \mathsf{M}_{\text{♊},p}$, under the common
    rules. Since v0.8.1 (#533) the no-growth case is charged like any other ($\infty$ if
    $\varrho < \mathsf{M}_{\text{♊},c}$). The bound $b$ rounds the stack size to a zone ($Q(s)$,
    GP #538; `heapBounds`). -/
def hostGrowHeap {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (jam : ByteArray) (x : X) :
    HostOut X :=
  let (a, b, h, w) := growHeapCore ω μ jam
  let r7 := if w ≤ h ∨ w > b then h else w
  let g := Constants.CgasGeminiconst + (r7 - h) * Constants.CgasGeminilinear
  charged g gas ω μ x fun out =>
    { out with regs := setR7 ω r7, mem := μ.setPages a (r7 - a) (some .write) }

/-! ## $\Omega_Y$, `fetch` = 2 -/

/-- The context `fetch` reads from (GP Appendix B, $\Omega_Y$'s arguments): the work package $p$,
    entropy $n$, authorizer trace $\mathbf{r}$, item index $i$, imports $\bar{\imath}$, extrinsics
    $\bar{x}$ and accumulation inputs $\mathbf{i}$; any may be $\emptyset$ (`none`) depending on the
    invocation. -/
structure FetchContext where
  params : Params := .full
  package : Option WorkPackage := none
  entropy : Option (List UInt8) := none
  authTrace : Option (List UInt8) := none
  itemIndex : Option Nat := none
  imports : Option (List (List (List UInt8))) := none
  extrinsics : Option (List (List (List UInt8))) := none
  accInputs : Option (List AccumulateInput) := none

/-- $S(w)$: the summary of a work item that `fetch` cases 11 and 12 return. -/
def itemSummary (w : WorkItem) : List UInt8 :=
  Codec.fixed 4 w.service ++ Codec.blob w.codeHash ++ Codec.fixed 8 w.refineGasLimit ++
    Codec.fixed 8 w.accumulateGasLimit ++ Codec.fixed 2 w.exportCount ++
    Codec.fixed 2 w.importSegments.length ++ Codec.fixed 2 w.extrinsics.length ++
    Codec.fixed 4 w.payload.size

/-- $\mathbf{v}$ of $\Omega_Y$ for case $\varphi_{10}$ with arguments $\varphi_{11}$, $\varphi_{12}$. -/
def fetchValue (cx : FetchContext) (c a b : Nat) : Option (List UInt8) :=
  let nth {α} (xs : List α) (k : Nat) : Option α := xs[k]?
  match c with
  | 0 => some cx.params.encode
  | 1 => cx.entropy
  | 2 => cx.authTrace
  | 3 => do let x ← cx.extrinsics; let xs ← nth x a; nth xs b
  | 4 => do let x ← cx.extrinsics; let i ← cx.itemIndex; let xs ← nth x i; nth xs a
  | 5 => do let x ← cx.imports; let xs ← nth x a; nth xs b
  | 6 => do let x ← cx.imports; let i ← cx.itemIndex; let xs ← nth x i; nth xs a
  | 7 => cx.package.map (·.encode)
  | 8 => cx.package.map (·.authConfig.toList)
  | 9 => cx.package.map (·.authToken.toList)
  | 10 => cx.package.map (·.context.encode)
  | 11 => cx.package.map fun p => Codec.varSeq itemSummary p.items
  | 12 => do let p ← cx.package; let w ← nth p.items a; some (itemSummary w)
  | 13 => do let p ← cx.package; let w ← nth p.items a; some w.payload.toList
  | 14 => cx.accInputs.map (Codec.varSeq AccumulateInput.encode)
  | 15 => do let is ← cx.accInputs; let i ← nth is a; some i.encode
  | _ => none

/-- $\Omega_Y$: write the requested item, with
    $g = \mathsf{M}_{Y,c,c} + \mathcal{G}(\mathsf{M}_{Y,c,\ell}, \varphi_9)$. -/
def hostFetch {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (cx : FetchContext) (x : X) :
    HostOut X :=
  let c := reg ω 10
  let (gc, gl) := Constants.CgasY (if c < 16 then some c else none)
  let g := gc + memGas gl (reg ω 9)
  charged g gas ω μ x fun out =>
    writeValue out (.ok (fetchValue cx c (reg ω 11) (reg ω 12))) (reg ω 7) (reg ω 8) (reg ω 9)

/-! ## $\Omega_L$, `lookup` = 3 (an accumulate function in GP v0.8.1)

`lookup`, `read` and `info` are accumulate functions in GP v0.8.1 (§B, "Accumulate Functions");
`write` is defined with the accumulation context in `JAM/Accumulate.lean`. These three only read the
context, so they take the accumulating service's account $\mathbf{x}_s$ and the accounts
$\mathbf{d} = (x_e)_d$. -/

/-- The account $\varphi_7$ names (GP v0.8.1, $\Omega_L$, $\Omega_R$, $\Omega_I$): $\mathbf{x}_s$
    for $\varphi_7 = 2^{64} - 1$, otherwise $\mathbf{d}[\varphi_7]$ if any. -/
def namedAccount (self : ServiceAccount) (d : Accounts) (w : Nat) : Option ServiceAccount :=
  if w = 2 ^ 64 - 1 then some self else d.get? w

/-- $\Omega_L(\varrho, \varphi, \mu, (x, y))$ (GP v0.8.1): look up the preimage of the 32-octet hash
    at $\varphi_8$ in the named account, with
    $g = \mathsf{M}_{L,c} + \mathcal{G}(\mathsf{M}_{L,\ell}, \varphi_{11})$. -/
def hostLookup {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount)
    (d : Accounts) (x : X) : HostOut X :=
  let g := Constants.CgasLconst + memGas Constants.CgasLlinear (reg ω 11)
  charged g gas ω μ x fun out =>
    let h := reg ω 8
    let v : Except Unit (Option (List UInt8)) :=
      if !μ.rangeReadable h 32 then .error ()
      else .ok ((namedAccount self d (reg ω 7)).bind fun a => a.preimages.get? (μ.readN h 32))
    writeValue out v (reg ω 9) (reg ω 10) (reg ω 11)

/-! ## $\Omega_R$, `read` = 4 -/

/-- $\Omega_R(\varrho, \varphi, \mu, (x, y))$ (GP v0.8.1): read the storage value under the key at
    $\varphi_8$ (length $\varphi_9$) of the named account, with
    $g = \mathsf{M}_{R,c} + \mathcal{G}(\mathsf{M}_{R,\mathrm{k},\ell}, \varphi_9) +
    \mathcal{G}(\mathsf{M}_{R,\mathrm{v},\ell}, \varphi_{12})$. -/
def hostRead {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount)
    (d : Accounts) (x : X) : HostOut X :=
  let kO := reg ω 8
  let kZ := reg ω 9
  let g := Constants.CgasRconst + memGas Constants.CgasRkeylinear kZ +
    memGas Constants.CgasRvallinear (reg ω 12)
  charged g gas ω μ x fun out =>
    let v : Except Unit (Option (List UInt8)) :=
      if !μ.rangeReadable kO kZ then .error ()
      else .ok ((namedAccount self d (reg ω 7)).bind fun a => a.storageGet (μ.readN kO kZ))
    writeValue out v (reg ω 10) (reg ω 11) (reg ω 12)

/-! ## $\Omega_I$, `info` = 6 -/

/-- The octets `info` returns for an account (GP v0.8.1, $\Omega_I$):
    $\mathcal{E}(c, \mathcal{E}_4(u, u'), \mathcal{E}_8(b, b', t, g, m, o), \mathcal{E}_4(i),
    \mathcal{E}_8(f), \mathcal{E}_4(r, a, p))$, with $u$ the supervisor, $u'$ its creation slot and
    $b'$ the supervisor balance. -/
def infoValue (a : ServiceAccount) : List UInt8 :=
  let e := Codec.fixed
  a.codeHash ++ e 4 a.supervisor ++ e 4 a.supervisorCreated ++ e 8 a.balance ++
    e 8 a.supervisorBalance ++ e 8 a.minBalance ++ e 8 a.minAccGas ++ e 8 a.minMemoGas ++
    e 8 a.octets ++ e 4 a.items ++ e 8 a.gratis ++ e 4 a.created ++ e 4 a.lastAcc ++ e 4 a.parent

/-- $\Omega_I(\varrho, \varphi, \mu, (x, y))$ (GP v0.8.1): information about the named account,
    with $g = \mathsf{M}_I$. -/
def hostInfo {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount)
    (d : Accounts) (x : X) : HostOut X :=
  charged Constants.CgasI gas ω μ x fun out =>
    writeValue out (.ok ((namedAccount self d (reg ω 7)).map infoValue)) (reg ω 8) (reg ω 9)
      (reg ω 10)

end JAM
