import JAM.Fast.Blake2b
import JAM.Host.General
import JAM.Blake2b
import PVM.Fast.Host
import JAM.Fast.HostGeneral

/-!
# The refine and is-authorized invocations $\Psi_R$ and $\Psi_I$ (GP v0.8.1 Appendix B)

* the PVM instance type (GP v0.8.1 eq. `innerpvm`, here `InnerPvm`) and the program modules;
* the refine host functions `historical_lookup` ($\Omega_H$), `export` ($\Omega_E$), `compile` ($\Omega_\Gamma$), `machine`
  ($\Omega_M$), `peek` ($\Omega_P$), `poke` ($\Omega_O$), `pages` ($\Omega_Z$), `invoke` ($\Omega_K$) and `expunge` ($\Omega_X$)
  (`sec:refinefunctions`; `compile` and the module map are new in v0.8.1, #530);
* the refine invocation $\Psi_R$ with its dispatcher $F$ (eqs. `refinvocation`, `refinemutator`);
* the is-authorized invocation $\Psi_I$ with its dispatcher $F$ (eqs. `isauthinvocation`,
  `isauthorizedmutator`), with the authorization code $\mathbf{p}_c$ (eq. in §14.3, `sec:packagesanditems`).

Both invocations draw implicitly on a recent account state $\mathbf{d}$; here it is an explicit argument.
-/

namespace JAM

open PVM

/-- A PVM instance $\equiv (\mathbf{p} \in \mathbb{B}, \mathbf{u} \in \mathbb{M}, i \in \mathbb{N}_R, \tilde\varrho \in \{\bot, \top\}, h \in \mathbb{N})$ (GP v0.8.1 eq. `innerpvm`):
    program blob, RAM, instruction counter, the gas-charged flag, and the handle of the program
    module it was instantiated from (#530). -/
structure InnerPvm where
  code : ByteArray
  ram : Memory
  pc : Nat
  charged : Bool
  handle : Nat

/-- The refine context $(\mathbf{m}, \mathbf{P}, \mathbf{e}) \in (\langle \mathbb{N} \to \text{instance} \rangle, \langle \mathbb{N} \to \mathbb{B} \rangle, [\![ \mathbb{J} ]\!])$ (GP v0.8.1
    eq. `refinemutator`): the PVM instances, the compiled program modules (blobs, by handle) and the
    exported segments. All start empty. -/
abbrev RefineCtx := Std.ExtTreeMap Nat InnerPvm × Std.ExtTreeMap Nat ByteArray × List (List UInt8)

namespace RefineHost

open Result

-- Inner-PVM result codes (GP Appendix B "Host-Call Result Constants").
def HALT : Nat := 0
def PANIC : Nat := 1
def FAULT : Nat := 2
def HOST : Nat := 3
def OOG : Nat := 4

def r7 {X} (out : HostOut X) (v : Nat) : HostOut X := { out with regs := setR7 out.regs v }
def panic {X} (out : HostOut X) : HostOut X := { out with status := .panic }

/-! ## $\Omega_H$, `historical_lookup` = 7 -/

/-- $\Omega_H(\varrho, \varphi, \mu, x, s, \mathbf{d}, t)$, $g = \mathsf{M}_{H,c} + \mathfrak{G}(\mathsf{M}_{H,\ell}, \varphi_{11})$ (GP v0.8.1): the historical
    lookup $\Lambda$ of the preimage of the hash at $\varphi_8$, in service $\mathbf{a} = \mathbf{d}[s]$ ($\varphi_7 = 2^{64} - 1$) or
    $\mathbf{d}[\varphi_7]$, at time $t$. -/
def historicalLookup {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (s : Nat) (d : Accounts)
    (t : Nat) (x : X) : HostOut X :=
  let z := reg ω 11
  charged (Constants.CgasHconst + memGas Constants.CgasHlinear z) gas ω μ x fun out =>
    let a : Option ServiceAccount :=
      if reg ω 7 = 2 ^ 64 - 1 then d.get? s else d.get? (reg ω 7)
    let h := reg ω 8
    let v : Except Unit (Option (List UInt8)) :=
      if !μ.rangeReadable h 32 then .error ()
      else .ok (a.bind fun a => a.historicalLookup t (μ.readN h 32))
    writeValue out v (reg ω 9) (reg ω 10) z

/-! ## $\Omega_E$, `export` = 8 -/

/-- $\Omega_E(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{P}, \mathbf{e}), \varsigma)$, $g = \mathsf{M}_E$: append the octets at $\varphi_7$ (length $\min(\varphi_8, \mathsf{W}_G)$), zero-padded
    to $\mathsf{W}_G$, to the exports; $\varphi'_7$ is the new segment's index $\varsigma + |\mathbf{e}|$. -/
def exportSeg (gas : Nat) (ω : Regs) (μ : Memory) (off : Nat) (c : RefineCtx) : HostOut RefineCtx :=
  charged Constants.CgasE gas ω μ c fun out =>
    let p := reg ω 7
    let z := min (reg ω 8) Constants.Csegmentsize
    if !μ.rangeReadable p z then panic out
    else if off + c.2.2.length ≥ Constants.Cmaxpackageexports then r7 out FULL
    else
      let x := μ.readN p z ++ List.replicate (Constants.Csegmentsize - z) 0
      r7 { out with ctx := (c.1, c.2.1, c.2.2 ++ [x]) } (off + c.2.2.length)

/-! ## $\Omega_\Gamma$, `compile` = 9 (new in GP v0.8.1, #530) -/

/-- $\min(n \in \mathbb{N} : n \notin K)$, for a set $K$ given as a membership test on at most `bound` naturals: one of
    0, …, `bound` is free. -/
def freeIn (mem : Nat → Bool) (bound : Nat) : Nat :=
  ((List.range (bound + 1)).find? (!mem ·)).getD bound

/-- $\mathbf{H} = \mathcal{K}(\mathbf{P}) \cup \{\mathbf{m}[n]_h : n \in \mathcal{K}(\mathbf{m})\}$, the handles in use (GP v0.8.1 $\Omega_\Gamma$), as a list
    (possibly with repeats). -/
def handlesInUse (c : RefineCtx) : List Nat :=
  c.2.1.keys ++ c.1.values.map (·.handle)

/-- The program blob $\mathbf{p}$ of $\Omega_\Gamma$ (GP v0.8.1), with $\nabla$ as `.error ()` and $\varnothing$ as `.ok none`: from our
    RAM at $p$ (length $l$) for $m = 0$; for $m = 1$, the historical lookup $\mathbf{h}$ of the hash at $p$, in
    service $\mathbf{a}$, at time $t$, cut to $\mathbf{h}_{f^{\ast}\dots+l^{\ast}}$ with $f^{\ast} = \min(f, |\mathbf{h}|)$ and
    $l^{\ast} = \min(l, |\mathbf{h}| - f^{\ast})$; $\varnothing$ otherwise. -/
def compileBlob (μ : Memory) (a : Option ServiceAccount) (t m p l f : Nat) :
    Except Unit (Option ByteArray) :=
  if m = 0 then
    if μ.rangeReadable p l then .ok (some ⟨(μ.readN p l).toArray⟩) else .error ()
  else if m = 1 then
    if !μ.rangeReadable p 32 then .error ()
    else match a.bind fun a => a.historicalLookup t (μ.readN p 32) with
      | some h =>
        let fS := min f h.length
        let lS := min l (h.length - fS)
        .ok (some ⟨((h.drop fS).take lS).toArray⟩)
      | none => .ok none
  else .ok none

/-- The gas of `compile` for mode $m$ and length $l$ (GP v0.8.1 $\Omega_\Gamma$). -/
def compileGas (m l : Nat) : Nat :=
  if m = 0 then Constants.CgasGammamemconst + memGas Constants.CgasGammamemlinear l
  else if m = 1 then Constants.CgasGammadbconst + memGas Constants.CgasGammadblinear l
  else Constants.CgasGammamemconst

/-- $\Omega_\Gamma(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{P}, \mathbf{e}), s, \mathbf{d}, t)$ (GP v0.8.1 Appendix B, #530), with
    $[m, p, l, f, i] = \varphi_{7\dots+5}$: compile a program module from our RAM ($m = 0$) or from the preimage
    of the hash at $p$ in service $\mathbf{a} = \mathbf{d}[s]$ ($i = 2^{64} - 1$) or $\mathbf{d}[i]$ ($m = 1$). FULL if 128
    handles are in use; ☇ if the source is unreadable; NONE if the preimage is not available; HUH if
    there is no blob or it does not deblob at 0; otherwise the module gets the least free handle $k$,
    returned in $\varphi'_7$. -/
def compile (gas : Nat) (ω : Regs) (μ : Memory) (s : Nat) (d : Accounts) (t : Nat) (c : RefineCtx) :
    HostOut RefineCtx :=
  let m := reg ω 7; let p := reg ω 8; let l := reg ω 9; let f := reg ω 10; let i := reg ω 11
  charged (compileGas m l) gas ω μ c fun out =>
    let a : Option ServiceAccount := if i = 2 ^ 64 - 1 then d.get? s else d.get? i
    let hs := handlesInUse c
    let H := hs.eraseDups
    if H.length ≥ 128 then r7 out FULL
    else match compileBlob μ a t m p l f with
      | .error () => panic out
      | .ok none => if m = 1 then r7 out NONE else r7 out HUH
      | .ok (some blob) =>
        if (deblob blob 0).isNone then r7 out HUH
        else
          let k := freeIn (hs.contains ·) hs.length
          r7 { out with ctx := (c.1, c.2.1.insert k blob, c.2.2) } k

/-! ## $\Omega_M$, `machine` = 10 -/

/-- $\min(n \in \mathbb{N} : n \notin \mathcal{K}(\mathbf{m}))$. One of $0, \dots, |\mathbf{m}|$ is free. -/
def freeId (m : Std.ExtTreeMap Nat InnerPvm) : Nat :=
  ((List.range (m.size + 1)).find? (!m.contains ·)).getD m.size

/-- $\Omega_M(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{P}, \mathbf{e}))$, $g = \mathsf{M}_M$ (GP v0.8.1 Appendix B, #530): with $[h, i] = \varphi_{7\dots+2}$,
    instantiate program module $h$, starting at $i$, with empty RAM. FULL if there are already 63
    instances; WHO if there is no module $h$; HUH if its blob does not deblob at $i$. (v0.8.0 read the
    program blob from RAM.) -/
def machine (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let h := reg ω 7; let i := reg ω 8
  charged Constants.CgasM gas ω μ c fun out =>
    let m := c.1
    if m.size ≥ 63 then r7 out FULL
    else match c.2.1.get? h with
      | none => r7 out WHO
      | some p =>
        if (deblob p i).isNone then r7 out HUH
        else
          let n := freeId m
          r7 { out with ctx := (m.insert n ⟨p, Memory.empty, i, false, h⟩, c.2) } n

/-! ## $\Omega_P$, `peek` = 11 -/

/-- $\Omega_P(\varrho, \varphi, \mu, \mathbf{m})$, $g = \mathsf{M}_{P,c} + \mathfrak{G}(\mathsf{M}_{P,\ell}, z)$: copy $z$ octets from address $s$ of machine $n$'s
    RAM to address $o$ of ours, with $[n, o, s, z] = \varphi_{7\dots+4}$. -/
def peek (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let n := reg ω 7; let o := reg ω 8; let s := reg ω 9; let z := reg ω 10
  charged (Constants.CgasPconst + memGas Constants.CgasPlinear z) gas ω μ c fun out =>
    if !μ.rangeWritable o z then panic out
    else match c.1.get? n with
      | none => r7 out WHO
      | some vm =>
        if !vm.ram.rangeReadable s z then r7 out OOB
        else r7 { out with mem := μ.writeN o (vm.ram.readN s z) } OK

/-! ## $\Omega_O$, `poke` = 12 -/

/-- $\Omega_O(\varrho, \varphi, \mu, \mathbf{m})$, $g = \mathsf{M}_{O,c} + \mathfrak{G}(\mathsf{M}_{O,\ell}, z)$: copy $z$ octets from address $s$ of our RAM to
    address $o$ of machine $n$'s, with $[n, s, o, z] = \varphi_{7\dots+4}$. -/
def poke (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let n := reg ω 7; let s := reg ω 8; let o := reg ω 9; let z := reg ω 10
  charged (Constants.CgasOconst + memGas Constants.CgasOlinear z) gas ω μ c fun out =>
    if !μ.rangeReadable s z then panic out
    else match c.1.get? n with
      | none => r7 out WHO
      | some vm =>
        if !vm.ram.rangeWritable o z then r7 out OOB
        else
          let vm' := { vm with ram := vm.ram.writeN o (μ.readN s z) }
          r7 { out with ctx := (c.1.insert n vm', c.2) } OK

/-! ## $\Omega_Z$, `pages` = 13 -/

/-- The gas of `pages` for mode $r$ and page count $c$. -/
def pagesGas (r c : Nat) : Nat :=
  if r = 0 then Constants.CgasZfreeconst + c * Constants.CgasZfreelinear
  else if r = 1 ∨ r = 2 then Constants.CgasZallocconst + c * Constants.CgasZalloclinear
  else if r = 3 ∨ r = 4 then Constants.CgasZsetmodeconst + c * Constants.CgasZsetmodelinear
  else Constants.CgasZinvalid

/-- $\mathbf{u}'$ of $\Omega_Z$: zero the values of pages $p, \dots, p + c - 1$ when $r < 3$, and set their access to $\varnothing$
    ($r = 0$), R ($r \in \{1, 3\}$) or W ($r \in \{2, 4\}$). -/
def setPagesMode (u : Memory) (p c r : Nat) : Memory :=
  let lo := p * pageSize
  let hi := (p + c) * pageSize
  let u := if r < 3 then { u with bytes := u.bytes.filter fun a _ => !(lo ≤ a ∧ a < hi) } else u
  u.setPages p c (if r = 0 then none else if r = 1 ∨ r = 3 then some .read else some .write)

/-- $\Omega_Z(\varrho, \varphi, \mu, \mathbf{m})$: change the $c$ pages from page $p$ of machine $n$'s RAM to mode $r$, with
    $[n, p, c, r] = \varphi_{7\dots+4}$. -/
def pages (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let n := reg ω 7; let p := reg ω 8; let k := reg ω 9; let r := reg ω 10
  charged (pagesGas r k) gas ω μ c fun out =>
    match c.1.get? n with
    | none => r7 out WHO
    | some vm =>
      if r > 4 ∨ p < 16 ∨ p + k ≥ 2 ^ 32 / Constants.Cpvmpagesize then r7 out HUH
      else if r > 2 ∧ (List.range k).any (fun j => !(vm.ram.pages.contains (p + j))) then r7 out HUH
      else r7 { out with ctx := (c.1.insert n { vm with ram := setPagesMode vm.ram p k r }, c.2) } OK

/-! ## $\Omega_K$, `invoke` = 14 -/

/-- $\mathcal{E}_8$ of thirteen registers. -/
def encodeRegs (w : Regs) : List UInt8 := (w.toList.map fun r => Codec.fixed 8 r.toNat).flatten

/-- The thirteen registers $\mathcal{E}_8^{-1}$ of 104 octets. -/
def decodeRegs (b : List UInt8) : Regs :=
  Vector.ofFn fun k => UInt64.ofNat (Num.decodeLE ((b.drop (8 * k.val)).take 8))

/-- $\Omega_K(\varrho, \varphi, \mu, \mathbf{m})$, $g = \mathsf{M}_K + g_R$: run inner machine $n = \varphi_7$ by $\Psi$, with gas $g_R$ and registers
    $\mathbf{w}$ read from (and written back to) the 112 octets at $o = \varphi_8$. $\varphi'_7$ gives the exit reason, and
    $\varphi'_8$ the host-call id or fault address. The gas left by the inner run is returned:
    $\varrho^{\ast} = \max(\varrho - g, 0) + g'_R$ (GP v0.8.1). -/
def invoke (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let n := reg ω 7; let o := reg ω 8
  let w? : Option (Nat × Regs) :=
    if μ.rangeWritable o 112 then
      let b := μ.readN o 112
      some (Num.decodeLE (b.take 8), decodeRegs (b.drop 8))
    else none
  let gR := match w? with | some (g, _) => g | none => 0
  let g := Constants.CgasK + gR
  charged g gas ω μ c fun out =>
    match w? with
    | none => panic out
    | some (gR, w) =>
      match c.1.get? n with
      | none => r7 out WHO
      | some vm =>
        let r := psi vm.code vm.pc (UInt64.ofNat gR) vm.charged w vm.ram
        let mStar := μ.writeN o (Codec.fixed 8 r.gas.toNat ++ encodeRegs r.regs)
        let pc' := match r.status with
          | .host _ => blobNext vm.code r.pc
          | _ => r.pc
        let m' := c.1.insert n { vm with ram := r.mem, pc := pc', charged := r.charged }
        let base : HostOut RefineCtx :=
          { out with gas := out.gas + r.gas.toNat, mem := mStar, ctx := (m', c.2) }
        let (code, r8) : Nat × Nat := match r.status with
          | .host h => (HOST, h.toNat)
          | .fault x => (FAULT, x.toNat)
          | .oog => (OOG, reg ω 8)
          | .panic => (PANIC, reg ω 8)
          | _ => (HALT, reg ω 8)
        { base with regs := (setR7 ω code).set 8 (UInt64.ofNat r8) }

/-! ## $\Omega_X$, `expunge` = 15 -/

/-- $\Omega_X(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{P}, \mathbf{e}))$, $g = \mathsf{M}_X$ (GP v0.8.1, #530), with $[m, n] = \varphi_{7, 8}$: for
    $m = 0$ remove instance $n$, returning its instruction counter; for $m = 1$ remove program module $n$,
    returning OK; WHO if there is no such instance or module; HUH for any other $m$. -/
def expunge (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  charged Constants.CgasX gas ω μ c fun out =>
    let m := reg ω 7; let n := reg ω 8
    if m = 0 then
      match c.1.get? n with
      | none => r7 out WHO
      | some vm => r7 { out with ctx := (c.1.erase n, c.2) } vm.pc
    else if m = 1 then
      if c.2.1.contains n then r7 { out with ctx := (c.1, c.2.1.erase n, c.2.2) } OK
      else r7 out WHO
    else r7 out HUH

/-- The fixed part of a refine invocation's environment. -/
structure Env where
  params : Params
  /-- the service $s = w_s$ -/
  service : Nat
  /-- $\mathbf{d}$, the account state drawn upon -/
  accounts : Accounts
  /-- $(p_c)_t$, the lookup-anchor timeslot -/
  lookupSlot : Nat
  /-- the service code, for `grow_heap` -/
  code : ByteArray
  /-- $\varsigma$, the export offset -/
  exportOffset : Nat
  /-- what `fetch` sees: $p$, $\mathbb{H}_0$ (32 zero octets), $\mathbf{r}$, $i$, $\bar{\imath}$, $\bar{x}$ -/
  fetch : FetchContext

/-- The unknown-host-call case (GP v0.8.1 eqs. `refinemutator`, `isauthorizedmutator`):
    $(\infty, 0, \varphi', \mu, x)$ if $\varrho < \mathsf{M}_\varnothing$, otherwise $(\blacktriangleright, \varrho - \mathsf{M}_\varnothing, \varphi', \mu, x)$, where $\varphi' = \varphi$ except $\varphi'_7 = \text{WHAT}$. -/
def unknown {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) : HostOut X :=
  if gas < Constants.Cgasunknown then ⟨.oog, 0, setR7 ω WHAT, μ, x⟩
  else ⟨.cont, gas - Constants.Cgasunknown, setR7 ω WHAT, μ, x⟩

/-- $F \in \mathfrak{F}_{(\langle \mathbb{N} \to \text{instance} \rangle, \langle \mathbb{N} \to \text{module} \rangle, [\![ \mathbb{J} ]\!])}$ (GP v0.8.1 eq. `refinemutator`): dispatch on the
    host-call id. v0.8.1 inserts `compile` = 9 and renumbers `machine` … `expunge` to 10 … 15 (#530). -/
def dispatch (env : Env) (n gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  match n with
  | 0 => hostGas gas ω μ c
  | 1 => hostGrowHeap gas ω μ env.code c
  | 2 => hostFetch gas ω μ env.fetch c
  | 7 => historicalLookup gas ω μ env.service env.accounts env.lookupSlot c
  | 8 => exportSeg gas ω μ env.exportOffset c
  | 9 => compile gas ω μ env.service env.accounts env.lookupSlot c
  | 10 => machine gas ω μ c
  | 11 => peek gas ω μ c
  | 12 => poke gas ω μ c
  | 13 => pages gas ω μ c
  | 14 => invoke gas ω μ c
  | 15 => expunge gas ω μ c
  | _ => unknown gas ω μ c

/-- $F$ of $\Psi_I$ (GP eq. `isauthorizedmutator`): `gas`, `grow_heap` and `fetch` only; the context is
    $\varnothing$ (`Unit`). -/
def dispatchI (params : Params) (p : WorkPackage) (code : ByteArray) (n gas : Nat) (ω : Regs)
    (μ : Memory) (c : Unit) : HostOut Unit :=
  match n with
  | 0 => hostGas gas ω μ c
  | 1 => hostGrowHeap gas ω μ code c
  | 2 => hostFetch gas ω μ { params, package := some p } c
  | _ => unknown gas ω μ c

end RefineHost

/-- A host function as a `PVM.HostFn` (its gas is in $\mathbb{N}_G$ under the v0.8.1 common rules). -/
def toHostFn {X : Type} (f : Nat → Nat → Regs → Memory → X → HostOut X) : HostFn X :=
  fun n gas ω μ x =>
    let o := f n gas.toNat ω μ x
    ⟨o.status, UInt64.ofNat o.gas, o.regs, o.mem, o.ctx⟩

/-- The work result of a $\Psi_M$ output: the blob, or ☇ / $\infty$. -/
def _root_.PVM.InvOutput.toWorkResult : InvOutput → WorkResult
  | .ok b => .ok b
  | .panic => .err .panic
  | .oog => .err .outOfGas

/-- The result of $\Psi_R$: the output or error, the exported segments, and the gas used. -/
structure RefineOut where
  result : WorkResult
  exports : List (List UInt8)
  gasUsed : Nat

/-- $\Psi_R(c, i, p, \mathbf{r}, \bar{\imath}, \varsigma)$ (GP eq. `refinvocation`), refining item $i$ of package $p$ on core $c$,
    with authorizer trace $\mathbf{r}$, import segments $\bar{\imath}$ and export offset $\varsigma$, over accounts $\mathbf{d}$.

    `extrinsics` is $\bar{x}$: the extrinsic data of every item, the $\mathbf{x}$ with $(\mathcal{H}(\mathbf{x}), |\mathbf{x}|) \in w_x$
    (eq. `refinemutator`). The paper builds $\bar{x}$ from preimages it does not pass to $\Psi_R$; we take them
    as an argument. -/
def psiR (params : Params) (d : Accounts) (c i : Nat) (p : WorkPackage) (r : List UInt8)
    (imports : List (List (List UInt8))) (extrinsics : List (List (List UInt8))) (off : Nat) :
    RefineOut :=
  match p.items[i]? with
  | none => ⟨.err .bad, [], 0⟩
  | some w =>
    let t := p.context.lookupAnchorSlot
    let lookup := (d.get? w.service).bind fun a => a.historicalLookup t w.codeHash.toList
    match lookup with
    | none => ⟨.err .bad, [], 0⟩
    | some l =>
      if l.length > Constants.Cmaxservicecodesize then ⟨.err .big, [], 0⟩
      else
          -- the whole preimage is the JAM blob (GP v0.8.1 eq. `refinvocation`, GP #582)
          let code : ByteArray := ⟨l.toArray⟩
          let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++
            Codec.var w.payload ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩
          let env : RefineHost.Env :=
            { params, service := w.service, accounts := d, lookupSlot := t, code, exportOffset := off,
              fetch := { params, package := some p, entropy := some (List.replicate 32 0),
                         authTrace := some r, itemIndex := some i, imports := some imports,
                         extrinsics := some extrinsics } }
          let (u, o, (_, _, e)) := psiM code 0 (UInt64.ofNat w.refineGasLimit) a
            (toHostFn (RefineHost.dispatch env)) (∅, ∅, [])
          match o with
          | .ok b => ⟨.ok b, e, u⟩
          | o => ⟨o.toWorkResult, [], u⟩

/-- $\mathbf{p}_\mathbf{u} \equiv \Lambda(\delta[p_h], (p_c)_t, p_u)$, the authorization code, the whole preimage (GP v0.8.1
    eq. 14.12, §14.3, GP #582). -/
def WorkPackage.authCode (d : Accounts) (p : WorkPackage) : Option ByteArray := do
  let a ← d.get? p.authCodeHost
  let l ← a.historicalLookup p.context.lookupAnchorSlot p.authCodeHash.toList
  some ⟨l.toArray⟩

/-- $\Psi_I(p, c)$ (GP eq. `isauthinvocation`), over accounts $\mathbf{d}$: the authorizer trace or an error,
    and the gas used. -/
def psiI (params : Params) (d : Accounts) (p : WorkPackage) (c : Nat) : WorkResult × Nat :=
  match p.authCode d with
  | none => (.err .bad, 0)
  | some code =>
    if code.size > Constants.Cmaxauthcodesize then (.err .big, 0)
    else
      let (u, o, _) := psiM code 0 (UInt64.ofNat Constants.Cpackageauthgas)
        ⟨(Codec.fixed 2 c).toArray⟩ (toHostFn (RefineHost.dispatchI params p code)) ()
      (o.toWorkResult, u)

end JAM
