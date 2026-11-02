import JAM.Host.General
import JAM.Blake2b

/-!
# The refine and is-authorized invocations Ψ_R and Ψ_I (GP v0.8.0 Appendix B)

* the integrated PVM type 𝕄 (eq. `innerpvm`, here `InnerPvm`);
* the refine host functions `historical_lookup` (Ω_H), `export` (Ω_E), `machine` (Ω_M), `peek` (Ω_P),
  `poke` (Ω_O), `pages` (Ω_Z), `invoke` (Ω_K) and `expunge` (Ω_X) (`sec:refinefunctions`);
* the refine invocation Ψ_R with its dispatcher F (eqs. `refinvocation`, `refinemutator`);
* the is-authorized invocation Ψ_I with its dispatcher F (eqs. `isauthinvocation`,
  `isauthorizedmutator`), with the authorization code **p**_c (eq. in §14.3, `sec:packagesanditems`).

Both invocations draw implicitly on a recent account state **d**; here it is an explicit argument.
-/

namespace JAM

open PVM

/-- An integrated PVM 𝕄 ≡ (**p** ∈ 𝔹, **u** ∈ 𝕄, i ∈ ℕ_R, ϱ̃ ∈ 𝔹ool) (GP eq. `innerpvm`): program
    blob, RAM, instruction counter and the gas-charged flag. -/
structure InnerPvm where
  code : ByteArray
  ram : Memory
  pc : Nat
  charged : Bool

/-- The refine context (**m**, **e**) ∈ (⟨ℕ → 𝕄⟩, ⟦𝕁⟧): the inner machines and the exported
    segments. Both start empty. -/
abbrev RefineCtx := Std.ExtTreeMap Nat InnerPvm × List (List UInt8)

/-- (**m**, c): the code split ℰ(↕**m**, **c**) of a preimage: the metadata is skipped. `none` if
    the octets do not have that form. -/
def splitMetadata (b : List UInt8) : Option ByteArray := do
  let ba : ByteArray := ⟨b.toArray⟩
  let (mLen, pos) ← Blob.decodeNat? ba 0
  if pos + mLen > ba.size then none
  some (ba.extract (pos + mLen) ba.size)

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

/-! ## Ω_H, `historical_lookup` = 7 -/

/-- Ω_H(ϱ, ω, μ, s, **d**, t), g = 𝖬_{H,c} + 𝔊(𝖬_{H,ℓ}, ω_11): the historical lookup Λ of the
    preimage of the hash at ω_8, in service s (ω_7 = 2^64 − 1) or ω_7, at time t. -/
def historicalLookup {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (s : Nat) (d : Accounts)
    (t : Nat) (x : X) : HostOut X :=
  let z := reg ω 11
  charged (Constants.CgasHconst + memGas Constants.CgasHlinear z) gas ω μ x fun out =>
    let a : Option ServiceAccount :=
      if reg ω 7 = 2 ^ 64 - 1 ∧ d.contains s then d.get? s
      else d.get? (reg ω 7)
    let h := reg ω 8
    let v : Except Unit (Option (List UInt8)) :=
      if !μ.rangeReadable h 32 then .error ()
      else .ok (a.bind fun a => a.historicalLookup t (μ.readN h 32))
    writeValue out v (reg ω 9) (reg ω 10) z

/-! ## Ω_E, `export` = 8 -/

/-- Ω_E(ϱ, ω, μ, **e**, ς), g = 𝖬_E: append the octets at ω_7 (length min(ω_8, 𝖶_G)), zero-padded
    to 𝖶_G, to the exports; ω'_7 is the new segment's index ς + |**e**|. -/
def exportSeg (gas : Nat) (ω : Regs) (μ : Memory) (off : Nat) (c : RefineCtx) : HostOut RefineCtx :=
  charged Constants.CgasE gas ω μ c fun out =>
    let p := reg ω 7
    let z := min (reg ω 8) Constants.Csegmentsize
    if !μ.rangeReadable p z then panic out
    else if off + c.2.length ≥ Constants.Cmaxpackageexports then r7 out FULL
    else
      let x := μ.readN p z ++ List.replicate (Constants.Csegmentsize - z) 0
      r7 { out with ctx := (c.1, c.2 ++ [x]) } (off + c.2.length)

/-! ## Ω_M, `machine` = 9 -/

/-- min(n ∈ ℕ : n ∉ K(**m**)). One of 0, …, |**m**| is free. -/
def freeId (m : Std.ExtTreeMap Nat InnerPvm) : Nat :=
  ((List.range (m.size + 1)).find? (!m.contains ·)).getD m.size

/-- Ω_M(ϱ, ω, μ, **m**), g = 𝖬_{M,c} + 𝔊(𝖬_{M,ℓ}, p_Z): create an inner machine from the program
    at ω_7 (length ω_8), starting at ω_9, with empty RAM. FULL if there are already 63. -/
def machine (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let pO := reg ω 7; let pZ := reg ω 8; let i := reg ω 9
  charged (Constants.CgasMconst + memGas Constants.CgasMlinear pZ) gas ω μ c fun out =>
    let m := c.1
    if m.size ≥ 63 then r7 out FULL
    else if !μ.rangeReadable pO pZ then panic out
    else
      let p : ByteArray := ⟨(μ.readN pO pZ).toArray⟩
      if (deblob p i).isNone then r7 out HUH
      else
        let n := freeId m
        r7 { out with ctx := (m.insert n ⟨p, Memory.empty, i, false⟩, c.2) } n

/-! ## Ω_P, `peek` = 10 -/

/-- Ω_P(ϱ, ω, μ, **m**), g = 𝖬_{P,c} + 𝔊(𝖬_{P,ℓ}, z): copy z octets from address s of machine n's
    RAM to address o of ours, with [n, o, s, z] = ω_{7…+4}. -/
def peek (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let n := reg ω 7; let o := reg ω 8; let s := reg ω 9; let z := reg ω 10
  charged (Constants.CgasPconst + memGas Constants.CgasPlinear z) gas ω μ c fun out =>
    if !μ.rangeWritable o z then panic out
    else match c.1.get? n with
      | none => r7 out WHO
      | some vm =>
        if !vm.ram.rangeReadable s z then r7 out OOB
        else r7 { out with mem := μ.writeN o (vm.ram.readN s z) } OK

/-! ## Ω_O, `poke` = 11 -/

/-- Ω_O(ϱ, ω, μ, **m**), g = 𝖬_{O,c} + 𝔊(𝖬_{O,ℓ}, z): copy z octets from address s of our RAM to
    address o of machine n's, with [n, s, o, z] = ω_{7…+4}. -/
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

/-! ## Ω_Z, `pages` = 12 -/

/-- The gas of `pages` for mode r and page count c. -/
def pagesGas (r c : Nat) : Nat :=
  if r = 0 then Constants.CgasZfreeconst + c * Constants.CgasZfreelinear
  else if r = 1 ∨ r = 2 then Constants.CgasZallocconst + c * Constants.CgasZalloclinear
  else if r = 3 ∨ r = 4 then Constants.CgasZsetmodeconst + c * Constants.CgasZsetmodelinear
  else Constants.CgasZinvalid

/-- **u**' of Ω_Z: zero the values of pages p, …, p + c − 1 when r < 3, and set their access to ∅
    (r = 0), R (r ∈ {1, 3}) or W (r ∈ {2, 4}). -/
def setPagesMode (u : Memory) (p c r : Nat) : Memory :=
  let lo := p * pageSize
  let hi := (p + c) * pageSize
  let u := if r < 3 then { u with bytes := u.bytes.filter fun a _ => !(lo ≤ a ∧ a < hi) } else u
  u.setPages p c (if r = 0 then none else if r = 1 ∨ r = 3 then some .read else some .write)

/-- Ω_Z(ϱ, ω, μ, **m**): change the c pages from page p of machine n's RAM to mode r, with
    [n, p, c, r] = ω_{7…+4}. -/
def pages (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  let n := reg ω 7; let p := reg ω 8; let k := reg ω 9; let r := reg ω 10
  charged (pagesGas r k) gas ω μ c fun out =>
    match c.1.get? n with
    | none => r7 out WHO
    | some vm =>
      if r > 4 ∨ p < 16 ∨ p + k ≥ 2 ^ 32 / Constants.Cpvmpagesize then r7 out HUH
      else if r > 2 ∧ (List.range k).any (fun j => !(vm.ram.pages.contains (p + j))) then r7 out HUH
      else r7 { out with ctx := (c.1.insert n { vm with ram := setPagesMode vm.ram p k r }, c.2) } OK

/-! ## Ω_K, `invoke` = 13 -/

/-- ℰ_8 of thirteen registers. -/
def encodeRegs (w : Regs) : List UInt8 := (w.toList.map fun r => Codec.fixed 8 r.toNat).flatten

/-- The thirteen registers ℰ_8⁻¹ of 104 octets. -/
def decodeRegs (b : List UInt8) : Regs :=
  Vector.ofFn fun k => UInt64.ofNat (Num.decodeLE ((b.drop (8 * k.val)).take 8))

/-- Ω_K(ϱ, ω, μ, **m**), g = 𝖬_K + g_R: run inner machine n = ω_7 by Ψ, with gas g_R and registers
    **w** read from (and written back to) the 112 octets at o = ω_8. ω'_7 gives the exit reason, and
    ω'_8 the host-call id or fault address. The gas left by the inner run is returned:
    ϱ' = ϱ − g + g_R'. -/
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

/-! ## Ω_X, `expunge` = 14 -/

/-- Ω_X(ϱ, ω, μ, **m**), g = 𝖬_X: remove machine n = ω_7, returning its instruction counter. -/
def expunge (gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  charged Constants.CgasX gas ω μ c fun out =>
    let n := reg ω 7
    match c.1.get? n with
    | none => r7 out WHO
    | some vm => r7 { out with ctx := (c.1.erase n, c.2) } vm.pc

/-- The fixed part of a refine invocation's environment. -/
structure Env where
  params : Params
  /-- the service s = w_s -/
  service : Nat
  /-- **d**, the account state drawn upon -/
  accounts : Accounts
  /-- (p_c)_t, the lookup-anchor timeslot -/
  lookupSlot : Nat
  /-- the service code, for `grow_heap` -/
  code : ByteArray
  /-- ς, the export offset -/
  exportOffset : Nat
  /-- what `fetch` sees: p, 𝟎 (32 zero octets), **r**, i, ī, x̄ -/
  fetch : FetchContext

/-- The unknown-host-call case: charge 𝖬_∅ and return WHAT. -/
def unknown {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) : HostOut X :=
  let g' : Int := (gas : Int) - Constants.Cgasunknown
  ⟨if g' < 0 then .oog else .cont, g', setR7 ω WHAT, μ, x⟩

/-- F ∈ 𝔉_{(⟨ℕ → 𝕄⟩, ⟦𝕁⟧)} (GP eq. `refinemutator`): dispatch on the host-call id. -/
def dispatch (env : Env) (n gas : Nat) (ω : Regs) (μ : Memory) (c : RefineCtx) : HostOut RefineCtx :=
  match n with
  | 0 => hostGas gas ω μ c
  | 1 => hostGrowHeap gas ω μ env.code c
  | 2 => hostFetch gas ω μ env.fetch c
  | 7 => historicalLookup gas ω μ env.service env.accounts env.lookupSlot c
  | 8 => exportSeg gas ω μ env.exportOffset c
  | 9 => machine gas ω μ c
  | 10 => peek gas ω μ c
  | 11 => poke gas ω μ c
  | 12 => pages gas ω μ c
  | 13 => invoke gas ω μ c
  | 14 => expunge gas ω μ c
  | _ => unknown gas ω μ c

/-- F of Ψ_I (GP eq. `isauthorizedmutator`): `gas`, `grow_heap` and `fetch` only; the context is
    ∅ (`Unit`). -/
def dispatchI (params : Params) (p : WorkPackage) (code : ByteArray) (n gas : Nat) (ω : Regs)
    (μ : Memory) (c : Unit) : HostOut Unit :=
  match n with
  | 0 => hostGas gas ω μ c
  | 1 => hostGrowHeap gas ω μ code c
  | 2 => hostFetch gas ω μ { params, package := some p } c
  | _ => unknown gas ω μ c

end RefineHost

/-- A host function with ℤ_G gas as a `PVM.HostFn`: the gas is clamped at 0, which only happens
    together with ∞ (as for `accHostFn`). -/
def toHostFn {X : Type} (f : Nat → Nat → Regs → Memory → X → HostOut X) : HostFn X :=
  fun n gas ω μ x =>
    let o := f n gas.toNat ω μ x
    ⟨o.status, UInt64.ofNat o.gas.toNat, o.regs, o.mem, o.ctx⟩

/-- The work result of a Ψ_M output: the blob, or ☇ / ∞. -/
def _root_.PVM.InvOutput.toWorkResult : InvOutput → WorkResult
  | .ok b => .ok b
  | .panic => .err .panic
  | .oog => .err .outOfGas

/-- The result of Ψ_R: the output or error, the exported segments, and the gas used. -/
structure RefineOut where
  result : WorkResult
  exports : List (List UInt8)
  gasUsed : Nat

/-- Ψ_R(c, i, p, **r**, ī, ς) (GP eq. `refinvocation`), refining item i of package p on core c,
    with authorizer trace **r**, import segments ī and export offset ς, over accounts **d**.

    `extrinsics` is x̄: the extrinsic data of every item, the **x** with (ℋ(**x**), |**x**|) ∈ w_x
    (eq. `refinemutator`). The paper builds x̄ from preimages it does not pass to Ψ_R; we take them
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
      else match splitMetadata l with
        | none => ⟨.err .bad, [], 0⟩
        | some code =>
          let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++
            Codec.var w.payload ++ (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩
          let env : RefineHost.Env :=
            { params, service := w.service, accounts := d, lookupSlot := t, code, exportOffset := off,
              fetch := { params, package := some p, entropy := some (List.replicate 32 0),
                         authTrace := some r, itemIndex := some i, imports := some imports,
                         extrinsics := some extrinsics } }
          let (u, o, (_, e)) := psiM code 0 (UInt64.ofNat w.refineGasLimit) a
            (toHostFn (RefineHost.dispatch env)) (∅, [])
          match o with
          | .ok b => ⟨.ok b, e, u⟩
          | o => ⟨o.toWorkResult, [], u⟩

/-- **p**_c, the authorization code (GP §14.3): ℰ(↕**p**_m, **p**_c) = Λ(**d**[p_h], (p_c)_t, p_u). -/
def WorkPackage.authCode (d : Accounts) (p : WorkPackage) : Option ByteArray := do
  let a ← d.get? p.authCodeHost
  let l ← a.historicalLookup p.context.lookupAnchorSlot p.authCodeHash.toList
  splitMetadata l

/-- Ψ_I(p, c) (GP eq. `isauthinvocation`), over accounts **d**: the authorizer trace or an error,
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
