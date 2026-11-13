import Services.Bootstrap.Spec
import Services.Bootstrap.Blob
import Services.Bootstrap.CodeX
import Services.Bootstrap.CodeA
import Services.Bootstrap.CodeF
import Services.Bootstrap.CodeR
import JAM.Theorems.RefineContract

/-!
# The bridge between bootstrap's spec and the model (refine)

The definitions T1 is stated with (`docs/bootstrap-target.md` §3 and step 1 of §4):

* `IsBootstrap l`: the looked-up preimage l is a bootstrap binary.
* `RSem.run`: `Spec.refine`'s host operations (`Spec.ROp`) under the GP refine host functions
  (GP v0.8.0 Appendix B.4: Ω_H `historical_lookup`, Ω_Y `fetch` and Ω_E `export`), with each
  reply as the bootstrap's SDK reads it.
* `ExhaustsHeap`: Ψ_R's run reaches an allocation failure (bootstrap decision 4).

These are definitions only. T1 relates them to Ψ_R (GP eq. `refineinvocation`, `JAM.psiR`).
-/

namespace Services.Bootstrap.Bridge

open PVM JAM Services.Bootstrap.Spec

/-! ## `IsBootstrap` -/

/-- The vendored bootstrap blob (`services/bootstrap/jam-bootstrap-service.jam`), parsed: the
    preimage's metadata split off, then the program blob's sections (GP eq. `conditions`). -/
def vendored : Option JamBlob := (splitMetadata Blob.preimage).bind fun code => JamBlob.parse? code

/-- **The looked-up preimage l is a bootstrap binary** (`docs/bootstrap-target.md` §3, the hypothesis
    `hboot` of T1):
    * l is within 𝖶_C (GP eq. `refineinvocation`'s size check);
    * its code splits from its metadata and parses as a program blob (GP §A.7);
    * the blob's read-only and read-write data, heap pages and stack size are those of the vendored
      blob, with heap bounds (48, 1044430) as deployed;
    * its instructions pass `checkCode` for every set of code facts the bootstrap proofs use
      (`Code`, `CodeX`, `CodeA`, `CodeF`, `CodeR`).

    T1 is about this binary, so the data sections and the layout are pinned to the vendored blob's
    exactly: refine's paths read formatting templates and the encoder's dispatch table from the
    read-only data. Only code outside the facts' ranges may differ. For the vendored blob the kernel
    discharges these (step 10). -/
def IsBootstrap (l : List UInt8) : Prop :=
  l.length ≤ Constants.Cmaxservicecodesize ∧
  ∃ (code : ByteArray) (jb vb : JamBlob), splitMetadata l = some code ∧ JamBlob.parse? code = some jb ∧
    vendored = some vb ∧ jb.ro = vb.ro ∧ jb.rw = vb.rw ∧ jb.heapPages = vb.heapPages ∧
    jb.stackSize = vb.stackSize ∧ heapBounds code = (48, 1044430) ∧
    checkCode jb.code Code.facts = true ∧ checkCode jb.code CodeX.facts = true ∧
    checkCode jb.code CodeA.facts = true ∧ checkCode jb.code CodeF.facts = true ∧
    checkCode jb.code CodeR.facts = true

/-! ## `RSem`: refine's host operations under the GP refine host functions -/

namespace RSem

/-- What refine's host operations see: the account state **d**, the lookup-anchor timeslot
    (p_c)_t, this work item's import segments ī_i and the export offset ς (GP eq.
    `refineinvocation`). -/
structure Env where
  accounts : Accounts
  lookupSlot : Nat
  imports : List Bytes
  exportOffset : Nat

/-- The environment of Ψ_R for item i of package p (GP eq. `refineinvocation`): **d**, (p_c)_t,
    ī_i (none if there is no i-th entry) and ς. -/
def Env.of (d : Accounts) (p : WorkPackage) (imports : List (List Bytes)) (i off : Nat) : Env :=
  { accounts := d, lookupSlot := p.context.lookupAnchorSlot, imports := imports[i]?.getD [],
    exportOffset := off }

/-- b, cut or zero-padded to 𝖶_G octets: what the SDK reads into its zeroed 𝖶_G-octet buffer
    (`fetch`), and what Ω_E appends (GP Appendix B.4, Ω_E: the first min(z, 𝖶_G) octets, padded). -/
def padSeg (b : Bytes) : Bytes :=
  b.take Constants.Csegmentsize ++ List.replicate (Constants.Csegmentsize - b.length) 0

/-- One host operation: its reply, and the exports **e** after it.
    * `histLookup s h`: Ω_H (id 7) on service s: Λ(**d**[s], (p_c)_t, h) (`Account.historicalLookup`),
      none if s has no account. The SDK makes the call twice (length, then data); both see the
      same state, so the reply is the preimage.
    * `importSeg k`: Ω_Y (id 2) case 6 with ω₁₁ = k: ī_i[k], read into a zeroed 𝖶_G-octet buffer
      (`padSeg`); none if there is no such segment.
    * `exportSeg b`: Ω_E (id 8): while ς + |**e**| < 𝖶_X, the segment `padSeg b` is appended;
      otherwise Ω_E returns FULL and **e** is unchanged. The reply is ignored. -/
def reply : {β : Type} → ROp β → Env → List Bytes → β × List Bytes
  | _, .histLookup s h, env, e => ((env.accounts.get? s).bind (·.historicalLookup env.lookupSlot h), e)
  | _, .importSeg k, env, e => (env.imports[k]?.map padSeg, e)
  | _, .exportSeg b, env, e =>
    ((), if env.exportOffset + e.length < Constants.Cmaxpackageexports then e ++ [padSeg b] else e)

/-- Run a program from exports **e**: its result and the exports, or none if it panics. -/
def go {α : Type} : Prog ROp α → Env → List Bytes → Option (α × List Bytes)
  | .pure a, _, e => some (a, e)
  | .call op k, env, e => go (k (reply op env e).1) env (reply op env e).2
  | .panic, _, _ => none

/-- **`RSem.run`**: run refine's program from no exports: its output and the exported segments, or
    none if it panics (☇). -/
def run (prog : Prog ROp Bytes) (env : Env) : Option (Bytes × List Bytes) := go prog env []

end RSem

/-! ## `ExhaustsHeap` -/

/-- The return points in bootstrap's code where an allocation's result comes back null when the
    model's allocator fails: the `alloc` wrapper (40611), the `realloc` wrapper (40821),
    `read_vec`'s growth (33055), and the SDK's direct `alloc_impl` calls in the import-segment
    `fetch` (44741) and in `foreign_historical_lookup` (49149). -/
def allocRets : List Nat := [40611, 40821, 33055, 44741, 49149]

/-- `foreign_historical_lookup`'s size check (49061): a preimage longer than 2^37 − 32 octets cannot
    be allocated, and the wrapper traps at 49074 before allocating (it also goes there when its
    `alloc_impl` call returns null). -/
def sizeTrap : Nat := 49074

/-- **An allocation fails** at j: a null allocation (the run at one of `allocRets` with ω₇ = 0), or an
    allocation too large to attempt, refused by the size check before it (`sizeTrap`). Both are heap
    exhaustion (bootstrap decision 4; Adam's decision of 2026-11-13, recorded in
    `docs/bootstrap-target.md`). -/
def AllocFails (j : Nat) (ω : Regs) : Prop := (j ∈ allocRets ∧ ω[7] = UInt64.ofNat 0) ∨ j = sizeTrap

/-- The arguments **a** Ψ_R passes for item i (GP eq. `refineinvocation`):
    ℰ(c, i, w_s, ↕w_y, ℋ(p)). -/
def psiRArgs (c i : Nat) (w : WorkItem) (p : WorkPackage) : ByteArray :=
  ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat w.service ++ Codec.var w.payload ++
    (Blake2b.hash256 ⟨p.encode.toArray⟩).toList).toArray⟩

/-- The host environment Ψ_R runs item i's code under (GP eq. `refineinvocation`), as `JAM.psiR`
    builds it. -/
def psiREnv (params : Params) (d : Accounts) (i : Nat) (p : WorkPackage) (r : List UInt8)
    (imports extrinsics : List (List (List UInt8))) (off : Nat) (w : WorkItem) (code : ByteArray) :
    RefineHost.Env :=
  { params, service := w.service, accounts := d, lookupSlot := p.context.lookupAnchorSlot, code,
    exportOffset := off,
    fetch := { params, package := some p, entropy := some (List.replicate 32 0), authTrace := some r,
               itemIndex := some i, imports := some imports, extrinsics := some extrinsics } }

/-- **Ψ_R's run exhausts the heap** (bootstrap decision 4): item i's code, started as Ψ_M starts it
    (Y, GP §A.7), reaches a failed allocation (`AllocFails`: a null allocation, or one refused by
    the size check before it), gas aside (a run under the refine dispatcher's contract, which pins down the real handler:
    `refineContractK_pins`). -/
def ExhaustsHeap (params : Params) (d : Accounts) (c i : Nat) (p : WorkPackage) (r : List UInt8)
    (imports extrinsics : List (List (List UInt8))) (off : Nat) : Prop :=
  ∃ (w : WorkItem) (l : List UInt8) (code P : ByteArray) (ω : Regs) (μ : Memory),
    p.items[i]? = some w ∧
    (d.get? w.service).bind (fun a => a.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList) = some l ∧
    splitMetadata l = some code ∧ standardInit code (psiRArgs c i w p) = some (P, ω, μ) ∧
    ∃ (cap j n : Nat) (ω' : Regs) (μ' : Memory) (x' : RefineCtx),
      FreeStepsH P (refineContractK cap (psiREnv params d i p r imports extrinsics off w code)) 0 ω μ
        ((∅, []) : RefineCtx) j ω' μ' x' n ∧ AllocFails j ω'

end Services.Bootstrap.Bridge
