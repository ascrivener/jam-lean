import Services.Bootstrap.Vendored.Facts
import Services.Bootstrap.Acc.Final.Spec

/-!
# T1c and T2 for the deployed bootstrap binary (step 10 of `docs/bootstrap-target.md`)

`refine_t1c_deployed` and `accumulate_spec_deployed` are `Refine.T1c.refine_t1c` and
`Acc.Final.accumulate_spec` for the deployed binary `Blob.preimage` (the octets of
`services/bootstrap/jam-bootstrap-service.jam`), with the blob hypotheses discharged by the kernel
(`Vendored.Facts`): `VendoredFactsC` and `IsBootstrapC` for T1c, `AccVendoredFacts` and `IsBootstrapCode` for
T2. Every other hypothesis of the two theorems stays as it is: the Fmt summaries (`FmtHypsC`), the
items loop's and handlers' hypotheses (`AccHyps`), `hnoimport`, `hrsr`, `hpre`, `ValuesFit`, `InfoFits`.
-/

namespace Services.Bootstrap.Vendored

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.CodeF Services.Bootstrap.Acc Services.Bootstrap.Fmt Services.Bootstrap.Bridge
  Services.Bootstrap.Prefix Services.Bootstrap.Acc.Handlers.InstrRep Services.Bootstrap.Refine.T1c
  Services.Bootstrap.Acc.Final

/-- **T1c for the deployed binary** (`refine_t1c` with `hvend` and `hboot` discharged by the kernel): for a work
    item whose service's code, looked up historically, is the deployed bootstrap binary `Blob.preimage`, core
    index c < 2^16, item index i < 2^16, service id < 2^32, and payload y = ℰ(`Instructions { is, salt }`) ⌢ rest
    with 1 ≤ |is| well-formed instructions, none `Import` (`hnoimport`) or `RandomStorageRefine` (`hrsr`),
    |y| + 48 ≤ 2^24, and every preimage the historical lookup can return shorter than 2^63 octets (`hpre`):
    `Spec.refine C` under the GP refine host functions returns some output and exports, and Ψ_R's result and
    exports are those; or Ψ_R runs out of gas (∞, no exports); or the run reaches a failed allocation
    (`ExhaustsHeap`, decision 4). C = `Spec.Consts.ofParams Params.full rk`.

    Hypotheses besides the payload's shape: `FmtHypsC C` (the four fmt summaries, at gas cap 2^62),
    `hnoimport`, `hrsr`, `hpre`. GP v0.8.0 eq. `refinvocation`. -/
theorem refine_t1c_deployed (rk : Nat → Nat → List Spec.Bytes)
    (hfmt : FmtHypsC (Spec.Consts.ofParams Params.full rk)) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat) (w : WorkItem)
    (hw : p.items[i]? = some w)
    (hl : (d.get? w.service).bind (·.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList) =
      some Blob.preimage)
    (hc : c < 65536) (hi : i < 65536) (hs : w.service < 4294967296)
    (is : List Spec.Instr) (salt rest : List UInt8) (hy : w.payload.toList = Spec.encodePayload is salt ++ rest)
    (hsalt : salt.length = 32) (hn : 1 ≤ is.length) (hY : w.payload.size + 48 ≤ 16777216)
    (hwf : ∀ x ∈ is, x.WF (Spec.Consts.ofParams Params.full rk))
    (hnoimport : ∀ x ∈ is, ∀ ds, x ≠ .importSegs ds)
    (hrsr : ∀ x ∈ is, ∀ sd n, x ≠ .randomStorageRefine sd n)
    (hpre : ∀ s h v, (d.get? s).bind (·.historicalLookup p.context.lookupAnchorSlot h) = some v →
      v.length < 9223372036854775808) :
    let o := psiR Params.full d c i p r imports extrinsics off
    ∃ out ex, RSem.run (Spec.refine (Spec.Consts.ofParams Params.full rk) i w.payload.toList)
        (RSem.Env.of d p imports i off) = some (out, ex) ∧
      ((o.result, o.exports) = (.ok ⟨out.toArray⟩, ex) ∨ (o.result = .err .outOfGas ∧ o.exports = []) ∨
        ExhaustsHeap Params.full d c i p r imports extrinsics off) :=
  refine_t1c rk vendoredFactsC hfmt d c i p r imports extrinsics off w Blob.preimage hw hl
    isBootstrapC_preimage hc hi hs is salt rest hy hsalt hn hY hwf hnoimport hrsr hpre

/-- **T2 for the deployed binary** (`accumulate_spec` with `hvend` and `hboot` discharged by the kernel): as
    `accumulate_spec`, for a service whose code, after the transfers are credited, is the code of the deployed
    bootstrap binary (`splitMetadata Blob.preimage = some code`: the code after its metadata, GP §A.7).

    Hypotheses besides the run's shape: `AccHyps B C` (the items loop's and the start-up's named hypotheses),
    `ValuesFit` (`hfit`) and `InfoFits` (`hinfo`). -/
theorem accumulate_spec_deployed (B : InstrRep) (C : Spec.Consts) (hmax : C.maxRecent = 2 * 341 * 16)
    (hyps : AccHyps B C)
    (η : List UInt8) (e : PartialState) (t s g : Nat) (inputs : List AccumulateInput)
    (code : ByteArray) (hcode : ASem.codeOf (ASem.credit e s inputs) s = some code)
    (hdep : splitMetadata Blob.preimage = some code) (ht : t < 4294967296) (hs : s < 4294967296)
    (hn : inputs.length ≤ 89) (hsz : ∀ i ∈ inputs, InputSized i)
    (hfit : ValuesFit (ASem.accEnv η t inputs code) (initImplications (ASem.credit e s inputs) s t η))
    (hinfo : InfoFits e s) :
    let o := psiA Params.full η e t s g inputs
    let x₀ := initImplications (ASem.credit e s inputs) s t η
    let env := ASem.accEnv η t inputs code
    let args : ByteArray := ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
    ∃ n, (o.state, o.xfers, o.yield, o.provisions) = ASem.outcome (ASem.run n (Spec.accumulate C t) env (x₀, x₀)) ∧
      ((ASem.run n (Spec.accumulate C t) env (x₀, x₀)).1 ≠ .stopped ∨
        (psiM code 5 (UInt64.ofNat g) args (accHostFn env) (x₀, x₀)).2.1 = .oog ∨
        ∃ (p : ByteArray) (ω : Regs) (μ : Memory) (f : Stream) (s' : St Stream),
          standardInit code args = some (p, ω, μ) ∧
          Reaches p (accContractS env) ⟨5, ω, μ, (x₀, x₀), f⟩ s' ∧ AccAbort s') :=
  accumulate_spec B C hmax accVendoredFacts hyps η e t s g inputs code hcode (isBootstrapCode_of_split hdep)
    ht hs hn hsz hfit hinfo

end Services.Bootstrap.Vendored
