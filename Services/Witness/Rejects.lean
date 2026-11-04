import Services.Witness.PsiREmpty
import Services.Witness.CodeCheck

/-!
# Witness's refine rejects malformed payloads: the deployed binary, by the kernel alone

`Services.Witness.PsiREmpty.psiR_rejects_exact` holds of any code preimage with witness's layout
and code facts. Here the preimage is the vendored binary itself, `Services.Witness.Blob.preimage`
(the octets of `services/witness/witness-service.jam`), and every fact about it is checked by the
kernel: its sections (`CodeCheck.split`, `CodeCheck.jam`), its code facts and 𝔳_blob
(`CodeCheck.checkCode_ok`), the costs of the blocks the path visits (the `.block` facts), the
section sizes and data octets the path reads (`layout_ok`) and its heap bounds (`heap_ok`).

So `refine_rejects` depends on no compiled evaluation: only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

namespace Services.Witness.Rejects

open PVM PVM.NatBlob JAM Services.Witness.Blob Services.Witness.CodeCheck Services.Witness.Prefix

/-- The deployed blob's section sizes and the data octets the path reads (GP eq. `conditions`). -/
theorem layout_ok : layoutOk jamBlob = true := by
  simp only [layoutOk, jamBlob, size_ba, toList_ba, getElem!_bytes]
  decide +kernel

/-- The deployed blob's heap bounds: pages 48 … 1044368. -/
theorem heap_ok : heapBounds (ba N 71 222902) = (48, 1044368) := by
  simp only [heapBounds, jam, jamBlob, size_ba]
  decide

/-- **Witness's refine rejects malformed payloads, exactly** (GP eq. `refinvocation`). For a work
    item whose service's code, looked up historically, is the deployed witness binary, refined with
    the full-chain parameters and a refine gas limit of at least `gasBound` (about 4.1 × 10⁷, under
    1% of the full chain's 5 × 10⁹): for every core index c < 2^16, item index i < 2^16 and
    service id < 2^32, and a payload that is empty or of 1 to 15 octets with first octet at least
    12, Ψ_R's result is ℰ(`Rejected(BadPayload)`) = [12, 0]. -/
theorem refine_rejects (params : Params) (hpar : params = Params.full) (d : Accounts) (c i : Nat)
    (p : WorkPackage) (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (w : WorkItem) (hw : p.items[i]? = some w)
    (hl : (d.get? w.service).bind (fun a => a.historicalLookup p.context.lookupAnchorSlot
      w.codeHash.toList) = some preimage)
    (hgas : PsiR.gasBound ≤ w.refineGasLimit) (hg64 : w.refineGasLimit < 2 ^ 64)
    (hc : c < 65536) (hi : i < 65536) (hs : w.service < 4294967296)
    (hy : w.payload.size = 0 ∨
      (w.payload.size ≤ 15 ∧ 12 ≤ (w.payload.toList.headD 0).toNat)) :
    (psiR params d c i p r imports extrinsics off).result = .ok ⟨#[12, 0]⟩ :=
  PsiREmpty.psiR_rejects_exact params hpar d c i p r imports extrinsics off w hw preimage hl
    (by rw [preimage, length_bytes]; decide) _ split jamBlob jam layout_ok checkCode_ok heap_ok
    hgas hg64 hc hi hs hy

end Services.Witness.Rejects
