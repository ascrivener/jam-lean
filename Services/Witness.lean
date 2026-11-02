import JAM.Theorems.Confinement

/-!
# The witness service: what its deployed code can reach

`services/witness/witness-service.jam` is the witness bounty-market service
(github.com/ascrivener/witness at 71e585a634545b1cb90cf4737198a74865ee2100), built with
`cargo jam-build` 0.1.29 and rustc 1.97.0. Its PVM code names exactly the host-call ids in `ids`;
`lake build witnesscheck` reads the blob and checks that with the model's own `jamHostCallIdsOf`.

From the ids alone, with the confinement theorems of `JAM.Theorems.Confinement`:

* `accumulate_confined`: accumulating witness changes only witness's own account. Every other
  account, the staging set, the authorizer queue and the privileged services are left as they
  were, and it provides no preimages. Whatever bug witness's code has, its accumulate cannot
  reach another service except through the deferred transfers it sends.
* `refine_noExports`: witness's refine never exports a segment.

These hold for every input, every state and every amount of gas, and do not depend on what the
code computes, only on which host calls it can make.
-/

namespace Services.Witness

open JAM PVM

/-- The host-call ids named by witness's PVM code: the general functions 0–6, the refine functions
    `machine`, `poke`, `pages`, `invoke`, `expunge` (9, 11–14), the accumulate functions
    `checkpoint`, `upgrade`, `transfer`, `solicit` (18, 20, 21, 24), and 100 (`log`, JIP-1, not in
    the paper: an unknown id, answered WHAT). -/
def ids : List Nat := [0, 1, 2, 3, 4, 5, 6, 9, 11, 12, 13, 14, 18, 20, 21, 24, 100]

theorem ids_not_reaching : ∀ h ∈ ids, h ∉ reachingIds := by decide

theorem export_not_in_ids : 8 ∉ ids := by decide

/-- **Witness's accumulate is confined to its own account.** For any code that names only `ids`
    (witness's does), Ψ_A for the service running it, from any state, with any inputs and gas,
    leaves everything outside the service's own account as it was, and provides nothing. -/
theorem accumulate_confined (params : Params) (entropy : List UInt8) (e : PartialState)
    (t s g : Nat) (inputs : List AccumulateInput) (a : ServiceAccount) (code : ByteArray)
    (ha : e.accounts.get? s = some a) (hcode : a.code = some code)
    (hids : ∀ h ∈ jamHostCallIdsOf code, h ∈ ids) :
    Outside e s (psiA params entropy e t s g inputs).state ∧
      (psiA params entropy e t s g inputs).provisions = ∅ :=
  psiA_confined params entropy e t s g inputs a code ha hcode
    (fun h hh => ids_not_reaching h (hids h hh))

/-- **Witness's refine exports nothing.** If the code a work item's service resolves to names only
    `ids`, Ψ_R returns no exported segments. -/
theorem refine_noExports (params : Params) (d : Accounts) (c i : Nat) (p : WorkPackage)
    (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (hids : ∀ w ∈ p.items[i]?, ∀ a ∈ d.get? w.service,
      ∀ l ∈ a.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList,
      ∀ code ∈ splitMetadata l, ∀ h ∈ jamHostCallIdsOf code, h ∈ ids) :
    (psiR params d c i p r imports extrinsics off).exports = [] :=
  psiR_noExports params d c i p r imports extrinsics off
    (fun w hw a ha l hl code hc h8 => export_not_in_ids (hids w hw a ha l hl code hc 8 h8))

end Services.Witness
