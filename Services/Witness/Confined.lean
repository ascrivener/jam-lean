import Services.Witness
import Services.Witness.CodeOk

/-!
# The deployed witness binary is confined, by the kernel alone

`Services.Witness.accumulate_confined` and `refine_noExports` hold of any code that names only the
host calls `Services.Witness.ids`. Here the code is the vendored binary itself
(`Services.Witness.Blob.preimage`), and that it names only those ids is checked by the kernel
(`CodeCheck.hostIds_ok`, a scan of every opcode position of the code). The theorems depend only
on the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Services.Witness.Confined

open PVM PVM.NatBlob JAM Services.Witness.Blob Services.Witness.CodeCheck

/-- A service account's code is its code preimage less the metadata. -/
theorem code_eq (a : ServiceAccount) : a.code = (a.preimages.get? a.codeHash).bind splitMetadata := by
  unfold ServiceAccount.code splitMetadata
  cases a.preimages.get? a.codeHash <;> rfl

theorem hostIds_sub : ∀ n ∈ hostIds, n ∈ ids := by decide

/-- The deployed binary names only `ids`. -/
theorem deployed_ids : ∀ h ∈ jamHostCallIdsOf (ba N 71 222902), h ∈ ids :=
  fun h hh => hostIds_sub h (hostIds_ok h hh)

/-- **The deployed witness binary's accumulate is confined to its own account.** For a service
    whose code preimage is `services/witness/witness-service.jam`, Ψ_A from any state, with any
    inputs and gas, leaves everything outside the service's own account as it was, and provides
    nothing. -/
theorem accumulate_confined (params : Params) (entropy : List UInt8) (e : PartialState)
    (t s g : Nat) (inputs : List AccumulateInput) (a : ServiceAccount)
    (ha : e.accounts.get? s = some a) (hp : a.preimages.get? a.codeHash = some preimage) :
    Outside e s (psiA params entropy e t s g inputs).state ∧
      (psiA params entropy e t s g inputs).provisions = ∅ :=
  Services.Witness.accumulate_confined params entropy e t s g inputs a (ba N 71 222902) ha
    (by rw [code_eq, hp, Option.bind_some]; exact split) deployed_ids

/-- **The deployed witness binary's refine exports nothing.** If the code a work item's service
    resolves to is `services/witness/witness-service.jam`, Ψ_R returns no exported segments. -/
theorem refine_noExports (params : Params) (d : Accounts) (c i : Nat) (p : WorkPackage)
    (r : List UInt8) (imports extrinsics : List (List (List UInt8))) (off : Nat)
    (hl : ∀ w ∈ p.items[i]?, ∀ a ∈ d.get? w.service,
      ∀ l ∈ a.historicalLookup p.context.lookupAnchorSlot w.codeHash.toList, l = preimage) :
    (psiR params d c i p r imports extrinsics off).exports = [] :=
  Services.Witness.refine_noExports params d c i p r imports extrinsics off
    (fun w hw a ha l hl' code hc h hh => by
      have hlp := hl w hw a ha l hl'
      subst hlp
      rw [split] at hc
      cases hc
      exact deployed_ids h hh)

end Services.Witness.Confined
