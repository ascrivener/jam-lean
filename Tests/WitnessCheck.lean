import Services.Witness

/-!
# `lake build witnesscheck`: the vendored witness blob names only `Services.Witness.ids`

Installs `services/witness/witness-service.jam` as the code preimage of a service account (keyed by
its Blake2b-256 hash, as on chain), takes the account's code by the paper's rule
(`ServiceAccount.code`: the preimage less its metadata), and computes its host-call ids with
`jamHostCallIdsOf`, the same function the confinement theorems quantify over. Fails unless every
id is in `Services.Witness.ids`.

This is the one step not checked by the kernel: it runs compiled code over the 223 kB blob.
-/

open JAM PVM

def main (args : List String) : IO UInt32 := do
  let path := args.headD "services/witness/witness-service.jam"
  let bytes ← IO.FS.readBinFile path
  let h := (Blake2b.hash256 bytes).toList
  let acct : ServiceAccount :=
    { codeHash := h, balance := 0, minAccGas := 0, minMemoGas := 0,
      preimages := Std.ExtTreeMap.ofList [(h, bytes.toList)] }
  let hex (b : List UInt8) : String :=
    String.join (b.map fun x => let d := "0123456789abcdef".toList; String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])
  IO.println s!"{path}: {bytes.size} octets, code hash {hex h}"
  match acct.code with
  | none =>
    IO.eprintln "not a code preimage ℰ(↕m, c)"
    return 1
  | some code =>
    let ids := (jamHostCallIdsOf code).eraseDups.mergeSort
    IO.println s!"host-call ids: {ids}"
    let extra := ids.filter (· ∉ Services.Witness.ids)
    if !extra.isEmpty then
      IO.eprintln s!"ids not in Services.Witness.ids: {extra}"
      return 1
    IO.println "witnesscheck: every id is in Services.Witness.ids, so `accumulate_confined` and `refine_noExports` apply"
    return 0
