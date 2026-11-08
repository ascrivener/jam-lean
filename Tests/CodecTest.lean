import Tests.BlockJson

/-!
# Codec test (`lake build codectest`)

For every vector of the Gray Paper v0.8.0 codec suite (davxy/jam-test-vectors `v0.8.0`, `codec/tiny`
and `codec/full`), two checks against the vector's `.bin`:

* **encode**: build the term from the vector's JSON and encode it with `JAM`'s ℰ;
* **round trip**: decode the `.bin` with `JAM`'s ℰ⁻¹ (which must use every octet) and encode the
  result again.

A vector passes if both give exactly the `.bin`, and ℰ⁻¹ rejects the `.bin` with its last octet
dropped and with an extra octet appended. CI fails if any vector does not.
-/

namespace JAM.Tests.Codec

open Lean (Json)
open PVM.Tests (readJson)
open JAM.Tests.Json
open JAM.Codec

/-- One vector kind: its encoding from JSON, and decode-then-encode. -/
structure Case where
  name : String
  fromJson : Json → Except String (List UInt8)
  roundTrip : ByteArray → Except String (List UInt8)

def mk {α : Type} (name : String) (j : Json → Except String α) (d : Decoder α) (e : α → List UInt8) :
    Case :=
  { name, fromJson := fun js => do return e (← j js),
    roundTrip := fun bs => do return e (← Decoder.run d bs) }

def cases (p : Params) : List Case :=
  [mk "refine_context" context RefineContext.decode (·.encode),
   mk "work_item" workItem WorkItem.decode (·.encode),
   mk "work_package" workPackage WorkPackage.decode (·.encode),
   mk "work_result_0" workDigest WorkDigest.decode (·.encode),
   mk "work_result_1" workDigest WorkDigest.decode (·.encode),
   mk "work_report" workReport WorkReport.decode (·.encode),
   mk "header_0" header (Header.decode p) (·.encode),
   mk "header_1" header (Header.decode p) (·.encode),
   mk "tickets_extrinsic" (items · ticketProof) decodeTickets encodeTickets,
   mk "preimages_extrinsic" (items · preimage) decodePreimages encodePreimages,
   mk "guarantees_extrinsic" (items · guarantee) decodeGuarantees encodeGuarantees,
   mk "assurances_extrinsic" (items · (assurance p.coreCount)) (decodeAssurances p) encodeAssurances,
   mk "disputes_extrinsic" disputes Disputes.decode (·.encode),
   mk "extrinsic" (extrinsic p.coreCount) (Extrinsic.decode p) (·.encode),
   mk "block" (block p.coreCount) (Block.decode p) (·.encode)]

/-- Where two octet sequences first differ. -/
def firstDiff (a b : List UInt8) : Nat :=
  ((List.range (min a.length b.length)).find? fun k => a[k]! != b[k]!).getD (min a.length b.length)

/-- Run every case in `dir` with chain parameters `p`; returns (passes, failures). -/
def runDir (label : String) (dir : System.FilePath) (p : Params) : IO (Nat × Nat) := do
  let mut pass := 0
  let mut fail := 0
  for c in cases p do
    let bin ← IO.FS.readBinFile (dir / s!"{c.name}.bin")
    let j ← readJson (dir / s!"{c.name}.json")
    let expected := bin.toList
    let verdict : Except String Unit := do
      let got ← c.fromJson j
      if got != expected then
        throw s!"encode: {got.length} vs {expected.length} octets, first difference at {firstDiff got expected}"
      let again ← c.roundTrip bin
      if again != expected then throw s!"round trip: first difference at {firstDiff again expected}"
      if (c.roundTrip (bin.extract 0 (bin.size - 1))).toBool || (c.roundTrip (bin.push 0)).toBool then
        throw "ℰ⁻¹ accepts the .bin truncated by, or extended with, one octet"
    match verdict with
    | .ok () => pass := pass + 1
    | .error e => IO.eprintln s!"FAIL {label}/{c.name}: {e}"; fail := fail + 1
  return (pass, fail)

end JAM.Tests.Codec

open JAM.Tests.Codec in
/-- Arguments: the `codec/tiny` and `codec/full` directories. -/
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := "vendor/jam-test-vectors/codec"
  let tiny := args.getD 0 (root / "tiny").toString
  let full := args.getD 1 (root / "full").toString
  let mut failed := false
  for (label, dir, p) in [("tiny", tiny, JAM.Params.tiny), ("full", full, JAM.Params.full)] do
    let (pass, fail) ← runDir label dir p
    IO.println s!"codectest {label}: {pass} of {(cases p).length} vectors encode from JSON and round-trip through ℰ⁻¹ exactly"
    if fail ≠ 0 then failed := true
  return if failed then 1 else 0
