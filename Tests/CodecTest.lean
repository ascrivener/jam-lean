import Tests.Vectors
import JAM.Work

/-!
# Codec test (`lake build codectest`)

Builds each work-package-family term from the JSON of the Gray Paper v0.8.0 codec vectors
(davxy/jam-test-vectors `v0.8.0`, `codec/tiny`), encodes it with `JAM`'s ℰ, and compares the
octets with the vector's `.bin`.
-/

namespace JAM.Tests.Codec

open Lean (Json)
open PVM.Tests (field natField die readJson)

/-- A `0x…` hex string as octets. -/
def hex (j : Json) : Except String ByteArray := do
  let s ← j.getStr?
  let cs := s.toList
  let cs := if cs.take 2 == ['0', 'x'] then cs.drop 2 else cs
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else die s!"bad hex digit {c}"
  if cs.length % 2 ≠ 0 then die "odd-length hex"
  let mut out : ByteArray := .empty
  for k in [0:cs.length / 2] do
    out := out.push (UInt8.ofNat (16 * (← digit cs[2 * k]!) + (← digit cs[2 * k + 1]!)))
  return out

def hexField (j : Json) (k : String) : Except String ByteArray := do hex (← field j k)
def arr (j : Json) (k : String) : Except String (Array Json) := do (← field j k).getArr?

def context (j : Json) : Except String RefineContext := do
  return { anchorHash := ← hexField j "anchor", anchorSlot := ← natField j "anchor_slot",
           anchorStateRoot := ← hexField j "state_root", anchorAccOutLog := ← hexField j "beefy_root",
           lookupAnchorHash := ← hexField j "lookup_anchor",
           lookupAnchorSlot := ← natField j "lookup_anchor_slot",
           lookupAnchorStateRoot := ← hexField j "lookup_anchor_state_root",
           prerequisites := (← (← arr j "prerequisites").mapM hex).toList }

def workItem (j : Json) : Except String WorkItem := do
  let imports ← (← arr j "import_segments").mapM fun s => do
    -- The vectors give segment roots; a work-package reference would be tagged.
    return (SegmentRoot.root (← hexField s "tree_root"), ← natField s "index")
  let xts ← (← arr j "extrinsic").mapM fun x => do return (← hexField x "hash", ← natField x "len")
  return { service := ← natField j "service", codeHash := ← hexField j "code_hash",
           payload := ← hexField j "payload", refineGasLimit := ← natField j "refine_gas_limit",
           accumulateGasLimit := ← natField j "accumulate_gas_limit",
           exportCount := ← natField j "export_count", importSegments := imports.toList,
           extrinsics := xts.toList }

def workPackage (j : Json) : Except String WorkPackage := do
  return { authToken := ← hexField j "authorization", authCodeHost := ← natField j "auth_code_host",
           authCodeHash := ← hexField j "auth_code_hash",
           authConfig := ← hexField j "authorizer_config", context := ← context (← field j "context"),
           items := (← (← arr j "items").mapM workItem).toList }

def workResult (j : Json) : Except String WorkResult := do
  let .obj kvs := j | die "bad result"
  let some (k, v) := kvs.toArray[0]? | die "empty result"
  match k with
  | "ok" => return .ok (← hex v)
  | "out_of_gas" => return .err .outOfGas
  | "panic" => return .err .panic
  | "bad_exports" => return .err .badExports
  | "output_oversize" | "oversize" => return .err .oversize
  | "bad_code" => return .err .bad
  | "code_oversize" => return .err .big
  | other => die s!"unknown work result {other}"

def workDigest (j : Json) : Except String WorkDigest := do
  let l ← field j "refine_load"
  return { service := ← natField j "service_id", codeHash := ← hexField j "code_hash",
           payloadHash := ← hexField j "payload_hash", gasLimit := ← natField j "accumulate_gas",
           result := ← workResult (← field j "result"), gasUsed := ← natField l "gas_used",
           importCount := ← natField l "imports", extrinsicCount := ← natField l "extrinsic_count",
           extrinsicSize := ← natField l "extrinsic_size", exportCount := ← natField l "exports" }

def availSpec (j : Json) : Except String AvailabilitySpec := do
  return { packageHash := ← hexField j "hash", bundleLength := ← natField j "length",
           erasureRoot := ← hexField j "erasure_root", erasureShards := ← natField j "erasure_shards",
           segmentRoot := ← hexField j "exports_root", segmentCount := ← natField j "exports_count" }

def workReport (j : Json) : Except String WorkReport := do
  let lookup ← (← arr j "segment_root_lookup").mapM fun e => do
    return (← hexField e "work_package_hash", ← hexField e "segment_tree_root")
  return { spec := ← availSpec (← field j "package_spec"), context := ← context (← field j "context"),
           core := ← natField j "core_index", authorizerHash := ← hexField j "authorizer_hash",
           authTrace := ← hexField j "auth_output", segmentRootLookup := lookup.toList,
           digests := (← (← arr j "results").mapM workDigest).toList,
           authGasUsed := ← natField j "auth_gas_used" }

/-- The vectors this test covers: name and encoder from JSON. -/
def cases : List (String × (Json → Except String (List UInt8))) :=
  [("refine_context", fun j => (·.encode) <$> context j),
   ("work_item", fun j => (·.encode) <$> workItem j),
   ("work_package", fun j => (·.encode) <$> workPackage j),
   ("work_result_0", fun j => (·.encode) <$> workDigest j),
   ("work_result_1", fun j => (·.encode) <$> workDigest j),
   ("work_report", fun j => (·.encode) <$> workReport j)]

end JAM.Tests.Codec

open JAM.Tests.Codec in
def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "vendor/jam-test-vectors/codec/tiny"
  let mut pass := 0
  for (name, enc) in cases do
    let j ← PVM.Tests.readJson (dir / s!"{name}.json")
    let expected ← IO.FS.readBinFile (dir / s!"{name}.bin")
    match enc j with
    | .error e => IO.eprintln s!"FAIL {name}: {e}"
    | .ok got =>
      if got == expected.toList then pass := pass + 1
      else
        let i := ((List.range (min got.length expected.size)).find? fun k => got[k]! != expected[k]!).getD (min got.length expected.size)
        IO.eprintln s!"FAIL {name}: {got.length} vs {expected.size} octets, first difference at {i}"
  IO.println s!"codectest: {pass} of {cases.length} codec vectors match"
  return if pass == cases.length then 0 else 1
