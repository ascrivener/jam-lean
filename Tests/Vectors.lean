import Lean.Data.Json
import PVM.Machine

/-!
# Reading the test vectors (koute/jamtestvectors `pvm/`, schema in `pvm/schema.asn`)

Uses `Lean.Data.Json` from the Lean core distribution; the model itself (`PVM`) imports only
`Init` and `Std`.
-/

namespace PVM.Tests

open Lean (Json)

/-- Fail with a message. -/
def die {α} (msg : String) : Except String α := .error msg

/-- An object field. -/
def field (j : Json) (k : String) : Except String Json := j.getObjVal? k

/-- A natural-number field. -/
def natField (j : Json) (k : String) : Except String Nat := do (← field j k).getNat?

/-- An integer field. -/
def intField (j : Json) (k : String) : Except String Int := do (← field j k).getInt?

/-- An array of naturals. -/
def natArray (j : Json) : Except String (Array Nat) := do
  (← j.getArr?).mapM (·.getNat?)

/-- An array of octets. -/
def bytesOf (j : Json) : Except String ByteArray := do
  let ns ← natArray j
  if ns.any (· ≥ 256) then die "octet out of range"
  return ⟨ns.map UInt8.ofNat⟩

/-- The `program` field as a blob. -/
def programOf (j : Json) : Except String ByteArray := do bytesOf (← field j "program")

/-- The `block-gas-costs` field: a list of `{pc, cost}` objects in `programs/`, an object
    mapping pc to cost in `gas-tests/`. -/
def blockCostsOf (j : Json) : Except String (Array (Nat × Nat)) := do
  match ← field j "block-gas-costs" with
  | .arr xs => xs.mapM fun x => return (← natField x "pc", ← natField x "cost")
  | .obj kvs =>
    kvs.toArray.mapM fun ⟨k, v⟩ => do
      let some pc := k.toNat? | die s!"bad pc key {k}"
      return (pc, ← v.getNat?)
  | _ => die "bad block-gas-costs"

/-- Read and parse a JSON file. -/
def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw <| IO.userError s!"{path}: {e}"

/-- The `.json` files of a directory, sorted by name. -/
def jsonFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  unless ← dir.isDir do
    throw <| IO.userError s!"{dir} is not a directory; run scripts/fetch-vectors.sh first"
  let entries ← dir.readDir
  let files := entries.filter (·.fileName.endsWith ".json") |>.map (·.path)
  return files.qsort (·.toString < ·.toString)

end PVM.Tests
