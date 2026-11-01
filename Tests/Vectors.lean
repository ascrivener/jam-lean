import Lean.Data.Json
import PVM

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

/-- The opcode index of the instruction whose step ended a run of Ψ.

    The test vectors report this as `pc`, also on ∎ and ☇, where Ψ itself returns ı = 0. It is not
    part of Ψ's result, so the harness recomputes it by following the same steps as `PVM.runFuel`. -/
def exitIndexFuel (p : ByteArray) : Nat → Nat → UInt64 → Bool → Regs → Memory → Nat
  | 0, i, _, _, _, _ => i
  | fuel + 1, i, gas, ch, ω, μ =>
    match deblob p i with
    | none => i
    | some P =>
      let r := P.step i gas ch ω μ
      if r.status = .cont then exitIndexFuel p fuel r.pc r.gas r.charged r.regs r.mem else i

/-- `exitIndexFuel` with Ψ's own fuel bound. -/
def exitIndex (p : ByteArray) (i : Nat) (gas : UInt64) (ch : Bool) (ω : Regs) (μ : Memory) : Nat :=
  exitIndexFuel p (stepBound p i gas ch) i gas ch ω μ

end PVM.Tests
