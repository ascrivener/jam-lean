import Tests.JamJson

/-!
# Codec test (`lake build codectest`)

Builds each work-package-family term from the JSON of the Gray Paper v0.8.0 codec vectors
(davxy/jam-test-vectors `v0.8.0`, `codec/tiny`), encodes it with `JAM`'s ℰ, and compares the
octets with the vector's `.bin`.
-/

namespace JAM.Tests.Codec

open Lean (Json)
open PVM.Tests (field natField die readJson)
open JAM.Tests.Json

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
