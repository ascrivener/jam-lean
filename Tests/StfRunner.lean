import Tests.JamJson

/-!
# A shared runner for the STF vector tests

Runs a checker over every vector of a `tiny` and a `full` directory (davxy/jam-test-vectors
`v0.8.0`), with the matching chain parameters, and reports pass counts. Vectors in the known
deviations list are expected to fail; the run fails if any other vector fails or if a listed one
starts to pass.
-/

namespace JAM.Tests.Stf

open Lean (Json)

/-- Lower-case hex of an octet sequence. -/
def hexS (b : List UInt8) : String :=
  String.join (b.map fun x => let d := "0123456789abcdef".toList; String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

/-- Run `check` on every vector of `dirs` (each with its parameters and a label), returning the
    process exit code. `known` lists (label/file, reason) of expected deviations. -/
def runSuite (name : String) (dirs : List (String × Params × System.FilePath))
    (check : Params → Json → Except String (List String))
    (known : List (String × String) := []) : IO UInt32 := do
  let mut failed : Array String := #[]
  let mut total := 0
  let mut pass := 0
  for (label, params, dir) in dirs do
    let files ← PVM.Tests.jsonFiles dir
    let mut p := 0
    for f in files do
      let key := s!"{label}/{f.fileName.getD ""}"
      let r := check params (← PVM.Tests.readJson f)
      match r with
      | .ok [] => p := p + 1
      | .ok diffs =>
        failed := failed.push key
        IO.eprintln s!"FAIL {key}:"
        for d in diffs.take 4 do IO.eprintln s!"  {d.take 1500}"
      | .error e =>
        failed := failed.push key
        IO.eprintln s!"ERROR {key}: {e}"
    IO.println s!"{name} {label}: {p} of {files.size} vectors pass"
    total := total + files.size
    pass := pass + p
  if total = 0 then
    IO.eprintln s!"{name}: no vectors found"
    return 1
  let knownKeys := known.map (·.1)
  for (n, why) in known do
    IO.println s!"  expected deviation from GP 0.8.0: {n}: {why}"
  let unexpected := failed.toList.filter (!knownKeys.contains ·)
  let nowPassing := knownKeys.filter (!failed.contains ·)
  for n in unexpected do IO.eprintln s!"unexpected failure: {n}"
  for n in nowPassing do IO.eprintln s!"listed deviation now passes: {n}"
  return if unexpected.isEmpty && nowPassing.isEmpty then 0 else 1

/-- The default directories: `<base>/tiny` with `Params.tiny` and `<base>/full` with
    `Params.full`; a command-line argument replaces the base. -/
def defaultDirs (args : List String) (base : String) : List (String × Params × System.FilePath) :=
  let b : System.FilePath := args.headD base
  [("tiny", Params.tiny, b / "tiny"), ("full", Params.full, b / "full")]

end JAM.Tests.Stf
