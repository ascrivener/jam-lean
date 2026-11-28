import Tests.PvmHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.PvmHarness`. -/

open PVM.Tests in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "vendor/jamtestvectors/pvm/programs"
  let files ← jsonFiles dir
  let mut failed : Array String := #[]
  for f in files do
    let j ← readJson f
    match runVector j with
    | .ok () => pure ()
    | .error e =>
      IO.eprintln s!"FAIL {f.fileName.getD ""}: {e}"
      failed := failed.push (f.fileName.getD "")
  IO.println s!"pvmtest: {files.size - failed.size} of {files.size} vectors pass"
  return if failed.isEmpty && files.size > 0 then 0 else 1
