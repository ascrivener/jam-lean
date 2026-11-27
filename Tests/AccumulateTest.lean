import Tests.AccumulateHarness

/-! The runner's entry point; the harness (parsers, checks, and the documentation of what is
    compared) is `Tests.AccumulateHarness`. -/

open JAM.Tests.Accumulate in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "vendor/jam-test-vectors/stf/accumulate/tiny"
  let files ← PVM.Tests.jsonFiles dir
  let mut pass := 0
  let mut failed : Array String := #[]
  for f in files do
    let name := f.fileName.getD ""
    let t0 ← IO.monoMsNow
    let r := runVector JAM.V080.tiny080 (← PVM.Tests.readJson f)
    let ok := match r with | .ok [] => "ok" | _ => "FAIL"
    IO.println s!"{name}: {ok} ({(← IO.monoMsNow) - t0} ms)"
    (← IO.getStdout).flush
    match r with
    | .ok [] => pass := pass + 1
    | .ok diffs =>
      failed := failed.push name
      IO.eprintln s!"FAIL {name}:"
      for d in diffs.take 4 do IO.eprintln s!"  {d.take 1500}"
    | .error e =>
      failed := failed.push name
      IO.eprintln s!"ERROR {name}: {e}"
  IO.println s!"acctest: {pass} of {files.size} accumulate vectors pass"
  let known := knownDeviations.map (·.1)
  for (n, why) in knownDeviations do
    IO.println s!"  expected deviation from GP 0.8.0: {n}: {why}"
  let unexpected := failed.toList.filter (!known.contains ·)
  let nowPassing := known.filter (!failed.contains ·)
  for n in unexpected do IO.eprintln s!"unexpected failure: {n}"
  for n in nowPassing do IO.eprintln s!"listed deviation now passes: {n}"
  return if unexpected.isEmpty && nowPassing.isEmpty then 0 else 1
