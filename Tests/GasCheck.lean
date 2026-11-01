import Tests.Vectors

/-!
# Block gas checker (`lake build gascheck`)

For every program in `programs/` and `gas-tests/`, compares the model's ϱ^Δ(**c**, **k**, ı)
(GP eq. `gascostforblock`) against each block cost the vectors give, and also checks that the
blocks listed are exactly the model's ϖ (GP §A.3).
-/

namespace PVM.Tests

/-- Per-directory tallies. -/
structure Tally where
  programs : Nat := 0
  blocks : Nat := 0
  correct : Nat := 0
  blockSetMismatches : Nat := 0
  failures : Array String := #[]

/-- Check one program's block costs. -/
def checkProgram (name : String) (j : Lean.Json) (t : Tally) : Except String Tally := do
  let p ← programOf j
  let costs ← blockCostsOf j
  let some P := Blob.parse? p | die "program does not parse"
  unless P.vBlob do die "program fails 𝔳_blob"
  let mut t := { t with programs := t.programs + 1 }
  for (pc, expected) in costs do
    t := { t with blocks := t.blocks + 1 }
    match P.blockCost? pc with
    | some c =>
      if c == expected then t := { t with correct := t.correct + 1 }
      else t := { t with failures := t.failures.push s!"{name} @{pc}: model {c}, expected {expected}" }
    | none => t := { t with failures := t.failures.push s!"{name} @{pc}: simulation did not finish" }
  -- ϖ must be exactly the listed pcs.
  let listed : Std.HashSet Nat := costs.foldl (fun s (pc, _) => s.insert pc) {}
  let starts := (List.range P.code.size).filter P.isBlockStart
  let ours : Std.HashSet Nat := starts.foldl (·.insert ·) {}
  if starts.length != listed.size || starts.any (!listed.contains ·) then
    t := { t with blockSetMismatches := t.blockSetMismatches + 1,
                  failures := t.failures.push s!"{name}: ϖ differs from the listed blocks ({ours.size} vs {listed.size})" }
  return t

/-- Check every program in a directory. -/
def checkDir (dir : System.FilePath) : IO Tally := do
  let mut t : Tally := {}
  for f in ← jsonFiles dir do
    let name := f.fileName.getD ""
    match checkProgram name (← readJson f) t with
    | .ok t' => t := t'
    | .error e => t := { t with failures := t.failures.push s!"{name}: {e}" }
  return t

end PVM.Tests

open PVM.Tests in
def main (args : List String) : IO UInt32 := do
  let dirs := if args.isEmpty then
      ["vendor/jamtestvectors/pvm/programs", "vendor/jamtestvectors/pvm/gas-tests"] else args
  let mut ok := true
  for d in dirs do
    let t ← checkDir d
    for f in t.failures.toList.take 50 do IO.eprintln s!"FAIL {f}"
    IO.println s!"gascheck {d}: {t.correct} of {t.blocks} blocks correct in {t.programs} programs; \
      ϖ matches the listed blocks in {t.programs - t.blockSetMismatches} of {t.programs}"
    if !t.failures.isEmpty || t.blocks == 0 then ok := false
  return if ok then 0 else 1
