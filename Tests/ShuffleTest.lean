import Tests.JamJson
import JAM.Shuffle

/-!
# Shuffle test (`lake build shuffletest`)

For each case of `shuffle/shuffle_tests.json` (davxy/jam-test-vectors `v0.8.0`): ℱ (GP Appendix F)
of [0, 1, …, n − 1] with the case's 32-octet entropy against the expected sequence.
-/

open Lean (Json)
open JAM.Tests.Json

def runCase (j : Json) : Except String Bool := do
  let n ← PVM.Tests.natField j "input"
  let h ← hexField j "entropy"
  if h.size ≠ 32 then throw "entropy is not 32 octets"
  let expected ← (← arr j "output").mapM (·.getNat?)
  return JAM.Shuffle.shuffleHash (List.range n) h == expected.toList

def main (args : List String) : IO UInt32 := do
  let path := args.headD "vendor/jam-test-vectors/shuffle/shuffle_tests.json"
  let j ← PVM.Tests.readJson path
  let some cases := (j.getArr?).toOption | IO.eprintln "not an array"; return 1
  let mut pass := 0
  for (c, i) in cases.toList.zipIdx do
    match runCase c with
    | .ok true => pass := pass + 1
    | .ok false => IO.eprintln s!"FAIL case {i}: sequence differs"
    | .error e => IO.eprintln s!"FAIL case {i}: {e}"
  IO.println s!"shuffletest: {pass} of {cases.size} shuffles match"
  return if pass == cases.size then 0 else 1
