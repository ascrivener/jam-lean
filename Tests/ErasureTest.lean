import Tests.JamJson
import JAM.Erasure

/-!
# Erasure-coding test (`lake build erasuretest`)

The vectors in `erasure/tiny` (6 validators) and `erasure/full` (1023), davxy/jam-test-vectors
`v0.8.0`. Data whose length is not a multiple of 2·R(v) is first padded with zeroes, as §H says
("we pad with zeroes").

Every vector must match the model's ℰ_C shard for shard. GP v0.8.1 #580 fixed §H.3 to the layout
the vectors use: p has degree < d' = 2^⌈log₂ d⌉, with zeroes at d̃ … (d'−1)~, and parity goes to
the indices d', d' + 1, …. Under v0.8.0's §H.3 every vector was a listed deviation (upstream
candidate 28, now resolved).

For each vector the test also checks recovery: ℛ from the last R(v) shards, and from the R(v)
lowest odd-indexed ones, gives the padded data back. It also checks that x¹⁶ + x⁵ + x³ + x² + 1 is
primitive and that the Cantor basis is a basis, the two facts the field arithmetic relies on.
-/

open Lean (Json)
open JAM.Tests.Json
open JAM.Erasure

def runCase (v : Nat) (weights : Array (Array Nat)) (j : Json) : Except String Unit := do
  let data ← hexField j "data"
  let shards := (← (← arr j "shards").mapM hex).toList.map (·.toList)
  let d := originalShards v
  let padded := data ++ ⟨Array.replicate ((2 * d - data.size % (2 * d)) % (2 * d)) 0⟩
  let some got := encodeWith d weights padded | throw "encode rejected the data"
  let got' := got.map (·.toList)
  if got.length ≠ v ∨ shards.length ≠ v then throw s!"{got.length} shards, vector has {shards.length}"
  if got'.take d != shards.take d then throw "the first R(v) shards (the data) differ"
  if got' != shards then throw "the parity shards differ"
  let indexed := got.zipIdx
  let subsets := [indexed.drop (v - d), (indexed.filter (·.2 % 2 == 1)).take d]
  for (sub, n) in subsets.zipIdx do
    match recover v sub with
    | none => throw s!"recover rejected subset {n}"
    | some r => if r.toList != padded.toList then throw s!"recover from subset {n} differs"

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := "vendor/jam-test-vectors/erasure"
  let tiny := args.getD 0 (root / "tiny").toString
  let full := args.getD 1 (root / "full").toString
  let mut failed := false
  if !(GF.primitive GF.expTable GF.logTable && GF.cantorIsBasis) then
    IO.eprintln "FAIL: the field polynomial is not primitive or the Cantor basis is not a basis"
    failed := true
  for (label, dir, v) in [("tiny", tiny, 6), ("full", full, 1023)] do
    let weights := encodeWeights v
    let mut ok := 0
    let files := (← System.FilePath.readDir dir).filter (·.fileName.endsWith ".json")
    if files.isEmpty then IO.eprintln s!"FAIL {label}: no vectors"; failed := true
    for f in files do
      match runCase v weights (← PVM.Tests.readJson f.path) with
      | .ok () => ok := ok + 1
      | .error e => IO.eprintln s!"FAIL {label}/{f.fileName}: {e}"; failed := true
    IO.println s!"erasuretest {label} (v = {v}, R(v) = {originalShards v}): {ok} of {files.size} vectors match ℰ_C exactly; ℛ recovers the data from two shard subsets in each"
  return if failed then 1 else 0
