import Tests.JamJson
import JAM.Erasure

/-!
# Erasure-coding test (`lake build erasuretest`)

The vectors in `erasure/tiny` (6 validators) and `erasure/full` (1023), davxy/jam-test-vectors
`v0.8.0`. Data whose length is not a multiple of 2·R(v) is first padded with zeroes, as §H says
("we pad with zeroes").

## Known deviation from GP 0.8.0: every vector

GP §H.3 interpolates the polynomial p of degree < d = R(v) through the d message words at
0̃ … (d−1)~ and gives validator i ≥ d the word p(ĩ). The vectors instead interpolate through the d
message words and zeroes at d̃ … (n−1)~, where n = 2^⌈log₂ d⌉ (degree < n), and give validator
i ≥ d the word at the point (n + i − d)~. (Both agree on the first d shards, the data itself.)
We follow the paper, so no vector's shards match the model. `knownDeviations` lists them; for each,
the test checks that the deviation is exactly that convention:

* the model's first R(v) shards equal the vector's;
* the model's other shards differ from the vector's;
* the vectors' convention (`vectorEncode`, test-side, from the model's own interpolation) gives
  every shard of the vector.

And for the paper's code it checks recovery: ℛ from the last R(v) of the model's shards, and from
the R(v) lowest odd-indexed ones, gives the padded data back. It also checks that
x¹⁶ + x⁵ + x³ + x² + 1 is primitive and that the Cantor basis is a basis, the two facts the
field arithmetic relies on. CI fails on anything else, or if a listed vector starts to match.
-/

open Lean (Json)
open JAM.Tests.Json
open JAM.Erasure

/-- Every erasure vector deviates from GP 0.8.0 (see the module docstring). -/
def knownDeviations : List String :=
  ["ec-3", "ec-32", "ec-100", "ec-4096", "ec-4104", "ec-10000"]

/-- The least power of two ≥ d. -/
def nextPow2 (d : Nat) : Nat := ((List.range 17).map (2 ^ ·)).find? (· ≥ d) |>.getD d

/-- The vectors' code (test-side): p of degree < n = `nextPow2 d` through the d message words and
    n − d zeroes, evaluated at 0 … d−1 and then at n, n + 1, …, n + v − d − 1. -/
def vectorEncode (v : Nat) (data : ByteArray) : List ByteArray :=
  let d := originalShards v
  let n := nextPow2 d
  let m := lagrange (List.range n) (List.range d ++ (List.range (v - d)).map (n + ·))
  let k := data.size / (2 * d)
  let pieces := (List.range k).map fun p =>
    interpolate m ((Array.range n).map fun j => if j < d then word data (2 * k * j + 2 * p) else 0)
  (List.range v).map fun i => ⟨(pieces.flatMap fun c => wordOctets c[i]!).toArray⟩

def runCase (v : Nat) (weights : Array (Array Nat)) (j : Json) : Except String Unit := do
  let data ← hexField j "data"
  let shards := (← (← arr j "shards").mapM hex).toList.map (·.toList)
  let d := originalShards v
  let padded := data ++ ⟨Array.replicate ((2 * d - data.size % (2 * d)) % (2 * d)) 0⟩
  let some got := encodeWith d weights padded | throw "encode rejected the data"
  let got' := got.map (·.toList)
  if got.length ≠ v ∨ shards.length ≠ v then throw s!"{got.length} shards, vector has {shards.length}"
  if got'.take d != shards.take d then throw "the first R(v) shards (the data) differ"
  if got'.drop d == shards.drop d then throw "listed as a deviation but now matches"
  if (vectorEncode v padded).map (·.toList) != shards then
    throw "the vector's shards are not the zero-padded convention either"
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
  if !(GF.primitive && GF.cantorIsBasis) then
    IO.eprintln "FAIL: the field polynomial is not primitive or the Cantor basis is not a basis"
    failed := true
  for (label, dir, v) in [("tiny", tiny, 6), ("full", full, 1023)] do
    let weights := encodeWeights v
    let mut dev := 0
    for name in knownDeviations do
      match runCase v weights (← PVM.Tests.readJson (System.FilePath.mk dir / s!"{name}.json")) with
      | .ok () => dev := dev + 1
      | .error e => IO.eprintln s!"FAIL {label}/{name}: {e}"; failed := true
    let others := (← System.FilePath.readDir dir).filter fun f =>
      f.fileName.endsWith ".json" && !knownDeviations.any (fun n => f.fileName == n ++ ".json")
    for f in others do
      IO.eprintln s!"FAIL {label}/{f.fileName}: not covered by this test"; failed := true
    IO.println s!"erasuretest {label} (v = {v}, R(v) = {originalShards v}): {dev} of {knownDeviations.length} vectors deviate from GP 0.8.0 exactly as listed (data shards equal, parity by the zero-padded convention); ℛ recovers the paper's code from two shard subsets in each"
  return if failed then 1 else 0
