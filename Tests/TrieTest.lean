import Tests.JamJson
import JAM.Trie

/-!
# State-trie test (`lake build trietest`)

For each case of `trie/trie.json` (davxy/jam-test-vectors `v0.8.0`), M (GP Appendix D) of the
input dictionary against the expected root.

The vectors' keys are 32 octets; the paper's state keys are 31 (𝔹_31, GP §D.1) and L stores
exactly 31. The test passes the first 31 octets of each key to M, after checking that no two keys
of a case share them, so the last octet cannot matter.
-/

open Lean (Json)
open JAM.Tests.Json

def hexStr (s : String) : Except String ByteArray := hex (Json.str s)

def runCase (j : Json) : Except String (Bool × Nat) := do
  let .obj kvs := ← PVM.Tests.field j "input" | throw "input is not an object"
  let entries ← kvs.toArray.toList.mapM fun (k, v) => do
    let key ← hexStr k
    if key.size ≠ 32 then throw s!"key of {key.size} octets"
    return ((key.toList.take 31), (← hex v).toList)
  let keys := entries.map (·.1)
  if keys.eraseDups.length ≠ keys.length then throw "two keys share their first 31 octets"
  let expected ← hexStr (← (← PVM.Tests.field j "output").getStr?)
  let got := JAM.Trie.root (Std.ExtTreeMap.ofList entries)
  return (got == expected.toList, entries.length)

/-- Hand-written checks of the state-key constructor C (GP §D.1); no vector covers it. -/
def keyChecks : List (String × Bool) :=
  let h := (JAM.Blake2b.hash256 ⟨#[1, 2, 3]⟩).toList
  [("C(i) = [i, 0, …], 31 octets", JAM.Trie.keyOfIndex 13 == 13 :: List.replicate 30 0),
   ("C(255, s) interleaves ℰ_4(s)", JAM.Trie.keyOfService 255 0x04030201 ==
      ([255, 1, 0, 2, 0, 3, 0, 4] : List UInt8) ++ List.replicate 23 0),
   ("C(s, h) interleaves ℰ_4(s) with ℋ(h), then ℋ(h)₄…₂₆", JAM.Trie.keyOfServiceData 0x04030201 [1, 2, 3] ==
      ([1, h[0]!, 2, h[1]!, 3, h[2]!, 4, h[3]!] : List UInt8) ++ (h.drop 4).take 23),
   ("C(s, h) has 31 octets", (JAM.Trie.keyOfServiceData 7 []).length == 31)]

def main (args : List String) : IO UInt32 := do
  let path := args.headD "vendor/jam-test-vectors/trie/trie.json"
  let j ← PVM.Tests.readJson path
  let some cases := (j.getArr?).toOption | IO.eprintln "not an array"; return 1
  let mut pass := 0
  for (c, i) in cases.toList.zipIdx do
    match runCase c with
    | .ok (true, _) => pass := pass + 1
    | .ok (false, n) => IO.eprintln s!"FAIL case {i} ({n} entries): root differs"
    | .error e => IO.eprintln s!"FAIL case {i}: {e}"
  IO.println s!"trietest: {pass} of {cases.size} trie roots match"
  let keysOk := keyChecks.filter (·.2)
  for (name, ok) in keyChecks do
    if !ok then IO.eprintln s!"FAIL state key: {name}"
  IO.println s!"trietest: {keysOk.length} of {keyChecks.length} state-key checks pass"
  return if pass == cases.size && keysOk.length == keyChecks.length then 0 else 1
