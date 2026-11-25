import JAM.State
import JAM.Block
import JAM.StateDecode

/-!
# Reading the block-import traces (davxy/jam-test-vectors `traces/`, schema `schema.asn`)

A trace step is ℰ(pre-state, block, post-state) and the genesis file is ℰ(header, state), where a
raw state is ℰ(root, ↕[(key ∈ 𝔹_31, ↕value)]).

A raw state's key-values are turned into σ by `JAM.StateDecode.decodeState`, the inverse of T
(GP §D.1), which this module re-exports.
-/

namespace JAM.TraceState

open Decoder

export JAM.StateDecode (decodeState)

/-- A raw state: the root and the key-values. -/
structure RawState where
  root : ByteArray
  kvs : List (List UInt8 × List UInt8)

def rawState : Decoder RawState := do
  return { root := ← bytes 32,
           kvs := ← varSeq (do return ((← bytes 31).toList, (← var).toList)) }

/-- One step of a trace. -/
structure Step where
  pre : RawState
  block : Block
  post : RawState

def step (p : Params) : Decoder Step := do
  return { pre := ← rawState, block := ← Block.decode p, post := ← rawState }

/-- The genesis file. -/
def genesis (p : Params) : Decoder (Header × RawState) := do
  return (← Header.decode p, ← rawState)

/-! ## v0.8.0 raw states in v0.8.1 form (test-only conversion)

The published traces are GP v0.8.0 states. Until v0.8.1 traces exist, `upgradeRaw` rewrites the
two state rows whose encoding GP v0.8.1 changed, and nothing else (CLAUDE.md, "Vectors during the
migration"):

* C(13): the validator statistics π_V and π_L become variable-length naturals (GP #564,
  eq. `serialization`); π_C and π_S are unchanged.
* C(255, s): ℰ_4(a_u, a_u') is inserted after a_c and ℰ_8(a_b') after a_b (GP #539, junior
  services, eq. `serialization`). A v0.8.0 account has no supervisor, so it is given the values
  under which GP v0.8.1 behaves as v0.8.0 did: a_u = s with a_u' = a_r, so that the effective
  supervisor E(**d**, s) = s (eq. `effectivesupervisor`), and a_b' = 0, so that a_b + a_b' = a_b in
  every threshold test (Ω_W, Ω_S, Ω_N, Ω_T).

The root is recomputed from the rewritten key-values (`Trie.root`), after checking that the v0.8.0
root matches the v0.8.0 key-values. -/

/-- Rewrite one v0.8.0 C(13) value in the v0.8.1 encoding (GP #564). -/
def upgradeStats (v : List UInt8) : Except String (List UInt8) := do
  let old : Decoder (List (List Nat)) := varSeq (seqN 6 (fixed 4))
  let dec : Decoder (List (List Nat) × List (List Nat) × Nat) := do
    let a ← old; let b ← old; let pos ← get; let _ ← bytes (← remaining); return (a, b, pos)
  let (a, b, pos) ← match Decoder.run dec ⟨v.toArray⟩ with
    | .ok r => pure r
    | .error e => throw s!"C(13): {e}"
  let enc (xs : List (List Nat)) := Codec.varSeq (fun r => r.flatMap Codec.nat) xs
  return enc a ++ enc b ++ v.drop pos

/-- Rewrite one v0.8.0 C(255, s) value in the v0.8.1 layout (GP #539). -/
def upgradeInfo (s : Nat) (v : List UInt8) : Except String (List UInt8) := do
  if v.length != 1 + 32 + 40 + 16 then throw s!"C(255, {s}): {v.length} octets"
  let created := v.drop (1 + 32 + 40 + 4) |>.take 4
  return v.take 33 ++ Codec.fixed 4 s ++ created ++ (v.drop 33).take 8 ++ Codec.fixed 8 0 ++ v.drop 41

/-- A v0.8.0 raw state in v0.8.1 form (`upgradeStats`, `upgradeInfo`). -/
def upgradeRaw (raw : RawState) : Except String RawState := do
  let d : OctetDict := Std.ExtTreeMap.ofList raw.kvs
  if Trie.root d != raw.root.toList then throw "raw state: root does not match its key-values"
  let kvs ← raw.kvs.mapM fun (k, v) => do
    if k == Trie.keyOfIndex 13 then return (k, ← upgradeStats v)
    else if JAM.StateDecode.isInfoKey k then
      return (k, ← upgradeInfo (PVM.Num.decodeLE [k.getD 1 0, k.getD 3 0, k.getD 5 0, k.getD 7 0]) v)
    else return (k, v)
  return { root := ⟨(Trie.root (Std.ExtTreeMap.ofList kvs)).toArray⟩, kvs }

/-- A trace step with both raw states in v0.8.1 form. -/
def upgradeStep (st : Step) : Except String Step := do
  return { st with pre := ← upgradeRaw st.pre, post := ← upgradeRaw st.post }

end JAM.TraceState
