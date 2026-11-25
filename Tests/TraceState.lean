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

end JAM.TraceState
