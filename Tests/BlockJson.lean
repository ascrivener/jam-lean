import Tests.JamJson

/-!
# JSON readers for blocks, headers and extrinsics (davxy/jam-test-vectors `v0.8.0`, `codec/`)

The field names are the vectors'; each reader builds the model's term (`JAM.Block`).
-/

namespace JAM.Tests.Json

open Lean (Json)
open PVM.Tests (field natField die)

def boolField (j : Json) (k : String) : Except String Bool := do (← field j k).getBool?

def list {α : Type} (j : Json) (k : String) (f : Json → Except String α) : Except String (List α) := do
  return (← (← arr j k).mapM f).toList

def epochMark (j : Json) : Except String EpochMark := do
  return { entropy := ← hexField j "entropy", ticketsEntropy := ← hexField j "tickets_entropy",
           validators := ← list j "validators" fun v => do
             return (← hexField v "bandersnatch", ← hexField v "ed25519") }

def ticket (j : Json) : Except String Ticket := do
  return { id := ← hexField j "id", attempt := ← natField j "attempt" }

/-- A JSON value that may be `null`. -/
def nullable {α : Type} (j : Json) (k : String) (f : Json → Except String α) : Except String (Option α) := do
  match ← field j k with
  | .null => return none
  | v => return some (← f v)

def header (j : Json) : Except String Header := do
  return { parent := ← hexField j "parent", priorStateRoot := ← hexField j "parent_state_root",
           extrinsicHash := ← hexField j "extrinsic_hash", slot := ← natField j "slot",
           epochMark := ← nullable j "epoch_mark" epochMark,
           winnersMark := ← nullable j "tickets_mark" fun v => do
             return (← v.getArr?.bind (·.mapM ticket)).toList,
           offendersMark := ← list j "offenders_mark" hex, authorIndex := ← natField j "author_index",
           vrfSig := ← hexField j "entropy_source", sealSig := ← hexField j "seal" }

def ticketProof (j : Json) : Except String TicketProof := do
  return { attempt := ← natField j "attempt", proof := ← hexField j "signature" }

def preimage (j : Json) : Except String Preimage := do
  return { requester := ← natField j "requester", blob := ← hexField j "blob" }

def guarantee (j : Json) : Except String Guarantee := do
  return { report := ← workReport (← field j "report"), slot := ← natField j "slot",
           credential := ← list j "signatures" fun s => do
             return (← natField s "validator_index", ← hexField s "signature") }

/-- An assurance; its bit field has `cores` bits. -/
def assurance (cores : Nat) (j : Json) : Except String Assurance := do
  let some bits := PVM.Blob.decodeBits? (← hexField j "bitfield").toList cores
    | die s!"bit field is not {cores} bits"
  return { anchor := ← hexField j "anchor", bitfield := bits.toList,
           assurer := ← natField j "validator_index", signature := ← hexField j "signature" }

def disputes (j : Json) : Except String Disputes := do
  return {
    verdicts := ← list j "verdicts" fun v => do
      return { target := ← hexField v "target", age := ← natField v "age",
               votes := ← list v "votes" fun x => do
                 return { valid := ← boolField x "vote", index := ← natField x "index",
                          signature := ← hexField x "signature" } },
    culprits := ← list j "culprits" fun c => do
      return { target := ← hexField c "target", key := ← hexField c "key",
               signature := ← hexField c "signature" },
    faults := ← list j "faults" fun f => do
      return { target := ← hexField f "target", valid := ← boolField f "vote",
               key := ← hexField f "key", signature := ← hexField f "signature" } }

def extrinsic (cores : Nat) (j : Json) : Except String Extrinsic := do
  return { tickets := ← list j "tickets" ticketProof, preimages := ← list j "preimages" preimage,
           guarantees := ← list j "guarantees" guarantee,
           assurances := ← list j "assurances" (assurance cores),
           disputes := ← disputes (← field j "disputes") }

def block (cores : Nat) (j : Json) : Except String Block := do
  return { header := ← header (← field j "header"), extrinsic := ← extrinsic cores (← field j "extrinsic") }

/-- A JSON array as a list. -/
def items {α : Type} (j : Json) (f : Json → Except String α) : Except String (List α) := do
  return (← j.getArr?.bind (·.mapM f)).toList

end JAM.Tests.Json
