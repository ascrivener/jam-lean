import JAM.Work

/-!
# The deserialization function $\mathcal{E}^{-1}$ (GP v0.8.1 Appendix C)

GP Appendix C defines the decoding function as "the inverse of $\mathcal{E}$ … able to decode some sequence
into the original value". A `Decoder α` reads a term from an octet sequence at a position; `run`
accepts the sequence only if the term uses all of it. Each primitive accepts exactly the octets its
encoder produces, so a decoder built from them is a left inverse of the matching encoder and rejects
everything outside its image (non-canonical naturals, nonzero padding bits, discriminators other
than 0 and 1, lengths longer than the remaining input).

The primitives mirror `JAM.Codec`: $\mathcal{E}$ (`nat`), $\mathcal{E}_l$ (`fixed`), fixed-length octet sequences
(`bytes`), $\updownarrow x$ (`var`, `varSeq`), sequences of a known length (`seqN`), $\text{¿}x$ (`opt`) and bit sequences
(`bits`). The decoders of the work-package family (§11, §14) follow at the end; block terms are in
`JAM.Block`.
-/

namespace JAM

/-- A decoder: reads a term from the input at the current position, or fails with a message. -/
abbrev Decoder := ReaderT ByteArray (StateT Nat (Except String))

namespace Decoder

/-- Fail with a message, naming the offset. -/
def fail {α : Type} (msg : String) : Decoder α := do
  throw s!"at offset {← get}: {msg}"

/-- The number of octets not yet read. -/
def remaining : Decoder Nat := do return (← read).size - (← get)

/-- `n` octets, as they are: the identity encoding of a fixed-length octet sequence such as a hash
    (GP (C) "Trivial Encodings"). -/
def bytes (n : Nat) : Decoder ByteArray := do
  let bs ← read
  let pos ← get
  if pos + n ≤ bs.size then
    set (pos + n)
    return bs.extract pos (pos + n)
  else fail s!"need {n} octets, {bs.size - pos} left"

/-- One octet. -/
def byte : Decoder UInt8 := do
  let bs ← read
  let pos ← get
  if h : pos + 1 ≤ bs.size then
    set (pos + 1)
    return bs[pos]
  else fail s!"need {1} octets, {bs.size - pos} left"

/-- $\mathcal{E}_l^{-1}$: an `l`-octet little-endian natural (GP (C) "Fixed-length Integer Encoding"). Every
    `l`-octet sequence is $\mathcal{E}_l$ of exactly one $x < 2^{8l}$. -/
def fixed (l : Nat) : Decoder Nat := do
  return PVM.Num.decodeLE (← bytes l).toList

/-- $\mathcal{E}^{-1}$ of the general natural encoding (GP (C) "general natural number serialization"); only the
    canonical encoding of each $x$ is accepted (`PVM.Blob.decodeNat?`). -/
def nat : Decoder Nat := do
  match PVM.Blob.decodeNat? (← read) (← get) with
  | some (x, pos') => set pos'; return x
  | none => fail "not a canonical ℰ-encoded natural"

/-- A Boolean: one octet, $\mathcal{E}(\bot) = [0]$ and $\mathcal{E}(\top) = [1]$ (GP v0.8.1 eq. C.3);
    any other octet fails. -/
def bool : Decoder Bool := do
  match ← byte with
  | 0 => return false
  | 1 => return true
  | b => fail s!"bad Boolean {b}"

/-- `n` terms in sequence, without a length prefix (GP (C) "Sequence Encoding"), for a sequence
    whose length the type fixes. -/
def seqN {α : Type} (n : Nat) (d : Decoder α) : Decoder (List α) :=
  (List.range n).mapM fun _ => d

/-- $\mathcal{E}^{-1}(\updownarrow \mathbf{x})$ for a sequence: $\mathcal{E}(|\mathbf{x}|)$ then the terms (GP (C) "Discriminator Encoding").
    Every term here takes at least one octet, so a length beyond the remaining input is rejected
    before anything is read. -/
def varSeq {α : Type} (d : Decoder α) : Decoder (List α) := do
  let n ← nat
  if n > (← remaining) then fail s!"length {n} exceeds the input"
  seqN n d

/-- $\mathcal{E}^{-1}(\updownarrow x)$ for an octet sequence. -/
def var : Decoder ByteArray := do
  let n ← nat
  bytes n

/-- $\mathcal{E}^{-1}(\text{¿}x)$: 0 for $\varnothing$, 1 then $x$ otherwise (GP (C) "Discriminator Encoding"). -/
def opt {α : Type} (d : Decoder α) : Decoder (Option α) := do
  match ← byte with
  | 0 => return none
  | 1 => return some (← d)
  | b => fail s!"bad optional discriminator {b}"

/-- $\mathcal{E}^{-1}$ of a bit sequence of length `n`: $\lceil n/8 \rceil$ octets, least significant bit first, padding bits
    zero (GP (C) "Bit Sequence Encoding"; `PVM.Blob.decodeBits?`). -/
def bits (n : Nat) : Decoder (List Bool) := do
  let bs ← bytes ((n + 7) / 8)
  match PVM.Blob.decodeBits? bs.toList n with
  | some b => return b.toList
  | none => fail "nonzero padding bits"

/-- A set of 32-octet hashes, $\updownarrow$ and in ascending order (GP (C) "Set Encoding"). Ascending order is
    part of the encoding: a sequence out of order or with a repeat is not the encoding of any set. -/
def varHashSet : Decoder OctetSet := do
  let hs ← varSeq (bytes 32)
  let ls := hs.map (·.toList)
  if (ls.zip (ls.drop 1)).all (fun (a, b) => decide (a < b)) then return Std.ExtTreeSet.ofList ls
  else fail "set elements not in ascending order"

/-- A dictionary $\mathbb{H} \to \mathbb{H}$, $\updownarrow$ pairs in ascending key order (GP (C) "Dictionary Encoding"). -/
def varHashDict : Decoder OctetDict := do
  let kvs ← varSeq (do return ((← bytes 32).toList, (← bytes 32).toList))
  let ks := kvs.map (·.1)
  if (ks.zip (ks.drop 1)).all (fun (a, b) => decide (a < b)) then return Std.ExtTreeMap.ofList kvs
  else fail "dictionary keys not in ascending order"

/-- Run a decoder on a whole octet sequence: it must read every octet. -/
def run {α : Type} (d : Decoder α) (bs : ByteArray) : Except String α := do
  let (x, pos) ← StateT.run (ReaderT.run d bs) 0
  if pos = bs.size then return x
  else throw s!"{bs.size - pos} octets left over at offset {pos}"

end Decoder

/-! ## The work-package family (GP §11, §14; encodings in Appendix C) -/

open Decoder

/-- $\mathcal{E}^{-1}$ for $\mathbb{C}$, the refinement context. -/
def RefineContext.decode : Decoder RefineContext := do
  return { anchorHash := ← bytes 32, anchorSlot := ← fixed 4, anchorStateRoot := ← bytes 32,
           anchorAccOutLog := ← bytes 32, lookupAnchorHash := ← bytes 32,
           lookupAnchorSlot := ← fixed 4, lookupAnchorStateRoot := ← bytes 32,
           prerequisites := ← varHashSet }

/-- $I^{-1}$: an import reference, $\mathcal{E}_2(i)$ for a segment root and $\mathcal{E}_2(i + 2^{15})$ for $r^\boxplus$, so $i \in \mathbb{N}_{2^{15}}$
    (GP Appendix C). -/
def decodeImport : Decoder (SegmentRoot × Nat) := do
  let h ← bytes 32
  let i ← fixed 2
  return if i < 2 ^ 15 then (.root h, i) else (.package h, i - 2 ^ 15)

/-- $\mathcal{E}^{-1}$ for $\mathbb{W}$, a work item. -/
def WorkItem.decode : Decoder WorkItem := do
  return { service := ← fixed 4, codeHash := ← bytes 32, refineGasLimit := ← fixed 8,
           accumulateGasLimit := ← fixed 8, exportCount := ← fixed 2, payload := ← var,
           importSegments := ← varSeq decodeImport,
           extrinsics := ← varSeq (do return (← bytes 32, ← fixed 4)) }

/-- $\mathcal{E}^{-1}$ for $\mathbb{P}$, a work package. -/
def WorkPackage.decode : Decoder WorkPackage := do
  return { authCodeHost := ← fixed 4, authCodeHash := ← bytes 32, context := ← RefineContext.decode,
           authToken := ← var, authConfig := ← var, items := ← varSeq WorkItem.decode }

/-- $O^{-1}$: a work result (GP Appendix C). -/
def WorkResult.decode : Decoder WorkResult := do
  match ← nat with
  | 0 => return .ok (← var)
  | 1 => return .err .outOfGas
  | 2 => return .err .panic
  | 3 => return .err .badExports
  | 4 => return .err .oversize
  | 5 => return .err .bad
  | 6 => return .err .big
  | k => fail s!"bad work result discriminator {k}"

/-- $\mathcal{E}^{-1}$ for $\mathbb{D}$, a work digest. -/
def WorkDigest.decode : Decoder WorkDigest := do
  return { service := ← fixed 4, codeHash := ← bytes 32, payloadHash := ← bytes 32,
           gasLimit := ← fixed 8, result := ← WorkResult.decode, gasUsed := ← nat,
           importCount := ← nat, extrinsicCount := ← nat, extrinsicSize := ← nat,
           exportCount := ← nat }

/-- $\mathcal{E}^{-1}$ for $\mathbb{Y}$, an availability specification. -/
def AvailabilitySpec.decode : Decoder AvailabilitySpec := do
  return { packageHash := ← bytes 32, bundleLength := ← fixed 4, erasureRoot := ← bytes 32,
           erasureShards := ← fixed 2, segmentRoot := ← bytes 32, segmentCount := ← fixed 2 }

/-- $\mathcal{E}^{-1}$ for $\mathbb{R}$, a work report. -/
def WorkReport.decode : Decoder WorkReport := do
  return { spec := ← AvailabilitySpec.decode, context := ← RefineContext.decode, core := ← nat,
           authorizerHash := ← bytes 32, authGasUsed := ← nat, authTrace := ← var,
           segmentRootLookup := ← varHashDict, digests := ← varSeq WorkDigest.decode }

end JAM
