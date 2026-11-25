import JAM.BlockImport
import Tests.TraceState

/-!
# Reading the GP v0.8.0 vectors under the v0.8.1 model

The pinned test vectors (davxy/jam-test-vectors `v0.8.0`) encode blocks in the v0.8.0 format. One
v0.8.1 change alters that format: an assurance no longer carries the anchor a (GP #562,
`reporting_assurance.tex` eq. `xtassurances` and `serialization.tex` ℰ_A). The anchor had to equal
H_P, and the signature covers H_P anyway, so dropping it changes no outcome; it only removes 32
octets from each assurance's encoding, and so changes the extrinsic hash H_X of a block with
assurances.

This module reads the v0.8.0 encoding and converts it, for the harnesses only:

* `decodeAssurances080`, `Extrinsic.decode080` and `Block.decode080` read the v0.8.0 encoding and
  return the v0.8.1 terms together with the anchors;
* `encodeAssurances080` and `Extrinsic.hash080` give the v0.8.0 encoding and extrinsic hash, so
  that a trace block's H_X is checked against the formula it was made with
  (`JAM.importBlockCommitted`);
* `step080` reads a trace step (`Tests.TraceState.Step`) with v0.8.0 blocks.

The model itself (`JAM.Block`, `JAM.Assurances`) follows v0.8.1 only.
-/

namespace JAM.V080

open Codec Decoder

/-- ℰ_A of v0.8.0: ℰ(↕[(a, f, ℰ_2(v), s) | (a, f, v, s) ← 𝔼_A]), from the v0.8.1 assurances and
    their anchors. -/
def encodeAssurances080 (xs : List (Hash × Assurance)) : List UInt8 :=
  varSeq (fun (h, a) => blob h ++ encodeBits a.bitfield ++ fixed 2 a.assurer ++ blob a.signature) xs

/-- ℰ_A⁻¹ of v0.8.0: each assurance with its anchor. -/
def decodeAssurances080 (p : Params) : Decoder (List (Hash × Assurance)) :=
  varSeq do
    let anchor ← bytes hashSize
    return (anchor, { bitfield := ← bits p.coreCount, assurer := ← fixed 2,
                      signature := ← bytes edSigSize })

/-- ℰ⁻¹ for 𝔼 of v0.8.0: the v0.8.1 extrinsic and the assurances' anchors. -/
def Extrinsic.decode080 (p : Params) : Decoder (Extrinsic × List Hash) := do
  let tickets ← decodeTickets
  let preimages ← decodePreimages
  let guarantees ← decodeGuarantees
  let assurances ← decodeAssurances080 p
  let disputes ← Disputes.decode
  return ({ tickets, disputes, preimages, assurances := assurances.map (·.2), guarantees },
    assurances.map (·.1))

/-- ℰ⁻¹ for 𝔹 of v0.8.0: the v0.8.1 block and the assurances' anchors. -/
def Block.decode080 (p : Params) : Decoder (Block × List Hash) := do
  let header ← Header.decode p
  let (extrinsic, anchors) ← Extrinsic.decode080 p
  return ({ header, extrinsic }, anchors)

/-- H_X of v0.8.0 (GP v0.8.0 eq. `extrinsichash`): as v0.8.1, but with the v0.8.0 ℰ_A. -/
def Extrinsic.hash080 (x : Extrinsic) (anchors : List Hash) : List UInt8 :=
  let parts := x.hashParts.set 3 (encodeAssurances080 (anchors.zip x.assurances))
  hashL (parts.flatMap hashL)

/-- A trace step whose block is in the v0.8.0 encoding, with the block's v0.8.0 H_X commitment. -/
def step080 (p : Params) : Decoder (TraceState.Step × List UInt8) := do
  let pre ← TraceState.rawState
  let (block, anchors) ← Block.decode080 p
  let post ← TraceState.rawState
  return ({ pre, block, post }, Extrinsic.hash080 block.extrinsic anchors)

/-! Regression tests (GP v0.8.1 #562): an assurance encodes as f ⌢ ℰ_2(v) ⌢ s, with no anchor. -/

private def a0 : Assurance :=
  { bitfield := [true, false], assurer := 5, signature := ⟨(List.replicate 64 7).toArray⟩ }
private def h0 : Hash := ⟨(List.replicate 32 9).toArray⟩

-- v0.8.1: one length octet, one bit-field octet (2 cores), two index octets and the signature.
#guard encodeAssurances [a0] = [1, 1, 5, 0] ++ List.replicate 64 7
-- v0.8.0 had the 32-octet anchor first.
#guard encodeAssurances080 [(h0, a0)] = [1] ++ List.replicate 32 9 ++ [1, 5, 0] ++ List.replicate 64 7
-- The v0.8.1 decoder reads the v0.8.1 encoding back, and rejects the v0.8.0 one.
#guard ((decodeAssurances Params.tiny).run
    ⟨(encodeAssurances [a0]).toArray⟩).toOption.map (·.map (·.assurer)) = some [5]
#guard ((decodeAssurances Params.tiny).run
    ⟨(encodeAssurances080 [(h0, a0)]).toArray⟩).toOption.isNone

end JAM.V080
