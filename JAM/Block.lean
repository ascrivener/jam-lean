import JAM.Decode
import JAM.Params

/-!
# Blocks, headers and extrinsics (GP v0.8.0 §4, §5, §6, §10, §11, §12) and their codec
(Appendix C, "Block Serialization")

The block 𝔹 = (ℍ, 𝔼) (GP eq. `block`), the header (eq. `header`) and the five extrinsics
𝔼 = (𝔼_T, 𝔼_D, 𝔼_P, 𝔼_A, 𝔼_G) (eq. `extrinsic`), with ℰ exactly as Appendix C writes it and the
decoders that invert it. Keys, signatures and proofs are octet sequences of the paper's fixed
sizes; the types do not enforce the lengths, the decoders read exactly them.

Two parameters of the chain shape the encoding: 𝖢, the length of an assurance's bit field, and
𝖤, the length of the winning-tickets marker. Both come from `Params` (`.tiny` for the test
vectors' chain, `.full` for the paper's). Sequences the paper prefixes with ↕ are decoded with
their prefix even where a protocol rule fixes their length (the epoch marker's 𝖵 keys, a verdict's
judgments).
-/

namespace JAM

open Codec

/-- Sizes of the fixed-length terms, in octets (GP §3.8: ℍ, 𝕂_B and 𝕂_E keys, Ed25519 signatures
    𝕍̄, Bandersnatch signatures 𝕍̃ and ring proofs 𝕍̊). -/
def hashSize : Nat := 32
def keySize : Nat := 32
def edSigSize : Nat := 64
def bsSigSize : Nat := 96
def ringProofSize : Nat := 784

/-! ## The header (GP §5, eq. `header`) -/

/-- The epoch marker H_E (GP eq. `epochmarker`): the entropy η₀ and η₁, and the next epoch's
    validator keys, each a Bandersnatch and an Ed25519 key. -/
structure EpochMark where
  /-- η₀, the entropy accumulator -/
  entropy : Hash
  /-- η₁ -/
  ticketsEntropy : Hash
  /-- **k**, (bandersnatch, ed25519) per validator -/
  validators : List (Hash × Hash)

/-- A Safrole ticket 𝕋 = (y ∈ ℍ, e ∈ ℕ_N) (GP eq. `ticket`). -/
structure Ticket where
  /-- y, the ticket identifier -/
  id : Hash
  /-- e, the entry index -/
  attempt : Nat

/-- ℰ(t ∈ 𝕋) = ℰ(y, ℰ_1(e)) (GP Appendix C). -/
def Ticket.encode (t : Ticket) : List UInt8 := blob t.id ++ fixed 1 t.attempt

/-- The header ℍ (GP eq. `header`). -/
structure Header where
  /-- H_P, the parent header hash -/
  parent : Hash
  /-- H_R, the prior state root -/
  priorStateRoot : Hash
  /-- H_X, the extrinsic hash -/
  extrinsicHash : Hash
  /-- H_T, the timeslot -/
  slot : Nat
  /-- H_E, the epoch marker -/
  epochMark : Option EpochMark
  /-- H_W, the winning-tickets marker: 𝖤 tickets -/
  winnersMark : Option (List Ticket)
  /-- H_O, the offenders marker: Ed25519 keys -/
  offendersMark : List Hash
  /-- H_I, the block author's index -/
  authorIndex : Nat
  /-- H_V, the entropy-yielding VRF signature -/
  vrfSig : Blob
  /-- H_S, the block seal -/
  sealSig : Blob

/-- ℰ_E(H_E): 0 for ∅, otherwise ℰ(1, η₀, η₁, ↕**k**) (GP Appendix C). -/
def encodeEpochMark : Option EpochMark → List UInt8
  | none => nat 0
  | some m => nat 1 ++ blob m.entropy ++ blob m.ticketsEntropy ++
      varSeq (fun (b, e) => blob b ++ blob e) m.validators

/-- ℰ_U(H), the unsigned header (GP Appendix C). -/
def Header.encodeUnsigned (h : Header) : List UInt8 :=
  blob h.parent ++ blob h.priorStateRoot ++ blob h.extrinsicHash ++ fixed 4 h.slot ++
    encodeEpochMark h.epochMark ++ opt (seq Ticket.encode) h.winnersMark ++ fixed 2 h.authorIndex ++
    blob h.vrfSig ++ varSeq blob h.offendersMark

/-- ℰ(H) = ℰ(ℰ_U(H), H_S) (GP Appendix C). -/
def Header.encode (h : Header) : List UInt8 := h.encodeUnsigned ++ blob h.sealSig

/-! ## The extrinsics -/

/-- A ticket proof in 𝔼_T (GP eq. `ticketsextrinsic`): the entry index r and the ring proof p. -/
structure TicketProof where
  attempt : Nat
  proof : Blob

/-- A preimage in 𝔼_P (GP §12.4, eq. `preimagesareordered`): the requesting service s and the data **p**. -/
structure Preimage where
  requester : ServiceId
  blob : Blob

/-- A guarantee 𝔾 = (r, t, a) (GP eq. `guarantee`): a work report, a timeslot and a credential of
    (validator index, Ed25519 signature) pairs. -/
structure Guarantee where
  report : WorkReport
  slot : Nat
  credential : List (Nat × Blob)

/-- An assurance in 𝔼_A (GP eq. `xtassurances`): the anchor a, the availability bit field f ∈ 𝕓_𝖢,
    the assurer's validator index v and its signature s. -/
structure Assurance where
  anchor : Hash
  bitfield : List Bool
  assurer : Nat
  signature : Blob

/-- A judgment within a verdict (GP eq. `disputesextrinsics`): validity, judge index, signature. -/
structure Judgment where
  valid : Bool
  index : Nat
  signature : Blob

/-- A verdict: the report hash r, the epoch index a and the judgments **j**. -/
structure Verdict where
  target : Hash
  age : Nat
  votes : List Judgment

/-- A culprit (r, f, s): report hash, offender's Ed25519 key, signature. -/
structure Culprit where
  target : Hash
  key : Hash
  signature : Blob

/-- A fault (r, v, f, s): report hash, validity, offender's Ed25519 key, signature. -/
structure Fault where
  target : Hash
  valid : Bool
  key : Hash
  signature : Blob

/-- The disputes extrinsic 𝔼_D = (**v**, **c**, **f**) (GP eq. `disputesextrinsics`). -/
structure Disputes where
  verdicts : List Verdict
  culprits : List Culprit
  faults : List Fault

/-- ℰ on {⊤, ⊥}: ℰ of the indicator, 1 for ⊤ and 0 for ⊥. -/
def encodeBool (b : Bool) : List UInt8 := nat (if b then 1 else 0)

/-- ℰ of a bit sequence (GP (C) "Bit Sequence Encoding"): ⌈n/8⌉ octets, packed least
    significant bit first, the padding bits of the last octet zero. -/
def encodeBits (bs : List Bool) : List UInt8 :=
  (List.range ((bs.length + 7) / 8)).map fun k =>
    UInt8.ofNat ((List.range 8).foldl (fun acc i => acc + (if bs.getD (8 * k + i) false then 2 ^ i else 0)) 0)

/-- ℰ_T(𝔼_T) = ℰ(↕[(ℰ_1(r), p) | (r, p) ← 𝔼_T]) (GP Appendix C). -/
def encodeTickets (xs : List TicketProof) : List UInt8 :=
  varSeq (fun t => fixed 1 t.attempt ++ blob t.proof) xs

/-- ℰ_P(𝔼_P) = ℰ(↕[(ℰ_4(s), ↕**p**) | (s, **p**) ← 𝔼_P]) (GP Appendix C). -/
def encodePreimages (xs : List Preimage) : List UInt8 :=
  varSeq (fun p => fixed 4 p.requester ++ var p.blob) xs

/-- ℰ(g ∈ 𝔾) = ℰ(r, ℰ_4(t), ↕[(ℰ_2(v), s) | (v, s) ← a]) (GP Appendix C). -/
def Guarantee.encode (g : Guarantee) : List UInt8 :=
  g.report.encode ++ fixed 4 g.slot ++ varSeq (fun (v, s) => fixed 2 v ++ blob s) g.credential

/-- ℰ_G(𝔼_G) = ℰ(↕𝔼_G) (GP Appendix C). -/
def encodeGuarantees (xs : List Guarantee) : List UInt8 := varSeq Guarantee.encode xs

/-- ℰ_A(𝔼_A) = ℰ(↕[(a, f, ℰ_2(v), s) | (a, f, v, s) ← 𝔼_A]) (GP Appendix C). -/
def encodeAssurances (xs : List Assurance) : List UInt8 :=
  varSeq (fun a => blob a.anchor ++ encodeBits a.bitfield ++ fixed 2 a.assurer ++ blob a.signature) xs

/-- A judgment (v, ℰ_2(i), s) within ℰ_D. -/
def Judgment.encode (j : Judgment) : List UInt8 := encodeBool j.valid ++ fixed 2 j.index ++ blob j.signature

/-- ℰ_D((**v**, **c**, **f**)) = ℰ(↕[(r, ℰ_4(a), ↕[(v, ℰ_2(i), s) | … ← **j**]) | … ← **v**], ↕**c**, ↕**f**)
    (GP Appendix C). Each verdict's judgments carry a length prefix. -/
def Disputes.encode (d : Disputes) : List UInt8 :=
  varSeq (fun v => blob v.target ++ fixed 4 v.age ++ varSeq Judgment.encode v.votes) d.verdicts ++
    varSeq (fun c => blob c.target ++ blob c.key ++ blob c.signature) d.culprits ++
    varSeq (fun f => blob f.target ++ encodeBool f.valid ++ blob f.key ++ blob f.signature) d.faults

/-- The extrinsic 𝔼 = (𝔼_T, 𝔼_D, 𝔼_P, 𝔼_A, 𝔼_G) (GP eq. `extrinsic`). -/
structure Extrinsic where
  tickets : List TicketProof
  disputes : Disputes
  preimages : List Preimage
  assurances : List Assurance
  guarantees : List Guarantee

/-- ℰ of the extrinsic, in the order ℰ(𝔹) uses: ℰ_T, ℰ_P, ℰ_G, ℰ_A, ℰ_D (GP Appendix C). -/
def Extrinsic.encode (x : Extrinsic) : List UInt8 :=
  encodeTickets x.tickets ++ encodePreimages x.preimages ++ encodeGuarantees x.guarantees ++
    encodeAssurances x.assurances ++ x.disputes.encode

/-- A block 𝔹 = (ℍ, 𝔼) (GP eq. `block`). -/
structure Block where
  header : Header
  extrinsic : Extrinsic

/-- ℰ(𝔹) = ℰ(H, ℰ_T(𝔼_T), ℰ_P(𝔼_P), ℰ_G(𝔼_G), ℰ_A(𝔼_A), ℰ_D(𝔼_D)) (GP Appendix C). -/
def Block.encode (b : Block) : List UInt8 := b.header.encode ++ b.extrinsic.encode

/-! ## Decoders -/

open Decoder

/-- ℰ⁻¹ for 𝕋. -/
def Ticket.decode : Decoder Ticket := do
  return { id := ← bytes hashSize, attempt := ← fixed 1 }

/-- ℰ_E⁻¹. -/
def decodeEpochMark : Decoder (Option EpochMark) := do
  match ← nat with
  | 0 => return none
  | 1 => return some { entropy := ← bytes hashSize, ticketsEntropy := ← bytes hashSize,
                       validators := ← varSeq (do return (← bytes keySize, ← bytes keySize)) }
  | k => fail s!"bad epoch-marker discriminator {k}"

/-- ℰ⁻¹ for ℍ; the winning-tickets marker holds 𝖤 tickets. -/
def Header.decode (p : Params) : Decoder Header := do
  return { parent := ← bytes hashSize, priorStateRoot := ← bytes hashSize,
           extrinsicHash := ← bytes hashSize, slot := ← fixed 4, epochMark := ← decodeEpochMark,
           winnersMark := ← opt (seqN p.epochLen Ticket.decode), authorIndex := ← fixed 2,
           vrfSig := ← bytes bsSigSize, offendersMark := ← varSeq (bytes keySize),
           sealSig := ← bytes bsSigSize }

/-- ℰ_T⁻¹. -/
def decodeTickets : Decoder (List TicketProof) :=
  varSeq do return { attempt := ← fixed 1, proof := ← bytes ringProofSize }

/-- ℰ_P⁻¹. -/
def decodePreimages : Decoder (List Preimage) :=
  varSeq do return { requester := ← fixed 4, blob := ← var }

/-- ℰ⁻¹ for 𝔾. -/
def Guarantee.decode : Decoder Guarantee := do
  return { report := ← WorkReport.decode, slot := ← fixed 4,
           credential := ← varSeq (do return (← fixed 2, ← bytes edSigSize)) }

/-- ℰ_G⁻¹. -/
def decodeGuarantees : Decoder (List Guarantee) := varSeq Guarantee.decode

/-- ℰ_A⁻¹; each bit field has 𝖢 bits. -/
def decodeAssurances (p : Params) : Decoder (List Assurance) :=
  varSeq do return { anchor := ← bytes hashSize, bitfield := ← bits p.coreCount,
                     assurer := ← fixed 2, signature := ← bytes edSigSize }

/-- ℰ_D⁻¹. -/
def Disputes.decode : Decoder Disputes := do
  let judgment : Decoder Judgment := do
    return { valid := ← bool, index := ← fixed 2, signature := ← bytes edSigSize }
  return {
    verdicts := ← varSeq (do
      return { target := ← bytes hashSize, age := ← fixed 4, votes := ← varSeq judgment }),
    culprits := ← varSeq (do
      return { target := ← bytes hashSize, key := ← bytes keySize, signature := ← bytes edSigSize }),
    faults := ← varSeq (do
      return { target := ← bytes hashSize, valid := ← bool, key := ← bytes keySize,
               signature := ← bytes edSigSize }) }

/-- ℰ⁻¹ for 𝔼, in the order of ℰ(𝔹). -/
def Extrinsic.decode (p : Params) : Decoder Extrinsic := do
  let tickets ← decodeTickets
  let preimages ← decodePreimages
  let guarantees ← decodeGuarantees
  let assurances ← decodeAssurances p
  let disputes ← Disputes.decode
  return { tickets, disputes, preimages, assurances, guarantees }

/-- ℰ⁻¹ for 𝔹. -/
def Block.decode (p : Params) : Decoder Block := do
  return { header := ← Header.decode p, extrinsic := ← Extrinsic.decode p }

end JAM
