import JAM.Decode
import JAM.Params

/-!
# Blocks, headers and extrinsics (GP v0.8.1 §4, §5, §6, §10, §11, §12) and their codec
(Appendix C, "Block Serialization")

The block $\mathbf{B} = (\mathbf{H}, \mathbf{E})$ (GP eq. `block`), the header (eq. `header`) and the
five extrinsics $\mathbf{E} = (\mathbf{E}_T, \mathbf{E}_P, \mathbf{E}_G, \mathbf{E}_A, \mathbf{E}_D)$
(v0.8.1 eq. `extrinsic`), with $\mathcal{E}$ exactly as Appendix C writes it and the decoders that
invert it. Keys, signatures and proofs are octet sequences of the paper's fixed sizes; the types do
not enforce the lengths, the decoders read exactly them.

Two parameters of the chain shape the encoding: $\mathsf{C}$, the length of an assurance's bit
field, and $\mathsf{E}$, the length of the winning-tickets marker. Both come from `Params` (`.tiny` for the test
vectors' chain, `.full` for the paper's). Sequences the paper prefixes with $\updownarrow$ are decoded with
their prefix even where a protocol rule fixes their length (the epoch marker's $\mathsf{V}$ keys, a verdict's
judgments).
-/

namespace JAM

open Codec

/-- Sizes of the fixed-length terms, in octets (GP §3.8: $\mathbb{H}$, $\overset{\backsim}{\mathbb{H}}$ and
    $\bar{\mathbb{H}}$ keys, Ed25519 signatures $\bar{\mathbb{V}}$, Bandersnatch signatures
    $\overset{\backsim}{\mathbb{V}}$ and ring proofs $\mathring{\mathbb{V}}$). -/
def hashSize : Nat := 32
def keySize : Nat := 32
def edSigSize : Nat := 64
def bsSigSize : Nat := 96
def ringProofSize : Nat := 784

/-- The Ed25519 component of the null validator key: [2, 0, 0, …] (GP v0.8.1 eq. `nullvalkey`).
    The all-zero sequence encodes a point of order four, under which signatures can be forged;
    2 is a y-coordinate with no curve point, so no signature verifies under this key. -/
def nullEdKey : List UInt8 := 2 :: List.replicate 31 0

/-- The null validator key (GP v0.8.1 eq. `nullvalkey`), of 336 octets: Bandersnatch [0, 0, …],
    Ed25519 `nullEdKey`, BLS [0, 0, …] and metadata [0, 0, …]. Used in place of the key of a
    validator that must be kept out of the protocol ($\Phi$, eq. `blacklistfilter`). -/
def nullValidatorKey : List UInt8 :=
  List.replicate keySize 0 ++ nullEdKey ++ List.replicate 144 0 ++ List.replicate 128 0

/-! ## The header (GP §5, eq. `header`) -/

/-- The epoch marker $\mathbf{H}_E$ (GP eq. `epochmarker`): the entropy $\eta_0$ and $\eta_1$, and
    the next epoch's validator keys, each a Bandersnatch and an Ed25519 key. -/
structure EpochMark where
  /-- $\eta_0$, the entropy accumulator -/
  entropy : Hash
  /-- $\eta_1$ -/
  ticketsEntropy : Hash
  /-- $\mathbf{k}$, (bandersnatch, ed25519) per validator -/
  validators : List (Hash × Hash)

/-- A Safrole ticket $\mathbb{T} = (y \in \mathbb{H}, e \in \mathbb{N}_N)$ (GP eq. `ticket`). -/
structure Ticket where
  /-- $y$, the ticket identifier -/
  id : Hash
  /-- $e$, the entry index -/
  attempt : Nat

/-- $\mathcal{E}(t \in \mathbb{T}) = \mathcal{E}(y, \mathcal{E}_1(e))$ (GP Appendix C). -/
def Ticket.encode (t : Ticket) : List UInt8 := blob t.id ++ fixed 1 t.attempt

/-- The header $\mathbf{H}$ (GP eq. `header`). -/
structure Header where
  /-- $\mathbf{H}_P$, the parent header hash -/
  parent : Hash
  /-- $\mathbf{H}_R$, the prior state root -/
  priorStateRoot : Hash
  /-- $\mathbf{H}_X$, the extrinsic hash -/
  extrinsicHash : Hash
  /-- $\mathbf{H}_T$, the timeslot -/
  slot : Nat
  /-- $\mathbf{H}_E$, the epoch marker -/
  epochMark : Option EpochMark
  /-- $\mathbf{H}_W$, the winning-tickets marker: $\mathsf{E}$ tickets -/
  winnersMark : Option (List Ticket)
  /-- $\mathbf{H}_O$, the offenders marker: Ed25519 keys -/
  offendersMark : List Hash
  /-- $\mathbf{H}_I$, the block author's index -/
  authorIndex : Nat
  /-- $\mathbf{H}_V$, the entropy-yielding VRF signature -/
  vrfSig : Blob
  /-- $\mathbf{H}_S$, the block seal -/
  sealSig : Blob

/-- $\mathcal{E}_E(\mathbf{H}_E)$: 0 for $\emptyset$, otherwise
    $\mathcal{E}(1, \eta_0, \eta_1, \updownarrow\mathbf{k})$ (GP Appendix C). -/
def encodeEpochMark : Option EpochMark → List UInt8
  | none => nat 0
  | some m => nat 1 ++ blob m.entropy ++ blob m.ticketsEntropy ++
      varSeq (fun (b, e) => blob b ++ blob e) m.validators

/-- $\mathcal{E}_U(\mathbf{H})$, the unsigned header (GP Appendix C). -/
def Header.encodeUnsigned (h : Header) : List UInt8 :=
  blob h.parent ++ blob h.priorStateRoot ++ blob h.extrinsicHash ++ fixed 4 h.slot ++
    encodeEpochMark h.epochMark ++ opt (seq Ticket.encode) h.winnersMark ++ fixed 2 h.authorIndex ++
    blob h.vrfSig ++ varSeq blob h.offendersMark

/-- $\mathcal{E}(\mathbf{H}) = \mathcal{E}(\mathcal{E}_U(\mathbf{H}), \mathbf{H}_S)$ (GP Appendix C). -/
def Header.encode (h : Header) : List UInt8 := h.encodeUnsigned ++ blob h.sealSig

/-! ## The extrinsics -/

/-- A ticket proof in $\mathbf{E}_T$ (GP eq. `ticketsextrinsic`): the entry index $r$ and the ring
    proof $p$. -/
structure TicketProof where
  attempt : Nat
  proof : Blob

/-- A preimage in $\mathbf{E}_P$ (GP §12.4, eq. `preimagesareordered`): the requesting service $s$
    and the data $\mathbf{p}$. -/
structure Preimage where
  requester : ServiceId
  blob : Blob

/-- A guarantee $\mathbb{G} = (\mathbf{r}, t, a)$ (GP eq. `guarantee`): a work report, a timeslot and a credential of
    (validator index, Ed25519 signature) pairs. -/
structure Guarantee where
  report : WorkReport
  slot : Nat
  credential : List (Nat × Blob)

/-- An assurance in $\mathbf{E}_A$ (GP v0.8.1 eq. `xtassurances`): the availability bit field
    $f \in \text{𝕓}_{\mathsf{C}}$, the assurer's validator index $v$ and its signature $s$. v0.8.1
    drops v0.8.0's anchor $a$, which had to equal $\mathbf{H}_P$ (GP #562). -/
structure Assurance where
  bitfield : List Bool
  assurer : Nat
  signature : Blob

/-- A judgment within a verdict (GP eq. `disputesextrinsics`): validity, judge index, signature. -/
structure Judgment where
  valid : Bool
  index : Nat
  signature : Blob

/-- A verdict: the report hash $r$, the epoch index $a$ and the judgments $\mathbf{j}$. -/
structure Verdict where
  target : Hash
  age : Nat
  votes : List Judgment

/-- A culprit $(r, f, s)$: report hash, offender's Ed25519 key, signature. -/
structure Culprit where
  target : Hash
  key : Hash
  signature : Blob

/-- A fault $(r, v, f, s)$: report hash, validity, offender's Ed25519 key, signature. -/
structure Fault where
  target : Hash
  valid : Bool
  key : Hash
  signature : Blob

/-- The disputes extrinsic $\mathbf{E}_D = (\mathbf{v}, \mathbf{c}, \mathbf{f})$
    (GP eq. `disputesextrinsics`). -/
structure Disputes where
  verdicts : List Verdict
  culprits : List Culprit
  faults : List Fault

/-- $\mathcal{E}(\bot) = [0]$, $\mathcal{E}(\top) = [1]$ (GP v0.8.1 Appendix C; v0.8.0 left it implicit). -/
def encodeBool (b : Bool) : List UInt8 := nat (if b then 1 else 0)

/-- $\mathcal{E}$ of a bit sequence (GP (C) "Bit Sequence Encoding"): $\lceil n/8 \rceil$ octets, packed least
    significant bit first, the padding bits of the last octet zero. -/
def encodeBits (bs : List Bool) : List UInt8 :=
  (List.range ((bs.length + 7) / 8)).map fun k =>
    UInt8.ofNat ((List.range 8).foldl (fun acc i => acc + (if bs.getD (8 * k + i) false then 2 ^ i else 0)) 0)

/-- $\mathcal{E}_T(\mathbf{E}_T) = \mathcal{E}(\updownarrow[(\mathcal{E}_1(r), p) \mid (r, p) \leftarrow \mathbf{E}_T])$
    (GP Appendix C). -/
def encodeTickets (xs : List TicketProof) : List UInt8 :=
  varSeq (fun t => fixed 1 t.attempt ++ blob t.proof) xs

/-- $\mathcal{E}_P(\mathbf{E}_P) = \mathcal{E}(\updownarrow[(\mathcal{E}_4(s), \updownarrow\mathbf{p}) \mid (s, \mathbf{p}) \leftarrow \mathbf{E}_P])$
    (GP Appendix C). -/
def encodePreimages (xs : List Preimage) : List UInt8 :=
  varSeq (fun p => fixed 4 p.requester ++ var p.blob) xs

/-- $\mathcal{E}_C(a) = \mathcal{E}(\updownarrow[(\mathcal{E}_2(v), s) \mid (v, s) \leftarrow a])$, the credential
    encoding (GP v0.8.1 eq. 5.7 and Appendix C; #560 introduced it). -/
def encodeCredential (a : List (Nat × Blob)) : List UInt8 :=
  varSeq (fun (v, s) => fixed 2 v ++ blob s) a

/-- $\mathcal{E}(g \in \mathbb{G}) = \mathcal{E}(\mathbf{r}, \mathcal{E}_4(t), \mathcal{E}_C(a))$ (GP v0.8.1 Appendix C). -/
def Guarantee.encode (g : Guarantee) : List UInt8 :=
  g.report.encode ++ fixed 4 g.slot ++ encodeCredential g.credential

/-- $\mathcal{E}_G(\mathbf{E}_G) = \mathcal{E}(\updownarrow\mathbf{E}_G)$ (GP Appendix C). -/
def encodeGuarantees (xs : List Guarantee) : List UInt8 := varSeq Guarantee.encode xs

/-- $\mathcal{E}_A(\mathbf{E}_A) = \mathcal{E}(\updownarrow[(f, \mathcal{E}_2(v), s) \mid (f, v, s) \leftarrow \mathbf{E}_A])$
    (GP v0.8.1 Appendix C). -/
def encodeAssurances (xs : List Assurance) : List UInt8 :=
  varSeq (fun a => encodeBits a.bitfield ++ fixed 2 a.assurer ++ blob a.signature) xs

/-- A judgment $(v, \mathcal{E}_2(i), s)$ within $\mathcal{E}_D$. -/
def Judgment.encode (j : Judgment) : List UInt8 := encodeBool j.valid ++ fixed 2 j.index ++ blob j.signature

/-- $\mathcal{E}_D((\mathbf{v}, \mathbf{c}, \mathbf{f})) = \mathcal{E}(\updownarrow[(r, \mathcal{E}_4(a), \updownarrow[(v, \mathcal{E}_2(i), s) \mid \ldots \leftarrow \mathbf{j}]) \mid \ldots \leftarrow \mathbf{v}], \updownarrow\mathbf{c}, \updownarrow\mathbf{f})$
    (GP Appendix C). Each verdict's judgments carry a length prefix. -/
def Disputes.encode (d : Disputes) : List UInt8 :=
  varSeq (fun v => blob v.target ++ fixed 4 v.age ++ varSeq Judgment.encode v.votes) d.verdicts ++
    varSeq (fun c => blob c.target ++ blob c.key ++ blob c.signature) d.culprits ++
    varSeq (fun f => blob f.target ++ encodeBool f.valid ++ blob f.key ++ blob f.signature) d.faults

/-- The extrinsic $\mathbf{E} = (\mathbf{E}_T, \mathbf{E}_P, \mathbf{E}_G, \mathbf{E}_A, \mathbf{E}_D)$
    (GP v0.8.1 eq. `extrinsic`, reordered by #575 to match $\mathcal{E}(\mathbf{B})$; the fields are
    named, so the order of this structure's fields does not matter). -/
structure Extrinsic where
  tickets : List TicketProof
  disputes : Disputes
  preimages : List Preimage
  assurances : List Assurance
  guarantees : List Guarantee

/-- $\mathcal{E}$ of the extrinsic, in the order $\mathcal{E}(\mathbf{B})$ uses: $\mathcal{E}_T$,
    $\mathcal{E}_P$, $\mathcal{E}_G$, $\mathcal{E}_A$, $\mathcal{E}_D$ (GP Appendix C). -/
def Extrinsic.encode (x : Extrinsic) : List UInt8 :=
  encodeTickets x.tickets ++ encodePreimages x.preimages ++ encodeGuarantees x.guarantees ++
    encodeAssurances x.assurances ++ x.disputes.encode

/-- A block $\mathbf{B} = (\mathbf{H}, \mathbf{E})$ (GP eq. `block`). -/
structure Block where
  header : Header
  extrinsic : Extrinsic

/-- $\mathcal{E}(\mathbf{B}) = \mathcal{E}(\mathbf{H}, \mathcal{E}_T(\mathbf{E}_T), \mathcal{E}_P(\mathbf{E}_P), \mathcal{E}_G(\mathbf{E}_G), \mathcal{E}_A(\mathbf{E}_A), \mathcal{E}_D(\mathbf{E}_D))$
    (GP Appendix C). -/
def Block.encode (b : Block) : List UInt8 := b.header.encode ++ b.extrinsic.encode

/-! ## Decoders -/

open Decoder

/-- $\mathcal{E}^{-1}$ for $\mathbb{T}$. -/
def Ticket.decode : Decoder Ticket := do
  return { id := ← bytes hashSize, attempt := ← fixed 1 }

/-- $\mathcal{E}_E^{-1}$. -/
def decodeEpochMark : Decoder (Option EpochMark) := do
  match ← nat with
  | 0 => return none
  | 1 => return some { entropy := ← bytes hashSize, ticketsEntropy := ← bytes hashSize,
                       validators := ← varSeq (do return (← bytes keySize, ← bytes keySize)) }
  | k => fail s!"bad epoch-marker discriminator {k}"

/-- $\mathcal{E}^{-1}$ for $\mathbf{H}$; the winning-tickets marker holds $\mathsf{E}$ tickets. -/
def Header.decode (p : Params) : Decoder Header := do
  return { parent := ← bytes hashSize, priorStateRoot := ← bytes hashSize,
           extrinsicHash := ← bytes hashSize, slot := ← fixed 4, epochMark := ← decodeEpochMark,
           winnersMark := ← opt (seqN p.epochLen Ticket.decode), authorIndex := ← fixed 2,
           vrfSig := ← bytes bsSigSize, offendersMark := ← varSeq (bytes keySize),
           sealSig := ← bytes bsSigSize }

/-- $\mathcal{E}_T^{-1}$. -/
def decodeTickets : Decoder (List TicketProof) :=
  varSeq do return { attempt := ← fixed 1, proof := ← bytes ringProofSize }

/-- $\mathcal{E}_P^{-1}$. -/
def decodePreimages : Decoder (List Preimage) :=
  varSeq do return { requester := ← fixed 4, blob := ← var }

/-- $\mathcal{E}^{-1}$ for $\mathbb{G}$. -/
def Guarantee.decode : Decoder Guarantee := do
  return { report := ← WorkReport.decode, slot := ← fixed 4,
           credential := ← varSeq (do return (← fixed 2, ← bytes edSigSize)) }

/-- $\mathcal{E}_G^{-1}$. -/
def decodeGuarantees : Decoder (List Guarantee) := varSeq Guarantee.decode

/-- $\mathcal{E}_A^{-1}$; each bit field has $\mathsf{C}$ bits. -/
def decodeAssurances (p : Params) : Decoder (List Assurance) :=
  varSeq do return { bitfield := ← bits p.coreCount, assurer := ← fixed 2,
                     signature := ← bytes edSigSize }

/-- $\mathcal{E}_D^{-1}$. -/
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

/-- $\mathcal{E}^{-1}$ for $\mathbf{E}$, in the order of $\mathcal{E}(\mathbf{B})$. -/
def Extrinsic.decode (p : Params) : Decoder Extrinsic := do
  let tickets ← decodeTickets
  let preimages ← decodePreimages
  let guarantees ← decodeGuarantees
  let assurances ← decodeAssurances p
  let disputes ← Disputes.decode
  return { tickets, disputes, preimages, assurances, guarantees }

/-- $\mathcal{E}^{-1}$ for $\mathbf{B}$. -/
def Block.decode (p : Params) : Decoder Block := do
  return { header := ← Header.decode p, extrinsic := ← Extrinsic.decode p }

end JAM
