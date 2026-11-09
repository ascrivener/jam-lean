import JAM.Blake2b
import JAM.Block
import JAM.Crypto
import JAM.Params

/-!
# Safrole: block production and chain growth (GP v0.8.0 §6, `sec:blockproduction`)

The Safrole state γ = (γ_P, γ_Z, γ_S, γ_A) (eq. `consensusstatecomposition`) together with the
timeslot τ (eq. `timeslotindex`), the entropy η (eq. `entropycomposition`) and the validator key
sequences ι, γ_P, κ and λ (eq. `validatorkeys`), and their transition:

* key rotation with the offenders filter Φ and the new ring root γ_Z' (eq. `blacklistfilter`);
* the entropy accumulator η_0' and its rotation into η_1, η_2, η_3 (§6.4);
* the slot-sealer sequence γ_S' with the outside-in sequencer Z and the fallback F
  (eqs. `slotkeysequence`, `fallbackkeysequence`);
* the epoch and winning-tickets markers H_E and H_W (eqs. `epochmarker`, `winningticketsmarker`);
* the tickets extrinsic E_T and the ticket accumulator γ_A' (§6.7, eqs. `ticketsextrinsic`,
  `enforceticketlimit`).

The seal and entropy-source conditions on the header (eqs. `ticketconditiontrue`,
`ticketconditionfalse`, `vrfsigcheck`) are `sealValid`; the transition takes Y(H_V), the entropy
source's VRF output, as an input.

Cryptography enters through `JAM.Crypto`: the ring root O, Ring VRF verification and output for
tickets, and IETF VRF verification and output for the seal.

The paper states the extrinsic's conditions but names no errors and gives no order between them.
The errors here are the test vectors' names. They are checked in this order: the timeslot (§5,
eq. `timeslotindex`'s H_T > P(H)_T of the header), the extrinsic's length (eq.
`enforceticketlimit`), each ticket's entry index and then its proof (eq. `ticketsextrinsic`), the
ordering of **n**, its disjointness from γ_A, and **n** ⊆ γ_A'.
-/

namespace JAM

/-- A validator key k ∈ 𝕂 = 𝔹_336 (GP §6.3). -/
abbrev ValidatorKey := List UInt8

namespace ValidatorKey
/-- k_b = k_{0⋅⋅⋅+32}, the Bandersnatch key. -/
def bs (k : ValidatorKey) : List UInt8 := k.take 32
/-- k_e = k_{32⋅⋅⋅+32}, the Ed25519 key. -/
def ed (k : ValidatorKey) : List UInt8 := (k.drop 32).take 32
/-- The null key [0, 0, …] of Φ. -/
def null : ValidatorKey := List.replicate 336 0
end ValidatorKey

/-- γ_S ∈ ⟦𝕋⟧_𝖤 ∪ ⟦ℍ_B⟧_𝖤 (GP eq. `ticketaccumulatorsealticketsspec`): a full complement of tickets,
    or the fallback Bandersnatch keys. -/
inductive SealKeys where
  | tickets (t : List Ticket)
  | keys (k : List (List UInt8))
  deriving Inhabited

/-- The state Safrole reads and writes: τ, η, λ, κ, γ_P, ι, γ_A, γ_S and γ_Z. -/
structure SafroleState where
  /-- τ, the most recent block's timeslot. -/
  tau : Nat
  /-- η ∈ ⟦ℍ⟧_4. -/
  eta : List (List UInt8)
  /-- λ, the previous epoch's validators. -/
  prev : List ValidatorKey
  /-- κ, the active validators. -/
  active : List ValidatorKey
  /-- γ_P, the pending validators. -/
  pending : List ValidatorKey
  /-- ι, the staging validators. -/
  staging : List ValidatorKey
  /-- γ_A, the ticket accumulator. -/
  accumulator : List Ticket
  /-- γ_S, the slot-sealer sequence. -/
  sealKeys : SealKeys
  /-- γ_Z, the ring root of γ_P's Bandersnatch keys. -/
  ringRoot : List UInt8
  deriving Inhabited

/-- What the transition reads from the block and from the rest of the state. -/
structure SafroleInput where
  /-- H_T. -/
  slot : Nat
  /-- Y(H_V), the entropy source's VRF output (GP eq. `vrfsigcheck`). -/
  entropy : List UInt8
  /-- E_T. -/
  tickets : List TicketProof
  /-- ψ_O', the posterior offenders (Ed25519 keys, §10). -/
  offenders : List (List UInt8)

/-- The markers the transition produces: H_E and H_W. -/
structure SafroleOutput where
  epochMark : Option EpochMark
  ticketsMark : Option (List Ticket)

/-- Why a block is invalid for Safrole. The paper names no errors; these are the vectors'. -/
inductive SafroleError where
  /-- H_T ≤ τ. -/
  | badSlot
  /-- |E_T| exceeds the bound of eq. `enforceticketlimit` (0 in the epoch's tail). -/
  | unexpectedTicket
  /-- **n** is not ordered by identifier without duplicates. -/
  | badTicketOrder
  /-- A proof is not in 𝔹̄°_{γ_Z'}⟨$jam_ticket_seal ⌢ η_2' ⌢ e⟩⟨[]⟩. -/
  | badTicketProof
  /-- An entry index is not in ℕ_n. -/
  | badTicketAttempt
  /-- A new identifier is already in γ_A. -/
  | duplicateTicket
  /-- A new ticket is not in γ_A' (**n** ⊄ γ_A'). -/
  | uselessTicket
  deriving BEq, Repr

/-- $jam_ticket_seal (GP §6.4, X_T). -/
def Xticket : List UInt8 := contextString "$jam_ticket_seal"
/-- $jam_fallback_seal (GP §6.4, X_F). -/
def Xfallback : List UInt8 := contextString "$jam_fallback_seal"
/-- $jam_entropy (GP §6.4, X_E). -/
def Xentropy : List UInt8 := contextString "$jam_entropy"

/-- The context of a ticket's ring proof, and of a ticket-sealed block's seal:
    $jam_ticket_seal ⌢ η ⌢ e, the entry index appended as one octet (e < n ≤ 2𝖤/6 + 1). -/
def ticketContext (eta : List UInt8) (attempt : Nat) : List UInt8 :=
  Xticket ++ eta ++ [UInt8.ofNat attempt]

/-- ℋ, Blake2b-256 on octet lists. -/
def blake (m : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨m.toArray⟩).toList

/-- The order on identifiers: hashes compared as octet sequences, lexicographically (for hashes of
    equal length this is the order of their big-endian values). -/
def octetLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && octetLt as bs)

/-- Φ(**k**) (GP eq. `blacklistfilter`): keys whose Ed25519 component is an offender become the
    null key. -/
def offendersFilter (offenders : List (List UInt8)) (k : List ValidatorKey) : List ValidatorKey :=
  k.map fun v => if offenders.contains v.ed then ValidatorKey.null else v

/-- Z, the outside-in sequencer (GP §6.5): [s_0, s_{|s|−1}, s_1, s_{|s|−2}, …]. -/
def outsideIn {α : Type} (s : List α) : List α :=
  (List.range s.length).filterMap fun i => if i % 2 = 0 then s[i / 2]? else s[s.length - 1 - i / 2]?

/-- F(r, **k**), the fallback key sequence (GP eq. `fallbackkeysequence`):
    k_{ℰ_4⁻¹(ℋ(r ⌢ ℰ_4(i))_{⋅⋅⋅4}) mod |k|, b} for i ∈ ℕ_𝖤. -/
def fallbackKeys (params : Params) (r : List UInt8) (k : List ValidatorKey) : List (List UInt8) :=
  (List.range params.epochLen).map fun i =>
    let j := PVM.Num.decodeLE ((blake (r ++ PVM.Num.encodeLE 4 i)).take 4)
    (k.getD (j % k.length) ValidatorKey.null).bs

/-- The entry-index bound n = ⌈2𝖤 / |γ_P'|⌉ (GP eq. `ticketsextrinsic`). -/
def maxAttempts (params : Params) (pending' : List ValidatorKey) : Nat :=
  (2 * params.epochLen + pending'.length - 1) / pending'.length

/-- The tickets are sorted by identifier with no two equal. -/
def strictlyOrdered : List Ticket → Bool
  | a :: b :: rest => octetLt a.id.toList b.id.toList && strictlyOrdered (b :: rest)
  | _ => true

/-- The Safrole transition (GP §6). On success it returns the posterior state and the markers
    H_E and H_W. -/
def safrole (params : Params) (c : Crypto) (s : SafroleState) (i : SafroleInput) :
    Except SafroleError (SafroleState × SafroleOutput) := do
  let E := params.epochLen
  let Y := params.epochTailStart
  -- §5: the timeslot strictly increases; τ' = H_T (eq. `timeslotindex`).
  if i.slot ≤ s.tau then throw .badSlot
  let (e, m) := (s.tau / E, s.tau % E)
  let (e', m') := (i.slot / E, i.slot % E)
  let change := e' > e
  -- Key rotation (§6.3).
  let (pending', active', prev', ringRoot') :=
    if change then
      let p := offendersFilter i.offenders s.staging
      (p, s.pending, s.active, c.bsRingRoot (p.map ValidatorKey.bs))
    else (s.pending, s.active, s.prev, s.ringRoot)
  -- Entropy (§6.4).
  let eta := fun (k : Nat) => s.eta.getD k []
  let eta0' := blake (eta 0 ++ i.entropy)
  let (eta1', eta2', eta3') := if change then (eta 0, eta 1, eta 2) else (eta 1, eta 2, eta 3)
  -- The tickets extrinsic (§6.7).
  if i.tickets.length > (if m' < Y then params.maxBlockTickets else 0) then throw .unexpectedTicket
  let n := maxAttempts params pending'
  for t in i.tickets do
    if t.attempt ≥ n then throw .badTicketAttempt
  for t in i.tickets do
    if !c.bsRingVerify ringRoot' (ticketContext eta2' t.attempt) [] t.proof.toList then
      throw .badTicketProof
  -- **n** (§6.7)
  let new := i.tickets.map fun t => ({ id := ⟨(c.bsRingOut t.proof.toList).toArray⟩, attempt := t.attempt } : Ticket)
  if !strictlyOrdered new then throw .badTicketOrder
  let sameId (a b : Ticket) : Bool := a.id.toList == b.id.toList
  if new.any fun t => s.accumulator.any (sameId t) then throw .duplicateTicket
  let base := if change then [] else s.accumulator
  let acc' := ((new ++ base).mergeSort fun a b => !octetLt b.id.toList a.id.toList).take E
  if !new.all fun t => acc'.any (sameId t) then throw .uselessTicket
  -- The slot-sealer sequence (eq. `slotkeysequence`).
  let sealKeys' :=
    if e' = e + 1 ∧ m ≥ Y ∧ s.accumulator.length = E then .tickets (outsideIn s.accumulator)
    else if e' = e then s.sealKeys
    else .keys (fallbackKeys params eta2' active')
  -- The markers (eqs. `epochmarker`, `winningticketsmarker`).
  let epochMark := if change then
      some { entropy := ⟨(eta 0).toArray⟩, ticketsEntropy := ⟨(eta 1).toArray⟩,
             validators := pending'.map fun k => (⟨k.bs.toArray⟩, ⟨k.ed.toArray⟩) }
    else none
  let ticketsMark :=
    if e' = e ∧ m < Y ∧ Y ≤ m' ∧ s.accumulator.length = E then some (outsideIn s.accumulator)
    else none
  return ({ tau := i.slot, eta := [eta0', eta1', eta2', eta3'], prev := prev', active := active',
            pending := pending', staging := s.staging, accumulator := acc', sealKeys := sealKeys',
            ringRoot := ringRoot' },
          { epochMark, ticketsMark })

/-- The header's seal and entropy-source conditions (GP eqs. `ticketconditiontrue`,
    `ticketconditionfalse`, `vrfsigcheck`), for the posterior γ_S' and η_3' and the author's
    Bandersnatch key H_A = (κ'_{H_I})_b. Y(H_V) is then the transition's `entropy` input. -/
def sealValid (params : Params) (c : Crypto) (sealKeys' : SealKeys) (eta3' : List UInt8)
    (author : List UInt8) (h : Header) : Bool :=
  let sealSig := h.sealSig.toList
  let sealOk := match sealKeys' with
    | .tickets t =>
      match t[h.slot % params.epochLen]? with
      | some tk => tk.id.toList == c.bsOut sealSig &&
          c.bsVerify author (ticketContext eta3' tk.attempt) h.encodeUnsigned sealSig
      | none => false
    | .keys k =>
      k.getD (h.slot % params.epochLen) [] == author &&
        c.bsVerify author (Xfallback ++ eta3') h.encodeUnsigned sealSig
  sealOk && c.bsVerify author (Xentropy ++ c.bsOut sealSig) [] h.vrfSig.toList

end JAM
