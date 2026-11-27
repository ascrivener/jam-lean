import JAM.Fast.Blake2b
import JAM.Blake2b
import JAM.Block
import JAM.Crypto
import JAM.Params

/-!
# Safrole: block production and chain growth (GP v0.8.1 §6, `sec:blockproduction`)

The Safrole state $\gamma = (\gamma_P, \gamma_Z, \gamma_S, \gamma_A)$
(eq. `consensusstatecomposition`) together with the timeslot $\tau$ (eq. `timeslotindex`), the
entropy $\eta$ (eq. `entropycomposition`) and the validator key sequences $\iota$, $\gamma_P$,
$\kappa$ and $\lambda$ (eq. `validatorkeys`), and their transition:

* key rotation with the offenders filter $\Phi$ and the new ring root $\gamma'_Z$
  (eq. `blacklistfilter`);
* the entropy accumulator $\eta'_0$ and its rotation into $\eta_1$, $\eta_2$, $\eta_3$ (§6.4);
* the slot-sealer sequence $\gamma'_S$ with the outside-in sequencer $Z$ and the fallback $F$
  (eqs. `slotkeysequence`, `fallbackkeysequence`);
* the epoch and winning-tickets markers $\mathbf{H}_E$ and $\mathbf{H}_W$ (eqs. `epochmarker`,
  `winningticketsmarker`);
* the tickets extrinsic $\mathbf{E}_T$ and the ticket accumulator $\gamma'_A$ (§6.7,
  eqs. `ticketsextrinsic`, `enforceticketlimit`).

The seal and entropy-source conditions on the header (eqs. `ticketconditiontrue`,
`ticketconditionfalse`, `vrfsigcheck`) are `sealValid`; the transition takes
$\mathcal{Y}(\mathbf{H}_V)$, the entropy source's VRF output, as an input.

Cryptography enters through `JAM.Crypto`: the ring root $O$, Ring VRF verification and output for
tickets, and singly-contextualized VRF verification and output for the seal (Thin VRF in GP v0.8.1
Appendix G; the interface $\overset{\backsim}{\mathbb{V}}{}_k^{m}\langle c \rangle \subset
\mathbb{B}_{96}$ is unchanged from v0.8.0).

The paper states the extrinsic's conditions but names no errors and gives no order between them.
The errors here are the test vectors' names. They are checked in this order: the timeslot (§5,
eq. `timeslotindex`'s $\mathbf{H}_T > P(\mathbf{H})_T$ of the header), the extrinsic's length (eq.
`enforceticketlimit`), every ticket's entry index, then every ticket's proof (eq. `ticketsextrinsic`), the
ordering of $\mathbf{n}$, its disjointness from $\gamma_A$, and $\mathbf{n} \subseteq \gamma'_A$.
-/

namespace JAM

/-- A validator key $k \in \mathbb{K} = \mathbb{B}_{336}$ (GP §6.3). -/
abbrev ValidatorKey := List UInt8

namespace ValidatorKey
/-- $k_b = k_{0 \cdots +32}$, the Bandersnatch key. -/
def bs (k : ValidatorKey) : List UInt8 := k.take 32
/-- $k_e = k_{32 \cdots +32}$, the Ed25519 key. -/
def ed (k : ValidatorKey) : List UInt8 := (k.drop 32).take 32
/-- The null key $\mathbb{K}_0$ of $\Phi$ (GP v0.8.1 eq. `nullvalkey`): zero except for
    its Ed25519 component $[2, 0, \dots]$. -/
def null : ValidatorKey := nullValidatorKey
end ValidatorKey

/-- $\gamma_S \in [\![ \mathbb{T} ]\!]_{\mathsf{E}} \cup [\![ \overset{\backsim}{\mathbb{H}} ]\!]_{\mathsf{E}}$
    (GP eq. `ticketaccumulatorsealticketsspec`): a full complement of tickets, or the fallback
    Bandersnatch keys. -/
inductive SealKeys where
  | tickets (t : List Ticket)
  | keys (k : List (List UInt8))
  deriving Inhabited

/-- The state Safrole reads and writes: $\tau$, $\eta$, $\lambda$, $\kappa$, $\gamma_P$, $\iota$, $\gamma_A$, $\gamma_S$ and $\gamma_Z$. -/
structure SafroleState where
  /-- $\tau$, the most recent block's timeslot. -/
  tau : Nat
  /-- $\eta \in [\![\mathbb{H}]\!]_4$. -/
  eta : List (List UInt8)
  /-- $\lambda$, the previous epoch's validators. -/
  prev : List ValidatorKey
  /-- $\kappa$, the active validators. -/
  active : List ValidatorKey
  /-- $\gamma_P$, the pending validators. -/
  pending : List ValidatorKey
  /-- $\iota$, the staging validators. -/
  staging : List ValidatorKey
  /-- $\gamma_A$, the ticket accumulator. -/
  accumulator : List Ticket
  /-- $\gamma_S$, the slot-sealer sequence. -/
  sealKeys : SealKeys
  /-- $\gamma_Z$, the ring root of $\gamma_P$'s Bandersnatch keys. -/
  ringRoot : List UInt8
  deriving Inhabited

/-- What the transition reads from the block and from the rest of the state. -/
structure SafroleInput where
  /-- $\mathbf{H}_T$. -/
  slot : Nat
  /-- $\mathcal{Y}(\mathbf{H}_V)$, the entropy source's VRF output (GP eq. `vrfsigcheck`). -/
  entropy : List UInt8
  /-- $\mathbf{E}_T$. -/
  tickets : List TicketProof
  /-- $\psi'_O$, the posterior offenders (Ed25519 keys, §10). -/
  offenders : List (List UInt8)

/-- The markers the transition produces: $\mathbf{H}_E$ and $\mathbf{H}_W$. -/
structure SafroleOutput where
  epochMark : Option EpochMark
  ticketsMark : Option (List Ticket)

/-- Why a block is invalid for Safrole. The paper names no errors; these are the vectors'. -/
inductive SafroleError where
  /-- $\mathbf{H}_T \le \tau$. -/
  | badSlot
  /-- $|\mathbf{E}_T|$ exceeds the bound of eq. `enforceticketlimit` (0 in the epoch's tail). -/
  | unexpectedTicket
  /-- $\mathbf{n}$ is not ordered by identifier without duplicates. -/
  | badTicketOrder
  /-- A proof is not in
      $\mathring{\mathbb{V}}{}^{[]}_{\gamma'_Z}\langle \mathsf{X}_T \frown \eta'_2 \mathbin{+\!\!+} e
      \rangle$, with $\mathsf{X}_T$ = `$jam_ticket_seal`. -/
  | badTicketProof
  /-- An entry index is not in $\mathbb{N}_n$. -/
  | badTicketAttempt
  /-- A new identifier is already in $\gamma_A$. -/
  | duplicateTicket
  /-- A new ticket is not in $\gamma'_A$ ($\mathbf{n} \not\subseteq \gamma'_A$). -/
  | uselessTicket
  deriving BEq, Repr

/-- `$jam_ticket_seal` (GP §6.4, $\mathsf{X}_T$). -/
def Xticket : List UInt8 := contextString "$jam_ticket_seal"
/-- `$jam_fallback_seal` (GP §6.4, $\mathsf{X}_F$). -/
def Xfallback : List UInt8 := contextString "$jam_fallback_seal"
/-- `$jam_entropy` (GP §6.4, $\mathsf{X}_E$). -/
def Xentropy : List UInt8 := contextString "$jam_entropy"

#guard Xticket = "jam_ticket_seal".toUTF8.toList
#guard Xentropy = "jam_entropy".toUTF8.toList

/-- The context of a ticket's ring proof, and of a ticket-sealed block's seal:
    $\mathsf{X}_T \frown \eta \mathbin{+\!\!+} e$ with $\mathsf{X}_T$ = `$jam_ticket_seal` (GP eq. (6.31),
    `ticketsextrinsic`, appends $e$ as an element), the entry index as one octet. The paper does not define the encoding ([`docs/upstream-candidates.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues), 31).
    $e < n = \lceil 2\mathsf{E}/|\gamma'_P| \rceil$, and one octet holds every such $e$ exactly when $n \le 256$,
    i.e. when $2\mathsf{E} \le 256 \cdot |\gamma'_P|$; this holds for the paper's $|\gamma'_P| \ge 6$ (eq. `valcount`)
    whenever $\mathsf{E} \le 768$, so for the full ($\mathsf{E} = 600$) and tiny ($\mathsf{E} = 12$) chains (`safrole_attempt_fits`, `attempt_fits_of_six`
    in `JAM/Theorems/Safrole.lean`). For smaller $\gamma'_P$ `UInt8.ofNat` would reduce $e$ mod 256. -/
def ticketContext (eta : List UInt8) (attempt : Nat) : List UInt8 :=
  Xticket ++ eta ++ [UInt8.ofNat attempt]

/-- $\mathcal{H}$, Blake2b-256 on octet lists. -/
def blake (m : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨m.toArray⟩).toList

/-- The order on identifiers: hashes compared as octet sequences, lexicographically (for hashes of
    equal length this is the order of their big-endian values). -/
def octetLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && octetLt as bs)

/-- $\Phi(\mathbf{k})$ (GP v0.8.1 eq. `blacklistfilter`): keys whose Ed25519 component is an
    offender become the null key $\mathbb{K}_0$ (eq. `nullvalkey`). -/
def offendersFilter (offenders : List (List UInt8)) (k : List ValidatorKey) : List ValidatorKey :=
  k.map fun v => if offenders.contains v.ed then ValidatorKey.null else v

-- Regression tests (GP v0.8.1 #543): 𝕂^∅ has 336 octets, is zero but for its Ed25519 component
-- [2, 0, …], and Φ replaces an offender's key by it.
#guard ValidatorKey.null.length = 336
#guard ValidatorKey.null.ed = 2 :: List.replicate 31 0
#guard ValidatorKey.null.bs = List.replicate 32 0
#guard (ValidatorKey.null.drop 64).all (· == 0)
#guard offendersFilter [List.replicate 32 7]
    [List.replicate 32 1 ++ List.replicate 32 7 ++ List.replicate 272 1, List.replicate 336 1] =
  [ValidatorKey.null, List.replicate 336 1]

/-- $Z$, the outside-in sequencer (GP §6.5, eq. (6.27)):
    $[\mathbf{s}_0, \mathbf{s}_{|\mathbf{s}|-1}, \mathbf{s}_1, \mathbf{s}_{|\mathbf{s}|-2}, \dots]$. -/
def outsideIn {α : Type} (s : List α) : List α :=
  (List.range s.length).filterMap fun i => if i % 2 = 0 then s[i / 2]? else s[s.length - 1 - i / 2]?

/-- $F(r, \mathbf{k})$, the fallback key sequence (GP eq. (6.28), `fallbackkeysequence`):
    $\left(\mathbf{k}^{\circlearrowleft}_{\mathcal{E}_4^{-1}(\mathcal{H}(r \frown \mathcal{E}_4(i))_{\dots 4})}\right)_b$ for $i \in \mathbb{N}_{\mathsf{E}}$. -/
def fallbackKeys (params : Params) (r : List UInt8) (k : List ValidatorKey) : List (List UInt8) :=
  (List.range params.epochLen).map fun i =>
    let j := PVM.Num.decodeLE ((blake (r ++ PVM.Num.encodeLE 4 i)).take 4)
    (k.getD (j % k.length) ValidatorKey.null).bs

/-- The entry-index bound $n = \lceil 2\mathsf{E} / |\gamma'_P| \rceil$ (GP eq. (6.31), `ticketsextrinsic`). -/
def maxAttempts (params : Params) (pending' : List ValidatorKey) : Nat :=
  (2 * params.epochLen + pending'.length - 1) / pending'.length

/-- The tickets are sorted by identifier with no two equal. -/
def strictlyOrdered : List Ticket → Bool
  | a :: b :: rest => octetLt a.id.toList b.id.toList && strictlyOrdered (b :: rest)
  | _ => true

/-- The Safrole transition (GP §6). On success it returns the posterior state and the markers
    $\mathbf{H}_E$ and $\mathbf{H}_W$. -/
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
    `ticketconditionfalse`, `vrfsigcheck`), for the posterior $\gamma'_S$ and $\eta'_3$ and the author's
    Bandersnatch key $\mathbf{H}_A = (\kappa'_{\mathbf{H}_I})_b$. $\mathcal{Y}(\mathbf{H}_V)$ is then the transition's `entropy` input. -/
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
