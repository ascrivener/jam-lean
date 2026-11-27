import JAM.Fast.Trie
import JAM.Safrole
import JAM.Disputes
import JAM.History
import JAM.Statistics
import JAM.Accumulation
import JAM.Trie

/-!
# The state $\sigma$ and its serialization $T(\sigma)$ (GP v0.8.1 §4.2, Appendix D)

$\sigma \equiv (\alpha, \beta, \theta, \gamma, \delta, \eta, \iota, \kappa, \lambda, \rho, \tau, \phi, \chi, \psi, \pi, \omega, \xi)$ (GP eq. `statecomposition`), with
$\gamma \equiv (\gamma_P, \gamma_Z, \gamma_S, \gamma_A)$ (eq. `gammaspec`), $\chi \equiv (\chi_m, \chi_v, \chi_r, \chi_\mathbf{a}, \chi_\mathbf{z})$ (eq. `privilegesspec`)
and $\pi \equiv (\pi_V, \pi_L, \pi_C, \pi_S)$ (§13).

The components are stored in the types the state-transition functions already use; `State` adds
only the projections each transition needs. `serialize` is $T$ (GP §D.1) and `root` is $M_\sigma = M(T(\sigma))$
(GP §D.2).
-/

namespace JAM

/-- The state $\sigma$ (GP eq. `statecomposition`). -/
structure State where
  /-- $\alpha$, the authorizer pools: $\mathsf{C}$ sequences of at most $\mathsf{O}$ hashes. -/
  authPools : List (List (List UInt8))
  /-- $\phi$, the authorizer queues: $\mathsf{C}$ sequences of $\mathsf{Q}$ hashes. -/
  authQueue : List (List (List UInt8))
  /-- $\beta = (\beta_H, \beta_B)$, recent history and the accumulation-output belt. -/
  recent : Recent
  /-- $\theta$, the most recent accumulation outputs (service, hash), in order. -/
  lastAccOut : List (Nat × List UInt8)
  /-- $\gamma_P$, the pending validators. -/
  pending : List ValidatorKey
  /-- $\gamma_Z$, the ring root. -/
  ringRoot : List UInt8
  /-- $\gamma_S$, the slot-sealer sequence. -/
  sealKeys : SealKeys
  /-- $\gamma_A$, the ticket accumulator. -/
  accumulator : List Ticket
  /-- $\delta$, the service accounts. -/
  accounts : Accounts
  /-- $\eta \in [\![ \mathbb{H} ]\!]_4$. -/
  eta : List (List UInt8)
  /-- $\iota$, the staging validators. -/
  staging : List ValidatorKey
  /-- $\kappa$, the active validators. -/
  active : List ValidatorKey
  /-- $\lambda$, the previous epoch's validators. -/
  prev : List ValidatorKey
  /-- $\rho$, the availability assignments. -/
  avail : AvailAssignments
  /-- $\tau$, the most recent block's timeslot. -/
  tau : Nat
  /-- $\chi_m$, the manager service. -/
  manager : Nat
  /-- $\chi_\mathbf{a}$, the assigner of each core. -/
  assigners : List Nat
  /-- $\chi_v$, the delegator service. -/
  delegator : Nat
  /-- $\chi_r$, the registrar service. -/
  registrar : Nat
  /-- $\chi_\mathbf{z}$, the always-accumulate services and their gas. -/
  alwaysAcc : Std.ExtTreeMap Nat Nat
  /-- $\psi$, the disputes state. -/
  disputes : DisputesState
  /-- $\pi_V$, this epoch's validator statistics. -/
  valStats : List ValidatorRecord
  /-- $\pi_L$, the previous epoch's validator statistics. -/
  valStatsLast : List ValidatorRecord
  /-- $\pi_C$, the core statistics. -/
  coreStats : List CoreRecord
  /-- $\pi_S$, the service statistics. -/
  serviceStats : Std.ExtTreeMap Nat ServiceRecord
  /-- $\omega$, the accumulation ready queue: $\mathsf{E}$ sequences of (report, dependencies). -/
  ready : List (List ReadyEntry)
  /-- $\xi$, the accumulated package hashes of the last $\mathsf{E}$ blocks. -/
  accumulated : List OctetSet

namespace State

/-- The part of $\sigma$ Safrole reads and writes. -/
def safrole (s : State) : SafroleState :=
  { tau := s.tau, eta := s.eta, prev := s.prev, active := s.active, pending := s.pending,
    staging := s.staging, accumulator := s.accumulator, sealKeys := s.sealKeys,
    ringRoot := s.ringRoot }

/-- The partial state $(\delta, \iota, \phi, \chi)$ accumulation starts from (GP eq. `partialstate`). -/
def partialState (s : State) : PartialState :=
  { accounts := s.accounts, staging := s.staging, authQueue := s.authQueue, manager := s.manager,
    assigners := s.assigners, delegator := s.delegator, registrar := s.registrar,
    alwaysAcc := s.alwaysAcc }

end State

/-! ## Serialization $T$ (GP §D.1) -/

namespace Serialize

open Codec

/-- $\mathcal{E}$ of a validator key sequence with its length, $\updownarrow \mathbf{k}$ (each key 336 octets). -/
def keys (k : List ValidatorKey) : List UInt8 := varSeq id k

/-- $\mathcal{E}(\updownarrow[x \mid x \in s])$ of a set of hashes in ascending order. -/
def hashSet (s : OctetSet) : List UInt8 := varHashSet s

/-- $C(3)$: $\mathcal{E}(\updownarrow[(h, b, s, \mathcal{E}_4(t), \updownarrow \mathbf{p})], \mathcal{E}_M(\beta_B))$; $\mathcal{E}_M$ of a belt is $\updownarrow$ of its optional peaks. -/
def recent (r : Recent) : List UInt8 :=
  varSeq (fun (b : RecentBlock) => b.headerHash ++ b.accRoot ++ b.stateRoot ++ fixed 4 b.slot ++
      varHashDict b.reported) r.history ++
    varSeq (opt id) r.belt

/-- $C(4)$: $\mathcal{E}(\updownarrow \gamma_P, \gamma_Z, 0 \text{ or } 1, \gamma_S, \updownarrow \gamma_A)$. -/
def gamma (s : State) : List UInt8 :=
  keys s.pending ++ s.ringRoot ++
    (match s.sealKeys with
     | .tickets t => nat 0 ++ seq Ticket.encode t
     | .keys k => nat 1 ++ seq id k) ++
    varSeq Ticket.encode s.accumulator

/-- $C(5)$: $\mathcal{E}(\updownarrow \psi_G, \updownarrow \psi_B, \updownarrow \psi_W, \updownarrow \psi_O)$, each set in ascending order. -/
def disputes (d : DisputesState) : List UInt8 :=
  hashSet d.good ++ hashSet d.bad ++ hashSet d.wonky ++ hashSet d.offenders

/-- $C(10)$: $\mathcal{E}([\text{¿}(g, \mathcal{E}_4(t)) \mid (g, t) \in \rho])$, each $g$ a whole guarantee $\mathbb{G}$. -/
def avail (ρ : AvailAssignments) : List UInt8 :=
  seq (opt fun (a : AvailAssignment) => a.guarantee.encode ++ fixed 4 a.time) ρ

/-- $C(12)$: $\mathcal{E}(\mathcal{E}_4(\chi_m, \chi_\mathbf{a}, \chi_v, \chi_r), \chi_\mathbf{z})$, $\chi_\mathbf{z}$ a dictionary $\mathbb{N}_S \to \mathbb{N}_G$ ($\mathcal{E}_4$ keys, $\mathcal{E}_8$ gas). -/
def privileges (s : State) : List UInt8 :=
  fixed 4 s.manager ++ seq (fixed 4) s.assigners ++ fixed 4 s.delegator ++ fixed 4 s.registrar ++
    varSeq (fun (k, g) => fixed 4 k ++ fixed 8 g) s.alwaysAcc.toList

/-- $\mathcal{E}$ of a validator record's six counters, as variable-length naturals (GP v0.8.1
    eq. `serialization`, $C(13)$; GP #564). -/
def valRecord (r : ValidatorRecord) : List UInt8 :=
  [r.blocks, r.tickets, r.preimages, r.preimagesSize, r.guarantees, r.assurances].flatMap nat

/-- $\mathcal{E}$ of a core record: its eight naturals in the order of GP §13.2. -/
def coreRecord (r : CoreRecord) : List UInt8 :=
  [r.daLoad, r.popularity, r.imports, r.xtCount, r.xtSize, r.exports, r.bundleLen,
    r.gasUsed].flatMap nat

/-- $\mathcal{E}$ of a service record in the order of GP §13.2: $p, r, i, x, z, e, a$. -/
def serviceRecord (r : ServiceRecord) : List UInt8 :=
  let (an, atr, ag) := r.accumulation
  [r.provided.1, r.provided.2, r.refinement.1, r.refinement.2, r.imports, r.xtCount, r.xtSize,
    r.exports, an, atr, ag].flatMap nat

/-- $C(13)$: $\mathcal{E}(\updownarrow\pi_V, \updownarrow\pi_L, \pi_C, \updownarrow[(\mathcal{E}_4(s), \mathcal{E}(\pi_S[s])) \mid s \in \mathcal{K}(\pi_S)])$, the service entries in ascending order of $s$ (GP v0.8.1 eq. `serialization`). -/
def stats (s : State) : List UInt8 :=
  varSeq valRecord s.valStats ++ varSeq valRecord s.valStatsLast ++ seq coreRecord s.coreStats ++
    varSeq (fun (k, r) => fixed 4 k ++ serviceRecord r) s.serviceStats.toList

/-- $C(14)$: $\mathcal{E}([\updownarrow[(r, \updownarrow d) \mid (r, d) \in i] \mid i \in \omega])$. -/
def ready (ω : List (List ReadyEntry)) : List UInt8 :=
  seq (varSeq fun (r, d) => r.encode ++ hashSet d) ω

/-- $C(15)$: $\mathcal{E}([\updownarrow i \mid i \in \xi])$. -/
def accumulated (ξ : List OctetSet) : List UInt8 := seq hashSet ξ

/-- $C(16)$: $\mathcal{E}(\updownarrow[(\mathcal{E}_4(s), \mathcal{E}(h)) \mid (s, h) \in \theta])$. -/
def lastAccOut (θ : List (Nat × List UInt8)) : List UInt8 := varSeq (fun (s, h) => fixed 4 s ++ h) θ

/-- $C(255, s)$: $\mathcal{E}(0, a_c, \mathcal{E}_4(a_u, a'_u), \mathcal{E}_8(a_b, a'_b, a_g, a_m, a_o, a_f)) \frown \mathcal{E}_4(a_i, a_r, a_a, a_p)$,
    with $a'_u$ the supervisor's creation slot and $a'_b$ the supervisor balance (GP v0.8.1
    eq. `serialization`, $C(255, s)$). -/
def accountInfo (a : ServiceAccount) : List UInt8 :=
  nat 0 ++ a.codeHash ++ [a.supervisor, a.supervisorCreated].flatMap (fixed 4) ++
    [a.balance, a.supervisorBalance, a.minAccGas, a.minMemoGas, a.octets, a.gratis].flatMap (fixed 8) ++
    [a.items, a.created, a.lastAcc, a.parent].flatMap (fixed 4)

/-- The key-value pairs of one account: $C(255, s)$, its storage and request entries, already held
    under the hash parts of $C(s, \mathcal{E}_4(2^{32}-1) \frown k)$ and $C(s, \mathcal{E}_4(l) \frown h)$ with the values $T(\sigma)$ gives
    them (`ServiceAccount.entries`), and its preimages under $C(s, \mathcal{E}_4(2^{32}-2) \frown h)$. -/
def account (s : Nat) (a : ServiceAccount) : List (List UInt8 × List UInt8) :=
  (Trie.keyOfService 255 s, accountInfo a) ::
    (a.entries.toList.map fun (k, v) => (Trie.keyOfServiceHash s k, v)) ++
    (a.preimages.toList.map fun (h, p) => (Trie.keyOfServiceData s (fixed 4 (2 ^ 32 - 2) ++ h), p))

end Serialize

open Codec Serialize in
/-- $T(\sigma)$ (GP §D.1), as a list of (state key, value) pairs. -/
def State.serializeList (s : State) : List (List UInt8 × List UInt8) :=
  let c := Trie.keyOfIndex
  [(c 1, seq (varSeq id) s.authPools),
   (c 2, seq (seq id) s.authQueue),
   (c 3, Serialize.recent s.recent),
   (c 4, Serialize.gamma s),
   (c 5, Serialize.disputes s.disputes),
   (c 6, seq id s.eta),
   (c 7, Serialize.keys s.staging),
   (c 8, Serialize.keys s.active),
   (c 9, Serialize.keys s.prev),
   (c 10, Serialize.avail s.avail),
   (c 11, fixed 4 s.tau),
   (c 12, Serialize.privileges s),
   (c 13, Serialize.stats s),
   (c 14, Serialize.ready s.ready),
   (c 15, Serialize.accumulated s.accumulated),
   (c 16, Serialize.lastAccOut s.lastAccOut)] ++
  s.accounts.toList.flatMap fun (i, a) => Serialize.account i a

/-- $T(\sigma)$ (GP §D.1) as a dictionary from 31-octet state keys to values. -/
def State.serialize (s : State) : OctetDict := Std.ExtTreeMap.ofList s.serializeList

/-- $M_\sigma(\sigma) = M(T(\sigma))$ (GP §D.2), the state root. -/
def State.root (s : State) : List UInt8 := Trie.root s.serialize

end JAM
