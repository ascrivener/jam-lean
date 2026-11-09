import JAM.Safrole
import JAM.Disputes
import JAM.History
import JAM.Statistics
import JAM.Accumulation
import JAM.Trie

/-!
# The state σ and its serialization T(σ) (GP v0.8.0 §4.2, Appendix D)

σ ≡ (α, β, θ, γ, δ, η, ι, κ, λ, ρ, τ, φ, χ, ψ, π, ω, ξ) (GP eq. `statecomposition`), with
γ ≡ (γ_P, γ_Z, γ_S, γ_A) (eq. `gammaspec`), χ ≡ (χ_M, χ_A, χ_V, χ_R, χ_Z) (eq. `privilegesspec`)
and π ≡ (π_V, π_L, π_C, π_S) (§13).

The components are stored in the types the state-transition functions already use; `State` adds
only the projections each transition needs. `serialize` is T (GP §D.1) and `root` is M_σ = M(T(σ))
(GP §D.2).
-/

namespace JAM

/-- The state σ (GP eq. `statecomposition`). -/
structure State where
  /-- α, the authorizer pools: 𝖢 sequences of at most 𝖮 hashes. -/
  authPools : List (List (List UInt8))
  /-- φ, the authorizer queues: 𝖢 sequences of 𝖰 hashes. -/
  authQueue : List (List (List UInt8))
  /-- β = (β_H, β_B), recent history and the accumulation-output belt. -/
  recent : Recent
  /-- θ, the most recent accumulation outputs (service, hash), in order. -/
  lastAccOut : List (Nat × List UInt8)
  /-- γ_P, the pending validators. -/
  pending : List ValidatorKey
  /-- γ_Z, the ring root. -/
  ringRoot : List UInt8
  /-- γ_S, the slot-sealer sequence. -/
  sealKeys : SealKeys
  /-- γ_A, the ticket accumulator. -/
  accumulator : List Ticket
  /-- δ, the service accounts. -/
  accounts : Accounts
  /-- η ∈ ⟦ℍ⟧_4. -/
  eta : List (List UInt8)
  /-- ι, the staging validators. -/
  staging : List ValidatorKey
  /-- κ, the active validators. -/
  active : List ValidatorKey
  /-- λ, the previous epoch's validators. -/
  prev : List ValidatorKey
  /-- ρ, the availability assignments. -/
  avail : AvailAssignments
  /-- τ, the most recent block's timeslot. -/
  tau : Nat
  /-- χ_M, the manager service. -/
  manager : Nat
  /-- χ_A, the assigner of each core. -/
  assigners : List Nat
  /-- χ_V, the delegator service. -/
  delegator : Nat
  /-- χ_R, the registrar service. -/
  registrar : Nat
  /-- χ_Z, the always-accumulate services and their gas. -/
  alwaysAcc : Std.ExtTreeMap Nat Nat
  /-- ψ, the disputes state. -/
  disputes : DisputesState
  /-- π_V, this epoch's validator statistics. -/
  valStats : List ValidatorRecord
  /-- π_L, the previous epoch's validator statistics. -/
  valStatsLast : List ValidatorRecord
  /-- π_C, the core statistics. -/
  coreStats : List CoreRecord
  /-- π_S, the service statistics. -/
  serviceStats : Std.ExtTreeMap Nat ServiceRecord
  /-- ω, the accumulation ready queue: 𝖤 sequences of (report, dependencies). -/
  ready : List (List ReadyEntry)
  /-- ξ, the accumulated package hashes of the last 𝖤 blocks. -/
  accumulated : List OctetSet

namespace State

/-- The part of σ Safrole reads and writes. -/
def safrole (s : State) : SafroleState :=
  { tau := s.tau, eta := s.eta, prev := s.prev, active := s.active, pending := s.pending,
    staging := s.staging, accumulator := s.accumulator, sealKeys := s.sealKeys,
    ringRoot := s.ringRoot }

/-- The partial state (δ, ι, φ, χ) accumulation starts from (GP eq. `partialstate`). -/
def partialState (s : State) : PartialState :=
  { accounts := s.accounts, staging := s.staging, authQueue := s.authQueue, manager := s.manager,
    assigners := s.assigners, delegator := s.delegator, registrar := s.registrar,
    alwaysAcc := s.alwaysAcc }

end State

/-! ## Serialization T (GP §D.1) -/

namespace Serialize

open Codec

/-- ℰ of a validator key sequence with its length, ↕**k** (each key 336 octets). -/
def keys (k : List ValidatorKey) : List UInt8 := varSeq id k

/-- ℰ(↕[x | x ∈ s]) of a set of hashes in ascending order. -/
def hashSet (s : OctetSet) : List UInt8 := varHashSet s

/-- C(3): ℰ(↕[(h, b, s, ℰ_4(t), ↕**p**)], ℰ_M(β_B)); ℰ_M of a belt is ↕ of its optional peaks. -/
def recent (r : Recent) : List UInt8 :=
  varSeq (fun (b : RecentBlock) => b.headerHash ++ b.accRoot ++ b.stateRoot ++ fixed 4 b.slot ++
      varHashDict b.reported) r.history ++
    varSeq (opt id) r.belt

/-- C(4): ℰ(↕γ_P, γ_Z, 0 or 1, γ_S, ↕γ_A). -/
def gamma (s : State) : List UInt8 :=
  keys s.pending ++ s.ringRoot ++
    (match s.sealKeys with
     | .tickets t => nat 0 ++ seq Ticket.encode t
     | .keys k => nat 1 ++ seq id k) ++
    varSeq Ticket.encode s.accumulator

/-- C(5): ℰ(↕ψ_G, ↕ψ_B, ↕ψ_W, ↕ψ_O), each set in ascending order. -/
def disputes (d : DisputesState) : List UInt8 :=
  hashSet d.good ++ hashSet d.bad ++ hashSet d.wonky ++ hashSet d.offenders

/-- C(10): ℰ([¿(g, ℰ_4(t)) | (g, t) ∈ ρ]), each g a whole guarantee 𝔾. -/
def avail (ρ : AvailAssignments) : List UInt8 :=
  seq (opt fun (a : AvailAssignment) => a.guarantee.encode ++ fixed 4 a.time) ρ

/-- C(12): ℰ(ℰ_4(χ_M, χ_A, χ_V, χ_R), χ_Z), χ_Z a dictionary ℕ_S → ℕ_G (ℰ_4 keys, ℰ_8 gas). -/
def privileges (s : State) : List UInt8 :=
  fixed 4 s.manager ++ seq (fixed 4) s.assigners ++ fixed 4 s.delegator ++ fixed 4 s.registrar ++
    varSeq (fun (k, g) => fixed 4 k ++ fixed 8 g) s.alwaysAcc.toList

/-- ℰ_4 of a validator record's six counters. -/
def valRecord (r : ValidatorRecord) : List UInt8 :=
  [r.blocks, r.tickets, r.preimages, r.preimagesSize, r.guarantees, r.assurances].flatMap (fixed 4)

/-- ℰ of a core record: its eight naturals in the order of GP §13.2. -/
def coreRecord (r : CoreRecord) : List UInt8 :=
  [r.daLoad, r.popularity, r.imports, r.xtCount, r.xtSize, r.exports, r.bundleLen,
    r.gasUsed].flatMap nat

/-- ℰ of a service record in the order of GP §13.2: p, r, i, x, z, e, a. -/
def serviceRecord (r : ServiceRecord) : List UInt8 :=
  let (an, atr, ag) := r.accumulation
  [r.provided.1, r.provided.2, r.refinement.1, r.refinement.2, r.imports, r.xtCount, r.xtSize,
    r.exports, an, atr, ag].flatMap nat

/-- C(13): ℰ(↕[ℰ_4(v) | v ∈ π_V], ↕[ℰ_4(v) | v ∈ π_L], π_C, π_S). -/
def stats (s : State) : List UInt8 :=
  varSeq valRecord s.valStats ++ varSeq valRecord s.valStatsLast ++ seq coreRecord s.coreStats ++
    varSeq (fun (k, r) => fixed 4 k ++ serviceRecord r) s.serviceStats.toList

/-- C(14): ℰ([↕[(r, ↕d) | (r, d) ∈ i] | i ∈ ω]). -/
def ready (ω : List (List ReadyEntry)) : List UInt8 :=
  seq (varSeq fun (r, d) => r.encode ++ hashSet d) ω

/-- C(15): ℰ([↕i | i ∈ ξ]). -/
def accumulated (ξ : List OctetSet) : List UInt8 := seq hashSet ξ

/-- C(16): ℰ(↕[(ℰ_4(s), ℰ(h)) | (s, h) ∈ θ]). -/
def lastAccOut (θ : List (Nat × List UInt8)) : List UInt8 := varSeq (fun (s, h) => fixed 4 s ++ h) θ

/-- C(255, s): ℰ(0, a_c, ℰ_8(a_b, a_g, a_m, a_o, a_f), ℰ_4(a_i, a_r, a_a, a_p)). -/
def accountInfo (a : ServiceAccount) : List UInt8 :=
  nat 0 ++ a.codeHash ++ [a.balance, a.minAccGas, a.minMemoGas, a.octets, a.gratis].flatMap (fixed 8) ++
    [a.items, a.created, a.lastAcc, a.parent].flatMap (fixed 4)

/-- The key-value pairs of one account: C(255, s), and its storage, preimage and request entries
    under C(s, ℰ_4(2³²−1) ⌢ k), C(s, ℰ_4(2³²−2) ⌢ h) and C(s, ℰ_4(l) ⌢ h). -/
def account (s : Nat) (a : ServiceAccount) : List (List UInt8 × List UInt8) :=
  (Trie.keyOfService 255 s, accountInfo a) ::
    (a.storage.toList.map fun (k, v) => (Trie.keyOfServiceData s (fixed 4 (2 ^ 32 - 1) ++ k), v)) ++
    (a.preimages.toList.map fun (h, p) => (Trie.keyOfServiceData s (fixed 4 (2 ^ 32 - 2) ++ h), p)) ++
    (a.requests.toList.map fun ((h, l), t) =>
      (Trie.keyOfServiceData s (fixed 4 l ++ h), varSeq (fixed 4) t))

end Serialize

open Codec Serialize in
/-- T(σ) (GP §D.1), as a list of (state key, value) pairs. -/
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

/-- T(σ) (GP §D.1) as a dictionary from 31-octet state keys to values. -/
def State.serialize (s : State) : OctetDict := Std.ExtTreeMap.ofList s.serializeList

/-- M_σ(σ) = M(T(σ)) (GP §D.2), the state root. -/
def State.root (s : State) : List UInt8 := Trie.root s.serialize

end JAM
