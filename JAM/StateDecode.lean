import JAM.Fast.Blake2b
import JAM.State
import JAM.Block

/-!
# σ from its key-values: the inverse of T (GP v0.8.1 §D.1)

T (GP §D.1, eq. D.2) maps σ to key-value pairs: the components keyed by C(i), i ∈ 1 … 16, each
service account's fields under C(255, s), and its data under C(s, ·) (eq. D.1). `decodeState`
inverts T on a state's key-values. The components keyed by C(i) are decoded with the decoders of
Appendix C, each the inverse of the encoder of the same component in eq. D.2, and each service
account is built in the form the model holds it (`JAM.ServiceAccount`): a_o and a_i come from
C(255, s); an entry under C(s, ℰ_4(2³²−2) ⌢ ℋ(**p**)) for its own value **p** is a preimage; every
other entry of s (storage, or a request) goes into `entries` under the 27 hash octets of its key.
The decoding is total on states whose service entries all belong to an account with a C(255, s)
entry.

[`Tests/TraceTest.lean`](https://github.com/ascrivener/jam-lean/blob/main/Tests/TraceTest.lean) checks the round trip T(decodeState(T(σ))) = T(σ), key by key, and the
state root, on every state of the block-import traces.
-/

namespace JAM.StateDecode

open Decoder

def hash32 : Decoder (List UInt8) := do return (← bytes 32).toList
def vkey : Decoder ValidatorKey := do return (← bytes 336).toList
def ticket : Decoder Ticket := Ticket.decode

/-- A validator record of C(13): six variable-length naturals (GP v0.8.1 eq. `serialization`,
    GP #564). -/
def valRecord : Decoder ValidatorRecord := do
  return { blocks := ← nat, tickets := ← nat, preimages := ← nat,
           preimagesSize := ← nat, guarantees := ← nat, assurances := ← nat }

def coreRecord : Decoder CoreRecord := do
  return { daLoad := ← nat, popularity := ← nat, imports := ← nat, xtCount := ← nat,
           xtSize := ← nat, exports := ← nat, bundleLen := ← nat, gasUsed := ← nat }

def serviceRecord : Decoder ServiceRecord := do
  let p1 ← nat; let p2 ← nat; let r1 ← nat; let r2 ← nat
  let i ← nat; let x ← nat; let z ← nat; let e ← nat
  let a1 ← nat; let a2 ← nat; let a3 ← nat
  return { provided := (p1, p2), refinement := (r1, r2), imports := i, xtCount := x, xtSize := z,
           exports := e, accumulation := (a1, a2, a3) }

def recent : Decoder Recent := do
  let history ← varSeq do
    let h ← hash32; let b ← hash32; let s ← hash32; let t ← fixed 4; let p ← varHashDict
    return ({ headerHash := h, accRoot := b, stateRoot := s, slot := t, reported := p } : RecentBlock)
  let belt ← varSeq (opt hash32)
  return { history, belt }

def sealKeysD (E : Nat) : Decoder SealKeys := do
  match ← nat with
  | 0 => return .tickets (← seqN E ticket)
  | 1 => return .keys (← seqN E hash32)
  | k => fail s!"bad γ_S discriminator {k}"

def gamma (E : Nat) : Decoder (List ValidatorKey × List UInt8 × SealKeys × List Ticket) := do
  let pk ← varSeq vkey
  let z ← bytes 144
  let sk ← sealKeysD E
  let acc ← varSeq ticket
  return (pk, z.toList, sk, acc)

/-- An availability assignment (g, t). -/
def availEntry : Decoder AvailAssignment := do
  let g ← Guarantee.decode
  let t ← fixed 4
  return { guarantee := g, time := t }

/-- Whether a 31-octet key is C(255, s) for some s (GP eq. `serialization`). -/
def isInfoKey (k : List UInt8) : Bool :=
  k.headD 0 == 255 && k.length == 31 &&
    (List.range 31).all fun j => j ∈ [0, 1, 3, 5, 7] || k.getD j 0 == 0

/-- The service-account fields of C(255, s), without the storage, preimages and requests. -/
def accountInfo : Decoder ServiceAccount := do
  let v ← nat
  if v ≠ 0 then fail s!"account version {v}"
  let c ← hash32
  let u ← fixed 4; let uc ← fixed 4
  let b ← fixed 8; let bs ← fixed 8; let g ← fixed 8; let m ← fixed 8; let o ← fixed 8
  let f ← fixed 8
  let i ← fixed 4; let r ← fixed 4; let a ← fixed 4; let p ← fixed 4
  return { codeHash := c, supervisor := u, supervisorCreated := uc, balance := b,
           supervisorBalance := bs, minAccGas := g, minMemoGas := m, octets := o, gratis := f,
           items := i, created := r, lastAcc := a, parent := p }

def get (kvs : List (List UInt8 × List UInt8)) (i : Nat) : Except String ByteArray :=
  match kvs.lookup (Trie.keyOfIndex i) with
  | some v => .ok ⟨v.toArray⟩
  | none => .error s!"no C({i})"

def dec {α : Type} (kvs : List (List UInt8 × List UInt8)) (i : Nat) (d : Decoder α) :
    Except String α := do
  match Decoder.run d (← get kvs i) with
  | .ok x => .ok x
  | .error e => .error s!"C({i}): {e}"

/-- Decode a raw state into σ (see the module note for what can be decoded). -/
def decodeState (p : Params) (kvs : List (List UInt8 × List UInt8)) : Except String State := do
  let C := p.coreCount
  let E := p.epochLen
  let authPools ← dec kvs 1 (seqN C (varSeq hash32))
  let authQueue ← dec kvs 2 (seqN C (seqN p.authQueueSize hash32))
  let rec_ ← dec kvs 3 recent
  let (pending, ringRoot, sealKeys, accumulator) ← dec kvs 4 (gamma E)
  let disputes ← dec kvs 5 do
    return ({ good := ← varHashSet, bad := ← varHashSet, wonky := ← varHashSet,
              offenders := ← varHashSet } : DisputesState)
  let eta ← dec kvs 6 (seqN 4 hash32)
  let staging ← dec kvs 7 (varSeq vkey)
  let active ← dec kvs 8 (varSeq vkey)
  let prev ← dec kvs 9 (varSeq vkey)
  let avail ← dec kvs 10 (seqN C (opt availEntry))
  let tau ← dec kvs 11 (fixed 4)
  let (manager, assigners, delegator, registrar, alwaysAcc) ← dec kvs 12 do
    let m ← fixed 4; let a ← seqN C (fixed 4); let v ← fixed 4; let r ← fixed 4
    let z ← varSeq (do return (← fixed 4, ← fixed 8))
    return (m, a, v, r, Std.ExtTreeMap.ofList z)
  let (valStats, valStatsLast, coreStats, serviceStats) ← dec kvs 13 do
    let v ← varSeq valRecord; let l ← varSeq valRecord; let c ← seqN C coreRecord
    let s ← varSeq (do return (← fixed 4, ← serviceRecord))
    return (v, l, c, Std.ExtTreeMap.ofList s)
  let ready ← dec kvs 14 (seqN E (varSeq (do return (← WorkReport.decode, ← varHashSet))))
  let accumulated ← dec kvs 15 (seqN E varHashSet)
  let lastAccOut ← dec kvs 16 (varSeq (do return (← fixed 4, ← hash32)))
  -- Service accounts.
  let infoKeys := kvs.filter fun (k, _) => isInfoKey k
  let mut accounts : Accounts := ∅
  let mut used : List (List UInt8) := infoKeys.map (·.1)
  for (k, v) in infoKeys do
    let s := PVM.Num.decodeLE [k.getD 1 0, k.getD 3 0, k.getD 5 0, k.getD 7 0]
    let a ← match Decoder.run accountInfo ⟨v.toArray⟩ with
      | .ok a => pure a
      | .error e => throw s!"C(255, {s}): {e}"
    accounts := accounts.insert s a
  let small := (List.range 17).map Trie.keyOfIndex
  used := used ++ small
  let rest := kvs.filter fun (k, _) => !used.contains k
  -- Every other key is C(s, x) = [n₀, a₀, n₁, a₁, n₂, a₂, n₃, a₃, a₄, …, a₂₆] with n = ℰ_4(s)
  -- and a = ℋ(x) (GP §D.1): a preimage if x = ℰ_4(2³²−2) ⌢ ℋ(v) for its value v, else an entry.
  for (k, v) in rest do
    if k.length != 31 then throw s!"key {k} is not 31 octets"
    let s := PVM.Num.decodeLE [k.getD 0 0, k.getD 2 0, k.getD 4 0, k.getD 6 0]
    let hk := [k.getD 1 0, k.getD 3 0, k.getD 5 0, k.getD 7 0] ++ k.drop 8
    let some a := accounts.get? s | throw s!"key {k}: service {s} has no C(255, {s})"
    let h := (Blake2b.hash256 ⟨v.toArray⟩).toList
    if Trie.keyOfServiceData s (Codec.fixed 4 (2 ^ 32 - 2) ++ h) == k then
      accounts := accounts.insert s { a with preimages := a.preimages.insert h v }
    else
      accounts := accounts.insert s { a with entries := a.entries.insert hk v }
  return { authPools, authQueue, recent := rec_, lastAccOut, pending, ringRoot, sealKeys,
           accumulator, accounts, eta, staging, active, prev, avail, tau, manager, assigners,
           delegator, registrar, alwaysAcc, disputes, valStats, valStatsLast, coreStats,
           serviceStats, ready, accumulated }

end JAM.StateDecode
