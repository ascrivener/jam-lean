import JAM.State
import JAM.Block

/-!
# Reading the block-import traces (davxy/jam-test-vectors `traces/`, schema `schema.asn`)

A trace step is ℰ(pre-state, block, post-state) and the genesis file is ℰ(header, state), where a
raw state is ℰ(root, ↕[(key ∈ 𝔹_31, ↕value)]).

`decodeState` inverts T (GP §D.1) on a raw state for the components keyed by C(i), and for the
service accounts as far as the key-values allow. Storage keys are hashed (C(s, h) keeps only
ℋ(h)), so a storage entry cannot be decoded; a preimage entry is recognised by C(s, ℰ_4(2³²−2) ⌢
ℋ(p)) for its value p, and a request entry by C(s, ℰ_4(l) ⌢ h) for a known preimage of hash h and
length l. A raw state with any other entry is rejected. The runner therefore decodes only the
genesis state and keeps its own σ from there.
-/

namespace JAM.TraceState

open Decoder

/-- A raw state: the root and the key-values. -/
structure RawState where
  root : ByteArray
  kvs : List (List UInt8 × List UInt8)

def rawState : Decoder RawState := do
  return { root := ← bytes 32,
           kvs := ← varSeq (do return ((← bytes 31).toList, (← var).toList)) }

/-- One step of a trace. -/
structure Step where
  pre : RawState
  block : Block
  post : RawState

def step (p : Params) : Decoder Step := do
  return { pre := ← rawState, block := ← Block.decode p, post := ← rawState }

/-- The genesis file. -/
def genesis (p : Params) : Decoder (Header × RawState) := do
  return (← Header.decode p, ← rawState)

def hash32 : Decoder (List UInt8) := do return (← bytes 32).toList
def vkey : Decoder ValidatorKey := do return (← bytes 336).toList
def ticket : Decoder Ticket := Ticket.decode

def valRecord : Decoder ValidatorRecord := do
  return { blocks := ← fixed 4, tickets := ← fixed 4, preimages := ← fixed 4,
           preimagesSize := ← fixed 4, guarantees := ← fixed 4, assurances := ← fixed 4 }

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

/-- The service-account fields of C(255, s), without the storage, preimages and requests. -/
def accountInfo : Decoder ServiceAccount := do
  let v ← nat
  if v ≠ 0 then fail s!"account version {v}"
  let c ← hash32
  let b ← fixed 8; let g ← fixed 8; let m ← fixed 8; let _o ← fixed 8; let f ← fixed 8
  let _i ← fixed 4; let r ← fixed 4; let a ← fixed 4; let p ← fixed 4
  return { codeHash := c, balance := b, minAccGas := g, minMemoGas := m, gratis := f,
           created := r, lastAcc := a, parent := p }

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
def decodeState (p : Params) (kvs : List (List UInt8 × List UInt8))
    (knownKeys : List (Nat × List UInt8) := []) : Except String State := do
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
  let infoKeys := kvs.filter fun (k, _) => k.headD 0 == 255 && k.length == 31 &&
    (List.range 31).all fun j => j ∈ [0, 1, 3, 5, 7] || k.getD j 0 == 0
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
  -- Storage entries under keys already known, then preimages, then the requests of known
  -- preimages.
  let known : Std.ExtTreeMap (List UInt8) (Nat × List UInt8) := Std.ExtTreeMap.ofList
    (knownKeys.map fun (s, k) => (Trie.keyOfServiceData s (Codec.fixed 4 (2 ^ 32 - 1) ++ k), (s, k)))
  let mut rest' : List (List UInt8 × List UInt8) := []
  for (k, v) in rest do
    match known.get? k with
    | some (s, sk) =>
      if let some a := accounts.get? s then
        accounts := accounts.insert s { a with storage := a.storage.insert sk v }
      else rest' := rest' ++ [(k, v)]
    | none => rest' := rest' ++ [(k, v)]
  let mut left : List (List UInt8 × List UInt8) := []
  for (k, v) in rest' do
    let h := (Blake2b.hash256 ⟨v.toArray⟩).toList
    match accounts.keys.find? fun s => Trie.keyOfServiceData s (Codec.fixed 4 (2 ^ 32 - 2) ++ h) == k with
    | some s =>
      let a := accounts.getD s default
      accounts := accounts.insert s { a with preimages := a.preimages.insert h v }
    | none => left := left ++ [(k, v)]
  for (k, v) in left do
    let found := accounts.toList.findSome? fun (s, a) =>
      a.preimages.toList.findSome? fun (h, pv) =>
        if Trie.keyOfServiceData s (Codec.fixed 4 pv.length ++ h) == k then some (s, h, pv.length)
        else none
    match found with
    | some (s, h, l) =>
      let t ← match Decoder.run (varSeq (fixed 4)) ⟨v.toArray⟩ with
        | .ok t => pure t
        | .error e => throw s!"request entry: {e}"
      let a := accounts.getD s default
      accounts := accounts.insert s { a with requests := a.requests.insert (h, l) t }
    | none => throw s!"cannot decode key {k} (storage, or a request without its preimage)"
  return { authPools, authQueue, recent := rec_, lastAccOut, pending, ringRoot, sealKeys,
           accumulator, accounts, eta, staging, active, prev, avail, tau, manager, assigners,
           delegator, registrar, alwaysAcc, disputes, valStats, valStatsLast, coreStats,
           serviceStats, ready, accumulated }

end JAM.TraceState
