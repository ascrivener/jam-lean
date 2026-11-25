import JAM.State
import JAM.Block

/-!
# Reading the block-import traces (davxy/jam-test-vectors `traces/`, schema `schema.asn`)

A trace step is ℰ(pre-state, block, post-state) and the genesis file is ℰ(header, state), where a
raw state is ℰ(root, ↕[(key ∈ 𝔹_31, ↕value)]).

`decodeState` inverts T (GP §D.1) on a raw state. The components keyed by C(i) are decoded, and
each service account is built in the form the model holds it (`JAM.ServiceAccount`): a_o and a_i
come from C(255, s); an entry under C(s, ℰ_4(2³²−2) ⌢ ℋ(**p**)) for its own value **p** is a
preimage; every other entry of s (storage, or a request) goes into `entries` under the 27 hash
octets of its key. The decoding is total on states whose service entries all belong to an account
with a C(255, s) entry.
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

/-- A validator record of C(13): six variable-length naturals (GP v0.8.1, GP #564). -/
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

/-! ## v0.8.0 raw states in v0.8.1 form

The published traces are GP v0.8.0 states. Until v0.8.1 traces exist, `upgradeRaw` rewrites the
two state rows whose encoding GP v0.8.1 changed, and nothing else (CLAUDE.md, "Vectors during the
migration"):

* C(13): the validator statistics π_V and π_L become variable-length naturals (GP #564,
  eq. `serialization`); π_C and π_S are unchanged.
* C(255, s): ℰ_4(a_u, a_u') is inserted after a_c and ℰ_8(a_b') after a_b (GP #539, junior
  services, eq. `serialization`). A v0.8.0 account has no supervisor, so it is given the values
  under which GP v0.8.1 behaves as v0.8.0 did: a_u = s with a_u' = a_r (the effective supervisor
  is s itself, eq. `effectivesupervisor`) and a_b' = 0.

The root is recomputed from the rewritten key-values (`Trie.root`). -/

/-- Rewrite one v0.8.0 C(13) value in the v0.8.1 encoding (GP #564). -/
def upgradeStats (v : List UInt8) : Except String (List UInt8) := do
  let old : Decoder (List (List Nat)) := varSeq (seqN 6 (fixed 4))
  let dec : Decoder (List (List Nat) × List (List Nat) × Nat) := do
    let a ← old; let b ← old; let pos ← get; let _ ← bytes (← remaining); return (a, b, pos)
  let (a, b, pos) ← match Decoder.run dec ⟨v.toArray⟩ with
    | .ok r => pure r
    | .error e => throw s!"C(13): {e}"
  let enc (xs : List (List Nat)) := Codec.varSeq (fun r => r.flatMap Codec.nat) xs
  return enc a ++ enc b ++ v.drop pos

/-- Rewrite one v0.8.0 C(255, s) value in the v0.8.1 layout (GP #539). -/
def upgradeInfo (s : Nat) (v : List UInt8) : Except String (List UInt8) := do
  if v.length != 1 + 32 + 40 + 16 then throw s!"C(255, {s}): {v.length} octets"
  let created := v.drop (1 + 32 + 40 + 4) |>.take 4
  return v.take 33 ++ Codec.fixed 4 s ++ created ++ (v.drop 33).take 8 ++ Codec.fixed 8 0 ++ v.drop 41

/-- A v0.8.0 raw state in v0.8.1 form; also checks that its root is the v0.8.0 one. -/
def upgradeRaw (raw : RawState) : Except String RawState := do
  let d : OctetDict := Std.ExtTreeMap.ofList raw.kvs
  if Trie.root d != raw.root.toList then throw "raw state: root does not match its key-values"
  let kvs ← raw.kvs.mapM fun (k, v) => do
    if k == Trie.keyOfIndex 13 then return (k, ← upgradeStats v)
    else if isInfoKey k then
      return (k, ← upgradeInfo (PVM.Num.decodeLE [k.getD 1 0, k.getD 3 0, k.getD 5 0, k.getD 7 0]) v)
    else return (k, v)
  return { root := ⟨(Trie.root (Std.ExtTreeMap.ofList kvs)).toArray⟩, kvs }

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

end JAM.TraceState

namespace JAM.TraceState

/-- A trace step with both raw states in v0.8.1 form (`upgradeRaw`). -/
def upgradeStep (st : Step) : Except String Step := do
  return { st with pre := ← upgradeRaw st.pre, post := ← upgradeRaw st.post }

end JAM.TraceState
