import JAM.Params

/-!
# Bootstrap's behaviour: the spec

What Parity's bootstrap service (`services/bootstrap/jam-bootstrap-service.jam`, crate
`jam-bootstrap-service` 0.1.29) does, as Lean definitions. The target theorems in
`docs/bootstrap-target.md` say the binary does exactly this. The file has no theorems.

**The spec describes what the binary does today, not what it was meant to do.** Behaviour that may
be surprising is specified exactly and listed as a quirk (Q1, Q2, …) in the doc's "Quirks"
section; the definitions that implement a quirk say so. Whether a quirk was intended is not
decided here.

Every definition here is read off the Rust source of the crate and of the crates it uses at the
versions in its `Cargo.lock`: `jam-bootstrap-service-common` 0.1.29 (the `Instruction` type and
the storage keys), `jam-pvm-common` 0.1.29 (the SDK: entry points and host-call wrappers),
`jam-types` 0.1.29 and `jam-codec` 0.1.1 (the codec). Where the source leaves something open, the
definition takes it as a parameter (`Consts.randomKeys`).

The file has four parts:

* **Values and their codec.** `Instr` (the 25 instructions), `Ret` and `Err` (an instruction's
  result), their encodings ℰ, and the decoder `Dec` that the binary runs. The decoder is
  `jam-codec`'s, which accepts more than the canonical ℰ: see `Dec.compact`.
* **Programs over host calls.** `Prog E α` is a program that may call the host operations `E`,
  panic, or return an `α`. It says which host calls bootstrap makes, in what order and with which
  arguments, and what it does with each reply. It fixes nothing about what the host replies: the
  JAM model's host functions supply that in the theorems.
* **Refine** (`refine`): decode the payload as `Instructions`, rewrite the instructions that need
  in-core work (eager lookups, imports, exports, random keys), and return the encoded
  `BootstrapWorkOutput`.
* **Accumulate** (`accumulate`): for each operand, decode the work output, record it in the
  recent-work-item ring, and run its instructions through the accumulate host calls, storing the
  results; for each incoming transfer, count it and store it.

Host calls made only for logging are left out: `log` (100), the `gas` calls in log lines, and the
`info` call that feeds accumulate's first log line. They change nothing but gas and registers.

Two outcomes are allowed beyond what `Prog` says, and the theorems carry them:

* **Heap exhaustion.** Any allocation may fail, and a failed allocation panics (Rust's
  `handle_alloc_error`). So refine may end in ☇, and accumulate may stop and roll back to its last
  checkpoint, at any point where the binary allocates. The theorems allow this; they do not prove
  that it cannot happen.
* **Running out of gas**, as for any service.

The test-only instructions (`Instr.testOnly`) are in the spec like the others.
-/

namespace Services.Bootstrap.Spec

/-- Octet strings. -/
abbrev Bytes := List UInt8

open JAM.Codec (nat fixed)

/-! ## Constants -/

/-- The chain parameters bootstrap reads (the SDK fetches them at entry), and the one function the
    source leaves to a library. -/
structure Consts where
  /-- 𝖰, the length of an authorizer queue (`AuthQueueLen`). -/
  authQueueLen : Nat
  /-- The validator-key limit of `Designate` (`MaxValCount` = 3·𝖢). -/
  maxValCount : Nat
  /-- The size of the recent-work-item ring (`max_recent_work_items` = 2·𝖢·𝖨). -/
  maxRecent : Nat
  /-- The keys `RandomStorageRefine { seed, nb_items }` generates: `nb_items` draws of 32 octets
      from `rand` 0.9's `SmallRng::seed_from_u64 seed`. Left as a parameter: see the doc's open
      questions. -/
  randomKeys : Nat → Nat → List Bytes

/-- The constants for chain parameters `p`. -/
def Consts.ofParams (p : JAM.Params) (randomKeys : Nat → Nat → List Bytes) : Consts :=
  { authQueueLen := p.authQueueSize, maxValCount := 3 * p.coreCount,
    maxRecent := 2 * p.coreCount * p.maxPackageItems, randomKeys }

/-! ## Values -/

/-- `PreimageId`: a preimage by hash, or inline. -/
inductive Preimage where
  | hash (h : Bytes)
  | inline (data : Bytes)

/-- `Instruction` (jam-bootstrap-service-common 0.1.29), in declaration order, so the codec tag is
    the constructor's index (`createService` = 0, …, `checkpoint` = 15, …, `assignForGasCost` = 24).
    Hashes are 32 octets, memos 128, validator keysets 336. The last seven are internal: refine
    produces `lookedUp`, `imported`, `exported` and `randomStorageAccumulate`; the others are for
    tests and benchmarks. -/
inductive Instr where
  | createService (codeHash : Bytes) (codeLen minItemGas minMemoGas endowment : Nat) (memo : Bytes)
      (registration : Option Bytes) (depositOffset : Nat) (id : Option Nat)
  | upgrade (codeHash : Bytes) (minItemGas minMemoGas : Nat)
  | transfer (dest amount gasLimit : Nat) (memo : Bytes)
  | zombify (ejector : Nat)
  | eject (target : Nat) (codeHash : Bytes)
  | deleteItems (keys : List Bytes)
  | solicit (hash : Bytes) (len : Nat)
  | forget (hash : Bytes) (len : Nat)
  | lookup (service : Nat) (hash : Bytes) (eager : Bool)
  | importSegs (items : List (Nat × Nat))
  | exportSegs (data : List Bytes)
  | bless (manager assigner designator registrar : Nat) (alwaysAcc : List (Nat × Nat))
  | assign (core : Nat) (queue : List Bytes) (assigner : Nat)
  | designate (keys : List Bytes)
  | yield (hash : Bytes)
  | checkpoint
  | panic
  | provide (service : Nat) (preimage : Preimage)
  | lookedUp (data : Option Bytes)
  | imported (data : List Bytes)
  | exported (count : Nat)
  | randomStorageRefine (seed nbItems : Nat)
  | randomStorageAccumulate (keys : Option (List Bytes))
  | benchmark
  | assignForGasCost (core : Nat) (queue : List Bytes) (assigner : Nat)

/-- The instructions the source marks as being for tests and benchmarks: `RandomStorageRefine`,
    `RandomStorageAccumulate`, `Benchmark` and `AssignForGasCost`. They are specified like the
    others; the predicate only labels them. -/
def Instr.testOnly : Instr → Bool
  | .randomStorageRefine .. | .randomStorageAccumulate _ | .benchmark | .assignForGasCost .. => true
  | _ => false

/-- `InstructionRet`: what a successful instruction returns. -/
inductive Ret where
  | unit
  | serviceId (id : Nat)
  | length (n : Nat)
  | transferred (dest amount : Nat) (memo : Bytes)
  | hash (h : Bytes)
  | data (d : Bytes)
  | dataVec (ds : List Bytes)

/-- `InstructionError`, in declaration order (the codec tag is the index). bootstrap never
    produces `missingOutput` or `panic`. -/
inductive Err where
  | createService | solicit | provision | transfer | query | forget | lookup | zombify | eject
  | assign | designate | invalid | missingOutput | panic

/-- An instruction's result. -/
abbrev Result := Except Err Ret

/-- The service storage keys bootstrap itself maintains (`StorageKey`). -/
inductive Key where
  /-- the next slot of the recent-work-item ring -/
  | counter
  /-- slot `i` of the ring: the package hash and item index of a recent work item -/
  | recent (i : Nat)
  /-- the results of the instructions of one work item -/
  | results (package : Bytes) (item : Nat)
  /-- the service registry -/
  | registry

/-! ## Encoding ℰ

`jam-codec`'s derived encoding: fields in order, fixed-width integers little-endian (ℰ_l), an
enum's tag as one octet, `Vec` with its length as ℰ (GP's general natural encoding), arrays and
`FixedVec` without a length, `Option` and `Result` with a 0/1 tag. -/

/-- ℰ(↕x) for an octet string: `Vec<u8>`. -/
def bytes (b : Bytes) : Bytes := nat b.length ++ b

/-- ℰ(↕xs) for a `Vec` of encoded elements. -/
def vec {α : Type} (e : α → Bytes) (xs : List α) : Bytes := nat xs.length ++ (xs.map e).flatten

/-- ℰ of an `Option`. -/
def opt {α : Type} (e : α → Bytes) : Option α → Bytes
  | none => [0]
  | some x => 1 :: e x

/-- ℰ(i) for an instruction. -/
def Instr.encode : Instr → Bytes
  | .createService h l g m b memo r f id =>
      [0] ++ h ++ fixed 8 l ++ fixed 8 g ++ fixed 8 m ++ fixed 8 b ++ memo ++ opt bytes r ++
        fixed 8 f ++ opt (fixed 4) id
  | .upgrade h g m => [1] ++ h ++ fixed 8 g ++ fixed 8 m
  | .transfer d a g memo => [2] ++ fixed 4 d ++ fixed 8 a ++ fixed 8 g ++ memo
  | .zombify e => [3] ++ fixed 4 e
  | .eject t h => [4] ++ fixed 4 t ++ h
  | .deleteItems ks => [5] ++ vec bytes ks
  | .solicit h l => [6] ++ h ++ fixed 8 l
  | .forget h l => [7] ++ h ++ fixed 8 l
  | .lookup s h e => [8] ++ fixed 4 s ++ h ++ [if e then 1 else 0]
  | .importSegs is => [9] ++ vec (fun (i, l) => fixed 8 i ++ fixed 8 l) is
  | .exportSegs ds => [10] ++ vec bytes ds
  | .bless m a v r z => [11] ++ fixed 4 m ++ fixed 4 a ++ fixed 4 v ++ fixed 4 r ++
      vec (fun (s, g) => fixed 4 s ++ fixed 8 g) z
  | .assign c q a => [12] ++ fixed 2 c ++ q.flatten ++ fixed 4 a
  | .designate ks => [13] ++ vec id ks
  | .yield h => [14] ++ h
  | .checkpoint => [15]
  | .panic => [16]
  | .provide s (.hash h) => [17] ++ fixed 4 s ++ [0] ++ h
  | .provide s (.inline d) => [17] ++ fixed 4 s ++ [1] ++ bytes d
  | .lookedUp d => [18] ++ opt bytes d
  | .imported ds => [19] ++ vec bytes ds
  | .exported n => [20] ++ fixed 8 n
  | .randomStorageRefine s n => [21] ++ fixed 8 s ++ fixed 1 n
  | .randomStorageAccumulate none => [22, 1]
  | .randomStorageAccumulate (some ks) => [22, 0] ++ vec id ks
  | .benchmark => [23]
  | .assignForGasCost c q a => [24] ++ fixed 2 c ++ vec id q ++ fixed 4 a

/-- x fits in l octets. -/
def fits (l x : Nat) : Prop := x < 2 ^ (8 * l)

/-- A `Vec` length ℰ can carry (`Compact<u32>`). -/
def short {α : Type} (xs : List α) : Prop := xs.length < 2 ^ 32

/-- The instructions ℰ can encode faithfully: hashes of 32 octets, memos of 128, keysets of 336, an
    authorizer queue of exactly 𝖰 hashes, at most `maxValCount` keysets, every number within its
    width and every list shorter than 2^32. These are exactly the values the decoder can return. -/
def Instr.WF (C : Consts) : Instr → Prop
  | .createService h l g m b memo r f id => h.length = 32 ∧ fits 8 l ∧ fits 8 g ∧ fits 8 m ∧
      fits 8 b ∧ memo.length = 128 ∧ (∀ n ∈ r, short n) ∧ fits 8 f ∧ (∀ s ∈ id, fits 4 s)
  | .upgrade h g m => h.length = 32 ∧ fits 8 g ∧ fits 8 m
  | .transfer d a g memo => fits 4 d ∧ fits 8 a ∧ fits 8 g ∧ memo.length = 128
  | .zombify e => fits 4 e
  | .eject t h => fits 4 t ∧ h.length = 32
  | .deleteItems ks => short ks ∧ ∀ k ∈ ks, short k
  | .solicit h l | .forget h l => h.length = 32 ∧ fits 8 l
  | .lookup s h _ => fits 4 s ∧ h.length = 32
  | .importSegs is => short is ∧ ∀ p ∈ is, fits 8 p.1 ∧ fits 8 p.2
  | .exportSegs ds | .imported ds => short ds ∧ ∀ d ∈ ds, short d
  | .bless m a v r z => fits 4 m ∧ fits 4 a ∧ fits 4 v ∧ fits 4 r ∧ short z ∧
      ∀ p ∈ z, fits 4 p.1 ∧ fits 8 p.2
  | .assign c q a => fits 2 c ∧ q.length = C.authQueueLen ∧ (∀ h ∈ q, h.length = 32) ∧ fits 4 a
  | .designate ks => ks.length ≤ C.maxValCount ∧ short ks ∧ ∀ k ∈ ks, k.length = 336
  | .yield h => h.length = 32
  | .checkpoint | .panic | .benchmark => True
  | .provide s (.hash h) => fits 4 s ∧ h.length = 32
  | .provide s (.inline d) => fits 4 s ∧ short d
  | .lookedUp d => ∀ x ∈ d, short x
  | .exported n => fits 8 n
  | .randomStorageRefine s n => fits 8 s ∧ fits 1 n
  | .randomStorageAccumulate ks => ∀ l ∈ ks, short l ∧ ∀ k ∈ l, k.length = 32
  | .assignForGasCost c q a => fits 2 c ∧ short q ∧ (∀ h ∈ q, h.length = 32) ∧ fits 4 a

/-- ℰ(`Instructions { instructions, salt }`), the payload format. -/
def encodePayload (is : List Instr) (salt : Bytes) : Bytes := vec Instr.encode is ++ salt

/-- ℰ(`BootstrapWorkOutput { instructions, work_item_index }`), refine's output. -/
def encodeOutput (is : List Instr) (item : Nat) : Bytes := vec Instr.encode is ++ fixed 2 item

/-- The codec tag of an `Err`. -/
def Err.tag : Err → Nat
  | .createService => 0 | .solicit => 1 | .provision => 2 | .transfer => 3 | .query => 4
  | .forget => 5 | .lookup => 6 | .zombify => 7 | .eject => 8 | .assign => 9 | .designate => 10
  | .invalid => 11 | .missingOutput => 12 | .panic => 13

/-- ℰ of an instruction's result. -/
def Result.encode : Result → Bytes
  | .error e => [1, UInt8.ofNat e.tag]
  | .ok .unit => [0, 0]
  | .ok (.serviceId i) => [0, 1] ++ fixed 4 i
  | .ok (.length n) => [0, 2] ++ fixed 4 n
  | .ok (.transferred d a m) => [0, 3] ++ fixed 4 d ++ fixed 8 a ++ m
  | .ok (.hash h) => [0, 4] ++ h
  | .ok (.data d) => [0, 5] ++ bytes d
  | .ok (.dataVec ds) => [0, 6] ++ vec bytes ds

/-- ℰ(`InstructionResults`), the value stored under `Key.results`. -/
def encodeResults (rs : List Result) : Bytes := vec Result.encode rs

/-- ℰ of a storage key: the octets of the storage item's key. -/
def Key.encode : Key → Bytes
  | .counter => [0]
  | .recent i => [1] ++ fixed 4 i
  | .results p i => [2] ++ p ++ fixed 2 i
  | .registry => [3]

/-- ℰ(`RecentWorkItem { package, item }`). -/
def encodeRecent (package : Bytes) (item : Nat) : Bytes := package ++ fixed 2 item

/-- The service registry: (name, (service id, code hash)) in insertion order. -/
abbrev Registry := List (Bytes × Nat × Bytes)

/-- ℰ(`ServiceRegistry`). -/
def encodeRegistry (r : Registry) : Bytes := vec (fun (n, s, h) => bytes n ++ fixed 4 s ++ h) r

/-- `ServiceRegistry::update`: drop the entry named `name`, if any, and append the new one. -/
def Registry.update (r : Registry) (name : Bytes) (id : Nat) (codeHash : Bytes) : Registry :=
  r.filter (fun e => e.1 != name) ++ [(name, id, codeHash)]

/-! ## The decoder the binary runs

`jam-codec` 0.1.1's `Decode`, as a parser. It reads a prefix and leaves the rest, so trailing octets
are ignored: bootstrap calls `decode`, not `decode_all` (quirk Q2). -/

/-- A parser: consume a prefix, or fail. -/
abbrev Dec := StateT Bytes Option

namespace Dec

def fail {α : Type} : Dec α := fun _ => none

/-- n octets. -/
def take (n : Nat) : Dec Bytes := fun s => if n ≤ s.length then some (s.take n, s.drop n) else none

/-- One octet, as a number. -/
def byte : Dec Nat := do
  let b ← take 1
  pure (b.headD 0).toNat

/-- ℰ_l⁻¹: an l-octet little-endian number. -/
def fixedN (l : Nat) : Dec Nat := do
  let b ← take l
  pure (PVM.Num.decodeLE b)

/-- The number of leading one bits of an octet b < 255 (`(0..8).find(|i| b & (0x80 >> i) == 0)`). -/
def leadingOnes (b : Nat) : Nat := ((List.range 8).find? (fun i => (b / 2 ^ (7 - i)) % 2 == 0)).getD 8

/-- A natural in `jam-codec`'s compact form (`WrappedPrimitive::decode`): the prefix octet b, then
    l octets, where l is b's number of leading ones; 255 is followed by 8 octets. This inverts GP's
    ℰ, but it also accepts encodings ℰ never produces (a value in a longer form than needed, such as
    [128, 5] for 5). Quirk Q1. -/
def compact : Dec Nat := do
  let b ← byte
  if b = 255 then fixedN 8
  else
    let l := leadingOnes b
    let lo ← fixedN l
    pure (lo + (b % 2 ^ (7 - l)) * 2 ^ (8 * l))

/-- A `Vec` length: a compact natural below 2^32 (`Compact<u32>`). -/
def len : Dec Nat := do
  let n ← compact
  if n < 2 ^ 32 then pure n else fail

/-- n elements. -/
def count {α : Type} (p : Dec α) : Nat → Dec (List α)
  | 0 => pure []
  | n + 1 => do
    let x ← p
    let xs ← count p n
    pure (x :: xs)

/-- `Vec<T>`. -/
def vec {α : Type} (p : Dec α) : Dec (List α) := do count p (← len)

/-- `Vec<u8>`. -/
def bytes : Dec Bytes := do take (← len)

/-- `bool`: 0 or 1. -/
def bool : Dec Bool := do
  match ← byte with
  | 0 => pure false
  | 1 => pure true
  | _ => fail

/-- `Option<T>`: tag 0 or 1. -/
def opt {α : Type} (p : Dec α) : Dec (Option α) := do
  match ← byte with
  | 0 => pure none
  | 1 => some <$> p
  | _ => fail

/-- One instruction. -/
def instr (C : Consts) : Dec Instr := do
  let h32 := take 32
  match ← byte with
  | 0 => do
    let h ← h32
    let l ← fixedN 8
    let g ← fixedN 8
    let m ← fixedN 8
    let b ← fixedN 8
    let memo ← take 128
    let r ← opt bytes
    let f ← fixedN 8
    let id ← opt (fixedN 4)
    pure (.createService h l g m b memo r f id)
  | 1 => return .upgrade (← h32) (← fixedN 8) (← fixedN 8)
  | 2 => return .transfer (← fixedN 4) (← fixedN 8) (← fixedN 8) (← take 128)
  | 3 => return .zombify (← fixedN 4)
  | 4 => return .eject (← fixedN 4) (← h32)
  | 5 => return .deleteItems (← vec bytes)
  | 6 => return .solicit (← h32) (← fixedN 8)
  | 7 => return .forget (← h32) (← fixedN 8)
  | 8 => return .lookup (← fixedN 4) (← h32) (← bool)
  | 9 => return .importSegs (← vec (do return (← fixedN 8, ← fixedN 8)))
  | 10 => return .exportSegs (← vec bytes)
  | 11 => do
    let (m, a, v, r) := (← fixedN 4, ← fixedN 4, ← fixedN 4, ← fixedN 4)
    return .bless m a v r (← vec (do return (← fixedN 4, ← fixedN 8)))
  | 12 => return .assign (← fixedN 2) (← count h32 C.authQueueLen) (← fixedN 4)
  | 13 => do
    let n ← len
    if n > C.maxValCount then fail
    return .designate (← count (take 336) n)
  | 14 => return .yield (← h32)
  | 15 => pure .checkpoint
  | 16 => pure .panic
  | 17 => do
    let s ← fixedN 4
    match ← byte with
    | 0 => return .provide s (.hash (← h32))
    | 1 => return .provide s (.inline (← bytes))
    | _ => fail
  | 18 => return .lookedUp (← opt bytes)
  | 19 => return .imported (← vec bytes)
  | 20 => return .exported (← fixedN 8)
  | 21 => return .randomStorageRefine (← fixedN 8) (← fixedN 1)
  | 22 => do
    match ← byte with
    | 0 => return .randomStorageAccumulate (some (← vec h32))
    | 1 => pure (.randomStorageAccumulate none)
    | _ => fail
  | 23 => pure .benchmark
  | 24 => return .assignForGasCost (← fixedN 2) (← vec h32) (← fixedN 4)
  | _ => fail

/-- `Instructions`: the instruction list and the 32-octet salt. -/
def payload (C : Consts) : Dec (List Instr × Bytes) := do
  let is ← vec (instr C)
  let salt ← take 32
  pure (is, salt)

/-- `BootstrapWorkOutput`: the instruction list and the work item's index. -/
def output (C : Consts) : Dec (List Instr × Nat) := do
  let is ← vec (instr C)
  let i ← fixedN 2
  pure (is, i)

end Dec

/-- Run a parser on the whole input, ignoring what it leaves. -/
def decode {α : Type} (p : Dec α) (s : Bytes) : Option α := (p.run s).map (·.1)

/-! ## Programs over host calls -/

/-- A program over host operations `E` (an operation `op : E β` replies with a `β`): it returns an
    `α`, calls an operation and continues with its reply, or panics (traps). -/
inductive Prog (E : Type → Type) (α : Type) : Type 1 where
  | pure (a : α)
  | call {β : Type} (op : E β) (k : β → Prog E α)
  | panic

namespace Prog

def bind {E : Type → Type} {α β : Type} : Prog E α → (α → Prog E β) → Prog E β
  | pure a, f => f a
  | call op k, f => call op (fun b => bind (k b) f)
  | panic, _ => panic

instance {E : Type → Type} : Monad (Prog E) where
  pure := Prog.pure
  bind := Prog.bind

/-- Call one operation and return its reply. -/
def op {E : Type → Type} {β : Type} (o : E β) : Prog E β := call o Prog.pure

end Prog

open Prog (op)

/-! ## Refine -/

/-- The refine host operations bootstrap uses, at the level of the SDK call. -/
inductive ROp : Type → Type where
  /-- `historical_lookup` (7) of `hash` in `service`'s preimages, as the SDK's
      `foreign_historical_lookup` makes it (two calls: the length, then the data). -/
  | histLookup (service : Nat) (hash : Bytes) : ROp (Option Bytes)
  /-- `fetch` (2) of this work item's import segment `index`; `none` if there is none. -/
  | importSeg (index : Nat) : ROp (Option Bytes)
  /-- `export` (8) of `data` (the host pads it to a segment). The reply is ignored. -/
  | exportSeg (data : Bytes) : ROp Unit

/-- What refine does with one instruction (`Service::refine`'s loop body). -/
def refineInstr (C : Consts) : Instr → Prog ROp Instr
  | .lookup s h true => do
    let d ← op (ROp.histLookup s h)
    pure (.lookedUp d)
  | .randomStorageRefine seed n => pure (.randomStorageAccumulate (some (C.randomKeys seed n)))
  | .exportSegs ds => do
    for d in ds do op (ROp.exportSeg d)
    pure (.exported ds.length)  -- quirk Q11: counts attempts, failed exports included
  | .importSegs items => do
    let segs ← items.mapM fun (i, l) => do
      match ← op (ROp.importSeg i) with
      | some seg => pure (seg.take l)
      | none => Prog.panic  -- quirk Q10
    pure (.imported segs)
  | i => pure i  -- quirk Q3: internal variants pass through too

/-- **Refine** for work item `item` with payload `y`: decode `Instructions` (panic if that fails),
    rewrite each instruction with `refineInstr`, and return ℰ(`BootstrapWorkOutput`). The core
    index, service id and package hash are not used, except in log lines. -/
def refine (C : Consts) (item : Nat) (y : Bytes) : Prog ROp Bytes := do
  match decode (Dec.payload C) y with
  | none => Prog.panic
  | some (is, _) =>
    let out ← is.mapM (refineInstr C)
    pure (encodeOutput out item)

/-! ## Accumulate -/

/-- The fields of `ServiceInfo` that bootstrap reads. -/
structure Info where
  codeHash : Bytes
  bytes : Nat
  items : Nat

/-- The accumulate host operations bootstrap uses, at the level of the SDK call. `Except Unit α`
    is the SDK's `Result<α, ApiError>`, with the error code forgotten: bootstrap only tests for
    success. -/
inductive AOp : Type → Type where
  /-- `fetch` (2), kind 14: the accumulate inputs, encoded as ℰ(↕**i**) (kind 15 is a single item). -/
  | fetchItems : AOp (Option Bytes)
  /-- `info` (6) of this service. -/
  | myInfo : AOp Info
  /-- `read` (4) of this service's `key`. -/
  | read (key : Bytes) : AOp (Option Bytes)
  /-- `write` (5) of `value` under `key`. -/
  | write (key value : Bytes) : AOp (Except Unit Unit)
  /-- `write` (5) of nothing under `key`: remove it. -/
  | remove (key : Bytes) : AOp Unit
  /-- `checkpoint` (18). -/
  | checkpoint : AOp Unit
  /-- `lookup` (3) of `hash` in `service`'s preimages (`none`: this service's). -/
  | lookup (service : Option Nat) (hash : Bytes) : AOp (Option Bytes)
  /-- `new` (19); replies with the new service's id. -/
  | new (codeHash : Bytes) (codeLen minItemGas minMemoGas depositOffset : Nat) (id : Option Nat) :
      AOp (Except Unit Nat)
  /-- `upgrade` (20). -/
  | upgrade (codeHash : Bytes) (minItemGas minMemoGas : Nat) : AOp (Except Unit Unit)
  /-- `transfer` (21). -/
  | transfer (dest amount gasLimit : Nat) (memo : Bytes) : AOp (Except Unit Unit)
  /-- `eject` (22). -/
  | eject (target : Nat) (codeHash : Bytes) : AOp (Except Unit Unit)
  /-- `query` (23); whether the request exists. -/
  | query (hash : Bytes) (len : Nat) : AOp Bool
  /-- `solicit` (24). -/
  | solicit (hash : Bytes) (len : Nat) : AOp (Except Unit Unit)
  /-- `forget` (25). -/
  | forget (hash : Bytes) (len : Nat) : AOp (Except Unit Unit)
  /-- `yield` (26). -/
  | yield (hash : Bytes) : AOp (Except Unit Unit)
  /-- `provide` (27). -/
  | provide (service : Nat) (preimage : Bytes) : AOp (Except Unit Unit)
  /-- `bless` (15), every core assigned to `assigner`. -/
  | bless (manager assigner designator registrar : Nat) (alwaysAcc : List (Nat × Nat)) :
      AOp (Except Unit Unit)
  /-- `assign` (16) of the 𝖰·32 octets at the start of `queue`. -/
  | assign (core : Nat) (queue : Bytes) (assigner : Nat) : AOp (Except Unit Unit)
  /-- `designate` (17) of the concatenated keysets. -/
  | designate (keys : List Bytes) : AOp (Except Unit Unit)

/-- Run a fallible operation; panic if it fails (the source's `unwrap` / `expect`). -/
def orPanic {α : Type} (o : AOp (Except Unit α)) : Prog AOp α := do
  match ← op o with
  | .ok a => pure a
  | .error _ => Prog.panic

/-- `set(key, value).unwrap()`. -/
def store (k : Key) (v : Bytes) : Prog AOp Unit := orPanic (.write k.encode v)

/-- `get(key)`: read and decode; `none` if absent or if the value does not decode. -/
def load {α : Type} (k : Key) (p : Dec α) : Prog AOp (Option α) := do
  pure ((← op (AOp.read k.encode)).bind (decode p))

/-- `add_recent_work_item`: write (package, item) into the ring's next slot, removing the results of
    the work item it replaces, and advance the slot. -/
def addRecent (C : Consts) (package : Bytes) (item : Nat) : Prog AOp Unit := do
  let c := (← load .counter (Dec.fixedN 4)).getD 0  -- quirk Q12: undecodable reads as 0
  match ← load (.recent c) (do return (← Dec.take 32, ← Dec.fixedN 2)) with
  | some (p, i) => op (AOp.remove (Key.results p i).encode)
  | none => pure ()
  store (.recent c) (encodeRecent package item)
  store .counter (fixed 4 ((c + 1) % C.maxRecent))

/-- `remove_all_recent_work_items`, from slot `i` on: stop at the first empty slot. -/
def removeRecentFrom : List Nat → Prog AOp Unit
  | [] => pure ()
  | i :: is => do
    match ← load (.recent i) (do return (← Dec.take 32, ← Dec.fixedN 2)) with
    | none => pure ()
    | some (p, it) =>
      op (AOp.remove (Key.results p it).encode)
      op (AOp.remove (Key.recent i).encode)
      removeRecentFrom is

/-- `remove_all_keys`: the ring and its results, the counter and the registry. -/
def removeAllKeys (C : Consts) : Prog AOp Unit := do
  removeRecentFrom (List.range C.maxRecent)
  op (AOp.remove Key.counter.encode)
  op (AOp.remove Key.registry.encode)

/-- Succeed with `r` if the operation succeeds, else fail with `e`. -/
def check {α : Type} (o : AOp (Except Unit α)) (e : Err) (r : Ret) : Prog AOp Result := do
  match ← op o with
  | .ok _ => pure (.ok r)
  | .error _ => pure (.error e)

/-- `FOOTPRINT_PREIMAGE_OVERHEAD`. -/
def preimageOverhead : Nat := 81

/-- **One instruction in accumulate** (`on_instruction`), at timeslot `now`. -/
def onInstr (C : Consts) (now : Nat) : Instr → Prog AOp Result
  | .createService h l g m b memo reg f id => do
    match ← op (AOp.new h l g m f id) with
    | .error _ => pure (.error .createService)
    | .ok s =>
      -- provide the code if this service has it; the reply is ignored
      match ← op (AOp.lookup none h) with
      | some code => do let _ ← op (AOp.provide s code)
      | none => pure ()
      match ← op (AOp.transfer s b m memo) with
      | .error _ => pure (.error .transfer)  -- quirk Q5: the new service stays
      | .ok _ =>
        match reg with
        | some name => do
          -- quirk Q12: an undecodable registry reads as empty and is overwritten
          let r := (← load .registry (Dec.vec (do
            return (← Dec.bytes, ← Dec.fixedN 4, ← Dec.take 32)))).getD []
          store .registry (encodeRegistry (Registry.update r name s h))
        | none => pure ()
        pure (.ok (.serviceId s))
  | .upgrade h g m => do orPanic (.upgrade h g m); pure (.ok .unit)  -- quirk Q8
  | .transfer d a g memo => check (.transfer d a g memo) .transfer (.transferred d a memo)
  | .zombify e => do
    removeAllKeys C  -- quirk Q4: before the precondition check
    let info ← op AOp.myInfo
    if ¬ (info.bytes ≥ preimageOverhead ∧ info.items = 2) then pure (.error .zombify)
    else
      match ← op (AOp.forget info.codeHash (info.bytes - preimageOverhead)) with
      | .error _ => pure (.error .forget)
      | .ok _ => do
        -- `zombify(ejector)`: upgrade to the code hash ℰ_4(ejector) ⌢ 0^28, gas 0 and 0
        orPanic (.upgrade (fixed 4 e ++ List.replicate 28 0) 0 0)
        pure (.ok .unit)
  | .eject t h => check (.eject t h) .eject .unit
  | .deleteItems ks => do
    for k in ks do op (AOp.remove k)  -- quirk Q6: own keys included
    pure (.ok .unit)
  | .imported ds => pure (.ok (.dataVec ds))
  | .exported n => pure (.ok (.length (n % 2 ^ 32)))  -- quirk Q9
  | .solicit h l => check (.solicit h l) .solicit (.hash h)
  | .forget h l => do
    if ← op (AOp.query h l) then check (.forget h l) .forget (.hash h)
    else pure (.error .query)
  | .lookup s h _ => do
    match ← op (AOp.lookup (some s) h) with
    | some d => pure (.ok (.data d))
    | none => pure (.error .lookup)
  | .lookedUp (some d) => pure (.ok (.data d))
  | .lookedUp none => pure (.error .lookup)
  | .assign c q a => check (.assign c q.flatten a) .assign .unit
  | .assignForGasCost c q a =>
    -- quirk Q7: the raw call is passed ℰ(q), length prefix included
    if q.isEmpty then pure (.ok .unit) else check (.assign c (vec id q) a) .assign .unit
  | .bless m a v r z => do orPanic (.bless m a v r z); pure (.ok .unit)  -- quirk Q8
  | .designate ks => check (.designate ks) .designate .unit
  | .yield h => do orPanic (.yield h); pure (.ok .unit)  -- quirk Q8
  | .provide s (.hash h) => do
    match ← op (AOp.lookup none h) with
    | none => pure (.error .lookup)
    | some d => check (.provide s d) .provision .unit
  | .provide s (.inline d) => check (.provide s d) .provision .unit
  | .checkpoint => do op AOp.checkpoint; pure (.ok .unit)
  | .panic => Prog.panic
  | .randomStorageAccumulate none => pure (.ok .unit)
  | .randomStorageAccumulate (some ks) => do
    let key := "count_random_storage".toUTF8.toList
    let n ← match ← op (AOp.read key) with
      | none => pure 0
      | some v => match decode (Dec.fixedN 8) v with
        | some n => pure n
        | none => Prog.panic  -- quirk Q13
    for k in ks do orPanic (.write k k)
    orPanic (.write key (fixed 8 (n + ks.length)))
    pure (.ok .unit)
  | .benchmark => do
    for i in List.range 1000 do
      orPanic (.write s!"item-{now}-{i}".toUTF8.toList s!"{i}".toUTF8.toList)
      op AOp.checkpoint
    pure (.ok .unit)
  | .importSegs _ | .exportSegs _ | .randomStorageRefine _ _ => pure (.error .invalid)

/-- **One work item in accumulate** (`on_work_item`), from its work output `out`: decode it (panic if
    that fails), record it in the ring, store empty results and checkpoint, then run the
    instructions in order. Before each `Checkpoint` instruction, store the results so far. At the
    end, store all results, unless the list contains a `Zombify`. -/
def onWorkItem (C : Consts) (now : Nat) (package out : Bytes) : Prog AOp Unit := do
  match decode (Dec.output C) out with
  | none => Prog.panic
  | some (is, item) =>
    let key := Key.results package item
    addRecent C package item
    store key (encodeResults [])
    op AOp.checkpoint
    let mut results : List Result := []
    for i in is do
      match i with
      | .checkpoint => store key (encodeResults results)
      | _ => pure ()
      let r ← onInstr C now i
      results := results ++ [r]
    -- quirk Q4: any `Zombify`, failed or not, suppresses the final write
    unless is.any (fun | .zombify _ => true | _ => false) do
      store key (encodeResults results)

/-- **One incoming transfer in accumulate** (`on_transfer`): bump the counter under "transfer-count"
    and store ℰ(source, amount, memo) under "transfer{count}". -/
def onTransfer (source amount : Nat) (memo : Bytes) : Prog AOp Unit := do
  let key := "transfer-count".toUTF8.toList
  let n := ((← op (AOp.read key)).bind (decode (Dec.fixedN 4))).getD 0  -- quirk Q12
  orPanic (.write key (fixed 4 ((n + 1) % 2 ^ 32)))  -- quirk Q14
  orPanic (.write s!"transfer{n}".toUTF8.toList (fixed 4 source ++ fixed 8 amount ++ memo))

/-- An accumulate input, as bootstrap decodes it (`AccumulateItem`): an operand, with its package
    hash and its work output (`none` for a work error), or an incoming transfer. -/
inductive Item where
  | work (package : Bytes) (output : Option Bytes)
  | transfer (source amount : Nat) (memo : Bytes)

/-- `AccumulateItem`, as the SDK decodes it. -/
def Dec.item : Dec Item := do
  match ← Dec.byte with
  | 0 => do
    let p ← Dec.take 32
    let _ ← Dec.take 96  -- the segment root, authorizer hash and payload hash
    let _ ← Dec.compact  -- the gas limit
    let r ← match ← Dec.byte with
      | 0 => some <$> Dec.bytes
      | e => if 1 ≤ e ∧ e ≤ 6 then pure none else Dec.fail
    let _ ← Dec.bytes    -- the authorizer trace
    pure (.work p r)
  | 1 => do
    let s ← Dec.fixedN 4
    let _ ← Dec.fixedN 4
    let a ← Dec.fixedN 8
    let m ← Dec.take 128
    let _ ← Dec.fixedN 8
    pure (.transfer s a m)
  | _ => Dec.fail

/-- **Accumulate** at timeslot `now`: fetch the inputs (panic if they do not decode) and handle them
    in order. It returns no hash; a `Yield` instruction sets the yield through the host. -/
def accumulate (C : Consts) (now : Nat) : Prog AOp Unit := do
  match (← op AOp.fetchItems).bind (decode (Dec.vec Dec.item)) with
  | none => Prog.panic
  | some items =>
    for it in items do
      match it with
      | .work p (some out) => onWorkItem C now p out
      | .work _ none => pure ()
      | .transfer s a m => onTransfer s a m

end Services.Bootstrap.Spec
