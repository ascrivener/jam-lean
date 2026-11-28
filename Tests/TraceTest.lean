import JAM.BlockImport
import Tests.TraceState
import Tests.V080
import JamCrypto.Bandersnatch
import JAM.Model

/-!
# Block-import trace runner (davxy/jam-test-vectors `traces/`, GP v0.8.0)

`tracetest [DIR [TRACE …]]` imports each trace's blocks in order with Υ (`JAM.importBlockWith`, the parametric core) under
the tiny parameters; by default every trace present under `vendor/jam-traces/traces`, fetched by
`scripts/fetch-trace-vectors.sh`. **On `gp-v0.8.1` block import is suspended** until v0.8.1 traces
exist (`blockImportSuspended`); only the T(σ) round trip below runs.

The genesis state is decoded from its key-values (`Tests.TraceState`); from then on the runner keeps
the model's own σ and, after each block, compares T(σ') and M_σ(σ') with the step's post-state
key by key. A step whose post-state root equals its pre-state root is a block the importer must
reject; the runner then expects an error and keeps σ. If the model's σ does not match a step's
post-state, the runner reports it (or, at a step listed in `knownDeviations`, counts it as a
known deviation) and continues from the trace's post-state, which `decodeState` always decodes.

The closed model `JAM.importBlock` (Υ with the GP v0.8.1 crypto fixed) is also run once, on the
first block of the first trace present, and checked to give the same result as the parametric core
`JAM.importBlockWith` at the composition it fixes (`closedAgrees`).

Every raw state of the trace (genesis, and each step's pre- and post-state) is also checked by
`roundTrip`: decoded and serialized again, it must give the same key-values and root.

The trace blocks are in the v0.8.0 encoding, whose assurances carry an anchor (equal to H_P,
GP #562); each block is read with `Tests.V080.step080`, which drops the anchors.

The cryptographic primitives (`JAM.Crypto`) are supplied as follows:
* verification (Ed25519, Bandersnatch VRF signatures, Ring VRF): accepts every signature and proof,
  as the trace blocks are known to be validly signed;
* the VRF output Y (`bsOut`, `bsRingOut`): `JamCrypto.Bandersnatch.octetOutput`, the output-point hash
  of the Bandersnatch VRF specification over the signature's first 32 octets as given;
* the ring root O (`bsRingRoot`): the pairs (keys of γ_P, γ_Z) of the states seen so far, since
  every state satisfies γ_Z = O(γ_P); an unknown key sequence yields the empty root.
-/

open JAM JAM.TraceState

def hexS (l : List UInt8) : String :=
  "0x" ++ String.join (l.map fun b => (if b < 16 then "0" else "") ++ (Nat.toDigits 16 b.toNat).asString)

/-- The oracle crypto, given the known ring roots. -/
def oracle (roots : List (List (List UInt8) × List UInt8)) : Crypto :=
  { edVerify := fun _ _ _ => true
    bsVerify := fun _ _ _ _ => true
    bsOut := JamCrypto.Bandersnatch.octetOutput
    bsRingRoot := fun ks => (roots.lookup ks).getD []
    bsRingVerify := fun _ _ _ _ => true
    bsRingOut := JamCrypto.Bandersnatch.octetOutput }

/-- The names of the state components, by the first octet of C(i). -/
def componentName (k : List UInt8) : String :=
  match k.headD 0 with
  | 1 => "α" | 2 => "φ" | 3 => "β" | 4 => "γ" | 5 => "ψ" | 6 => "η" | 7 => "ι" | 8 => "κ"
  | 9 => "λ" | 10 => "ρ" | 11 => "τ" | 12 => "χ" | 13 => "π" | 14 => "ω" | 15 => "ξ" | 16 => "θ"
  | 255 => "δ(info)" | _ => "δ(data)"

/-- The keys whose values differ between the model's T(σ') and the expected key-values. -/
def diffKvs (got exp : List (List UInt8 × List UInt8)) : List String :=
  let missing := exp.filterMap fun (k, v) =>
    match got.lookup k with
    | none => some s!"  missing {componentName k} {hexS k}"
    | some v' => if v == v' then none else
        some s!"  differs {componentName k} {hexS (k.take 8)}…: got {v'.length} octets {hexS (v'.take 48)}… expected {v.length} octets {hexS (v.take 48)}…"
  let extra := got.filterMap fun (k, _) =>
    if (exp.lookup k).isNone then some s!"  extra {componentName k} {hexS k}" else none
  missing ++ extra

/-- T(σ) round trip on a raw state of the trace: decode it (`decodeState`), serialize the result
    again and compare with the raw key-values, key by key and octet by octet, and the state roots.
    This checks the loader and T together, including a_o and a_i, which the decoded accounts carry
    from C(255, s) and T writes back. -/
def roundTrip (p : Params) (what : String) (raw : RawState) : List String :=
  match decodeState p raw.kvs with
  | .error e => [s!"{what}: round trip: cannot decode: {e}"]
  | .ok σ =>
    let got := σ.serializeList
    let gotM : Std.ExtTreeMap (List UInt8) (List UInt8) := Std.ExtTreeMap.ofList got
    let same := got.length == raw.kvs.length && gotM.size == got.length &&
      raw.kvs.all fun (k, v) => gotM.get? k == some v
    if same && σ.root == raw.root.toList then []
    else [s!"{what}: round trip differs ({got.length} keys against {raw.kvs.length})\n" ++
      "\n".intercalate ((diffKvs got raw.kvs).take 12)]

/-- Steps where the trace follows a rule other than GP v0.8.0's, by trace and step number, with
    the reason. At such a step the runner reports the difference, then continues from the trace's
    post-state. -/
def knownDeviations : List (String × Nat × String) :=
  let bless := "bless from a non-manager is accepted (GP #519, vectors' CHANGELOG); GP 0.8.0 answers HUH and the service then panics"
  let handOver := "the delegator hands its role over with bless from a non-manager (GP #519, vectors' CHANGELOG); GP 0.8.0 answers HUH and the service then panics"
  [("fuzzy_light", 77, bless), ("fuzzy_light", 86, handOver), ("fuzzy_light", 118, bless),
   ("fuzzy_light", 148, bless), ("fuzzy_light", 151, bless), ("fuzzy_light", 163, bless),
   ("fuzzy_light", 165, bless), ("fuzzy_light", 179, handOver),
   ("fuzzy", 17, "bless, designate and assign from a service without the privilege answer HUH in GP 0.8.0; the fuzz service stores the results, and the trace's differ (GP #519, vectors' CHANGELOG)")]

structure Summary where
  name : String
  steps : Nat := 0
  passed : Nat := 0
  rejectedOk : Nat := 0
  deviations : Nat := 0
  /-- Raw states (genesis, and each step's pre- and post-state) checked by `roundTrip`. -/
  roundTrips : Nat := 0
  roundTripFails : List String := []
  failures : List String := []
  stoppedAt : Option Nat := none
  totalMs : Nat := 0
  maxMs : Nat := 0
  maxStep : Nat := 0

/-- A step, its block read from the v0.8.0 encoding, with the block's v0.8.0 H_X commitment
    (`Tests.V080`, GP #562). -/
def readStep (path : System.FilePath) : IO (Step × List UInt8) := do
  match Decoder.run (V080.step080 V080.tiny080) (← IO.FS.readBinFile path) >>=
      fun (st, xh) => do return (← upgradeStep st, xh) with
  | .ok s => return s
  | .error e => throw (IO.userError s!"{path}: {e}")

/-- **Block import is suspended until v0.8.1 traces are published** (`docs/gp-v0.8.1-migration.md`,
    "Suspended until v0.8.1 vectors"). The published traces are GP v0.8.0: every header's H_R is a
    v0.8.0 state root, which GP v0.8.1's C(255) and C(13) encodings no longer produce, so Υ rejects
    every block. Rewriting headers would fabricate vectors. Meanwhile the runner checks only the
    T(σ) round trip of every raw state, converted to v0.8.1 form (`upgradeRaw`). -/
def blockImportSuspended : Bool := true

def runTrace (dir : System.FilePath) (name : String) : IO Summary := do
  let p := V080.tiny080
  let tdir := dir / name
  let (gh, graw) ← match Decoder.run (genesis p) (← IO.FS.readBinFile (tdir / "genesis.bin")) >>=
      fun (h, r) => do return (h, ← upgradeRaw r) with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"{name}/genesis.bin: {e}")
  let mut σ ← match decodeState p graw.kvs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name}: genesis state: {e}")
  let mut sum : Summary := { name, roundTrips := 1, roundTripFails := roundTrip p "genesis" graw }
  if σ.root != graw.root.toList then
    sum := { sum with failures := ["genesis: decoded state's root differs"] }
  let mut chain : Chain := { ancestors := [gh] }
  let mut roots : List (List (List UInt8) × List UInt8) := [(σ.pending.map ValidatorKey.bs, σ.ringRoot)]
  let files := ((← tdir.readDir).map (·.fileName)).filter
    (fun f => f.endsWith ".bin" && f != "genesis.bin") |>.qsort (· < ·)
  for f in files do
    let (st, xh) ← readStep (tdir / f)
    let idx := sum.steps + 1
    sum := { sum with steps := idx, roundTrips := sum.roundTrips + 2,
                      roundTripFails := sum.roundTripFails ++ roundTrip p s!"{f} pre" st.pre ++
                        roundTrip p s!"{f} post" st.post }
    if blockImportSuspended then continue
    -- The model's σ against the step's pre-state.
    if σ.root != st.pre.root.toList then
      match decodeState p st.pre.kvs with
      | .ok s =>
        sum := { sum with failures := sum.failures ++ [s!"{f}: σ ≠ pre-state; re-synchronised"] }
        σ := s
      | .error _ =>
        sum := { sum with stoppedAt := some idx,
                          failures := sum.failures ++ [s!"{f}: σ ≠ pre-state and the pre-state has undecodable entries; trace stopped"] }
        break
    let key := σ.pending.map ValidatorKey.bs
    unless roots.any (·.1 == key) do roots := (key, σ.ringRoot) :: roots
    let expectReject := st.pre.root.toList == st.post.root.toList
    let t0 ← IO.monoMsNow
    let r := importBlockWith p (oracle roots) chain σ st.block
    let r ← match r with
      | .ok (s', _) => do let _ := s'.root.length; pure r
      | .error _ => pure r
    let ms := (← IO.monoMsNow) - t0
    sum := { sum with totalMs := sum.totalMs + ms }
    if ms > sum.maxMs then sum := { sum with maxMs := ms, maxStep := idx }
    match r, expectReject with
    | .error e, true =>
      sum := { sum with rejectedOk := sum.rejectedOk + 1,
                        failures := sum.failures ++ [s!"{f}: rejected as expected ({repr e})"] }
    | .error e, false =>
      sum := { sum with failures := sum.failures ++ [s!"{f}: rejected a valid block: {repr e}"] }
      match decodeState p st.post.kvs with
      | .ok s => σ := s; chain := { ancestors := chain.ancestors ++ [st.block.header] }
      | .error _ => sum := { sum with stoppedAt := some idx }; break
    | .ok _, true =>
      sum := { sum with failures := sum.failures ++ [s!"{f}: imported a block the trace rejects"] }
    | .ok (s', _), false =>
      chain := { ancestors := chain.ancestors ++ [st.block.header] }
      if s'.root == st.post.root.toList then
        sum := { sum with passed := sum.passed + 1 }
        σ := s'
      else
        let d := diffKvs s'.serializeList st.post.kvs
        let known := knownDeviations.find? fun (t, i, _) => t == name && i == idx
        if known.isSome then sum := { sum with deviations := sum.deviations + 1 }
        let head := match known with
          | some (_, _, why) => s!"{f}: known deviation: {why}"
          | none => s!"{f}: post-state root differs"
        -- Continue from the trace's post-state, with the storage keys of σ and σ'.
        match decodeState p st.post.kvs with
        | .ok s =>
          sum := { sum with failures := sum.failures ++ [head ++ "; continuing from the trace's post-state\n" ++ "\n".intercalate (d.take 12)] }
          σ := s
        | .error e =>
          sum := { sum with stoppedAt := some idx,
                            failures := sum.failures ++ [head ++ s!"; the post-state cannot be decoded ({e}); trace stopped\n" ++ "\n".intercalate (d.take 12)] }
          break
  return sum

/-! ## `lookupAnchorKnown` (§11.4.1, GP v0.8.1 eq. 11.38)

Regression test: the lookup anchor's child must carry the lookup anchor's posterior state root
x_lookupanchorpoststate as its prior state root, not the anchor's x_stateroot. Here the two roots
differ, so a context that names the lookup anchor's root is accepted and one that names the
anchor's root is rejected. -/

/-- 32 copies of `b`, a stand-in hash. -/
def h32 (b : UInt8) : ByteArray := ⟨(List.replicate 32 b).toArray⟩

/-- A header with only the fields `lookupAnchorKnown` reads set. -/
def hdrLA (parent root : ByteArray) (slot : Nat) : Header :=
  { parent, priorStateRoot := root, extrinsicHash := h32 0, slot, epochMark := none,
    winnersMark := none, offendersMark := [], authorIndex := 0, vrfSig := .empty, sealSig := .empty }

/-- The lookup anchor (slot 7, posterior state root 0xbb…) and its child. -/
def laAnchor : Header := hdrLA (h32 1) (h32 2) 7
def laChild : Header := hdrLA ⟨laAnchor.hash.toArray⟩ (h32 0xbb) 8

/-- A context whose anchor root (0xaa…) differs from its lookup anchor's root `lookupRoot`. -/
def laCtx (lookupRoot : ByteArray) : RefineContext :=
  { anchorHash := h32 3, anchorSlot := 8, anchorStateRoot := h32 0xaa, anchorAccOutLog := h32 4,
    lookupAnchorHash := ⟨laAnchor.hash.toArray⟩, lookupAnchorSlot := 7,
    lookupAnchorStateRoot := lookupRoot }

#guard lookupAnchorKnown [laAnchor, laChild] (laCtx (h32 0xbb))
#guard !lookupAnchorKnown [laAnchor, laChild] (laCtx (h32 0xaa))
#guard !lookupAnchorKnown [laAnchor, laChild] { laCtx (h32 0xbb) with anchorStateRoot := h32 0xbb, lookupAnchorStateRoot := h32 0xaa }

/-- `JAM.importBlock srs` (the closed model) agrees with `JAM.importBlockWith` at the composed crypto
    `withSignatures (Ring.crypto srs V c)` (v0.8.1, `Reading.vectors`) on the first block of trace
    `name`: the same error, or post-states with the same root. They are equal by definition
    (`JAM.importBlock_eq`, `JAM.crypto_eq_compose`); this checks that the closed function
    runs on a vector. -/
def closedAgrees (dir : System.FilePath) (name : String) : IO Bool := do
  let p := V080.tiny080
  let tdir := dir / name
  let (gh, graw) ← match Decoder.run (genesis p) (← IO.FS.readBinFile (tdir / "genesis.bin")) >>=
      fun (h, r) => do return (h, ← upgradeRaw r) with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"{name}/genesis.bin: {e}")
  let σ ← match decodeState p graw.kvs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name}: genesis state: {e}")
  let files := ((← tdir.readDir).map (·.fileName)).filter
    (fun f => f.endsWith ".bin" && f != "genesis.bin") |>.qsort (· < ·)
  let some (f : String) := files[0]? | return true
  let (st, _) ← readStep (tdir / f)
  let srs ← JamCrypto.Ring.Srs.load "JamCryptoTest/data/bls12-381-srs-2-11-uncompressed-zcash.bin"
  let chain : Chain := { ancestors := [gh] }
  let composed := JamCrypto.withSignatures
    (JamCrypto.Ring.crypto srs 6 (oracle []) (gp := .v081) (rd := .vectors))
    (gp := .v081) (rd := .vectors)
  let outcome (r : Except BlockError (State × ImportTrace)) : String :=
    match r with
    | .ok (s', _) => s!"ok {hexS s'.root}"
    | .error e => s!"error {repr e}"
  let closed := outcome (JAM.importBlock srs p chain σ st.block)
  let param := outcome (importBlockWith p composed chain σ st.block)
  IO.println s!"{name}/{f}: closed Υ (JAM.importBlock): {closed}"
  if closed == param then return true
  IO.println s!"  differs from the parametric call: {param}"
  return false

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "vendor/jam-traces/traces"
  let all := ["fallback", "safrole", "storage", "storage_light", "preimages", "preimages_light",
              "fuzzy", "fuzzy_light"]
  let names : List String ← match args.drop 1 with
    | [] => all.filterM fun (n : String) => (dir / n / "genesis.bin").pathExists
    | ns => pure ns
  let mut bad := false
  for n in names do
    let s ← runTrace dir n
    if blockImportSuspended then
      IO.println s!"{n}: {s.steps} steps; block import suspended (v0.8.0 traces: header roots are v0.8.0; block import resumes with v0.8.1 traces)"
    else
      IO.println s!"{n}: {s.passed}/{s.steps} imported with matching state, {s.rejectedOk} rejected as expected, {s.deviations} known deviations; total {s.totalMs} ms, slowest block {s.maxStep} at {s.maxMs} ms"
    IO.println s!"  T(σ) round trip: {s.roundTrips - s.roundTripFails.length}/{s.roundTrips} raw states decode and re-serialize byte-identically"
    for f in s.roundTripFails do IO.println s!"  {f}"
    unless s.roundTripFails.isEmpty do bad := true
    for f in s.failures do IO.println s!"  {f}"
    if let some i := s.stoppedAt then
      IO.println s!"  stopped at step {i}: the trace's state could not be decoded"
    if !blockImportSuspended && s.passed + s.rejectedOk + s.deviations != s.steps then bad := true
  if let some n := names.head? then
    unless ← closedAgrees dir n do bad := true
  return if bad then 1 else 0
