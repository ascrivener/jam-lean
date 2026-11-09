import JAM.BlockImport
import Tests.TraceState
import Tests.Sha512

/-!
# Block-import trace runner (davxy/jam-test-vectors `traces/`, GP v0.8.0)

`tracetest [DIR [TRACE …]]` imports each trace's blocks in order with `JAM.importBlock` (Υ) under
the tiny parameters; by default every trace present under `vendor/jam-traces/traces`, fetched by
`scripts/fetch-trace-vectors.sh`.

The genesis state is decoded from its key-values (`Tests.TraceState`); from then on the runner keeps
the model's own σ and, after each block, compares T(σ') and M_σ(σ') with the step's post-state
key by key. A step whose post-state root equals its pre-state root is a block the importer must
reject; the runner then expects an error and keeps σ. If the model's σ does not match a step's
pre-state, the runner reports it and re-synchronises from the pre-state when that state can be
decoded, and otherwise stops the trace.

The cryptographic primitives (`JAM.Crypto`) are supplied as follows:
* verification (Ed25519, Bandersnatch IETF VRF, Ring VRF): accepts every signature and proof,
  as the trace blocks are known to be validly signed;
* the VRF output Y (`bsOut`, `bsRingOut`): `JAM.Sha512.vrfOutput`, the output-point hash of the
  Bandersnatch VRF specification (see `Tests/Sha512.lean`);
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
    bsOut := Sha512.vrfOutput
    bsRingRoot := fun ks => (roots.lookup ks).getD []
    bsRingVerify := fun _ _ _ _ => true
    bsRingOut := Sha512.vrfOutput }

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

structure Summary where
  name : String
  steps : Nat := 0
  passed : Nat := 0
  rejectedOk : Nat := 0
  failures : List String := []
  stoppedAt : Option Nat := none
  totalMs : Nat := 0
  maxMs : Nat := 0
  maxStep : Nat := 0

def readStep (path : System.FilePath) : IO Step := do
  match Decoder.run (step Params.tiny) (← IO.FS.readBinFile path) with
  | .ok s => return s
  | .error e => throw (IO.userError s!"{path}: {e}")

def runTrace (dir : System.FilePath) (name : String) : IO Summary := do
  let p := Params.tiny
  let tdir := dir / name
  let (gh, graw) ← match Decoder.run (genesis p) (← IO.FS.readBinFile (tdir / "genesis.bin")) with
    | .ok g => pure g
    | .error e => throw (IO.userError s!"{name}/genesis.bin: {e}")
  let mut σ ← match decodeState p graw.kvs with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"{name}: genesis state: {e}")
  let mut sum : Summary := { name }
  if σ.root != graw.root.toList then
    sum := { sum with failures := ["genesis: decoded state's root differs"] }
  let mut chain : Chain := { ancestors := [gh] }
  let mut roots : List (List (List UInt8) × List UInt8) := [(σ.pending.map ValidatorKey.bs, σ.ringRoot)]
  let files := ((← tdir.readDir).map (·.fileName)).filter
    (fun f => f.endsWith ".bin" && f != "genesis.bin") |>.qsort (· < ·)
  for f in files do
    let st ← readStep (tdir / f)
    let idx := sum.steps + 1
    sum := { sum with steps := idx }
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
    let r := importBlock p (oracle roots) chain σ st.block
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
      let got := s'.serializeList
      if s'.root == st.post.root.toList then
        sum := { sum with passed := sum.passed + 1 }
      else
        let d := diffKvs got st.post.kvs
        sum := { sum with failures := sum.failures ++ [s!"{f}: post-state root differs\n" ++ "\n".intercalate (d.take 12)] }
      σ := s'
  return sum

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "vendor/jam-traces/traces"
  let all := ["fallback", "safrole", "storage", "storage_light", "preimages", "preimages_light",
              "fuzzy", "fuzzy_light"]
  let names ← match args.drop 1 with
    | [] => all.filterM fun n => (dir / n / "genesis.bin").pathExists
    | ns => pure ns
  let mut bad := false
  for n in names do
    let s ← runTrace dir n
    IO.println s!"{n}: {s.passed}/{s.steps} imported with matching state, {s.rejectedOk} rejected as expected; total {s.totalMs} ms, slowest block {s.maxStep} at {s.maxMs} ms"
    for f in s.failures do IO.println s!"  {f}"
    if s.passed + s.rejectedOk != s.steps then bad := true
  return if bad then 1 else 0
