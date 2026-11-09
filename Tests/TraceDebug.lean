import JAM.BlockImport
import JAM.Sha512
import Tests.TraceState

/-! Development aid: replay a trace up to a step, then show that step's accumulation, with every
host call of the deferred-transfer recipients' runs. `lake env lean --run Tests/TraceDebug.lean DIR TRACE N`. -/

open JAM JAM.TraceState PVM

def oracle (roots : List (List (List UInt8) × List UInt8)) : Crypto :=
  { edVerify := fun _ _ _ => true, bsVerify := fun _ _ _ _ => true, bsOut := Sha512.vrfOutput
    bsRingRoot := fun ks => (roots.lookup ks).getD [], bsRingVerify := fun _ _ _ _ => true
    bsRingOut := Sha512.vrfOutput }

def readStep (path : System.FilePath) : IO Step := do
  match Decoder.run (step Params.tiny) (← IO.FS.readBinFile path) with
  | .ok s => return s
  | .error e => throw (IO.userError s!"{path}: {e}")

def runLogged (params : Params) (entropy : List UInt8) (st : PartialState) (t s g : Nat)
    (inputs : List AccumulateInput) : IO Unit := do
  let some c := (st.accounts.get? s).bind (·.code) | IO.println s!"  {s}: no code"; return
  let env : AccEnv := { params, slot := t, entropy, inputs, code := c }
  let x := initImplications st s t entropy
  let args : ByteArray := ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat inputs.length).toArray⟩
  let f : HostFn AccCtx := fun n gas ω μ ctx =>
    let r := accHostFn env n gas ω μ ctx
    dbgTrace s!"    host {n} gas {gas} ω7..12 {(ω.toList.drop 7)} -> {repr r.status} ω7={r.regs.toList.getD 7 0} gas'={r.gas}" fun _ => r
  let (u, o, _) := psiM c 5 (UInt64.ofNat g) args f (x, x)
  IO.println s!"  {s}: used {u}, {match o with | .ok b => s!"ok {b.size}" | .panic => "panic" | .oog => "oog"}"

def storageKeys (σ : State) : List (Nat × List UInt8) :=
  σ.accounts.toList.flatMap fun (s, a) => a.storage.keys.map (s, ·)

/-- Each service of **R** run alone with its operands, logging host calls; returns the last host
    call and its ω7 result, and the outcome. -/
def showStep (p : Params) (σ : State) (roots : List (List (List UInt8) × List UInt8)) (chain : Chain)
    (st : Step) : IO Unit := do
  let .ok (_, tr) := importBlock p (oracle roots) chain σ st.block | IO.println "  import failed"; return
  let H := st.block.header
  let entropy := hashL ((σ.eta.getD 0 []) ++ Sha512.vrfOutput H.vrfSig.toList)
  let e := σ.partialState
  IO.println s!"  χ: manager {e.manager} assigners {e.assigners} delegator {e.delegator} registrar {e.registrar}"
  for s in ((tr.available.flatMap fun w => w.digests.map (·.service))).eraseDups do
    let r := tr.available
    let iU := r.flatMap fun w => (w.digests.filter (·.service == s)).map fun d =>
      AccumulateInput.operand
        { packageHash := w.spec.packageHash, segmentRoot := w.spec.segmentRoot,
          authorizer := w.authorizerHash, payloadHash := d.payloadHash, gasLimit := d.gasLimit,
          authTrace := w.authTrace, result := d.result }
    let g := e.alwaysAcc.getD s 0 + (r.flatMap fun w => (w.digests.filter (·.service == s)).map (·.gasLimit)).sum
    runLogged p entropy e H.slot s g iU

def main (args : List String) : IO Unit := do
  let dir :: name :: steps := args | throw (IO.userError "DIR TRACE N…")
  let want := steps.map String.toNat!
  let p := Params.tiny
  let tdir : System.FilePath := dir / name
  let .ok (gh, graw) := Decoder.run (genesis p) (← IO.FS.readBinFile (tdir / "genesis.bin")) | throw (IO.userError "genesis")
  let .ok σ0 := decodeState p graw.kvs | throw (IO.userError "genesis state")
  let mut σ := σ0
  let mut chain : Chain := { ancestors := [gh] }
  let roots := [(σ.pending.map ValidatorKey.bs, σ.ringRoot)]
  let last := want.foldl max 0
  for i in [1:last + 1] do
    let st ← readStep (tdir / s!"{String.ofList (List.replicate (8 - (toString i).length) '0')}{i}.bin")
    if want.contains i then
      IO.println s!"step {i}:"
      showStep p σ roots chain st
    if st.pre.root == st.post.root then continue
    match importBlock p (oracle roots) chain σ st.block with
    | .ok (s', _) =>
      chain := { ancestors := chain.ancestors ++ [st.block.header] }
      if s'.root == st.post.root.toList then σ := s'
      else match decodeState p st.post.kvs (storageKeys σ ++ storageKeys s') with
        | .ok s => σ := s
        | .error e => throw (IO.userError s!"step {i}: {e}")
    | .error e => throw (IO.userError s!"step {i}: {repr e}")
