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

def main (args : List String) : IO Unit := do
  let [dir, name, nS] := args | throw (IO.userError "DIR TRACE N")
  let n := nS.toNat!
  let p := Params.tiny
  let tdir : System.FilePath := dir / name
  let .ok (gh, graw) := Decoder.run (genesis p) (← IO.FS.readBinFile (tdir / "genesis.bin")) | throw (IO.userError "genesis")
  let .ok σ0 := decodeState p graw.kvs | throw (IO.userError "genesis state")
  let mut σ := σ0
  let mut chain : Chain := { ancestors := [gh] }
  let roots := [(σ.pending.map ValidatorKey.bs, σ.ringRoot)]
  for i in [1:n] do
    let st ← readStep (tdir / s!"{String.ofList (List.replicate (8 - (toString i).length) '0')}{i}.bin")
    if st.pre.root == st.post.root then continue
    match importBlock p (oracle roots) chain σ st.block with
    | .ok (s', _) => σ := s'; chain := { ancestors := chain.ancestors ++ [st.block.header] }
    | .error e => throw (IO.userError s!"step {i}: {repr e}")
  let st ← readStep (tdir / s!"{String.ofList (List.replicate (8 - (toString n).length) '0')}{n}.bin")
  IO.println s!"replayed to {n - 1}; σ matches pre-state: {σ.root == st.pre.root.toList}"
  let .ok (_, tr) := importBlock p (oracle roots) chain σ st.block | throw (IO.userError "import")
  let H := st.block.header
  let entropy := hashL ((σ.eta.getD 0 []) ++ Sha512.vrfOutput H.vrfSig.toList)
  IO.println s!"R: {tr.available.map fun w => (w.core, w.digests.map fun d => (d.service, d.gasLimit))}"
  let e := σ.partialState
  let (e1, t1, b1, u1) := accPar p entropy H.slot e [] tr.available e.alwaysAcc
  IO.println s!"round 1: used {u1}, yields {b1.map (·.1)}, transfers {t1.map fun x => (x.source, x.dest, x.amount, x.gas)}"
  for s in ((tr.available.flatMap fun w => w.digests.map (·.service))).eraseDups do
    let r := tr.available
    let iU := r.flatMap fun w => (w.digests.filter (·.service == s)).map fun d =>
      AccumulateInput.operand
        { packageHash := w.spec.packageHash, segmentRoot := w.spec.segmentRoot,
          authorizer := w.authorizerHash, payloadHash := d.payloadHash, gasLimit := d.gasLimit,
          authTrace := w.authTrace, result := d.result }
    let g := e.alwaysAcc.getD s 0 + (r.flatMap fun w => (w.digests.filter (·.service == s)).map (·.gasLimit)).sum
    runLogged p entropy e H.slot s g iU
  for d in (t1.map (·.dest)).eraseDups do
    let ins := (t1.filter (·.dest == d)).map AccumulateInput.transfer
    let g := ((t1.filter (·.dest == d)).map (·.gas)).sum
    let st1 : PartialState := match e1.accounts.get? d with
      | some a => { e1 with accounts := e1.accounts.insert d { a with balance := a.balance + ((t1.filter (·.dest == d)).map (·.amount)).sum } }
      | none => e1
    runLogged p entropy st1 H.slot d g ins
