import JAM
open PVM JAM

def go (Q : Prepared) (f : HostFn RefineCtx) (i : Nat) (gas : UInt64) (ch : Bool)
    (ω : Regs) (μ : Memory) (x : RefineCtx) (acc : Array (Nat × Regs × Memory)) (hosts : Array Nat) :
    Nat → Array (Nat × Regs × Memory) × Array Nat × Status × Regs × Memory
  | 0 => (acc, hosts, .panic, ω, μ)
  | n + 1 =>
    if !(Q.valid && Q.prog.vInst i) then (acc, hosts, .panic, ω, μ) else
    let r := Q.step i gas ch ω μ
    let acc := acc.push (i, ω, μ)
    match r.status with
    | .cont => go Q f r.pc r.gas r.charged r.regs r.mem x acc hosts n
    | .host h =>
      let y := f h.toNat r.gas r.regs r.mem x
      match y.status with
      | .cont => go Q f (Q.prog.next i) y.gas r.charged y.regs y.mem y.ctx acc (hosts.push h.toNat) n
      | _ => (acc, hosts.push h.toNat, .panic, y.regs, y.mem)
    | st => (acc, hosts, st, r.regs, r.mem)

def mkItem (h : List UInt8) (sid : Nat) (y : List UInt8) : WorkItem where
  service := sid
  codeHash := ⟨h.toArray⟩
  payload := ⟨y.toArray⟩
  refineGasLimit := 1000000000
  accumulateGasLimit := 0
  exportCount := 0
  importSegments := []
  extrinsics := []

def ctx0 : RefineContext where
  anchorHash := ⟨#[]⟩
  anchorSlot := 0
  anchorStateRoot := ⟨#[]⟩
  anchorAccOutLog := ⟨#[]⟩
  lookupAnchorHash := ⟨#[]⟩
  lookupAnchorSlot := 10
  lookupAnchorStateRoot := ⟨#[]⟩

def mkPkg (h : List UInt8) (sid n : Nat) (w : WorkItem) : WorkPackage where
  authToken := ⟨#[]⟩
  authCodeHost := sid
  authCodeHash := ⟨h.toArray⟩
  authConfig := ⟨#[]⟩
  context := ctx0
  items := List.replicate n w

def mkEnv (code : ByteArray) (sid i : Nat) (d : Accounts) (pkg : WorkPackage) : RefineHost.Env where
  params := .full
  service := sid
  accounts := d
  lookupSlot := 10
  code := code
  exportOffset := 0
  fetch := { params := .full, package := some pkg, entropy := some (List.replicate 32 0),
             authTrace := some [], itemIndex := some i, imports := some [[]], extrinsics := some [[]] }

def cases : List (Nat × Nat × Nat × List UInt8) :=
  [(3, 0, 7, [255]), (1, 0, 7, [255]), (200, 5, 70000, [255]), (3, 0, 7, List.replicate 100 255),
   (3, 0, 7, []), (3, 0, 7, [12, 9, 9]), (3, 0, 2^31, [255]), (3, 0, 7, List.replicate 20000 255)]


def leanInstr (ins : Instr) : String :=
  let r := toString (repr ins)
  r.replace "PVM.Instr." "." |>.replace "PVM.NoArgsOp." "." |>.replace "PVM.OneImmOp." "." |>.replace "PVM.RegExtImmOp." "."
   |>.replace "PVM.TwoImmOp." "." |>.replace "PVM.OneOffsetOp." "." |>.replace "PVM.RegImmOp." "." |>.replace "PVM.RegTwoImmOp." "."
   |>.replace "PVM.RegImmOffsetOp." "." |>.replace "PVM.TwoRegOp." "." |>.replace "PVM.TwoRegImmOp." "." |>.replace "PVM.TwoRegOffsetOp." "."
   |>.replace "PVM.TwoRegTwoImmOp." "." |>.replace "PVM.ThreeRegOp." "."

/-- A service the generator works on: its blob, the Lean namespace and name of its files, the
    base input of the traced run and the classes of inputs of the segment analysis, and the
    functions whose code facts are emitted in full for summaries. Inputs are refine's
    (core index, item index, service id, payload). -/
structure Svc where
  name : String
  label : String
  blob : String
  flag : String
  base : Nat × Nat × Nat × List UInt8
  emptyBase : Nat × Nat × Nat × List UInt8
  segClass : List (Nat × Nat × Nat × List UInt8)
  emptyClass : List (Nat × Nat × Nat × List UInt8)
  postClass : List (Nat × Nat × Nat × List UInt8)
  fnRanges : List (Nat × Nat)
  /-- Whether `Services/<name>/Memcpy.lean` exists (`memcpy_small` at the head of `fnRanges`):
      the prefix then calls it for each `memcpy` of fewer than 16 octets instead of stepping. -/
  memcpySummary : Bool := false
  /-- `segx`: more inputs for the class (values of the widths and ranges that the base classes
      leave out, so that no value they happen to share is stated). -/
  segxExtra : List (Nat × Nat × Nat × List UInt8) := []
  /-- `segx`: facts about the variables that the steps need, each proved by `omega` from the
      variables' bounds, with the variables they use. -/
  segFacts : List (List String × String) := []
  /-- `segx0` / `chainx0`: more inputs for the class of empty payloads. -/
  emptyExtra : List (Nat × Nat × Nat × List UInt8) := []
  /-- `code`: also the instructions on the run of `emptyBase`. -/
  emptyCode : Bool := false

/-- Witness (`services/witness`). -/
def witnessSvc : Svc where
  name := "Witness"
  label := "witness"
  blob := "services/witness/witness-service.jam"
  flag := ""
  base := (3, 0, 7, [255])
  emptyBase := (3, 0, 7, [])
  segClass := [(5, 0, 9, [200]), (3, 0, 7, List.replicate 15 255), (3, 0, 7, List.replicate 8 13), (200, 0, 70000, [12])]
  emptyClass := [(5, 0, 9, []), (200, 0, 70000, []), (300, 0, 3, [])]
  postClass := [(5, 0, 9, [200]), (3, 0, 7, List.replicate 15 255), (200, 1, 70000, [12]), (20000, 300, 3, []),
    (3, 0, 7, List.replicate 300 255)]
  fnRanges := [(186740, 187150), (184570, 184870), (43276, 43490)]
  segxExtra := [(3, 0, 2147483653, [200]), (3, 1, 7, [255]), (20000, 300, 4000000000, List.replicate 3 77)]
  segFacts := [(["Y"], "(Y + 31) / 32 = 1")]
  emptyExtra := [(3, 0, 2147483653, []), (3, 1, 7, []), (20000, 300, 4000000000, [])]
  emptyCode := true

/-- Parity's bootstrap service (`services/bootstrap`): the payload is an encoded `Instructions`,
    the instruction list then a 32-octet salt; the base input has no instructions. -/
def bootstrapSvc : Svc where
  name := "Bootstrap"
  label := "bootstrap"
  blob := "services/bootstrap/jam-bootstrap-service.jam"
  flag := "--service bootstrap "
  base := (3, 0, 7, 0 :: List.replicate 32 0)
  emptyBase := (3, 0, 7, [])
  segClass := [(5, 0, 9, 0 :: List.replicate 32 7), (200, 0, 70000, 0 :: List.replicate 32 255)]
  emptyClass := [(5, 0, 9, []), (200, 0, 70000, [])]
  postClass := [(5, 0, 9, 0 :: List.replicate 32 7), (200, 1, 70000, 0 :: List.replicate 32 255),
    (20000, 300, 3, 0 :: List.replicate 32 1)]
  fnRanges := [(68729, 69139)]
  memcpySummary := true

def services : List Svc := [witnessSvc, bootstrapSvc]

/-- The traced refine of a service for arguments `c`, `i`, `sid`, payload `y`. -/
def traceFor (code : ByteArray) (h : List UInt8) (acct : ServiceAccount) (Q : Prepared)
    (c i sid : Nat) (y : List UInt8) : Option (Array (Nat × Regs × Memory)) := do
  let pkg := mkPkg h sid (i + 1) (mkItem h sid y)
  let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat sid ++ Codec.var ⟨y.toArray⟩ ++
    (Blake2b.hash256 ⟨pkg.encode.toArray⟩).toList).toArray⟩
  let (_, ω, μ) ← standardInit code a
  let env := mkEnv code sid i (Std.ExtTreeMap.ofList [(sid, acct)]) pkg
  let (tr, _, _, _, _) := go Q (toHostFn (RefineHost.dispatch env)) 0 1000000000 false ω μ (∅, []) #[] #[] 300000
  return tr

/-- Maximal runs of consecutive naturals in a sorted list, as [lo, hi). -/
def ranges (xs : List Nat) : List (Nat × Nat) :=
  xs.foldl (fun acc x => match acc with
    | (lo, hi) :: rest => if x == hi then (lo, hi + 1) :: rest else (x, x + 1) :: acc
    | [] => [(x, x + 1)]) [] |>.reverse

/-- The symbolic variables a class of inputs offers: `ext` (`segx`) adds the payload's first
    octet T and the reader position Q after the argument header. -/
def varNames (ext : Bool) (baseP : Nat × Nat × Nat × List UInt8) : List String :=
  if ext then (if baseP.2.2.2.isEmpty then ["Y", "S", "C", "I", "L", "Q"] else ["Y", "S", "C", "I", "L", "T", "Q"])
  else ["Y", "S", "C", "I", "L"]

/-- A variable's value for input `q = (c, i, s, y)`. -/
def pickVar (q : Nat × Nat × Nat × List UInt8) (v : String) : Nat :=
  let header := (Codec.nat q.1).length + (Codec.nat q.2.1).length + (Codec.nat q.2.2.1).length + (Codec.nat q.2.2.2.length).length
  match v with
  | "C" => q.1 | "I" => q.2.1 | "S" => q.2.2.1
  | "L" => header + q.2.2.2.length + 32
  | "T" => (q.2.2.2.headD 0).toNat
  | "Q" => 2 ^ 32 - 2 ^ 16 - 2 ^ 24 + header
  | _ => q.2.2.2.length

/-- A value that equals an input parameter (`ext`: or a constant plus one or two of them) in every
    run of the class `allQ` (the base input first), as a Lean expression over the variables. -/
def matchVarG (ext : Bool) (names : List String) (allQ : List (Nat × Nat × Nat × List UInt8))
    (valBase : Nat) (valsOther : List Nat) : Option String := Id.run do
  let vals := valBase :: valsOther
  let baseP := allQ.head!
  let fits (f : (Nat × Nat × Nat × List UInt8) → Int) : Option Int :=
    let k := (vals.head! : Int) - f baseP
    if (vals.zip allQ).all (fun (x, q) => (x : Int) == f q + k) then some k else none
  let showE (vs : List String) (k : Int) : String :=
    "(" ++ " + ".intercalate vs ++ (if k == 0 then "" else if k > 0 then s!" + {k}" else s!" - {-k}") ++ ")"
  for v in names do
    if let some 0 := fits (fun q => (pickVar q v : Int)) then return some v
  if !ext then return none
  for v in names do
    if let some k := fits (fun q => (pickVar q v : Int)) then
      if k ≥ 0 || (allQ.all fun q => (pickVar q v : Int) + k ≥ 0) then return some (showE [v] k)
  for v in names do
    for u in names do
      if v < u then
        if let some k := fits (fun q => (pickVar q v : Int) + pickVar q u) then
          if k ≥ 0 then return some (showE [v, u] k)
  return none

/-- What a segment of the traced path reads and leaves (see the `seg` mode). -/
structure SegInfo where
  A : Nat
  B : Nat
  pcA : Nat
  pcB : Nat
  vars : List String
  regFacts : List (Nat × Nat)
  symRegs : List (Nat × String)
  symLoads : List (Nat × Nat × String)
  wr : List (Nat × Nat)
  rr : List (Nat × Nat)
  loads : List (Nat × Nat × List Nat)
  byteFacts : List (Nat × Nat)
  wregs : List Nat
  regPost : List (Nat × Option Nat)
  symPost : List (Nat × String)
  memPost : List (Nat × Nat)
  pcs : List Nat
  /-- `segx`: 8-octet words the segment leaves holding a symbolic value. -/
  symMem : List (Nat × String) := []
  deriving Inhabited

/-- Analyze steps `k0 + a … k0 + b − 1` of trace `tr`, against the other traces of the class
    (aligned at `k0`/their own join index) and their input parameters `(c, i, s, |y|)`. -/
def analyzeSeg (P : Program) (tr : Array (Nat × Regs × Memory))
    (others : Array (Array (Nat × Regs × Memory) × Nat)) (otherPs : Array (Nat × Nat × Nat × List UInt8))
    (k0 a b : Nat) (out : Bool) (baseP : Nat × Nat × Nat × List UInt8 := (3, 0, 7, [255]))
    (ext : Bool := false) (extra : List Nat := []) (staticW : List Nat := []) : IO SegInfo := do
  let A := k0 + a; let B := k0 + b
  let some (pcA, rA, mA) := tr[A]? | throw (IO.userError "step out of range")
  let some (pcB, rB, mB) := tr[B]? | throw (IO.userError "step out of range")
  let agreeReg (k : Nat) (j : Nat) : Bool :=
    others.all fun (t2, k2) => (t2[k2 + (k - k0)]?.map (fun x => x.2.1[j]!)) == (tr[k]?.map (fun x => x.2.1[j]!))
  let agreeMem (k : Nat) (addr : Nat) : Bool :=
    others.all fun (t2, k2) => (t2[k2 + (k - k0)]?.map (fun x => x.2.2.read addr)) == (tr[k]?.map (fun x => x.2.2.read addr))
  -- registers written in the slice
  let mut wregs : List Nat := staticW
  for k in [A:B] do
    let some (_, r0, _) := tr[k]? | continue
    let some (_, r1, _) := tr[k+1]? | continue
    for j in [0:13] do
      if r0[j]! != r1[j]! && !wregs.contains j then wregs := j :: wregs
  -- memory: loads before writes, written and read addresses
  let mut written : Std.HashSet Nat := {}
  let mut wlist : List Nat := []
  let mut rlist : List Nat := []
  let mut loads : Array (Nat × Nat) := #[]
  for k in [A:B] do
    let some (pc, regs, mem) := tr[k]? | continue
    let some ins := P.decode pc | continue
    let m := P.exec pc ins regs mem
    match m.reads.head? with
    | some r0 =>
      let a0 := r0 % 2 ^ 32
      if m.reads.all (fun r => !written.contains (r % 2 ^ 32)) && !(loads.contains (a0, m.reads.length)) then
        loads := loads.push (a0, m.reads.length)
    | none => pure ()
    for r in m.reads do
      let a := r % 2 ^ 32
      if !written.contains a && !rlist.contains a then rlist := a :: rlist
    for w in m.writes do
      let a := w % 2 ^ 32
      if !written.contains a then wlist := a :: wlist
      written := written.insert a
  -- live written octets: read after B before being overwritten
  let mut live : List Nat := []
  let mut over : Std.HashSet Nat := {}
  for k in [B:tr.size] do
    let some (pc, regs, mem) := tr[k]? | continue
    let some ins := P.decode pc | continue
    let m := P.exec pc ins regs mem
    for r in m.reads do
      let a := r % 2 ^ 32
      if written.contains a && !over.contains a && !live.contains a then live := a :: live
    for w in m.writes do over := over.insert (w % 2 ^ 32)
  let wr := ranges (wlist.mergeSort)
  let rr := ranges (rlist.mergeSort)
  let regFacts := (List.range 13).filter (agreeReg A)
  let goodLoads := loads.toList.filter fun (a, k) =>
    (List.range k).all fun j => agreeMem A (a + j)
  let names := varNames ext baseP
  let allQ := baseP :: otherPs.toList
  let matchVar (valBase : Nat) (valsOther : List Nat) : Option String :=
    matchVarG ext names allQ valBase valsOther
  let mut symLoads : List (Nat × Nat × String) := []
  for (a, k) in loads.toList do
    if !goodLoads.contains (a, k) then
      let vb := Num.decodeLE (mA.readN a k)
      let vo := (others.toList).map fun (t2, k2) =>
        (t2[k2 + (A - k0)]?.map (fun x => Num.decodeLE (x.2.2.readN a k))).getD 0
      match matchVar vb vo with
      | some v => symLoads := (a, k, v) :: symLoads
      | none => IO.eprintln s!"input-dependent load at {a} ({k} octets)"
  let mut symRegs : List (Nat × String) := []
  for j in [0:13] do
    if !agreeReg A j then
      let vo := (others.toList).map fun (t2, k2) => (t2[k2 + (A - k0)]?.map (fun x => x.2.1[j]!.toNat)).getD 0
      if let some v := matchVar rA[j]!.toNat vo then symRegs := (j, v) :: symRegs
  let mut symPost : List (Nat × String) := []
  for j in wregs do
    if !agreeReg B j then
      let vo := (others.toList).map fun (t2, k2) => (t2[k2 + (B - k0)]?.map (fun x => x.2.1[j]!.toNat)).getD 0
      if let some v := matchVar rB[j]!.toNat vo then symPost := (j, v) :: symPost
  let vars0 := ((symLoads.map (·.2.2) ++ symRegs.map (·.2) ++ symPost.map (·.2)).flatMap
    (fun e => ((e.replace "(" "").replace ")" "" |>.splitOn " ").filter names.contains)).eraseDups
  let regPost := (List.range 13).filter fun j => !wregs.contains j || agreeReg B j
  for j in wregs do
    if !agreeReg B j then IO.eprintln s!"input-dependent register {j} at the end"
  -- `out`: also the octets of the output, ω₇ … ω₇ + ω₈ at the end (what Ψ_R returns at the halt)
  let outBytes := if out then
      (List.range rB[8]!.toNat).map (rB[7]!.toNat + ·) else []
  -- `ext`: live 8-octet words, all written, that hold the same symbolic value in every run
  let mut symMem : List (Nat × String) := []
  if ext then
    let words := ((live.map (fun a => a - a % 8)).eraseDups.mergeSort).filter fun a =>
      (List.range 8).all fun j => written.contains (a + j)
    for a in words do
      if !((List.range 8).all fun j => agreeMem B (a + j)) then
        let vb := Num.decodeLE (mB.readN a 8)
        let vo := (others.toList).map fun (t2, k2) =>
          (t2[k2 + (B - k0)]?.map (fun x => Num.decodeLE (x.2.2.readN a 8))).getD 0
        if let some e := matchVar vb vo then symMem := (a, e) :: symMem
  let inSym (b : Nat) : Bool := symMem.any fun (a, _) => a ≤ b && b < a + 8
  -- `ext`: an octet of a word with an input-dependent written octet is not stated on its own
  let mixed (b : Nat) : Bool := ext && (List.range 8).any fun j =>
    let c := b - b % 8 + j
    written.contains c && !agreeMem B c
  let livePost := ((live ++ outBytes ++ extra.filter written.contains).eraseDups.mergeSort).filter fun b => agreeMem B b && !inSym b
  let vars := (vars0 ++ symMem.flatMap (fun (_, e) =>
    ((e.replace "(" "").replace ")" "" |>.splitOn " ").filter names.contains)).eraseDups
  let pcs := (List.range (B - A)).filterMap fun j => tr[A + j]?.map (·.1)
  return { A, B, pcA, pcB, vars, regFacts := regFacts.map (fun j => (j, rA[j]!.toNat)), symRegs, symLoads, wr, rr,
           loads := goodLoads.map (fun (a, k) => (a, k, (List.range k).map fun j => (mA.read (a + j)).toNat)),
           byteFacts := ((rlist.mergeSort).filter (agreeMem A)).map (fun a => (a, (mA.read a).toNat)),
           wregs,
           regPost := regPost.map (fun j => (j, if wregs.contains j then some rB[j]!.toNat else none)),
           symPost, memPost := livePost.map (fun a => (a, (mB.read a).toNat)), pcs, symMem := symMem.reverse }


/-- Where path `pb` leaves and rejoins path `pa`, from step `n` on. -/
def divReport (pa pb : Array Nat) (n : Nat) : IO Unit := do
  let ok (x y : Nat) : Bool := (List.range 8).all fun d => pa[x + d]? == pb[y + d]?
  let rejoin (x y : Nat) : Option (Nat × Nat) :=
    (List.range 4000).findSome? fun d =>
      (List.range (d + 1)).findSome? fun a => if ok (x + a) (y + d - a) then some (a, d - a) else none
  let mut x := n; let mut y := n
  for _ in [0:100000] do
    if x ≥ pa.size || y ≥ pb.size then break
    if pa[x]! == pb[y]! then
      x := x + 1; y := y + 1
    else
      match rejoin x y with
      | some (a, b) =>
        IO.println s!"diverge at base {x} (pc {pa[x]!}) / other {y}: base +{a}, other +{b}, rejoin pc {pa[x + a]!}"
        x := x + a; y := y + b
      | none => IO.println s!"no rejoin after base {x} / other {y}"; return
  IO.println s!"ends: base {pa.size}, other {pb.size}"

/-- What every mode of the generator shares: the arguments, the blob and the base run. -/
structure Cx where
  svc : Svc
  args : List String
  mode0 : String
  empty : Bool
  mode : String
  n : Nat
  bytes : ByteArray
  code : ByteArray
  h : List UInt8
  acct : ServiceAccount
  jb : JamBlob
  P : Program
  Q : Prepared
  c : Nat
  i : Nat
  sid : Nat
  y : List UInt8
  pkg : WorkPackage
  a : ByteArray
  ω : Regs
  μ : Memory
  env : RefineHost.Env
  tr : Array (Nat × Regs × Memory)
  path : List Nat

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_calls (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- the path's calls, returns and host calls from step n on, with the depth of the call stack
    let mut depth := 0
    let mut k := 0
    for (pc, regs, _) in tr.toList do
      if k ≥ n then
        match P.decode pc with
        | some (.regImmOffset .loadImmJump 0 _ y) =>
          IO.println s!"{k} {String.mk (List.replicate (2 * depth) ' ')}call {P.sjump pc y |>.2} from {pc}  r7={(regs.get 7).toNat} r8={(regs.get 8).toNat} r9={(regs.get 9).toNat}"
          depth := depth + 1
        | some (.regImm .jumpInd 0 0) =>
          depth := depth - 1
          IO.println s!"{k} {String.mk (List.replicate (2 * depth) ' ')}ret"
        | some (.oneImm .ecalli h) => IO.println s!"{k} {String.mk (List.replicate (2 * depth) ' ')}host {h.toNat}"
        | _ => pure ()
      k := k + 1
    IO.println s!"{tr.size} end"
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_div (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `div N c i s k`: where the path for (c, i, s, payload of k octets 255) leaves and rejoins the
    -- base path, from step N on
    let some t2 := traceFor code h acct Q ((args.getD 2 "3").toNat!) ((args.getD 3 "0").toNat!)
      ((args.getD 4 "7").toNat!) (List.replicate ((args.getD 5 "1").toNat!) 255) | IO.println "no trace"; return
    divReport (tr.map (·.1)) (t2.map (·.1)) n
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_cmp (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `cmp PC`: where each test input first reaches PC, and the first later difference from the base run
    let inputs : List (Nat × Nat × Nat × List UInt8) :=
      [(5, 0, 9, [200]), (3, 0, 7, List.replicate 15 255), (3, 0, 7, []), (3, 0, 7, List.replicate 8 13)]
    let some k0 := (List.range tr.size).find? (fun k => (tr[k]?.map (·.1)) == some n) | IO.println "pc not reached"; return
    IO.println s!"base: pc {n} at step {k0}, ends at {tr.size}"
    for (c2, i2, s2, y2) in inputs do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k2 := (List.range t2.size).find? (fun k => (t2[k]?.map (·.1)) == some n) | IO.println s!"{y2.length}: pc not reached"; continue
      -- first step after the join where the pcs, registers or memory reads differ
      let mut diff := "none"
      for j in [0:tr.size - k0] do
        let some (pa, ra, _) := tr[k0 + j]? | break
        let some (pb, rb, _) := t2[k2 + j]? | diff := s!"shorter at +{j}"; break
        if pa != pb then diff := s!"pc at +{j}: {pa} vs {pb}"; break
        if ra != rb then
          let js := (List.range 13).filter fun r => ra[r]! != rb[r]!
          diff := s!"registers {js} at +{j} (pc {pa})"; break
      IO.println s!"input c={c2} i={i2} s={s2} |y|={y2.length}: reaches at {k2}, ends at {t2.size}; first difference: {diff}"
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_vals (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `vals PC off ADDR LEN`: the LEN-octet value at ADDR, `off` steps after reaching PC, for each input
    let off := (args.getD 2 "0").toNat!; let addr := (args.getD 3 "0").toNat!; let len := (args.getD 4 "8").toNat!
    for (c2, i2, s2, y2) in [(3, 0, 7, [255]), (5, 0, 9, [200]), (3, 0, 7, List.replicate 15 255),
        (3, 0, 7, List.replicate 8 13), (200, 0, 70000, [12])] do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k := (List.range t2.size).find? (fun k => (t2[k]?.map (·.1)) == some n) | continue
      let some (_, rg, mem) := t2[k + off]? | continue
      IO.println s!"|y|={y2.length} c={c2} s={s2}: value {Num.decodeLE (mem.readN addr len)}  regs {(List.range 13).map (fun j => rg[j]!.toNat)}"
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_reads (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `reads ADDR`: the steps that read or write octet ADDR
    let addr := n
    let mut k := 0
    for (pc, regs, mem) in tr.toList do
      if let some ins := P.decode pc then
        let m := P.exec pc ins regs mem
        if m.reads.any (· % 2 ^ 32 == addr) then IO.println s!"{k} read  pc {pc} {repr ins}"
        if m.writes.any (· % 2 ^ 32 == addr) then IO.println s!"{k} write pc {pc} {repr ins}"
      k := k + 1
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_chainx (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `chain PC name b₀ b₁ … bₙ`: the theorem from step b₀ to step bₙ after PC, composing the segment
    -- theorems `name0 … name(n-1)` (steps bᵢ … bᵢ₊₁ − 1; the last with `out`)
    let joinPc := n
    let name := args.getD 2 "chain"
    let bs := ((args.drop 3).filter (!·.startsWith "keep=")).map String.toNat!
    -- `keep=j,…`: the start registers it may assume (those the summary before guarantees; the first
    -- segment must be generated with the same `keep=`)
    let keepO : Option (List Nat) := ((args.drop 3).find? (·.startsWith "keep=")).map fun o =>
      (((o.drop 5).toString).splitOn ",").map String.toNat!
    let classInputs : List (Nat × Nat × Nat × List UInt8) :=
      if empty then cx.svc.emptyClass ++ cx.svc.emptyExtra else cx.svc.segClass ++ cx.svc.segxExtra
    let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
      (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
    let some k0 := align tr | IO.eprintln "join not reached"; return
    let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
    let mut otherPs : Array (Nat × Nat × Nat × List UInt8) := #[]
    for (c2, i2, s2, y2) in classInputs do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k2 := align t2 | return
      others := others.push (t2, k2)
      otherPs := otherPs.push (c2, i2, s2, y2)
    let nseg := bs.length - 1
    let mut infos : Array SegInfo := #[]
    for k in [0:nseg] do
      infos := infos.push (← analyzeSeg P tr others otherPs k0 bs[k]! bs[k+1]! (k + 1 == nseg) (c, i, sid, y) true)
    -- what the path writes before each segment: registers and octets
    let writtenBefore (k : Nat) : Std.HashSet Nat × List Nat := Id.run do
      let mut w : Std.HashSet Nat := {}
      let mut rs : List Nat := []
      for j in [k0 + bs[0]!:k0 + bs[k]!] do
        let some (pc, regs, mem) := tr[j]? | continue
        if let some (_, r1, _) := tr[j+1]? then
          for q in [0:13] do
            if regs[q]! != r1[q]! && !rs.contains q then rs := q :: rs
        let some ins := P.decode pc | continue
        let m := P.exec pc ins regs mem
        for x in m.writes do w := w.insert (x % 2 ^ 32)
      return (w, rs)
    -- the start-state facts: those the segments read and nothing earlier in the chain wrote
    let mut vars : List String := []
    let mut iregs : List (Nat × String) := []
    let mut ibytes : List (Nat × Nat) := []
    let mut isym : List (Nat × Nat × String) := []
    for k in [0:nseg] do
      let info := infos[k]!
      let (w, rs) := writtenBefore k
      vars := (vars ++ info.vars).eraseDups
      for (j, v) in info.regFacts do
        if !rs.contains j && !(iregs.any (·.1 == j)) then iregs := iregs ++ [(j, toString v)]
      for (j, v) in info.symRegs do
        if !rs.contains j && !(iregs.any (·.1 == j)) then iregs := iregs ++ [(j, v)]
      for (a, kk, vs) in info.loads do
        for q in [0:kk] do
          if !w.contains (a + q) && !(ibytes.any (·.1 == a + q)) then ibytes := ibytes ++ [(a + q, vs[q]!)]
      for (a, v) in info.byteFacts do
        if !w.contains a && !(ibytes.any (·.1 == a)) then ibytes := ibytes ++ [(a, v)]
      for (a, kk, v) in info.symLoads do
        if !(isym.any (·.1 == a)) then isym := isym ++ [(a, kk, v)]
    iregs := match keepO with
      | some ks => iregs.filter (fun (j, _) => ks.contains j)
      | none => iregs
    let last := infos[nseg - 1]!
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}{mode0} {joinPc} {name} {" ".intercalate ((args.drop 3))}` from {BLOB}.
  Do not edit by hand.
-/
{"\n".intercalate ((List.range nseg).map (s!"import Services.{NS}.{name}{·}"))}
import PVM.Logic.Chase

namespace Services.{NS}.{name}

open PVM JAM Services.{NS}.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 100000000

/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**, composed from the segment theorems
    `{name}0` … `{name}{nseg - 1}`: from the facts the path reads before writing them, to the end. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
    for v in vars do
      let bound := match v with
        | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => "S < 4294967296" | "C" => "C < 65536" | "L" => "L < 4294967296"
        | "T" => "12 ≤ T ∧ T < 256" | "Q" => "4278124548 ≤ Q ∧ Q ≤ 4278124564" | _ => "I < 65536"
      IO.println s!"    ({v} : Nat) (h{v} : {bound})"
    for (j, v) in iregs do
      IO.println s!"    (hreg{j} : ω[{j}] = UInt64.ofNat {v})"
    for (a, v) in ibytes do
      IO.println s!"    (hb_{a} : μ.read {a} = {v})"
    for (a, kk, v) in isym do
      IO.println s!"    (hsym_{a} : μ.readN {a} {kk} = Num.encodeLE {kk} {v})"
    for k in [0:nseg] do
      let info := infos[k]!
      for q in [0:info.wr.length] do
        let (lo, hi) := info.wr[q]!
        IO.println s!"    (hw{k}_{q} : ∀ a, {lo} ≤ a → a < {hi} → μ.writable a = true)"
      for q in [0:info.rr.length] do
        let (lo, hi) := info.rr[q]!
        IO.println s!"    (hrd{k}_{q} : ∀ a, {lo} ≤ a → a < {hi} → μ.readable a = true)"
    let fin := (last.regPost.filter (fun (j, _) => j == 0 || j == 7 || j == 8))
    IO.println s!"    : ∃ ω' μ', FreeStepsH p (refineContract env) {infos[0]!.pcA} ω μ x {last.pcB} ω' μ' x ∧"
    IO.println s!"      ω'[0] = UInt64.ofNat {(tr[k0 + bs[nseg]!]?.map (·.2.1[0]!.toNat)).getD 0} ∧ ω'[7] = UInt64.ofNat {(tr[k0 + bs[nseg]!]?.map (·.2.1[7]!.toNat)).getD 0} ∧ ω'[8] = UInt64.ofNat {(tr[k0 + bs[nseg]!]?.map (·.2.1[8]!.toNat)).getD 0} ∧"
    let outFacts := last.memPost.filter fun (a, _) =>
      let o := (tr[k0 + bs[nseg]!]?.map (·.2.1[7]!.toNat)).getD 0
      let l := (tr[k0 + bs[nseg]!]?.map (·.2.1[8]!.toNat)).getD 0
      o ≤ a && a < o + l
    IO.println ("      " ++ " ∧ ".intercalate ((outFacts.map fun (a, v) => s!"μ'.read {a} = {v}") ++
      (outFacts.map fun (a, _) => s!"μ'.readable {a} = true")) ++ " := by")
    -- compose: each segment's hypotheses by `chase`, from the start facts and the posts before
    let segBinders (k : Nat) : IO (List String) := do
      let t ← IO.FS.readFile s!"Services/{NS}/{name}{k}.lean"
      let some st := (t.splitOn "theorem run").tail.head? | throw (IO.userError s!"no run in {name}{k}")
      let st := (st.splitOn ": ∃ ω").head!
      let st := ((st.splitOn "(x : RefineCtx)").getD 1 "")
      -- the binder names: `(name : `
      let parts := (st.splitOn "(").drop 1
      return parts.filterMap fun q => match q.splitOn " : " with
        | n :: _ :: _ => if n.any (· == ' ') then none else some n
        | _ => none
    let symNames := isym.map fun (a, _, _) => s!"hsym_{a}"
    if !symNames.isEmpty then
      IO.println s!"  chase_prep at {" ".intercalate symNames}"
    let mut ind := "  "
    let mut cw := "ω"; let mut cm := "μ"
    for k in [0:nseg] do
      let bsK ← segBinders k
      let args := bsK.map fun b => if vars.contains b || (b.startsWith "h" && vars.contains (b.drop 1).toString) then b else "?_"
      IO.println s!"{ind}refine (fun h{k} => ?_) ({name}{k}.run p P env {cw} {cm} x {" ".intercalate args})"
      IO.println s!"{ind}· obtain ⟨ω{k+1}, μ{k+1}, run{k+1}, post{k+1}⟩ := h{k}"
      IO.println s!"{ind}  chase_prep at post{k+1}"
      cw := s!"ω{k+1}"; cm := s!"μ{k+1}"
      ind := ind ++ "  "
    let runs := (List.range nseg).map (s!"run{· + 1}")
    let chainT := runs.foldr (fun r acc => if acc == "" then r else s!"({r}.trans {acc})") ""
    let nOut := outFacts.length
    let finals := ["by chase", "by chase", "by chase"] ++ (List.replicate nOut "by chase") ++
      (List.replicate nOut "Memory.readable_of_writable (by chase)")
    IO.println s!"{ind}exact ⟨{cw}, {cm}, {chainT}, {", ".intercalate finals}⟩"
    for _ in [0:nseg] do
      ind := (ind.toList.drop 2).asString
      IO.println s!"{ind}all_goals chase"
    IO.println s!"\nend Services.{NS}.{name}"
    return

def mode_chain (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `chain PC name b₀ b₁ … bₙ`: the theorem from step b₀ to step bₙ after PC, composing the segment
    -- theorems `name0 … name(n-1)` (steps bᵢ … bᵢ₊₁ − 1; the last with `out`)
    let joinPc := n
    let name := args.getD 2 "chain"
    let bs := (args.drop 3).map String.toNat!
    let classInputs : List (Nat × Nat × Nat × List UInt8) :=
      if empty then cx.svc.emptyClass else cx.svc.segClass
    let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
      (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
    let some k0 := align tr | IO.eprintln "join not reached"; return
    let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
    let mut otherPs : Array (Nat × Nat × Nat × List UInt8) := #[]
    for (c2, i2, s2, y2) in classInputs do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k2 := align t2 | return
      others := others.push (t2, k2)
      otherPs := otherPs.push (c2, i2, s2, y2)
    let nseg := bs.length - 1
    let mut infos : Array SegInfo := #[]
    for k in [0:nseg] do
      infos := infos.push (← analyzeSeg P tr others otherPs k0 bs[k]! bs[k+1]! (k + 1 == nseg) (c, i, sid, y))
    -- what the path writes before each segment: registers and octets
    let writtenBefore (k : Nat) : Std.HashSet Nat × List Nat := Id.run do
      let mut w : Std.HashSet Nat := {}
      let mut rs : List Nat := []
      for j in [k0 + bs[0]!:k0 + bs[k]!] do
        let some (pc, regs, mem) := tr[j]? | continue
        if let some (_, r1, _) := tr[j+1]? then
          for q in [0:13] do
            if regs[q]! != r1[q]! && !rs.contains q then rs := q :: rs
        let some ins := P.decode pc | continue
        let m := P.exec pc ins regs mem
        for x in m.writes do w := w.insert (x % 2 ^ 32)
      return (w, rs)
    -- the start-state facts: those the segments read and nothing earlier in the chain wrote
    let mut vars : List String := []
    let mut iregs : List (Nat × String) := []
    let mut ibytes : List (Nat × Nat) := []
    let mut isym : List (Nat × Nat × String) := []
    for k in [0:nseg] do
      let info := infos[k]!
      let (w, rs) := writtenBefore k
      vars := (vars ++ info.vars).eraseDups
      for (j, v) in info.regFacts do
        if !rs.contains j && !(iregs.any (·.1 == j)) then iregs := iregs ++ [(j, toString v)]
      for (j, v) in info.symRegs do
        if !rs.contains j && !(iregs.any (·.1 == j)) then iregs := iregs ++ [(j, v)]
      for (a, kk, vs) in info.loads do
        for q in [0:kk] do
          if !w.contains (a + q) && !(ibytes.any (·.1 == a + q)) then ibytes := ibytes ++ [(a + q, vs[q]!)]
      for (a, v) in info.byteFacts do
        if !w.contains a && !(ibytes.any (·.1 == a)) then ibytes := ibytes ++ [(a, v)]
      for (a, kk, v) in info.symLoads do
        if !(isym.any (·.1 == a)) then isym := isym ++ [(a, kk, v)]
    let last := infos[nseg - 1]!
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}{mode0} {joinPc} {name} {" ".intercalate (bs.map toString)}` from {BLOB}.
  Do not edit by hand.
-/
{"\n".intercalate ((List.range nseg).map (s!"import Services.{NS}.{name}{·}"))}

namespace Services.{NS}.{name}

open PVM JAM Services.{NS}.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**, composed from the segment theorems
    `{name}0` … `{name}{nseg - 1}`: from the facts the path reads before writing them, to the end. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
    for v in vars do
      let bound := match v with
        | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => "S < 4294967296" | "C" => "C < 65536" | "L" => "L < 4294967296"
        | "T" => "12 ≤ T ∧ T < 256" | "Q" => "4278124548 ≤ Q ∧ Q ≤ 4278124564" | _ => "I < 65536"
      IO.println s!"    ({v} : Nat) (h{v} : {bound})"
    for (j, v) in iregs do
      IO.println s!"    (hreg{j} : ω[{j}] = UInt64.ofNat {v})"
    for (a, v) in ibytes do
      IO.println s!"    (hb_{a} : μ.read {a} = {v})"
    for (a, kk, v) in isym do
      IO.println s!"    (hsym_{a} : μ.readN {a} {kk} = Num.encodeLE {kk} {v})"
    for k in [0:nseg] do
      let info := infos[k]!
      for q in [0:info.wr.length] do
        let (lo, hi) := info.wr[q]!
        IO.println s!"    (hw{k}_{q} : ∀ a, {lo} ≤ a → a < {hi} → μ.writable a = true)"
      for q in [0:info.rr.length] do
        let (lo, hi) := info.rr[q]!
        IO.println s!"    (hrd{k}_{q} : ∀ a, {lo} ≤ a → a < {hi} → μ.readable a = true)"
    let fin := (last.regPost.filter (fun (j, _) => j == 0 || j == 7 || j == 8))
    IO.println s!"    : ∃ ω' μ', FreeStepsH p (refineContract env) {infos[0]!.pcA} ω μ x {last.pcB} ω' μ' x ∧"
    IO.println s!"      ω'[0] = UInt64.ofNat {(tr[k0 + bs[nseg]!]?.map (·.2.1[0]!.toNat)).getD 0} ∧ ω'[7] = UInt64.ofNat {(tr[k0 + bs[nseg]!]?.map (·.2.1[7]!.toNat)).getD 0} ∧ ω'[8] = UInt64.ofNat {(tr[k0 + bs[nseg]!]?.map (·.2.1[8]!.toNat)).getD 0} ∧"
    let outFacts := last.memPost.filter fun (a, _) =>
      let o := (tr[k0 + bs[nseg]!]?.map (·.2.1[7]!.toNat)).getD 0
      let l := (tr[k0 + bs[nseg]!]?.map (·.2.1[8]!.toNat)).getD 0
      o ≤ a && a < o + l
    IO.println ("      " ++ " ∧ ".intercalate (outFacts.map fun (a, v) => s!"μ'.read {a} = {v}") ++ " := by")
    -- compose, with an explicit proof of each segment hypothesis from where its fact comes from
    let proj (i len : Nat) : String :=
      if len == 1 then "" else String.join (List.replicate i ".2") ++ (if i + 1 == len then "" else ".1")
    let regList (q : Nat) : List Nat := (infos[q]!.regPost.map (·.1)) ++ (infos[q]!.symPost.map (·.1))
    let inWr (q a : Nat) : Bool := infos[q]!.wr.any fun (lo, hi) => lo ≤ a && a < hi
    -- ω_k[j] = value: back through the segments to the last one that set it, or to the start
    let regProof (k j : Nat) : String := Id.run do
      let mut pf := ""
      let mut q := k
      while q > 0 do
        q := q - 1
        let L := regList q
        let some i := L.idxOf? j | return s!"missingFact /- register {j} missing after segment {q} -/"
        let step := s!"regs{q + 1}{proj i L.length}"
        pf := if pf == "" then step else s!"(Eq.trans {pf} {step})"
        if infos[q]!.wregs.contains j then return pf
      return if pf == "" then s!"hreg{j}" else s!"(Eq.trans {pf} hreg{j})"
    let frameArgs (q a : Nat) : String :=
      " ".intercalate ((infos[q]!.wr.map fun _ => "(by decide)"))
    -- μ_k.read a = value
    let byteProof (k a : Nat) : String := Id.run do
      let mut pf := ""
      let mut q := k
      while q > 0 do
        q := q - 1
        if inWr q a then
          let L := infos[q]!.memPost.map (·.1)
          let some i := L.idxOf? a | return s!"missingFact /- octet {a} missing after segment {q} -/"
          let step := s!"mem{q + 1}{proj i L.length}"
          return if pf == "" then step else s!"(Eq.trans {pf} {step})"
        let step := s!"(frame{q + 1} {a} rfl)"
        pf := if pf == "" then step else s!"(Eq.trans {pf} {step})"
      return if pf == "" then s!"hb_{a}" else s!"(Eq.trans {pf} hb_{a})"
    let mut prevω := "ω"; let mut prevμ := "μ"
    for k in [0:nseg] do
      let info := infos[k]!
      -- the octet facts this segment needs, as `have`s
      let mut need : List Nat := []
      for (a, kk, _) in info.loads do
        for q in [0:kk] do if !need.contains (a + q) then need := need ++ [a + q]
      for (a, _) in info.byteFacts do if !need.contains a then need := need ++ [a]
      for a in need do
        IO.println s!"  have b{k}_{a} : {prevμ}.read {a} = {(tr[k0 + info.A - k0]?.map (fun x => (x.2.2.read a).toNat)).getD 0} := {byteProof k a}"
      let regArgs := (info.regFacts.map (·.1) ++ info.symRegs.map (·.1)).map fun j => s!"({regProof k j})"
      let rw1 := ", ".intercalate ((List.range k).reverse.map (s!"wr{· + 1} a"))
      let rd1 := ", ".intercalate ((List.range k).reverse.map (s!"rd{· + 1} a"))
      let wArgs := (List.range info.wr.length).map fun q =>
        if k == 0 then s!"hw{k}_{q}" else s!"(fun a h1 h2 => by rw [{rw1}]; exact hw{k}_{q} a h1 h2)"
      let rArgs := (List.range info.rr.length).map fun q =>
        if k == 0 then s!"hrd{k}_{q}" else s!"(fun a h1 h2 => by rw [{rd1}]; exact hrd{k}_{q} a h1 h2)"
      let loadArgs := info.loads.map fun (a, kk, _) =>
        let bs := ", ".intercalate ((List.range kk).map (s!"b{k}_{a + ·}"))
        s!"(by simp only [Memory.readN, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.map_append, List.nil_append, List.cons_append, Nat.add_zero, Nat.reduceAdd, {bs}])"
      let byteArgs := info.byteFacts.map fun (a, _) => s!"b{k}_{a}"
      let symArgs := info.symLoads.map fun (a, kk, _) =>
        if k == 0 then s!"hsym_{a}" else
        let frames := (List.range k).reverse.map fun q =>
          s!"(frame{q + 1} ({a} + j) (by simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and, Nat.not_lt]; omega))"
        let fr := frames.tail.foldl (fun acc f => s!"(Eq.trans {acc} {f})") frames.head!
        s!"(Eq.trans (Memory.readN_congr (fun j hj => {fr})) hsym_{a})"
      let varArgs := info.vars.map fun v => s!"{v} h{v}"
      let allArgs := " ".intercalate (varArgs ++ regArgs ++ symArgs ++ wArgs ++ rArgs ++ loadArgs ++ byteArgs)
      IO.println s!"  obtain ⟨ω{k+1}, μ{k+1}, run{k+1}, regs{k+1}, mem{k+1}, frame{k+1}, rd{k+1}, wr{k+1}⟩ :=\n    {name}{k}.run p P env {prevω} {prevμ} x {allArgs}"
      prevω := s!"ω{k+1}"; prevμ := s!"μ{k+1}"
    let runs := (List.range nseg).map (fun k => s!"run{k+1}")
    let trans := runs.dropLast.foldr (fun r acc => s!"({r}.trans {acc})") runs.getLast!
    let outA := outFacts.map fun (a, _) =>
      let L := last.memPost.map (·.1)
      s!"mem{nseg}{proj (L.idxOf a) L.length}"
    IO.println s!"  exact ⟨{prevω}, {prevμ}, {trans}, {regProof nseg 0}, {regProof nseg 7}, {regProof nseg 8}, {", ".intercalate outA}⟩"
    IO.println s!"\nend Services.{NS}.{name}"
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_seg (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
    -- `seg PC a b name`: a standalone theorem for steps a … b − 1 after the path first reaches PC,
    -- stating only the values on which every input of the class agrees
    let joinPc := n
    let a := (args.getD 2 "0").toNat!; let b := (args.getD 3 "0").toNat!; let name := args.getD 4 "seg"
    let classInputs : List (Nat × Nat × Nat × List UInt8) :=
      (if empty then cx.svc.emptyClass else cx.svc.segClass) ++
        (if mode0 == "segx" then cx.svc.segxExtra else if mode0 == "segx0" then cx.svc.emptyExtra else [])
    let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
      (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
    let some k0 := align tr | IO.eprintln "join not reached"; return
    let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
    let mut otherPs : Array (Nat × Nat × Nat × List UInt8) := #[]
    for (c2, i2, s2, y2) in classInputs do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k2 := align t2 | IO.eprintln s!"join not reached for |y| = {y2.length}"; return
      for j in [a:b+1] do
        if (tr[k0 + j]?.map (·.1)) != (t2[k2 + j]?.map (·.1)) then
          IO.eprintln s!"paths differ at +{j} for c={c2} s={s2} |y|={y2.length}"; return
      others := others.push (t2, k2)
      otherPs := otherPs.push (c2, i2, s2, y2)
    let opts := args.drop 5
    let info0 ← analyzeSeg P tr others otherPs k0 a b (opts.contains "out") (c, i, sid, y) (mode0 == "segx" || mode0 == "segx0")
    -- `keep=j,…`: assume only these registers at the start (those the summary before guarantees)
    let keep : Option (List Nat) := (opts.find? (·.startsWith "keep=")).map fun o =>
      (((o.drop 5).toString).splitOn ",").map String.toNat!
    let kept (j : Nat) : Bool := match keep with | some ks => ks.contains j | none => true
    let info := { info0 with regFacts := info0.regFacts.filter (kept ·.1), symRegs := info0.symRegs.filter (kept ·.1) }
    let A := info.A; let B := info.B; let pcA := info.pcA; let pcB := info.pcB
    let vars := info.vars; let wr := info.wr; let rr := info.rr; let wregs := info.wregs
    let symRegs := info.symRegs; let symLoads := info.symLoads; let symPost := info.symPost
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}{mode0} {joinPc} {a} {b} {name}{opts.foldl (fun acc o => acc ++ " " ++ o) ""}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.Code{if mode0 == "segx" || mode0 == "segx0" then "\nimport PVM.Logic.Chase" else ""}

namespace Services.{NS}.{name}

open PVM JAM Services.{NS}.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- **Steps {A} … {B - 1} of {LBL}'s refine** (pc {pcA} to pc {pcB}), from any state with the
    register values and memory octets they read, to a state with the values they leave. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
    for v in vars do
      let bound := match v with
        | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => "S < 4294967296" | "C" => "C < 65536" | "L" => "L < 4294967296"
        | "T" => "12 ≤ T ∧ T < 256" | "Q" => "4278124548 ≤ Q ∧ Q ≤ 4278124564" | _ => "I < 65536"
      IO.println s!"    ({v} : Nat) (h{v} : {bound})"
    for (j, v) in info.regFacts do
      IO.println s!"    (hreg{j} : ω[{j}] = UInt64.ofNat {v})"
    for (j, v) in symRegs do
      IO.println s!"    (hreg{j} : ω[{j}] = UInt64.ofNat {v})"
    for (a, k, v) in symLoads do
      IO.println s!"    (hbn_{a}_{k} : μ.readN {a} {k} = Num.encodeLE {k} {v})"
    let mut i := 0
    for (lo, hi) in wr do
      IO.println s!"    (hw{i} : ∀ a, {lo} ≤ a → a < {hi} → μ.writable a = true)"
      i := i + 1
    let mut i2 := 0
    for (lo, hi) in rr do
      IO.println s!"    (hrd{i2} : ∀ a, {lo} ≤ a → a < {hi} → μ.readable a = true)"
      i2 := i2 + 1
    for (a, k, bytes) in info.loads do
      IO.println s!"    (hbn_{a}_{k} : μ.readN {a} {k} = {bytes})"
    -- each octet read before written, for loads that straddle earlier writes
    for (a, v) in info.byteFacts do
      IO.println s!"    (hb_{a} : μ.read {a} = {v})"
    IO.println s!"    : ∃ ω' μ', FreeStepsH p (refineContract env) {pcA} ω μ x {pcB} ω' μ' x ∧"
    let regC := info.regPost.map (fun (j, v) =>
      match v with | some v => s!"ω'[{j}] = UInt64.ofNat {v}" | none => s!"ω'[{j}] = ω[{j}]") ++
      symPost.map fun (j, v) => s!"ω'[{j}] = UInt64.ofNat {v}"
    IO.println ("      (" ++ " ∧ ".intercalate regC ++ ") ∧")
    let memC := info.memPost.map fun (a, v) => s!"μ'.read {a} = {v}"
    IO.println ("      (" ++ (if memC.isEmpty then "True" else " ∧ ".intercalate memC) ++ ") ∧")
    if !info.symMem.isEmpty then
      IO.println ("      (" ++ " ∧ ".intercalate (info.symMem.map fun (a, e) => s!"μ'.readN {a} 8 = Num.encodeLE 8 {e}") ++ ") ∧")
    let outW := " && ".intercalate (wr.map fun (lo, hi) => s!"!(decide ({lo} ≤ a ∧ a < {hi}))")
    IO.println s!"      (∀ a, (decide (a < 4294967296){if outW == "" then "" else " && " ++ outW}) = true → μ'.read a = μ.read a) ∧"
    IO.println "      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by"
    let hws := ", ".intercalate ((List.range wr.length).map (s!"hw{·}"))
    let hrs := ", ".intercalate ((List.range wr.length).map (s!"hr{·}") ++ (List.range rr.length).map (s!"hrd{·}"))
    for k in [0:wr.length] do
      IO.println s!"  have hr{k} := fun a h1 h2 => Memory.readable_of_writable (hw{k} a h1 h2)"
    let regA := ", ".intercalate (info.regFacts.map (fun (j, _) => s!"hreg{j}") ++ symRegs.map (fun (j, _) => s!"hreg{j}"))
    let loadA := ", ".intercalate (info.loads.map (fun (a, k, _) => s!"hbn_{a}_{k}") ++ info.byteFacts.map (fun (a, _) => s!"hb_{a}") ++
      symLoads.map (fun (a, k, _) => s!"hbn_{a}_{k}") ++ vars.map (s!"h{·}"))
    let facts := if mode0 == "segx" || mode0 == "segx0" then cx.svc.segFacts.filter (fun (vs, _) => vs.all vars.contains) else []
    let mut fk := 0
    for (_, f) in facts do
      IO.println s!"  have hf{fk} : {f} := by omega"
      fk := fk + 1
    let factA := ", ".intercalate ((List.range facts.length).map (s!"hf{·}"))
    let simpArgs := ", ".intercalate ([regA, loadA, hws, hrs, factA].filter (· != ""))
    IO.println "  rw [show ω = regsNF ω [] from rfl]\n  refine ⟨?ω', ?μ', ?run, ?post⟩\n  case run =>"
    for pc in info.pcs do
      match P.decode pc with
      | some (.oneImm .ecalli _) =>
        IO.println s!"    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_host [{simpArgs}, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE]"
      | _ =>
        IO.println s!"    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [{simpArgs}]"
    if info.symMem.isEmpty then
      IO.println "    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?frame, ?rd, ?wr⟩"
    else
      IO.println "    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?smem, ?frame, ?rd, ?wr⟩"
      IO.println ("    case smem =>\n      " ++ (if info.symMem.length > 1 then "refine ⟨" ++ ", ".intercalate (info.symMem.map fun _ => "?_") ++ "⟩ <;>\n      " else "") ++ "simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,\n        PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]")
    IO.println s!"    case regs =>\n      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,\n        PVM.getD_some', List.lookup_nil, Option.getD_none, and_self, and_true, true_and{if regA == "" then "" else ", " ++ regA}]"
    if mode0 == "segx" || mode0 == "segx0" then
      IO.println "    case mem =>\n      try and_intros\n      all_goals simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,\n        Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,\n        List.getElem!_cons_succ, UInt8.reduceOfNat, and_self, PVM.Num.encodeLE] <;> chase_octet"
    else
      IO.println "    case mem =>\n      simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,\n        Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,\n        List.getElem!_cons_succ, UInt8.reduceOfNat, and_self]"
    let nW := wr.length
    let names := " ".intercalate ((List.range nW).map (s!"hx{·}"))
    IO.println s!"    case frame =>\n      intro a ha\n      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,\n        not_and, Nat.not_lt] at ha\n      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32]"
    IO.println "    case rd => intro a; simp only [PVM.Memory.readable_writeN]\n    case wr => intro a; simp only [PVM.Memory.writable_writeN]\n"
    IO.println s!"end Services.{NS}.{name}"
    return

set_option maxHeartbeats 2000000 in
/-- The segment analysis of steps 0 … N − 1 over a class of inputs of every width (the prefix's
    path does not depend on the input). -/
def prefixInfo (cx : Cx) : IO (SegInfo × Array (Array (Nat × Regs × Memory) × Nat) × Array (Nat × Nat × Nat × List UInt8)) := do
  let classInputs : List (Nat × Nat × Nat × List UInt8) := cx.svc.postClass
  let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
  let mut otherPs : Array (Nat × Nat × Nat × List UInt8) := #[]
  for (c2, i2, s2, y2) in classInputs do
    let some t2 := traceFor cx.code cx.h cx.acct cx.Q c2 i2 s2 y2 | continue
    for j in [0:cx.n+1] do
      if (cx.tr[j]?.map (·.1)) != (t2[j]?.map (·.1)) then
        throw (IO.userError s!"paths differ at {j} for c={c2}")
    others := others.push (t2, 0)
    otherPs := otherPs.push (c2, i2, s2, y2)
  return (← analyzeSeg cx.P cx.tr others otherPs 0 0 cx.n false (cx.c, cx.i, cx.sid, cx.y), others, otherPs)

set_option linter.unusedVariables false in
def mode_codeRun (cx : Cx) : IO Unit := do
  let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
  let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
  let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
  let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
  let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
  let mut facts : Array String := #[]
  let mut lemmas : Array String := #[]
  let mut seen : List Nat := []
  -- `code`: the instructions on the base run's first n steps, and on the empty payload's whole run
  let (ec, ei, es, ey) := cx.svc.emptyBase
  let emptyRun : List (Nat × Regs × Memory) :=
    if mode == "code" && cx.svc.emptyCode then ((traceFor code h acct Q ec ei es ey).map (·.toList)).getD [] else []
  let codePath := tr.toList.take n ++ emptyRun
  for (pc, regs, _) in codePath do
    if seen.contains pc then continue
    seen := pc :: seen
    let some ins := P.decode pc | continue
    facts := facts.push s!".instr {pc} ({leanInstr ins}) {P.next pc}"
    lemmas := lemmas.push s!"theorem d_{pc} \{p : ByteArray} \{P : Program} [h : HasCode p P] : deblob p {pc} = some P ∧ P.decode {pc} = some ({leanInstr ins}) ∧ P.next {pc} = {P.next pc} :=\n  h.ok.instr (by decide)"
    let bs (t : Nat) : Array String × Array String :=
      (#[s!".blockStart {t} {P.isBlockStart t}"],
       #[s!"@[pvm_code] theorem bs_{t} \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.isBlockStart {t} = {P.isBlockStart t} := h.ok.blockStart (by decide)"])
    let mut ts : List Nat := [P.next pc]
    match ins with
    | .oneOffset _ t | .regImmOffset _ _ _ t | .twoRegOffset _ _ _ t => if t ≥ 0 then ts := t.toNat :: ts
    | _ => pure ()
    for t in ts do
      let (f, l) := bs t
      facts := facts ++ f; lemmas := lemmas ++ l
  -- every instruction of the summarized functions
  for (lo, hi) in cx.svc.fnRanges do
    let mut pc := lo
    while pc < hi do
      if !seen.contains pc then
        seen := pc :: seen
        if let some ins := P.decode pc then
          facts := facts.push s!".instr {pc} ({leanInstr ins}) {P.next pc}"
          let mut ts : List Nat := [P.next pc]
          match ins with
          | .oneOffset _ t | .regImmOffset _ _ _ t | .twoRegOffset _ _ _ t => if t ≥ 0 then ts := t.toNat :: ts
          | _ => pure ()
          for t in ts do facts := facts.push s!".blockStart {t} {P.isBlockStart t}"
          -- a call: the return address it sets, through the jump table
          if let .regImmOffset .loadImmJump _ x _ := ins then
            let k := x.toNat / 2 - 1
            let t := P.jumpTable.getD k 0
            facts := facts.push s!".jumpTableSize {P.jumpTable.size}"
            facts := facts.push s!".jumpEntry {k} {t}"
            facts := facts.push s!".blockStart {t} {P.isBlockStart t}"
      pc := P.next pc
  -- jump-table facts: every jump_ind visit, since a return jumps to different callers
  for (pc, regs, _) in codePath do
    match P.decode pc with
    | some (.regImm .jumpInd ra x) =>
      let addr := ((regs.get ra).toNat + x.toNat) % 2 ^ 32
      if addr ≠ 2 ^ 32 - 2 ^ 16 ∧ addr ≥ 2 then
        let k := addr / 2 - 1
        let t := P.jumpTable.getD k 0
        facts := facts.push s!".jumpTableSize {P.jumpTable.size}"
        facts := facts.push s!".jumpEntry {k} {t}"
        facts := facts.push s!".blockStart {t} {P.isBlockStart t}"
    | some (.twoRegTwoImm .loadImmJumpInd _ rb _ y) =>
      let addr := ((regs.get rb).toNat + y.toNat) % 2 ^ 32
      if addr ≠ 2 ^ 32 - 2 ^ 16 ∧ addr ≥ 2 then
        let k := addr / 2 - 1
        let t := P.jumpTable.getD k 0
        facts := facts.push s!".jumpTableSize {P.jumpTable.size}"
        facts := facts.push s!".jumpEntry {k} {t}"
        facts := facts.push s!".blockStart {t} {P.isBlockStart t}"
    | _ => pure ()
  let factsL := facts.toList.eraseDups
  let idxOf (f : String) : Nat := (factsL.idxOf f)
  -- `facts` is split into chunks of 64, so each membership proof indexes two short lists
  let memFact (k : Nat) : String :=
    s!"List.mem_flatten_of_mem (List.getElem_mem (l := factChunks) (n := {k / 64}) (by decide)) (List.getElem_mem (l := facts_{k / 64}) (n := {k % 64}) (by decide))"
  -- lemmas, regenerated from the fact strings with their indices
  let mut lemmasL : Array String := #[]
  for pc in seen.reverse do
    let some ins := P.decode pc | continue
    let fi := s!".instr {pc} ({leanInstr ins}) {P.next pc}"
    let k := idxOf fi
    let l := s!"theorem d_{pc} \{p : ByteArray} \{P : Program} [h : HasCode p P] : deblob p {pc} = some P ∧ P.decode {pc} = some ({leanInstr ins}) ∧ P.next {pc} = {P.next pc} :=\n  h.ok.instr (show CodeFact.instr {pc} ({leanInstr ins}) {P.next pc} ∈ facts from {memFact (k)})\n\n@[pvm_code] theorem nx_{pc} \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.next {pc} = {P.next pc} := (d_{pc} (p := p)).2.2"
    if !lemmasL.contains l then lemmasL := lemmasL.push l
  for f in factsL do
    if f.startsWith ".jumpTableSize " then
      let m := (f.drop 15).toString
      lemmasL := lemmasL.push s!"@[pvm_code] theorem jts \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.jumpTable.size = {m} := h.ok.jumpTableSize (show CodeFact.jumpTableSize {m} ∈ facts from {memFact (idxOf f)})"
    if f.startsWith ".jumpEntry " then
      let parts := (f.drop 11).toString.splitOn " "
      let k := parts[0]!; let t := parts[1]!
      lemmasL := lemmasL.push s!"@[pvm_code] theorem jte_{k} \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.jumpTable.getD {k} 0 = {t} := h.ok.jumpEntry (show CodeFact.jumpEntry {k} {t} ∈ facts from {memFact (idxOf f)})"
    if f.startsWith ".blockStart " then
      let parts := (f.drop 12).toString.splitOn " "
      let t := parts[0]!; let b := parts[1]!
      lemmasL := lemmasL.push s!"@[pvm_code] theorem bs_{t} \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.isBlockStart {t} = {b} := h.ok.blockStart (show CodeFact.blockStart {t} {b} ∈ facts from {memFact (idxOf f)})"
  let endPc := (tr[n]?.map (·.1)).getD 0
  -- the octets the path reads before anything writes them, with their initial values
  let mut written : Std.HashSet Nat := {}
  let mut baseBytes : Array (Nat × Nat) := #[]
  let mut baseLoads : Array (Nat × Nat) := #[]
  let mut stepIx := 0
  for (pc, regs, mem) in tr.toList.take n do
    stepIx := stepIx + 1
    let some ins := P.decode pc | continue
    let m := P.exec pc ins regs mem
    -- a load none of whose octets the path wrote before: one fact for the whole read
    match m.reads.head? with
    | some r0 =>
      let a0 := r0 % 2 ^ 32
      if a0 < argStart && a0 + m.reads.length ≤ 2 ^ 32 && m.reads.all (fun r => !written.contains (r % 2 ^ 32)) &&
          !(baseLoads.contains (a0, m.reads.length)) then
        baseLoads := baseLoads.push (a0, m.reads.length)
    | none => pure ()
    for r in m.reads do
      let a := r % 2 ^ 32
      if a ≥ argStart && !written.contains a then
        IO.eprintln s!"args read at step {stepIx} pc {pc}: {a - argStart}"
      if a < argStart && !written.contains a && !(baseBytes.any (·.1 == a)) then
        baseBytes := baseBytes.push (a, (μ.read a).toNat)
    for w in m.writes do written := written.insert (w % 2 ^ 32)
  -- the octets any traced run reads from the starting memory before writing them, on its whole path
  -- (the facts the theorems after the prefix chase back to the start)
  let mut pathAcc : Array (Nat × Nat) := #[]
  let pathInputs := cx.svc.base :: cx.svc.emptyBase :: (cx.svc.segClass ++ cx.svc.segxExtra ++ cx.svc.emptyClass)
  for (c2, i2, s2, y2) in pathInputs do
    let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
    let mut w2 : Std.HashSet Nat := {}
    for (pc, regs, mem) in t2.toList do
      let some ins := P.decode pc | continue
      let m := P.exec pc ins regs mem
      for r in m.reads do
        let a := r % 2 ^ 32
        if a < argStart && !w2.contains a && !(baseBytes.any (·.1 == a)) && !(pathAcc.any (·.1 == a)) then
          pathAcc := pathAcc.push (a, (μ.read a).toNat)
      for x in m.writes do w2 := w2.insert (x % 2 ^ 32)
      -- a host call's writes: `fetch` writes at most ω₉ octets at ω₇
      if let .oneImm .ecalli 2 := ins then
        for j in [0:regs[9]!.toNat] do w2 := w2.insert ((regs[7]!.toNat + j) % 2 ^ 32)
  let pathBytes := pathAcc.qsort (fun x y => x.1 < y.1)
  let (hA, hB) := heapBounds code
  let hTop0 := (growHeapCore ω μ code).2.2.1
  let rwLo := rwStart jb
  let rwHi := rwStart jb + roundPage jb.rw.size + jb.heapPages * pageSize
  if mode == "code" then
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}code {n}` from {BLOB}.
  Do not edit by hand.
-/
import JAM.Theorems.GrowHeap

/-!
# Code facts of {LBL}

The code facts the proofs about {LBL} use: every instruction on the first {n} steps of its
refine path{if cx.svc.emptyCode then " and on the empty payload's refine path," else ""} and every instruction of the summarized functions (`fnRanges`), with the block
starts and jump-table entries they need. `checkCode` checks them against the blob
(`lake build {LBL}check`); `HasCode p P` assumes them.
-/

namespace Services.{NS}.Code

open PVM

"
    let chunks := (List.range ((factsL.length + 63) / 64)).map fun c => (factsL.drop (64 * c)).take 64
    for (c, ch) in (List.range chunks.length).zip chunks do
      IO.println (s!"/-- Code facts {64 * c}–{64 * c + ch.length - 1}. -/\ndef facts_{c} : List CodeFact := [\n  " ++ ",\n  ".intercalate ch ++ "]\n")
    IO.println ("/-- The chunks of `facts`. -/\ndef factChunks : List (List CodeFact) := [" ++ ", ".intercalate ((List.range chunks.length).map fun c => s!"facts_{c}") ++ "]\n")
    IO.println s!"/-- The code facts the {LBL} proofs use. -/\ndef facts : List CodeFact := factChunks.flatten\n"
    IO.println "/-- The blob `p` deblobs to `P`, and `facts` hold of it. -/\nclass HasCode (p : outParam ByteArray) (P : Program) : Prop where\n  ok : CodeOk p facts P\n"
    IO.println ("\n\n".intercalate lemmasL.toList)
    IO.println s!"\nend Services.{NS}.Code"
    return
  IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}run {n}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.{if cx.svc.memcpySummary then "Memcpy" else "Code"}

/-!
# The first {n} steps of {LBL}'s refine, proved symbolically

From Y's initial registers, with any argument length `L` in 1 … 𝖹_I and memory arbitrary except
for the facts `StartMem` lists, {LBL}'s code runs {n} gas-free steps from its entry point to the
instruction at {endPc}, through its host calls, assuming only the code facts
`Services.{NS}.Code.facts`, which `checkCode` checks against the blob (`lake build
{LBL}check`). Host calls take the outcome the refine dispatcher gives (`JAM.refineContract`), for
any refine environment with the full-chain parameters (`Params.full`). Values that depend on `L`
are kept symbolic and decided by `omega`.

Ordinary steps are proved by `pvm_simp`, host calls by `pvm_host`; nothing here is evaluated by
compiled code.
-/

namespace Services.{NS}.Prefix

open PVM JAM Services.{NS}.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 40000000
"
  IO.println ("/-- The octets the path reads from the starting memory before writing them. -/\ndef baseBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (baseBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  let inRw := fun (a : Nat) => decide (rwLo ≤ a ∧ a < rwLo + jb.rw.size)
  let inRo := fun (a : Nat) => decide (roStart ≤ a ∧ a < roStart + jb.ro.size)
  IO.println ("/-- The octets any traced run reads from the starting memory before writing them, beyond
    `baseBytes`: what the theorems after the prefix take from the start. -/\ndef pathBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (pathBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  let rwBytes := (baseBytes ++ pathBytes).filter (inRw ·.1)
  let roBytes := (baseBytes ++ pathBytes).filter (inRo ·.1)
  IO.println ("/-- The octets of `baseBytes` in the read-write data section. -/\ndef rwBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (rwBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  IO.println ("/-- The octets of `baseBytes` in the read-only data section. -/\ndef roBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (roBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  let (info0, others, otherPs) ← prefixInfo cx
  -- calls to `memcpy` of fewer than 16 octets, with the same arguments in every run of the class,
  -- are taken by `memcpy_small` (the head of `fnRanges`) instead of stepped through
  let memBase := (cx.svc.fnRanges.head?.map (·.1)).getD 0
  let agreeAt (k j : Nat) : Bool :=
    others.toList.all fun (t2, _) => (t2[k]?.map (fun q => q.2.1[j]!)) == (tr[k]?.map (fun q => q.2.1[j]!))
  let mut splices : Array (Nat × Nat) := #[]
  if cx.svc.memcpySummary then
    let mut k := 0
    for _ in [0:n] do
      if k ≥ n then break
      let some (pck, r, _) := tr[k]? | break
      if pck == memBase && r[9]!.toNat < 16 && [0, 1, 7, 8, 9].all (agreeAt k) then
        let t := P.jumpTable.getD (r[0]!.toNat / 2 - 1) 0
        match (List.range (n - k)).find? (fun d => (tr[k + d]?.map (·.1)) == some t) with
        | some d => splices := splices.push (k, k + d); k := k + d
        | none => k := k + 1
      else k := k + 1
  -- ω₈ … ω₁₁ after a spliced `memcpy` are its scratch values, which `memcpy_small_regs` does not
  -- state: the post leaves them out unless the path writes them again afterwards
  let scratch : List Nat := match splices.back? with
    | some (_, kr) => [8, 9, 10, 11].filter fun j =>
        (tr[kr]?.map (fun q => q.2.1[j]!)) == (tr[n]?.map (fun q => q.2.1[j]!))
    | none => []
  let argLo := ω[7]!.toNat
  -- 8-octet words the path writes with the argument length L, in every run of the class
  let lenAt := (info0.wr.foldr (fun (lo, hi) acc => (List.range ((hi - lo) / 8)).map (lo + 8 * ·) ++ acc) []).filter
    fun a => Num.decodeLE (((tr[n]?).map (fun x => x.2.2.readN a 8)).getD []) == ω[8]!.toNat &&
      (others.toList.zip otherPs.toList).all fun ((t2, _), q) =>
        Num.decodeLE (((t2[n]?).map (fun x => x.2.2.readN a 8)).getD []) ==
          (Codec.nat q.1).length + (Codec.nat q.2.1).length + (Codec.nat q.2.2.1).length +
            (Codec.nat q.2.2.2.length).length + q.2.2.2.length + 32
  -- what the prefix writes: its stores, and at most ω₉ octets at ω₇ for each `fetch`
  let mut fw : List Nat := info0.wr.flatMap fun (lo, hi) => List.range' lo (hi - lo)
  for k in [0:n] do
    let some (pck, r, _) := tr[k]? | break
    if let some (.oneImm .ecalli 2) := P.decode pck then
      fw := fw ++ (List.range r[9]!.toNat).map fun j => (r[7]!.toNat + j) % 2 ^ 32
  let frameR := ranges (fw.eraseDups.mergeSort)
  let info := { info0 with
    memPost := info0.memPost.filter (fun (b, _) => !lenAt.any fun a => a ≤ b && b < a + 8),
    regPost := info0.regPost.filter (fun (j, _) => !scratch.contains j),
    symPost := info0.symPost.filter (fun (j, _) => !scratch.contains j) }
  let regStr (j : Nat) : String := match info.symPost.lookup j with
    | some v => s!"ω'[{j}] = UInt64.ofNat {v}"
    | none => s!"ω'[{j}] = UInt64.ofNat {((info.regPost.lookup j).join).getD 0}"
  IO.println ("/-- The octets the path writes that later steps read, with the values it leaves there. -/\ndef postBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (info.memPost.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  IO.println ("/-- The 8-octet words the path leaves holding the argument length. -/\ndef lenAt : List Nat := [" ++ ", ".intercalate (lenAt.map toString) ++ "]\n")
  IO.println s!"/-- **What the path leaves**, for an argument of length `L` at {argLo}: the registers, the
    octets of `postBytes`, the arguments and their access unchanged, the stack and the read-write
    data and heap writable, and the refine context unchanged. -/
structure PrefixPost (L : Nat) (μ : Memory) (ω' : Regs) (μ' : Memory) (x' : RefineCtx) : Prop where
  regs : {" ∧ ".intercalate (((List.range 13).filter (!scratch.contains ·)).map regStr)}
  bytes : ∀ q ∈ postBytes, μ'.read q.1 = q.2
  args : ∀ a, {argLo} ≤ a → a < {argLo} + L → μ'.read a = μ.read a
  argsRd : ∀ a, {argLo} ≤ a → a < {argLo} + L → μ'.readable a = μ.readable a
  stack : ∀ a, {ω[1]!.toNat} - {jb.stackSize} ≤ a → a < {ω[1]!.toNat} → μ'.writable a = true
  heap : ∀ a, {rwLo} ≤ a → a < {rwHi} → μ'.writable a = true
  ctx : x' = ((∅, []) : RefineCtx)
  lenWords : ∀ a ∈ lenAt, μ'.readN a 8 = Num.encodeLE 8 L
  ro : ∀ a, {roStart} ≤ a → a < {roStart + jb.ro.size} → μ'.readable a = true
  frame : ∀ a, (decide (a < 4294967296){String.join (frameR.map fun (lo, hi) => s!" && !(decide ({lo} ≤ a ∧ a < {hi}))")}) = true →
    μ'.read a = μ.read a
"
  IO.println s!"
/-- Y's registers (GP eq. `registers`) for an argument of length `L`. -/
def initRegs (L : Nat) : Regs :=
  Vector.ofFn fun k => UInt64.ofNat (([{", ".intercalate ((ω.toList.map (·.toNat)).set 8 0 |>.map toString)}] : List Nat).set 8 L |>.getD k.val 0)

/-- What the path needs of its starting memory: the stack and the read-write data and heap are
    writable, and the octets it reads before writing them have their initial values. -/
structure StartMem (μ : Memory) : Prop where
  stack : ∀ a, {ω[1]!.toNat} - {jb.stackSize} ≤ a → a < {ω[1]!.toNat} → μ.writable a = true
  heap : ∀ a, {rwLo} ≤ a → a < {rwHi} → μ.writable a = true
  bytes : ∀ a b, (a, b) ∈ baseBytes → μ.read a = b
  heapPages : HeapPages μ {hA} {hB} {hTop0}
  path : ∀ a b, (a, b) ∈ pathBytes → μ.read a = b
  ro : ∀ a, {roStart} ≤ a → a < {roStart + jb.ro.size} → μ.readable a = true

theorem prefix_run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = ({hA}, {hB})) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (L : Nat) (hL : 0 < L ∧ L ≤ 16777216) (hμ : StartMem μ) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) {endPc} ω' μ' x' ∧
      PrefixPost L μ ω' μ' x' := by
  obtain ⟨hL0, hLI⟩ := hL
  have hw := hμ.stack
  have hwh := hμ.heap
  have hr : ∀ a, {ω[1]!.toNat} - {jb.stackSize} ≤ a → a < {ω[1]!.toNat} → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hrh : ∀ a, {rwLo} ≤ a → a < {rwHi} → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwh a h1 h2)"
  for (a, b) in baseBytes do
    IO.println s!"  have hb_{a} : μ.read {a} = {b} := hμ.bytes {a} {b} (by decide)"
  for (a, k) in baseLoads do
    let bytes := (List.range k).map fun j => (μ.read (a + j)).toNat
    let hbs := ", ".intercalate ((List.range k).map fun j => s!"hb_{a + j}")
    IO.println s!"  have hbn_{a}_{k} : μ.readN {a} {k} = {bytes} := by\n    simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.map_append, Nat.reduceAdd, Nat.add_zero, {hbs}]"
  let stepLine (pc : Nat) (gs : String) : String := match P.decode pc with
    | some (.oneImm .ecalli 1) => Id.run do
      let some (_, regsAt, memAt) := tr.find? (·.1 == pc) | return ""
      let top := (growHeapCore regsAt memAt code).2.2.1
      let t := growTop (regsAt[7]!.toNat) top hB
      return s!"    apply FreeStepsH.growHeap env {t} (d_{pc} (p := p) (P := P)) henv (h := {top})\n      (by heap_pages hμ.heapPages) (by decide) (by decide) (by decide)\n      (by pvm_simp [growTop, initRegs, List.set_cons_succ, List.set_cons_zero, reg{gs}])"
    | some (.oneImm .ecalli _) =>
      s!"    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_host [hw, hr, hwh, hrh, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE, initRegs, List.set_cons_succ, List.set_cons_zero, growTop, setR7, reg{gs}]"
    | _ =>
      s!"    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [hpar, Params.full_encode, hw, hr, hwh, hrh, {", ".intercalate (baseLoads.toList.map fun (a, k) => s!"hbn_{a}_{k}")}{if baseLoads.isEmpty then "" else ", "}{", ".intercalate (baseBytes.toList.map fun (a, _) => s!"hb_{a}")}{if baseBytes.isEmpty then "" else ", "}initRegs, List.set_cons_succ, List.set_cons_zero, growTop, setR7, reg{gs}]"
  IO.println s!"
  rw [show initRegs L = regsNF (initRegs L) [] from rfl]"
  let mut gs := ""
  if splices.isEmpty then
    IO.println "  refine ⟨?ω, ?μ, ?x, ?h, ?post⟩\n  case h =>"
    for pc in path do IO.println (stepLine pc "")
  else
    IO.println s!"  suffices hs : ∃ ω' μ', FreeStepsH p (refineContract env) 0 (regsNF (initRegs L) []) μ ((∅, []) : RefineCtx) {endPc} ω' μ' ((∅, []) : RefineCtx) ∧
      PrefixPost L μ ω' μ' ((∅, []) : RefineCtx) by
    obtain ⟨ω', μ', h, hp⟩ := hs
    exact ⟨ω', μ', _, h, hp⟩"
    let mut k := 0
    for s in [0:splices.size] do
      let (ks, kr) := splices[s]!
      let some (_, r, _) := tr[ks]? | break
      let ret := r[0]!.toNat
      let t := P.jumpTable.getD (ret / 2 - 1) 0
      IO.println s!"  refine FreeStepsH.ex_trans (i₁ := {memBase}) (ω₁ := ?ω₁_{s}) (μ₁ := ?μ₁_{s}) ?pre{s} ?rest{s}\n  case pre{s} =>"
      for j in [k:ks] do IO.println (stepLine path[j]! gs)
      IO.println s!"    exact FreeStepsH.refl
  refine FreeStepsH.bind_ex (memcpy_small_regs (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) _ _
    {ret} {t} {r[1]!.toNat} {r[7]!.toNat} {r[8]!.toNat} {r[9]!.toNat} ?m0_{s} ?m1_{s} ?m7_{s} ?m8_{s} ?m9_{s} (by decide)
    (by decide) ?mjt_{s} ?mbt_{s} (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf_{s} ?mr_{s} ?mw_{s}) ?k{s}
  case m0_{s} | m1_{s} | m7_{s} | m8_{s} | m9_{s} =>
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
      List.lookup_nil, Option.getD_none, initRegs, List.set_cons_succ, List.set_cons_zero, reg{gs}]
  case mjt_{s} => simp only [Nat.reduceDiv, Nat.reduceSub, jte_{ret / 2 - 1}]
  case mbt_{s} => exact bs_{t}
  case mwf_{s} | mw_{s} =>
    intro a h1 h2
    simp only [PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, pageSize]
    repeat' split
    all_goals first | rfl | exact hw a (by omega) (by omega) | exact hwh a (by omega) (by omega) | omega
  case mr_{s} =>
    intro a h1 h2
    simp only [PVM.Memory.readable_writeN, PVM.Memory.readable_setPages, pageSize]
    repeat' split
    all_goals first | rfl | exact hr a (by omega) (by omega) | exact hrh a (by omega) (by omega) | omega
  intro ω{s} ⟨g{s}_0, g{s}_1, g{s}_2, g{s}_3, g{s}_4, g{s}_5, g{s}_6, g{s}_7, g{s}_12⟩
  simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
    List.lookup_nil, Option.getD_none, initRegs, List.set_cons_succ, List.set_cons_zero, reg{gs}] at g{s}_0 g{s}_1 g{s}_2 g{s}_3 g{s}_4 g{s}_5 g{s}_6 g{s}_7 g{s}_12
  simp only [memcpyFrame, PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
    List.lookup_nil, Option.getD_none, initRegs, List.set_cons_succ, List.set_cons_zero, reg, UInt64.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, PVM.Memory.readN, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.map_append, List.nil_append, List.cons_append, Nat.reduceAdd, Nat.add_zero{gs}]
  rw [show ω{s} = regsNF ω{s} [] from rfl]"
      gs := gs ++ s!", g{s}_0, g{s}_1, g{s}_2, g{s}_3, g{s}_4, g{s}_5, g{s}_6, g{s}_7, g{s}_12"
      k := kr
    IO.println "  refine ⟨?ω, ?μ, ?h, ?post⟩\n  case h =>"
    for j in [k:n] do IO.println (stepLine path[j]! gs)
  IO.println s!"    exact FreeStepsH.refl
  case post =>
    refine ⟨?regs, ?bytes, ?args, ?argsRd, ?stk, ?hp, rfl, ?lw, ?ro, ?fr⟩
    case ro =>
      intro a h1 h2
      simp only [PVM.Memory.readable_writeN, PVM.Memory.readable_setPages, pageSize]
      repeat' split
      all_goals first | rfl | exact hμ.ro a h1 h2 | omega
    case fr =>
      intro a ha
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
        not_and, Nat.not_lt] at ha
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Memory.read_setPages,
        PVM.Num.length_encodeLE, PVM.Memory.length_readN, List.length_cons, List.length_nil, PVM.two32]
    case lw =>
      simp only [lenAt, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same,
        PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_setPages, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, PVM.two32]
    case regs =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        PVM.getD_some', List.lookup_nil, Option.getD_none, and_self, and_true, true_and{gs}]
    case bytes =>
      simp only [postBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
      and_intros
      all_goals simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.Memory.read_setPages, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,
        List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,
        Nat.reduceLT, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,
        List.getElem!_cons_succ, UInt8.reduceOfNat, and_self]
    case args =>
      intro a h1 h2
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Memory.read_setPages,
        PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
    case argsRd =>
      intro a h1 h2
      simp only [PVM.Memory.readable_writeN, PVM.Memory.readable_setPages, pageSize]
      repeat' split
      all_goals first | rfl | omega
    case stk =>
      intro a h1 h2
      simp only [PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, pageSize]
      repeat' split
      all_goals first | rfl | exact hw a h1 h2 | omega
    case hp =>
      intro a h1 h2
      simp only [PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, pageSize]
      repeat' split
      all_goals first | rfl | exact hwh a h1 h2 | omega

/-! ## From Y's starting state -/

/-- The section sizes of the deployed blob (GP eq. `conditions`): read-only data, read-write data,
    heap pages and stack, and the data octets the path reads (`rwBytes`, `roBytes`).
    `lake build {LBL}check` checks them. -/
def layoutOk (jb : JamBlob) : Bool :=
  jb.ro.size == {jb.ro.size} && jb.rw.size == {jb.rw.size} && jb.heapPages == {jb.heapPages} &&
    jb.stackSize == {jb.stackSize} && rwBytes.all (fun q => jb.rw.toList[q.1 - {rwLo}]! == q.2) &&
    roBytes.all (fun q => jb.ro.toList[q.1 - {roStart}]! == q.2)

/-- Every starting octet the path reads is a zero of the stack or of the heap beyond the
    read-write data, or a data octet listed in `rwBytes` or `roBytes`. -/
theorem baseBytes_cases : ∀ q ∈ baseBytes ++ pathBytes, (q.2 = 0 ∧
    (({ω[1]!.toNat} - {jb.stackSize} ≤ q.1 ∧ q.1 < {ω[1]!.toNat}) ∨ ({rwLo + jb.rw.size} ≤ q.1 ∧ q.1 < {rwHi}))) ∨
    (q ∈ rwBytes ∧ {rwLo} ≤ q.1 ∧ q.1 < {rwLo + jb.rw.size}) ∨
    (q ∈ roBytes ∧ {roStart} ≤ q.1 ∧ q.1 < {roStart + jb.ro.size}) := by
  decide

/-- **Y's RAM meets the path's needs**, for a blob with the deployed section sizes and any
    arguments. -/
theorem startMem_initial (jb : JamBlob) (a : ByteArray) (hl : layoutOk jb = true)
    (ha : a.size ≤ inputSize) : StartMem (initialMemory jb a) := by
  simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, hheap⟩, hstack⟩, hrwb⟩, hrob⟩ := hl
  have hrs : rwStart jb = {rwLo} := by simp [rwStart, hro, roundZone, zoneSize]
  refine ⟨fun x h1 h2 => ?_, fun x h1 h2 => ?_, fun x b hm => ?_, fun q h1 h2 => ?_, fun x b hm => ?_,
    fun x h1 h2 => ?_⟩
  · simp only [Memory.writable, initialMemory_pages, hstack, hrs, hrw, hro, hheap, argStart, stackEnd,
      roundPage, pageSize, zoneSize, inputSize, roStart]
    split
    · omega
    · rw [ite_eq_left (by omega)]; rfl
  · simp only [Memory.writable, initialMemory_pages, hstack, hrs, hrw, hro, hheap, argStart, stackEnd,
      roundPage, pageSize, zoneSize, inputSize, roStart]
    split
    · omega
    · split
      · omega
      · rw [ite_eq_left (by omega)]; rfl
  · have hrd := initialMemory_read jb a x
    rcases baseBytes_cases (x, b) (List.mem_append_left _ hm) with ⟨hb, hx⟩ | ⟨hq, hx1, hx2⟩ | ⟨hq, hx1, hx2⟩
    · simp only at hb hx
      subst hb
      rw [hrd (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
        (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
      rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
        ite_eq_right (by rw [hrs, hrw]; omega), ite_eq_right (by simp only [roStart, zoneSize, hro]; omega)]
    · have hv := beq_iff_eq.1 (List.all_eq_true.1 hrwb _ hq)
      simp only at hv hx1 hx2
      rw [hrd (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
        (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
      rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
        ite_eq_left (by rw [hrs, hrw]; omega), hrs, hv]
    · have hv := beq_iff_eq.1 (List.all_eq_true.1 hrob _ hq)
      simp only at hv hx1 hx2
      rw [hrd (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
        (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
      rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
        ite_eq_right (by rw [hrs]; omega), ite_eq_left (by simp only [roStart, zoneSize, hro]; omega)]
      simpa only [roStart, zoneSize] using hv
  · simp only [initialMemory_pages, hstack, hrs, hrw, hro, hheap, argStart, stackEnd,
      roundPage, pageSize, zoneSize, inputSize, roStart]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    by_cases hq : q < {hTop0}
    · rw [ite_eq_left (by omega)]; simp [hq]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]; simp [hq]
  · have hrd := initialMemory_read jb a x
    rcases baseBytes_cases (x, b) (List.mem_append_right _ hm) with ⟨hb, hx⟩ | ⟨hq, hx1, hx2⟩ | ⟨hq, hx1, hx2⟩
    · simp only at hb hx
      subst hb
      rw [hrd (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
        (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
      rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
        ite_eq_right (by rw [hrs, hrw]; omega), ite_eq_right (by simp only [roStart, zoneSize, hro]; omega)]
    · have hv := beq_iff_eq.1 (List.all_eq_true.1 hrwb _ hq)
      simp only at hv hx1 hx2
      rw [hrd (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
        (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
      rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
        ite_eq_left (by rw [hrs, hrw]; omega), hrs, hv]
    · have hv := beq_iff_eq.1 (List.all_eq_true.1 hrob _ hq)
      simp only at hv hx1 hx2
      rw [hrd (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
        (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
      rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
        ite_eq_right (by rw [hrs]; omega), ite_eq_left (by simp only [roStart, zoneSize, hro]; omega)]
      simpa only [roStart, zoneSize] using hv
  · simp only [Memory.readable, initialMemory_pages, hstack, hrs, hrw, hro, hheap, argStart, stackEnd,
      roundPage, pageSize, zoneSize, inputSize, roStart]
    repeat' split
    all_goals first | rfl | omega

/-- Y's registers are `initRegs |a|`. -/
theorem initRegs_eq (a : ByteArray) : initialRegs a = initRegs a.size := by
  apply Vector.ext
  intro k hk
  simp only [initialRegs, initRegs, Vector.getElem_ofFn, stackEnd, argStart, zoneSize, inputSize]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ =>
    simp

/-- **The first {n} steps of {LBL}'s refine, from Y.** For a JAM blob with the deployed section
    sizes whose PVM code passes `checkCode` (the vendored {LBL} blob does both: `lake build
    {LBL}check`), and any nonempty arguments Y accepts (refine's always are), the gas-free machine runs from Y's starting state
    to the instruction at {endPc}, through its host calls, in every refine environment with the full-chain parameters. -/
theorem prefix_from_Y (b a : ByteArray) (jb : JamBlob) (hjb : JamBlob.parse? b = some jb)
    (hl : layoutOk jb = true) (hc : checkCode jb.code facts = true) (p : ByteArray) (ω : Regs)
    (μ : Memory) (hY : standardInit b a = some (p, ω, μ)) (env : RefineHost.Env)
    (henv : heapBounds env.code = ({hA}, {hB})) (hpar : env.fetch.params = Params.full)
    (ha0 : 0 < a.size) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 ω μ ((∅, []) : RefineCtx) {endPc} ω' μ' x' ∧
      PrefixPost a.size μ ω' μ' x' := by
  obtain ⟨jb', hv, he⟩ := Option.map_eq_some_iff.1 hY
  have hjb' : jb' = jb ∧ a.size ≤ inputSize := by
    unfold validJamBlob? at hv
    by_cases ha : a.size > inputSize
    · rw [ite_eq_left ha] at hv; cases hv
    · rw [ite_eq_right ha, hjb, Option.bind_some] at hv
      split at hv
      · cases hv
      · cases hv; exact ⟨rfl, by omega⟩
  obtain ⟨rfl, ha⟩ := hjb'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  obtain ⟨P, hP⟩ := checkCode_sound hc
  haveI : HasCode jb'.code P := ⟨hP⟩
  rw [initRegs_eq]
  exact prefix_run _ P env henv hpar _ a.size ⟨ha0, by simpa only [inputSize] using ha⟩
    (startMem_initial _ a hl ha)

end Services.{NS}.Prefix"

set_option linter.unusedVariables false in
def mode_steps (cx : Cx) : IO Unit := do
    -- `steps N M`: steps N … M − 1 of the base run: pc, instruction, the registers it changes
    let m := (cx.args.getD 2 "0").toNat!
    for k in [cx.n:m] do
      let some (pc, r, _) := cx.tr[k]? | break
      let some (_, r2, _) := cx.tr[k + 1]? | break
      let ch := (List.range 13).filter fun j => r[j]! != r2[j]!
      IO.println s!"{k} {pc} {(cx.P.decode pc).map leanInstr |>.getD "?"}  {ch.map fun j => s!"r{j}={r2[j]!.toNat}"}"

set_option linter.unusedVariables false in
def mode_post (cx : Cx) : IO Unit := do
    -- `post N`: what steps 0 … N − 1 leave, by the segment analysis over a class of inputs
    let (info, _, _) ← prefixInfo cx
    IO.println s!"vars {info.vars}"
    IO.println s!"regs at start {info.regFacts} sym {info.symRegs}"
    IO.println s!"wregs {info.wregs}"
    IO.println s!"regPost {info.regPost}"
    IO.println s!"symPost {info.symPost}"
    IO.println s!"written {info.wr}"
    IO.println s!"memPost ({info.memPost.length}) {info.memPost}"

/-- `memcpy` in witness's blob, where `Services/Witness/Memcpy.lean` proves it: the template of
    the summaries for other blobs. -/
def memcpyTemplate : Nat × Nat := (186740, 187150)

/-- Shift every number in `[lo, hi)` in `t` by `d` (the pcs of a function moved as a whole). -/
def shiftPcs (t : String) (lo hi : Nat) (f : Nat → Nat) : String := Id.run do
  let mut out := ""
  let mut num := ""
  for ch in t.toList ++ [' '] do
    if ch.isDigit then num := num.push ch
    else
      if num != "" then
        let v := num.toNat!
        out := out ++ (if lo ≤ v && v < hi then toString (f v) else num)
        num := ""
      out := out.push ch
  return (out.toList.dropLast).asString

set_option linter.unusedVariables false in
def mode_memcpy (cx : Cx) : IO Unit := do
    -- `memcpy`: the `memcpy` summary of the service, from witness's proof with the pcs moved to
    -- where the service has the same code (`fnRanges` head), and its jump-table size
    let some (base, _) := cx.svc.fnRanges.head? | throw (IO.userError "no fnRanges")
    let t ← IO.FS.readFile "Services/Witness/Memcpy.lean"
    let (lo, hi) := memcpyTemplate
    let body := shiftPcs t lo hi (fun v => v + base - lo)
    let body := body.replace "Services.Witness" s!"Services.{cx.svc.name}"
    let body := body.replace "in witness's code" s!"in {cx.svc.label}'s code"
    let body := body.replace "in witness, summarized" s!"in {cx.svc.label}, summarized"
    let body := body.replace "ret ≤ 3426" s!"ret ≤ {2 * cx.P.jumpTable.size}"
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {cx.svc.flag}memcpy` from Services/Witness/Memcpy.lean, with
  the pcs moved by {base} − {lo} (the blob's `memcpy` is witness's, instruction for instruction,
  at {base}) and the jump-table bound of {cx.svc.blob}.
  Do not edit by hand.
-/"
    IO.print body

set_option linter.unusedVariables false in
def mode_valsx (cx : Cx) : IO Unit := do
    -- `valsx PC ADDR LEN`: the LEN-octet value at ADDR when each input of the segx class first reaches PC
    let addr := (cx.args.getD 2 "0").toNat!; let len := (cx.args.getD 3 "8").toNat!
    for (c2, i2, s2, y2) in cx.svc.base :: (cx.svc.segClass ++ cx.svc.segxExtra) do
      let some t2 := traceFor cx.code cx.h cx.acct cx.Q c2 i2 s2 y2 | continue
      let some k := (List.range t2.size).find? (fun k => (t2[k]?.map (·.1)) == some cx.n) | continue
      let some (_, _, mem) := t2[k]? | continue
      IO.println s!"c={c2} i={i2} s={s2} |y|={y2.length}: {mem.readN addr len}"

set_option maxHeartbeats 2000000 in
/-- The registers an instruction reads and writes (GP §A.5: the operand roles of each
    instruction). `ecalli`'s host calls take their arguments in ω₇ … ω₁₂ and return in ω₇. -/
def regRW : Instr → List Nat × List Nat
  | .noArgs _ => ([], [])
  | .oneImm _ _ => ([7, 8, 9, 10, 11, 12], [7])
  | .regExtImm _ a _ => ([], [a.1])
  | .twoImm _ _ _ => ([], [])
  | .oneOffset _ _ => ([], [])
  | .regImm op a _ => match op with
    | .jumpInd | .storeU8 | .storeU16 | .storeU32 | .storeU64 => ([a.1], [])
    | _ => ([], [a.1])
  | .regTwoImm _ a _ _ => ([a.1], [])
  | .regImmOffset op a _ _ => match op with
    | .loadImmJump => ([], [a.1])
    | _ => ([a.1], [])
  | .twoReg _ d a => ([a.1], [d.1])
  | .twoRegImm op a b _ => match op with
    | .storeIndU8 | .storeIndU16 | .storeIndU32 | .storeIndU64 => ([a.1, b.1], [])
    | .cmovIzImm | .cmovNzImm => ([a.1, b.1], [a.1])
    | _ => ([b.1], [a.1])
  | .twoRegOffset _ a b _ => ([a.1, b.1], [])
  | .twoRegTwoImm _ a b _ _ => ([b.1], [a.1])
  | .threeReg op a b d => match op with
    | .cmovIz | .cmovNz => ([a.1, b.1, d.1], [d.1])
    | _ => ([a.1, b.1], [d.1])

/-- The registers steps `A … B − 1` of the traced path read before writing them. -/
def regsRead (cx : Cx) (A B : Nat) : List Nat := Id.run do
  let mut written : List Nat := []
  let mut out : List Nat := []
  for k in [A:B] do
    let some (pc, _, _) := cx.tr[k]? | continue
    let some ins := cx.P.decode pc | continue
    let (rs, ws) := regRW ins
    for r in rs do
      if !written.contains r && !out.contains r then out := out ++ [r]
    written := written ++ ws
  return out.mergeSort

/-- The registers steps `A … B − 1` of the traced path write (by the instructions' operands, so
    also a register written with the value it already held). -/
def regsWritten (cx : Cx) (A B : Nat) : List Nat := Id.run do
  let mut out : List Nat := []
  for k in [A:B] do
    let some (pc, _, _) := cx.tr[k]? | continue
    let some ins := cx.P.decode pc | continue
    for w in (regRW ins).2 do
      if !out.contains w then out := out ++ [w]
  return out

/-- The Lean binder for a variable and its bound. -/
def varBinder (v : String) : String :=
  let bound := match v with
    | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => "S < 4294967296" | "C" => "C < 65536" | "L" => "L < 4294967296"
    | "T" => "12 ≤ T ∧ T < 256" | "Q" => "4278124548 ≤ Q ∧ Q ≤ 4278124564" | _ => "I < 65536"
  s!"({v} : Nat) (h{v} : {bound})"

/-- The variables an expression mentions. -/
def exprVars (names : List String) (e : String) : List String :=
  ((e.replace "(" "").replace ")" "" |>.splitOn " ").filter names.contains

/-- `cut PC name b₀ b₁ … bₙ [out]` (or `cut PC name A B every=N`): steps b₀ … bₙ − 1 after the path
    first reaches PC, as segments that each fit one refine of witness-lean's check. The state at each
    cut bₖ is a named predicate `Stₖ` (the registers, octets, symbolic words and page access the rest
    of the path needs), and segment k proves `Stₖ → ∃ run, Stₖ₊₁`, so the segments compose by
    transitivity alone. Writes `Services/NS/name/St.lean`, `…/name/S{k}.lean` and `…/name.lean`. -/
def mode_cut (cx : Cx) : IO Unit := do
  let args := cx.args; let tr := cx.tr; let P := cx.P
  let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
  let joinPc := cx.n
  let name := args.getD 2 "cut"
  let opts := args.drop 3
  let out := opts.contains "out"
  let nums := (opts.filter fun o => o.all Char.isDigit).map String.toNat!
  let bs : List Nat := match opts.find? (·.startsWith "every=") with
    | some e =>
      let N := ((e.drop 6).toString).toNat!
      let A := nums[0]!; let B := nums[1]!
      ((List.range ((B - A + N - 1) / N)).map (A + N * ·)) ++ [B]
    | none => nums
  let classInputs : List (Nat × Nat × Nat × List UInt8) :=
    if cx.empty then cx.svc.emptyClass ++ cx.svc.emptyExtra else cx.svc.segClass ++ cx.svc.segxExtra
  let baseP := (cx.c, cx.i, cx.sid, cx.y)
  let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
    (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
  let some k0 := align tr | IO.eprintln "join not reached"; return
  let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
  let mut otherPs : Array (Nat × Nat × Nat × List UInt8) := #[]
  for (c2, i2, s2, y2) in classInputs do
    let some t2 := traceFor cx.code cx.h cx.acct cx.Q c2 i2 s2 y2 | continue
    let some k2 := align t2 | IO.eprintln "join not reached"; return
    for j in [bs.head!:bs.getLast!+1] do
      if (tr[k0 + j]?.map (·.1)) != (t2[k2 + j]?.map (·.1)) then
        IO.eprintln s!"paths differ at +{j}"; return
    others := others.push (t2, k2)
    otherPs := otherPs.push (c2, i2, s2, y2)
  let names := varNames true baseP
  let allQ := baseP :: otherPs.toList
  -- the value of register j / octet a at path step b (after PC), if the class agrees on it or it
  -- is one of the variables' expressions
  let regAt (b j : Nat) : Option String :=
    let vb := (tr[k0 + b]?.map (·.2.1[j]!.toNat)).getD 0
    let vo := others.toList.map fun (t2, k2) => (t2[k2 + b]?.map (·.2.1[j]!.toNat)).getD 0
    if vo.all (· == vb) then some (toString vb) else matchVarG true names allQ vb vo
  let octAt (b a : Nat) : Option Nat :=
    let vb := (tr[k0 + b]?.map (·.2.2.read a |>.toNat)).getD 0
    let vo := others.toList.map fun (t2, k2) => (t2[k2 + b]?.map (·.2.2.read a |>.toNat)).getD 0
    if vo.all (· == vb) then some vb else none
  let nseg := bs.length - 1
  let mut infos : Array SegInfo := Array.replicate nseg default
  let mut reads : Array (List Nat) := Array.replicate nseg []
  let mut writes : Array (Std.HashSet Nat) := Array.replicate nseg {}
  -- the state each cut needs, backward from the end
  let fin := (List.range 13).map (fun j => (tr[k0 + bs.getLast!]?.map (·.2.1[j]!.toNat)).getD 0)
  let outO := if out then (List.range fin[8]!).map (fin[7]! + ·) else []
  let mut needR : List Nat := if out then [0, 7, 8] else []
  let mut needO : List Nat := outO
  let mut needS : List (Nat × Nat × String) := []
  let mut needW : List (Nat × Nat) := []
  let mut needRd : List (Nat × Nat) := if out && fin[8]! > 0 then [(fin[7]!, fin[7]! + fin[8]!)] else []
  let mut sts0 : Array (List Nat × List Nat × List (Nat × Nat × String) × List (Nat × Nat) × List (Nat × Nat)) :=
    #[(needR, needO, needS, needW, needRd)]
  for kk in [0:nseg] do
    let k := nseg - 1 - kk
    let info ← analyzeSeg P tr others otherPs k0 bs[k]! bs[k+1]! false baseP true needO
      (regsWritten cx (k0 + bs[k]!) (k0 + bs[k+1]!))
    let mut w : Std.HashSet Nat := {}
    for (lo, hi) in info.wr do
      for a in [lo:hi] do w := w.insert a
    infos := infos.set! k info
    writes := writes.set! k w
    reads := reads.set! k (regsRead cx (k0 + bs[k]!) (k0 + bs[k+1]!))
    -- what segment k must leave: check it does
    for j in needR do
      if info.wregs.contains j && !(info.regPost.any (fun (i, v) => i == j && v.isSome)) && !(info.symPost.any (·.1 == j)) then
        throw (IO.userError s!"segment {k} leaves register {j} input-dependent, and a later step reads it")
    for a in needO do
      if w.contains a && !(info.memPost.any (·.1 == a)) then
        throw (IO.userError s!"segment {k} leaves octet {a} input-dependent, and a later step reads it")
    for (a, n, e) in needS do
      if (List.range n).any (fun q => w.contains (a + q)) && !(n == 8 && info.symMem.any (· == (a, e))) then
        throw (IO.userError s!"segment {k} writes into the symbolic word at {a}, and a later step reads it")
    let rd := reads[k]!
    needR := (rd ++ needR.filter (fun j => !info.wregs.contains j)).eraseDups.mergeSort
    needO := (info.byteFacts.map (·.1) ++ needO.filter (fun a => !w.contains a)).eraseDups.mergeSort
    needS := (info.symLoads ++ needS.filter (fun (a, n, _) => !(List.range n).any (fun q => w.contains (a + q)))).eraseDups
    needW := (info.wr ++ needW).eraseDups
    needRd := (info.rr ++ needRd).eraseDups
    sts0 := sts0.push (needR, needO, needS, needW, needRd)
  let sts := sts0.reverse
  -- octets as runs inside aligned 8-octet words; page ranges merged into maximal intervals
  let runsOf (os : List Nat) : List (Nat × Nat) := Id.run do
    let mut rs : List (Nat × Nat) := []
    for a in os.mergeSort do
      match rs with
      | (c, m) :: rest => if c + m == a && c / 8 == a / 8 then rs := (c, m + 1) :: rest else rs := (a, 1) :: rs
      | [] => rs := [(a, 1)]
    return rs.reverse
  let merge (xs : List (Nat × Nat)) : List (Nat × Nat) := Id.run do
    let mut rs : List (Nat × Nat) := []
    for (lo, hi) in xs.mergeSort (fun x y => x.1 ≤ y.1) do
      match rs with
      | (l, h) :: rest => if lo ≤ h then rs := (l, max h hi) :: rest else rs := (lo, hi) :: rs
      | [] => rs := [(lo, hi)]
    return rs.reverse
  let runs (k : Nat) : List (Nat × Nat) := runsOf sts[k]!.2.1
  -- the run of cut k holding octet b, and b's index in it
  let runAt (k b : Nat) : Option (Nat × Nat × Nat) :=
    (runs k).findSome? fun (c, m) => if c ≤ b && b < c + m then some (c, m, b - c) else none
  let within (xs : List (Nat × Nat)) (lo hi : Nat) : Option (Nat × Nat) :=
    xs.find? fun (l, h) => l ≤ lo && hi ≤ h
  -- a range fact of cut k's state, for a sub-range
  let rangeArg (k : Nat) (wr : Bool) (lo hi : Nat) : String :=
    let xs := merge (if wr then sts[k]!.2.2.2.1 else sts[k]!.2.2.2.2)
    let pre := if wr then "hw" else "hrd"
    match within xs lo hi with
    | some (l, h) => if l == lo && h == hi then s!"h.{pre}_{l}_{h}"
        else s!"(fun a h1 h2 => h.{pre}_{l}_{h} a (Nat.le_trans (by decide) h1) (Nat.lt_of_lt_of_le h2 (by decide)))"
    | none => "noRange"
  -- every variable the cut states mention
  let mut vars0 : List String := []
  for k in [0:nseg + 1] do
    let (r, _, s, _, _) := sts[k]!
    for j in r do
      let some e := regAt bs[k]! j | throw (IO.userError s!"register {j} at cut {k} is input-dependent")
      vars0 := vars0 ++ exprVars names e
    for (_, _, e) in s do vars0 := vars0 ++ exprVars names e
  for info in infos do vars0 := vars0 ++ info.vars
  let vars := names.filter vars0.contains
  let varArgs := " ".intercalate (vars.flatMap fun v => [v, s!"h{v}"])
  let varBinders := " ".intercalate (vars.map varBinder)
  let dir := s!"Services/{NS}/{name}"
  IO.FS.createDirAll dir
  let header (what : String) : String := s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}{cx.mode0} {joinPc} {name} {" ".intercalate opts}` from {BLOB}.
  {what} Do not edit by hand.
-/"
  -- the cut states
  let fieldsOf (k : Nat) : List (String × String) := Id.run do
    let (r, o, s, wr, rr) := sts[k]!
    let b := bs[k]!
    let mut fs : List (String × String) := []
    for j in r do fs := fs ++ [(s!"hreg{j}", s!"ω[{j}] = UInt64.ofNat {(regAt b j).getD "0"}")]
    for (c, m) in runsOf o do
      fs := fs ++ [(s!"hm_{c}_{m}", s!"μ.readN {c} {m} = {(List.range m).map fun q => (octAt b (c + q)).getD 0}")]
    for (a, n, e) in s do fs := fs ++ [(s!"hbn_{a}_{n}", s!"μ.readN {a} {n} = Num.encodeLE {n} {e}")]
    for (lo, hi) in merge wr do fs := fs ++ [(s!"hw_{lo}_{hi}", s!"∀ a, {lo} ≤ a → a < {hi} → μ.writable a = true")]
    for (lo, hi) in merge rr do fs := fs ++ [(s!"hrd_{lo}_{hi}", s!"∀ a, {lo} ≤ a → a < {hi} → μ.readable a = true")]
    return fs
  for k in [0:nseg + 1] do
    let (_, o, _, _, _) := sts[k]!
    for a in o do
      if (octAt bs[k]! a).isNone then throw (IO.userError s!"octet {a} at cut {k} is input-dependent")
  let mut st := header "The state at each cut." ++ s!"
import PVM.Logic.Chase

namespace Services.{NS}.{name}

open PVM

set_option maxRecDepth 100000

"
  for k in [0:nseg + 1] do
    let fs := fieldsOf k
    st := st ++ s!"/-- The state at cut {k} (step {bs[k]!} after pc {joinPc}, pc {infos[min k (nseg - 1)]!.pcA}): what the rest of the path reads. -/
structure St{k} {" ".intercalate (vars.map (s!"({·} : Nat)"))} (ω : Regs) (μ : Memory) : Prop where
  {if fs.isEmpty then "triv : True" else "\n  ".intercalate (fs.map (fun (n, t) => s!"{n} : {t}"))}

"
  IO.FS.writeFile s!"{dir}/St.lean" (st ++ s!"end Services.{NS}.{name}\n")
  -- the segments
  for k in [0:nseg] do
    let info := infos[k]!
    let rd := reads[k]!
    let pre := fieldsOf k
    let post := fieldsOf (k + 1)
    let ivars := names.filter info.vars.contains
    -- the steps: as `seg`, from the registers the segment reads and the octets it reads first
    let mut sx := header s!"Steps {info.A} … {info.B - 1} of {LBL}'s refine." ++ s!"
import Services.{NS}.Code
import Services.{NS}.{name}.St

namespace Services.{NS}.{name}.S{k}

open PVM JAM Services.{NS}.Code Services.{NS}.{name}

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- **Steps {info.A} … {info.B - 1} of {LBL}'s refine** (pc {info.pcA} to pc {info.pcB}), from the
    registers they read and the octets they read first, to the values they leave. -/
theorem steps (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
    for v in ivars do sx := sx ++ s!"\n    {varBinder v}"
    let regB := rd.map fun j => (s!"hreg{j}", s!"ω[{j}] = UInt64.ofNat {(regAt bs[k]! j).getD "0"}")
    let symB := info.symLoads.map fun (a, n, e) => (s!"hbn_{a}_{n}", s!"μ.readN {a} {n} = Num.encodeLE {n} {e}")
    let wB := info.wr.map fun (lo, hi) => (s!"hw_{lo}_{hi}", s!"∀ a, {lo} ≤ a → a < {hi} → μ.writable a = true")
    let rB := info.rr.map fun (lo, hi) => (s!"hrd_{lo}_{hi}", s!"∀ a, {lo} ≤ a → a < {hi} → μ.readable a = true")
    let bB := info.byteFacts.map fun (a, v) => (s!"hb_{a}", s!"μ.read {a} = {v}")
    let binders := regB ++ symB ++ wB ++ rB ++ bB
    for (n, t) in binders do sx := sx ++ s!"\n    ({n} : {t})"
    sx := sx ++ s!"\n    : ∃ ω' μ', FreeStepsH p (refineContract env) {info.pcA} ω μ x {info.pcB} ω' μ' x ∧"
    let regC := info.regPost.map (fun (j, v) =>
      match v with | some v => (j, s!"ω'[{j}] = UInt64.ofNat {v}") | none => (j, s!"ω'[{j}] = ω[{j}]")) ++
      info.symPost.map fun (j, v) => (j, s!"ω'[{j}] = UInt64.ofNat {v}")
    sx := sx ++ "\n      (" ++ " ∧ ".intercalate (regC.map (·.2)) ++ ") ∧"
    let memC := info.memPost.map fun (a, v) => s!"μ'.read {a} = {v}"
    sx := sx ++ "\n      (" ++ (if memC.isEmpty then "True" else " ∧ ".intercalate memC) ++ ") ∧"
    if !info.symMem.isEmpty then
      sx := sx ++ "\n      (" ++ " ∧ ".intercalate (info.symMem.map fun (a, e) => s!"μ'.readN {a} 8 = Num.encodeLE 8 {e}") ++ ") ∧"
    let outW := " && ".intercalate (info.wr.map fun (lo, hi) => s!"!(decide ({lo} ≤ a ∧ a < {hi}))")
    sx := sx ++ s!"\n      (∀ a, (decide (a < 4294967296){if outW == "" then "" else " && " ++ outW}) = true → μ'.read a = μ.read a) ∧"
    sx := sx ++ "\n      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by"
    for (lo, hi) in info.wr do
      sx := sx ++ s!"\n  have hr_{lo}_{hi} := fun a h1 h2 => Memory.readable_of_writable (hw_{lo}_{hi} a h1 h2)"
    for (a, n, bytes) in info.loads do
      let rds := ", ".intercalate ((List.range n).map fun q => s!"μ.read {a + q}")
      let hbs := ", ".intercalate ((List.range n).map fun q => s!"hb_{a + q}")
      sx := sx ++ s!"\n  have hbn_{a}_{n} : μ.readN {a} {n} = {bytes} := by\n    rw [show μ.readN {a} {n} = [{rds}] from rfl, {hbs}]"
    let facts := cx.svc.segFacts.filter (fun (vs, _) => vs.all ivars.contains)
    let mut fk := 0
    for (_, f) in facts do
      sx := sx ++ s!"\n  have hf{fk} : {f} := by omega"
      fk := fk + 1
    let regA := ", ".intercalate (regB.map (·.1))
    let loadA := ", ".intercalate (info.loads.map (fun (a, n, _) => s!"hbn_{a}_{n}") ++ bB.map (·.1) ++
      symB.map (·.1) ++ ivars.map (s!"h{·}"))
    let hws := ", ".intercalate (wB.map (·.1))
    let hrs := ", ".intercalate (info.wr.map (fun (lo, hi) => s!"hr_{lo}_{hi}") ++ rB.map (·.1))
    let factA := ", ".intercalate ((List.range facts.length).map (s!"hf{·}"))
    let simpArgs := ", ".intercalate ([regA, loadA, hws, hrs, factA].filter (· != ""))
    sx := sx ++ "\n  rw [show ω = regsNF ω [] from rfl]\n  refine ⟨?ω', ?μ', ?run, ?post⟩\n  case run =>"
    for pc in info.pcs do
      match P.decode pc with
      | some (.oneImm .ecalli _) =>
        sx := sx ++ s!"\n    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_host [{simpArgs}, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE]"
      | _ =>
        sx := sx ++ s!"\n    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [{simpArgs}]"
    if info.symMem.isEmpty then
      sx := sx ++ "\n    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?frame, ?rd, ?wr⟩"
    else
      sx := sx ++ "\n    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?smem, ?frame, ?rd, ?wr⟩"
      sx := sx ++ "\n    case smem =>\n      " ++ (if info.symMem.length > 1 then "refine ⟨" ++ ", ".intercalate (info.symMem.map fun _ => "?_") ++ "⟩ <;>\n      " else "") ++ "simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,\n        PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]"
    sx := sx ++ s!"\n    case regs =>\n      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,\n        PVM.getD_some', List.lookup_nil, Option.getD_none, and_self, and_true, true_and{if regA == "" then "" else ", " ++ regA}]"
    sx := sx ++ "\n    case mem =>\n      try and_intros\n      all_goals simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,\n        Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,\n        List.getElem!_cons_succ, UInt8.reduceOfNat, and_self, PVM.Num.encodeLE] <;> chase_octet"
    sx := sx ++ "\n    case frame =>\n      intro a ha\n      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,\n        not_and, Nat.not_lt] at ha\n      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32]"
    sx := sx ++ "\n    case rd => intro a; simp only [PVM.Memory.readable_writeN]\n    case wr => intro a; simp only [PVM.Memory.writable_writeN]\n"
    -- the segment between cut states
    let pat (xs : List String) : String := match xs with
      | [] => "-" | [x] => x | xs => "⟨" ++ ", ".intercalate xs ++ "⟩"
    let rNames := (List.range regC.length).map (s!"r{·}")
    let mNames := (List.range memC.length).map (s!"m{·}")
    let sNames := (List.range info.symMem.length).map (s!"s{·}")
    let w := writes[k]!
    let proofs : List String := post.map fun (n, _) =>
      if n.startsWith "hreg" then
        let j := (n.drop 4).toString.toNat!
        match regC.findIdx? (·.1 == j) with
        | some q => if info.wregs.contains j then s!"r{q}" else s!"r{q}.trans h.hreg{j}"
        | none => "sorryNoReg"
      else if n.startsWith "hbn_" then
        let parts := (n.drop 4).toString.splitOn "_"
        let a := parts[0]!.toNat!; let len := parts[1]!.toNat!
        if (List.range len).any (fun q => w.contains (a + q)) then
          match info.symMem.findIdx? (·.1 == a) with
          | some q => s!"s{q}" | none => "sorryNoSym"
        else s!"(Memory.readN_of_frame hfr {a} {len} rfl).trans h.{n}"
      else if n.startsWith "hm_" then
        let parts := (n.drop 3).toString.splitOn "_"
        let c := parts[0]!.toNat!; let m := parts[1]!.toNat!
        let octs := (List.range m).map (c + ·)
        if !(octs.any w.contains) && (runAt k c).map (fun (c', m', _) => (c', m')) == some (c, m) then
          s!"(Memory.readN_of_frame hfr {c} {m} rfl).trans h.{n}"
        else
          let ps := octs.map fun b =>
            if w.contains b then
              match info.memPost.findIdx? (·.1 == b) with
              | some q => s!"m{q}" | none => "sorryNoOct"
            else match runAt k b with
              | some (c', m', j) => s!"((hfr {b} rfl).trans (Memory.read_of_readN h.hm_{c'}_{m'} {j} (by decide)))"
              | none => "sorryNoRun"
          ps.foldr (fun q acc => s!"(Memory.readN_cons {q} {acc})") s!"(Memory.readN_zero' μ' _)"
      else if n.startsWith "hw_" then
        let parts := (n.drop 3).toString.splitOn "_"
        s!"fun a h1 h2 => (hwr a).trans ({rangeArg k true parts[0]!.toNat! parts[1]!.toNat!} a h1 h2)"
      else
        let parts := (n.drop 4).toString.splitOn "_"
        s!"fun a h1 h2 => (hrd a).trans ({rangeArg k false parts[0]!.toNat! parts[1]!.toNat!} a h1 h2)"
    let argOf (nm : String) : String :=
      if nm.startsWith "hb_" then
        let b := (nm.drop 3).toString.toNat!
        match runAt k b with
        | some (c', m', j) => s!"(Memory.read_of_readN h.hm_{c'}_{m'} {j} (by decide))"
        | none => "noOctet"
      else if nm.startsWith "hw_" then
        let parts := (nm.drop 3).toString.splitOn "_"
        rangeArg k true parts[0]!.toNat! parts[1]!.toNat!
      else if nm.startsWith "hrd_" then
        let parts := (nm.drop 4).toString.splitOn "_"
        rangeArg k false parts[0]!.toNat! parts[1]!.toNat!
      else s!"h.{nm}"
    let stepArgs := " ".intercalate (ivars.flatMap (fun v => [v, s!"h{v}"]) ++ binders.map (argOf ·.1))
    sx := sx ++ s!"
/-- **Cut {k} to cut {k + 1}**: from the state `St{k}`, the steps reach `St{k + 1}`. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx) {varBinders} (h : St{k} {" ".intercalate vars} ω μ) :
    ∃ ω' μ', FreeStepsH p (refineContract env) {info.pcA} ω μ x {info.pcB} ω' μ' x ∧ St{k + 1} {" ".intercalate vars} ω' μ' := by
  obtain ⟨ω', μ', hrun, {pat rNames}, {pat mNames}, {if sNames.isEmpty then "" else pat sNames ++ ", "}hfr, hrd, hwr⟩ :=
    steps p P env ω μ x {stepArgs}
  exact ⟨ω', μ', hrun, ⟨{", ".intercalate (if proofs.isEmpty then ["trivial"] else proofs)}⟩⟩

end Services.{NS}.{name}.S{k}
"
    IO.FS.writeFile s!"{dir}/S{k}.lean" sx
  -- the chain, and its statement with the start state's facts as hypotheses
  let pre0 := fieldsOf 0
  let postN := fieldsOf nseg
  let mut ch := header "The segments composed." ++ "\n" ++ "\n".intercalate ((List.range nseg).map (s!"import Services.{NS}.{name}.S{·}")) ++ s!"

namespace Services.{NS}.{name}

open PVM JAM Services.{NS}.Code

set_option maxRecDepth 100000

/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**: the segments `S0` … `S{nseg - 1}`, composed. -/
theorem chain (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx) {varBinders} (h : St0 {" ".intercalate vars} ω μ) :
    ∃ ω' μ', FreeStepsH p (refineContract env) {infos[0]!.pcA} ω μ x {infos[nseg - 1]!.pcB} ω' μ' x ∧ St{nseg} {" ".intercalate vars} ω' μ' := by
"
  let mut cw := "ω"; let mut cm := "μ"; let mut ch' := "h"
  for k in [0:nseg] do
    ch := ch ++ s!"  obtain ⟨ω{k+1}, μ{k+1}, run{k+1}, h{k+1}⟩ := S{k}.run p P env {cw} {cm} x {varArgs} {ch'}\n"
    cw := s!"ω{k+1}"; cm := s!"μ{k+1}"; ch' := s!"h{k+1}"
  let runs := (List.range nseg).map (s!"run{· + 1}")
  let chainT := runs.foldr (fun r acc => if acc == "" then r else s!"({r}.trans {acc})") ""
  ch := ch ++ s!"  exact ⟨{cw}, {cm}, {chainT}, {ch'}⟩\n"
  -- `run`: the start state's facts as hypotheses, the end state's as a conjunction
  let concl := postN.flatMap fun (n, t) =>
    if n.startsWith "hm_" then
      let parts := (n.drop 3).toString.splitOn "_"
      let c := parts[0]!.toNat!; let m := parts[1]!.toNat!
      (List.range m).map fun j =>
        (s!"(Memory.read_of_readN hN.{n} {j} (by decide))", s!"μ'.read {c + j} = {(octAt bs[nseg]! (c + j)).getD 0}")
    else if n.startsWith "hrd_" then
      let parts := (n.drop 4).toString.splitOn "_"
      (List.range (parts[1]!.toNat! - parts[0]!.toNat!)).map fun q =>
        (s!"(hN.{n} {parts[0]!.toNat! + q} (by decide) (by decide))", s!"μ'.readable {parts[0]!.toNat! + q} = true")
    else [(s!"hN.{n}", ((t.replace "ω[" "ω'[").replace "μ." "μ'."))]
  ch := ch ++ s!"
/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**, from the facts the path reads before writing them. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
  for v in vars do ch := ch ++ s!"\n    {varBinder v}"
  for (n, t) in pre0 do ch := ch ++ s!"\n    ({n} : {t})"
  ch := ch ++ s!"\n    : ∃ ω' μ', FreeStepsH p (refineContract env) {infos[0]!.pcA} ω μ x {infos[nseg - 1]!.pcB} ω' μ' x ∧\n      " ++
    (if concl.isEmpty then "True" else " ∧ ".intercalate (concl.map (·.2))) ++ " := by"
  ch := ch ++ s!"\n  obtain ⟨ω', μ', hrun, hN⟩ :=\n    chain p P env ω μ x {varArgs} ⟨{", ".intercalate (if pre0.isEmpty then ["trivial"] else pre0.map (·.1))}⟩"
  ch := ch ++ s!"\n  exact ⟨ω', μ', hrun, {", ".intercalate (concl.map (·.1))}⟩\n\nend Services.{NS}.{name}\n"
  IO.FS.writeFile s!"Services/{NS}/{name}.lean" ch
  IO.eprintln s!"{nseg} segments; the start state needs registers {sts[0]!.1} and {pre0.length} facts"
where
  pat' (xs : List String) : String := match xs with
    | [] => "-" | [x] => x | xs => "⟨" ++ ", ".intercalate xs ++ "⟩"


def main (args0 : List String) : IO Unit := do
  -- `--service NAME` first selects the service (default witness)
  let (svc, args) : Svc × List String := match args0 with
    | "--service" :: nm :: rest => ((services.find? (fun s : Svc => s.label == nm)).getD witnessSvc, rest)
    | _ => (witnessSvc, args0)
  -- `seg0` / `chain0`: as `seg` / `chain`, for the class of empty payloads
  let mode0 := args.headD "run"
  let empty := mode0 == "seg0" || mode0 == "chain0" || mode0 == "segx0" || mode0 == "chainx0" || mode0 == "cut0"
  let mode1 := if empty then (mode0.toList.dropLast).asString else mode0
  let mode := if mode1 == "segx" then "seg" else mode1
  let n := (args.getD 1 "39").toNat!
  let bytes ← IO.FS.readBinFile svc.blob
  let some code := splitMetadata bytes.toList | return
  let h := (Blake2b.hash256 bytes).toList
  let acct : ServiceAccount := { codeHash := h, balance := 0, minAccGas := 0, minMemoGas := 0 }
  let some jb := JamBlob.parse? code | return
  let some P := Blob.parse? jb.code | return
  let Q := P.prepare
  -- `WITNESS_INPUT=c,i,s,k` replaces the base input (exploration only; generated files use the default)
  let inp := ((← IO.getEnv "WITNESS_INPUT").getD "").splitOn ","
  let (c, i, sid, y) : Nat × Nat × Nat × List UInt8 := match inp.filterMap String.toNat? with
    | [c, i, s, k] => (c, i, s, List.replicate k 255)
    | _ => if empty then svc.emptyBase else svc.base
  let pkg := mkPkg h sid (i + 1) (mkItem h sid y)
  let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat sid ++ Codec.var ⟨y.toArray⟩ ++ (Blake2b.hash256 ⟨pkg.encode.toArray⟩).toList).toArray⟩
  let some (_, ω, μ) := standardInit code a | return
  let env := mkEnv code sid i (Std.ExtTreeMap.ofList [(sid, acct)]) pkg
  let (tr, _, _, _, _) := go Q (toHostFn (RefineHost.dispatch env)) 0 1000000000 false ω μ (∅, []) #[] #[] 3000000
  let path := (tr.toList.take n).map (·.1)
  let cx : Cx := { svc, args, mode0, empty, mode, n, bytes, code, h, acct, jb, P, Q, c, i, sid, y, pkg, a, ω, μ, env, tr, path }
  match mode with
  | "calls" => mode_calls cx
  | "div" => mode_div cx
  | "cmp" => mode_cmp cx
  | "vals" => mode_vals cx
  | "valsx" => mode_valsx cx
  | "memcpy" => mode_memcpy cx
  | "post" => mode_post cx
  | "steps" => mode_steps cx
  | "reads" => mode_reads cx
  | "chain" => mode_chain cx
  | "seg" => mode_seg cx
  | "chainx" => mode_chainx cx
  | "cut" => mode_cut cx
  | _ => mode_codeRun cx
