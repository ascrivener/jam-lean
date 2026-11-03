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

/-- The traced refine of witness for arguments `c`, `i`, `sid`, payload `y`. -/
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
  deriving Inhabited

/-- Analyze steps `k0 + a … k0 + b − 1` of trace `tr`, against the other traces of the class
    (aligned at `k0`/their own join index) and their input parameters `(c, i, s, |y|)`. -/
def analyzeSeg (P : Program) (tr : Array (Nat × Regs × Memory))
    (others : Array (Array (Nat × Regs × Memory) × Nat)) (otherPs : Array (Nat × Nat × Nat × Nat))
    (k0 a b : Nat) (out : Bool) : IO SegInfo := do
  let A := k0 + a; let B := k0 + b
  let some (pcA, rA, mA) := tr[A]? | throw (IO.userError "step out of range")
  let some (pcB, rB, mB) := tr[B]? | throw (IO.userError "step out of range")
  let agreeReg (k : Nat) (j : Nat) : Bool :=
    others.all fun (t2, k2) => (t2[k2 + (k - k0)]?.map (fun x => x.2.1[j]!)) == (tr[k]?.map (fun x => x.2.1[j]!))
  let agreeMem (k : Nat) (addr : Nat) : Bool :=
    others.all fun (t2, k2) => (t2[k2 + (k - k0)]?.map (fun x => x.2.2.read addr)) == (tr[k]?.map (fun x => x.2.2.read addr))
  -- registers written in the slice
  let mut wregs : List Nat := []
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
  -- values equal to an input parameter in every run become a symbolic variable
  let baseP : Nat × Nat × Nat × Nat := (3, 0, 7, 1)
  let pick (q : Nat × Nat × Nat × Nat) (v : String) : Nat :=
    match v with | "C" => q.1 | "I" => q.2.1 | "S" => q.2.2.1 | _ => q.2.2.2
  let matchVar (valBase : Nat) (valsOther : List Nat) : Option String :=
    ["Y", "S", "C", "I"].find? fun v =>
      valBase == pick baseP v && (valsOther.zip otherPs.toList).all fun (x, q) => x == pick q v
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
  let vars := (symLoads.map (·.2.2) ++ symRegs.map (·.2) ++ symPost.map (·.2)).eraseDups
  let regPost := (List.range 13).filter fun j => !wregs.contains j || agreeReg B j
  for j in wregs do
    if !agreeReg B j then IO.eprintln s!"input-dependent register {j} at the end"
  -- `out`: also the octets of the output, ω₇ … ω₇ + ω₈ at the end (what Ψ_R returns at the halt)
  let outBytes := if out then
      (List.range rB[8]!.toNat).map (rB[7]!.toNat + ·) else []
  let livePost := ((live ++ outBytes).eraseDups.mergeSort).filter (agreeMem B)
  let pcs := (List.range (B - A)).filterMap fun j => tr[A + j]?.map (·.1)
  return { A, B, pcA, pcB, vars, regFacts := regFacts.map (fun j => (j, rA[j]!.toNat)), symRegs, symLoads, wr, rr,
           loads := goodLoads.map (fun (a, k) => (a, k, (List.range k).map fun j => (mA.read (a + j)).toNat)),
           byteFacts := ((rlist.mergeSort).filter (agreeMem A)).map (fun a => (a, (mA.read a).toNat)),
           wregs,
           regPost := regPost.map (fun j => (j, if wregs.contains j then some rB[j]!.toNat else none)),
           symPost, memPost := livePost.map (fun a => (a, (mB.read a).toNat)), pcs }

/-- Function bodies whose code facts are emitted in full, for summaries: `memcpy` and the SDK's
    `u32` decoder. -/
def fnRanges : List (Nat × Nat) := [(186740, 187150), (184570, 184870)]

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
def mode_chain (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    -- `chain PC name b₀ b₁ … bₙ`: the theorem from step b₀ to step bₙ after PC, composing the segment
    -- theorems `name0 … name(n-1)` (steps bᵢ … bᵢ₊₁ − 1; the last with `out`)
    let joinPc := n
    let name := args.getD 2 "chain"
    let bs := (args.drop 3).map String.toNat!
    let classInputs : List (Nat × Nat × Nat × List UInt8) :=
      if empty then [(5, 0, 9, []), (200, 0, 70000, []), (300, 0, 3, [])]
      else [(5, 0, 9, [200]), (3, 0, 7, List.replicate 15 255), (3, 0, 7, List.replicate 8 13), (200, 0, 70000, [12])]
    let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
      (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
    let some k0 := align tr | IO.eprintln "join not reached"; return
    let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
    let mut otherPs : Array (Nat × Nat × Nat × Nat) := #[]
    for (c2, i2, s2, y2) in classInputs do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k2 := align t2 | return
      others := others.push (t2, k2)
      otherPs := otherPs.push (c2, i2, s2, y2.length)
    let nseg := bs.length - 1
    let mut infos : Array SegInfo := #[]
    for k in [0:nseg] do
      infos := infos.push (← analyzeSeg P tr others otherPs k0 bs[k]! bs[k+1]! (k + 1 == nseg))
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
  GENERATED by `lake exe genwitnesssteps {mode0} {joinPc} {name} {" ".intercalate (bs.map toString)}` from services/witness/witness-service.jam.
  Do not edit by hand.
-/
{"\n".intercalate ((List.range nseg).map (s!"import Services.Witness.{name}{·}"))}

namespace Services.Witness.{name}

open PVM JAM Services.Witness.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**, composed from the segment theorems
    `{name}0` … `{name}{nseg - 1}`: from the facts the path reads before writing them, to the end. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
    for v in vars do
      let bound := match v with
        | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => "S < 4294967296" | "C" => "C < 65536" | _ => "I < 65536"
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
    IO.println s!"\nend Services.Witness.{name}"
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_seg (cx : Cx) : IO Unit := do
    let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
    let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
    let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
    let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
    -- `seg PC a b name`: a standalone theorem for steps a … b − 1 after the path first reaches PC,
    -- stating only the values on which every input of the class agrees
    let joinPc := n
    let a := (args.getD 2 "0").toNat!; let b := (args.getD 3 "0").toNat!; let name := args.getD 4 "seg"
    let classInputs : List (Nat × Nat × Nat × List UInt8) :=
      if empty then [(5, 0, 9, []), (200, 0, 70000, []), (300, 0, 3, [])]
      else [(5, 0, 9, [200]), (3, 0, 7, List.replicate 15 255), (3, 0, 7, List.replicate 8 13), (200, 0, 70000, [12])]
    let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
      (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
    let some k0 := align tr | IO.eprintln "join not reached"; return
    let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
    let mut otherPs : Array (Nat × Nat × Nat × Nat) := #[]
    for (c2, i2, s2, y2) in classInputs do
      let some t2 := traceFor code h acct Q c2 i2 s2 y2 | continue
      let some k2 := align t2 | IO.eprintln s!"join not reached for |y| = {y2.length}"; return
      for j in [a:b+1] do
        if (tr[k0 + j]?.map (·.1)) != (t2[k2 + j]?.map (·.1)) then
          IO.eprintln s!"paths differ at +{j} for c={c2} s={s2} |y|={y2.length}"; return
      others := others.push (t2, k2)
      otherPs := otherPs.push (c2, i2, s2, y2.length)
    let info ← analyzeSeg P tr others otherPs k0 a b (args.getD 5 "" == "out")
    let A := info.A; let B := info.B; let pcA := info.pcA; let pcB := info.pcB
    let vars := info.vars; let wr := info.wr; let rr := info.rr; let wregs := info.wregs
    let symRegs := info.symRegs; let symLoads := info.symLoads; let symPost := info.symPost
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {mode0} {joinPc} {a} {b} {name}{if args.getD 5 "" == "out" then " out" else ""}` from services/witness/witness-service.jam.
  Do not edit by hand.
-/
import Services.Witness.Code

namespace Services.Witness.{name}

open PVM JAM Services.Witness.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- **Steps {A} … {B - 1} of witness's refine** (pc {pcA} to pc {pcB}), from any state with the
    register values and memory octets they read, to a state with the values they leave. -/
theorem run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (x : RefineCtx)"
    for v in vars do
      let bound := match v with
        | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => "S < 4294967296" | "C" => "C < 65536" | _ => "I < 65536"
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
    let outW := " && ".intercalate (wr.map fun (lo, hi) => s!"!(decide ({lo} ≤ a ∧ a < {hi}))")
    IO.println s!"      (∀ a, (decide (a < 4294967296) && {outW}) = true → μ'.read a = μ.read a) ∧"
    IO.println "      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by"
    let hws := ", ".intercalate ((List.range wr.length).map (s!"hw{·}"))
    let hrs := ", ".intercalate ((List.range wr.length).map (s!"hr{·}") ++ (List.range rr.length).map (s!"hrd{·}"))
    for k in [0:wr.length] do
      IO.println s!"  have hr{k} := fun a h1 h2 => Memory.readable_of_writable (hw{k} a h1 h2)"
    let regA := ", ".intercalate (info.regFacts.map (fun (j, _) => s!"hreg{j}") ++ symRegs.map (fun (j, _) => s!"hreg{j}"))
    let loadA := ", ".intercalate (info.loads.map (fun (a, k, _) => s!"hbn_{a}_{k}") ++ info.byteFacts.map (fun (a, _) => s!"hb_{a}") ++
      symLoads.map (fun (a, k, _) => s!"hbn_{a}_{k}") ++ vars.map (s!"h{·}"))
    let simpArgs := ", ".intercalate ([regA, loadA, hws, hrs].filter (· != ""))
    IO.println "  rw [show ω = regsNF ω [] from rfl]\n  refine ⟨?ω', ?μ', ?run, ?post⟩\n  case run =>"
    for pc in info.pcs do
      match P.decode pc with
      | some (.oneImm .ecalli _) =>
        IO.println s!"    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_host [{simpArgs}, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE]"
      | _ =>
        IO.println s!"    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [{simpArgs}]"
    IO.println "    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?frame, ?rd, ?wr⟩"
    IO.println s!"    case regs =>\n      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,\n        PVM.getD_some', List.lookup_nil, Option.getD_none, and_self, and_true, true_and{if regA == "" then "" else ", " ++ regA}]"
    IO.println "    case mem =>\n      simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,\n        Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,\n        List.getElem!_cons_succ, UInt8.reduceOfNat, and_self]"
    let nW := wr.length
    let names := " ".intercalate ((List.range nW).map (s!"hx{·}"))
    IO.println s!"    case frame =>\n      intro a ha\n      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,\n        not_and, Nat.not_lt] at ha\n      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32]"
    IO.println "    case rd => intro a; simp only [PVM.Memory.readable_writeN]\n    case wr => intro a; simp only [PVM.Memory.writable_writeN]\n"
    IO.println s!"end Services.Witness.{name}"
    return

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
def mode_codeRun (cx : Cx) : IO Unit := do
  let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
  let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
  let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
  let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
  let mut facts : Array String := #[]
  let mut lemmas : Array String := #[]
  let mut seen : List Nat := []
  for (pc, regs, _) in tr.toList.take n do
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
  for (lo, hi) in fnRanges do
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
  for (pc, regs, _) in tr.toList.take n do
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
  let (hA, hB) := heapBounds code
  let hTop0 := (growHeapCore ω μ code).2.2.1
  let rwLo := rwStart jb
  let rwHi := rwStart jb + roundPage jb.rw.size + jb.heapPages * pageSize
  if mode == "code" then
    IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps code {n}` from services/witness/witness-service.jam.
  Do not edit by hand.
-/
import JAM.Theorems.GrowHeap

/-!
# Code facts of witness

The code facts the proofs about witness use: every instruction on the first {n} steps of its
refine path and every instruction of the summarized functions (`fnRanges`: `memcpy` and the
SDK's `u32` decoder), with the block starts and jump-table entries they need. `checkCode`
checks them against the blob (`lake build witnesscheck`); `HasCode p P` assumes them.
-/

namespace Services.Witness.Code

open PVM

"
    let chunks := (List.range ((factsL.length + 63) / 64)).map fun c => (factsL.drop (64 * c)).take 64
    for (c, ch) in (List.range chunks.length).zip chunks do
      IO.println (s!"/-- Code facts {64 * c}–{64 * c + ch.length - 1}. -/\ndef facts_{c} : List CodeFact := [\n  " ++ ",\n  ".intercalate ch ++ "]\n")
    IO.println ("/-- The chunks of `facts`. -/\ndef factChunks : List (List CodeFact) := [" ++ ", ".intercalate ((List.range chunks.length).map fun c => s!"facts_{c}") ++ "]\n")
    IO.println "/-- The code facts the witness proofs use. -/\ndef facts : List CodeFact := factChunks.flatten\n"
    IO.println "/-- The blob `p` deblobs to `P`, and `facts` hold of it. -/\nclass HasCode (p : outParam ByteArray) (P : Program) : Prop where\n  ok : CodeOk p facts P\n"
    IO.println ("\n\n".intercalate lemmasL.toList)
    IO.println "\nend Services.Witness.Code"
    return
  IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps run {n}` from services/witness/witness-service.jam.
  Do not edit by hand.
-/
import Services.Witness.Code

/-!
# The first {n} steps of witness's refine, proved symbolically

From Y's initial registers, with any argument length `L` in 1 … 𝖹_I and memory arbitrary except
for the facts `StartMem` lists, witness's code runs {n} gas-free steps from its entry point to the
instruction at {endPc}, through its host calls, assuming only the code facts
`Services.Witness.Code.facts`, which `checkCode` checks against the blob (`lake build
witnesscheck`). Host calls take the outcome the refine dispatcher gives (`JAM.refineContract`), for
any refine environment with the full-chain parameters (`Params.full`). Values that depend on `L`
are kept symbolic and decided by `omega`.

Ordinary steps are proved by `pvm_simp`, host calls by `pvm_host`; nothing here is evaluated by
compiled code.
-/

namespace Services.Witness.Prefix

open PVM JAM Services.Witness.Code

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
"
  IO.println ("/-- The octets the path reads from the starting memory before writing them. -/\ndef baseBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (baseBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  let inRw := fun (a : Nat) => decide (rwLo ≤ a ∧ a < rwLo + jb.rw.size)
  let inRo := fun (a : Nat) => decide (roStart ≤ a ∧ a < roStart + jb.ro.size)
  let rwBytes := baseBytes.filter (inRw ·.1)
  let roBytes := baseBytes.filter (inRo ·.1)
  IO.println ("/-- The octets of `baseBytes` in the read-write data section. -/\ndef rwBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (rwBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
  IO.println ("/-- The octets of `baseBytes` in the read-only data section. -/\ndef roBytes : List (Nat × UInt8) := [" ++ ", ".intercalate (roBytes.toList.map fun (a, b) => s!"({a}, {b})") ++ "]\n")
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

theorem prefix_run (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env)
    (henv : heapBounds env.code = ({hA}, {hB})) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (L : Nat) (hL : 0 < L ∧ L ≤ 16777216) (hμ : StartMem μ) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) {endPc} ω' μ' x' := by
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
  IO.println s!"
  rw [show initRegs L = regsNF (initRegs L) [] from rfl]
  refine ⟨?ω, ?μ, ?x, ?h⟩
  case h =>"
  for pc in path do
    match P.decode pc with
    | some (.oneImm .ecalli 1) =>
      let some (_, regsAt, memAt) := tr.find? (·.1 == pc) | continue
      let top := (growHeapCore regsAt memAt code).2.2.1
      let t := growTop (regsAt[7]!.toNat) top hB
      IO.println s!"    apply FreeStepsH.growHeap env {t} (d_{pc} (p := p) (P := P)) henv (h := {top})\n      (by heap_pages hμ.heapPages) (by decide) (by decide) (by decide)\n      (by pvm_simp [growTop, initRegs, List.set_cons_succ, List.set_cons_zero, reg])"
    | some (.oneImm .ecalli _) =>
      IO.println s!"    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_host [hw, hr, hwh, hrh, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE, initRegs, List.set_cons_succ, List.set_cons_zero, growTop, setR7, reg]"
    | _ =>
      IO.println s!"    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [hpar, Params.full_encode, hw, hr, hwh, hrh, {", ".intercalate (baseLoads.toList.map fun (a, k) => s!"hbn_{a}_{k}")}{if baseLoads.isEmpty then "" else ", "}{", ".intercalate (baseBytes.toList.map fun (a, _) => s!"hb_{a}")}{if baseBytes.isEmpty then "" else ", "}initRegs, List.set_cons_succ, List.set_cons_zero, growTop, setR7, reg]"
  IO.println s!"    exact FreeStepsH.refl

/-! ## From Y's starting state -/

/-- The section sizes of the deployed blob (GP eq. `conditions`): read-only data, read-write data,
    heap pages and stack, and the data octets the path reads (`rwBytes`, `roBytes`).
    `lake build witnesscheck` checks them. -/
def layoutOk (jb : JamBlob) : Bool :=
  jb.ro.size == {jb.ro.size} && jb.rw.size == {jb.rw.size} && jb.heapPages == {jb.heapPages} &&
    jb.stackSize == {jb.stackSize} && rwBytes.all (fun q => jb.rw.toList[q.1 - {rwLo}]! == q.2) &&
    roBytes.all (fun q => jb.ro.toList[q.1 - {roStart}]! == q.2)

/-- Every starting octet the path reads is a zero of the stack or of the heap beyond the
    read-write data, or a data octet listed in `rwBytes` or `roBytes`. -/
theorem baseBytes_cases : ∀ q ∈ baseBytes, (q.2 = 0 ∧
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
  refine ⟨fun x h1 h2 => ?_, fun x h1 h2 => ?_, fun x b hm => ?_, fun q h1 h2 => ?_⟩
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
    rcases baseBytes_cases (x, b) hm with ⟨hb, hx⟩ | ⟨hq, hx1, hx2⟩ | ⟨hq, hx1, hx2⟩
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

/-- Y's registers are `initRegs |a|`. -/
theorem initRegs_eq (a : ByteArray) : initialRegs a = initRegs a.size := by
  apply Vector.ext
  intro k hk
  simp only [initialRegs, initRegs, Vector.getElem_ofFn, stackEnd, argStart, zoneSize, inputSize]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ =>
    simp

/-- **The first {n} steps of witness's refine, from Y.** For a JAM blob with the deployed section
    sizes whose PVM code passes `checkCode` (the vendored witness blob does both: `lake build
    witnesscheck`), and any nonempty arguments Y accepts (refine's always are), the gas-free machine runs from Y's starting state
    to the instruction at {endPc}, through its host calls, in every refine environment with the full-chain parameters. -/
theorem prefix_from_Y (b a : ByteArray) (jb : JamBlob) (hjb : JamBlob.parse? b = some jb)
    (hl : layoutOk jb = true) (hc : checkCode jb.code facts = true) (p : ByteArray) (ω : Regs)
    (μ : Memory) (hY : standardInit b a = some (p, ω, μ)) (env : RefineHost.Env)
    (henv : heapBounds env.code = ({hA}, {hB})) (hpar : env.fetch.params = Params.full)
    (ha0 : 0 < a.size) :
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 ω μ ((∅, []) : RefineCtx) {endPc} ω' μ' x' := by
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

end Services.Witness.Prefix"

set_option maxHeartbeats 2000000 in
def main (args : List String) : IO Unit := do
  -- `seg0` / `chain0`: as `seg` / `chain`, for the class of empty payloads
  let mode0 := args.headD "run"
  let empty := mode0 == "seg0" || mode0 == "chain0"
  let mode := if empty then (mode0.toList.dropLast).asString else mode0
  let n := (args.getD 1 "39").toNat!
  let bytes ← IO.FS.readBinFile "services/witness/witness-service.jam"
  let some code := splitMetadata bytes.toList | return
  let h := (Blake2b.hash256 bytes).toList
  let acct : ServiceAccount := { codeHash := h, balance := 0, minAccGas := 0, minMemoGas := 0 }
  let some jb := JamBlob.parse? code | return
  let some P := Blob.parse? jb.code | return
  let Q := P.prepare
  -- `WITNESS_INPUT=c,i,s,k` replaces the base input (exploration only; generated files use the default)
  let inp := ((← IO.getEnv "WITNESS_INPUT").getD "").splitOn ","
  let (c, i, sid, y) : Nat × Nat × Nat × List UInt8 := match inp.map String.toNat! with
    | [c, i, s, k] => (c, i, s, List.replicate k 255)
    | _ => (3, 0, 7, if empty then [] else [255])
  let pkg := mkPkg h sid (i + 1) (mkItem h sid y)
  let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat sid ++ Codec.var ⟨y.toArray⟩ ++ (Blake2b.hash256 ⟨pkg.encode.toArray⟩).toList).toArray⟩
  let some (_, ω, μ) := standardInit code a | return
  let env := mkEnv code sid i (Std.ExtTreeMap.ofList [(sid, acct)]) pkg
  let (tr, _, _, _, _) := go Q (toHostFn (RefineHost.dispatch env)) 0 1000000000 false ω μ (∅, []) #[] #[] 3000000
  let path := (tr.toList.take n).map (·.1)
  let cx : Cx := { args, mode0, empty, mode, n, bytes, code, h, acct, jb, P, Q, c, i, sid, y, pkg, a, ω, μ, env, tr, path }
  match mode with
  | "calls" => mode_calls cx
  | "div" => mode_div cx
  | "cmp" => mode_cmp cx
  | "vals" => mode_vals cx
  | "reads" => mode_reads cx
  | "chain" => mode_chain cx
  | "seg" => mode_seg cx
  | _ => mode_codeRun cx
