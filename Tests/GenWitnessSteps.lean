import JAM
import PVM.Logic.FastCheck
import Services.Picoalloc.Invariant
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
  /-- More inputs whose paths' starting octets the prefix states (e.g. every hex digit of s). -/
  pathExtra : List (Nat × Nat × Nat × List UInt8) := []
  /-- Further inputs whose whole refine paths the code facts cover (`code`, `codecheck`). -/
  codeExtra : List (Nat × Nat × Nat × List UInt8) := []
  /-- `code` only: more inputs whose instructions the code facts cover, not used by the other modes,
      each run up to its first visit to `codeOnlyStop`. -/
  codeOnly : List (Nat × Nat × Nat × List UInt8) := []
  codeOnlyStop : Nat := 0
  fnRanges : List (Nat × Nat)
  /-- `codex` / `codexcheck`: more summarized functions, whose code facts go in a separate module
      (`Services/<name>/CodeX.lean`, assumed by `HasCodeX p P`) so the base facts are not regenerated. -/
  fnRangesX : List (Nat × Nat) := []
  /-- `codex` / `codexcheck`: also every jump-table entry whose target lies in these ranges (and that the
      base facts lack). A dispatch through a table in memory names no entry in its instructions. -/
  jumpRangesX : List (Nat × Nat) := []
  /-- `codea` / `codeacheck`: as `fnRangesX`, for accumulate, in a third module
      (`Services/<name>/CodeA.lean`, assumed by `HasCodeA p P`) holding what neither `Code` nor
      `CodeX` has. -/
  fnRangesA : List (Nat × Nat) := []
  /-- `codef` / `codefcheck`: as `fnRangesA`, for logging (`format!`, `core::fmt` and the `String`
      sink), in a fourth module (`Services/<name>/CodeF.lean`, assumed by `HasCodeF p P`) holding
      what none of `Code`, `CodeX` and `CodeA` has. -/
  fnRangesF : List (Nat × Nat) := []
  /-- `coder` / `codercheck`: as `fnRangesA`, for refine's body (its transform loop, handlers and output),
      in the module `CodeR` (class `HasCodeR`), holding what neither `Code` nor `CodeX` has, so that the
      proofs about refine's body import only `Code`, `CodeX` and `CodeR`. -/
  fnRangesR : List (Nat × Nat) := []
  /-- Whether `Services/<name>/Memcpy.lean` exists (`memcpy_small` at the head of `fnRanges`):
      the prefix then calls it for each `memcpy` of fewer than 16 octets instead of stepping. -/
  memcpySummary : Bool := false
  /-- `segx`: more inputs for the class (values of the widths and ranges that the base classes
      leave out, so that no value they happen to share is stated). -/
  segxExtra : List (Nat × Nat × Nat × List UInt8) := []
  /-- `segx`: facts about the variables that the steps need, each proved by `omega` from the
      variables' bounds, with the variables they use. -/
  segFacts : List (List String × String) := []
  /-- `segx0` / `cut0`: more inputs for the class of empty payloads. -/
  emptyExtra : List (Nat × Nat × Nat × List UInt8) := []
  /-- `code`: also the instructions on the run of `emptyBase`. -/
  emptyCode : Bool := false
  /-- `cut`: the bound stated for the argument length L (Y's arguments are at most 𝖹_I octets). -/
  lBound : Nat := 4294967296

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

/-- ℰ_l(x), little-endian, for the payloads below. -/
def le (l x : Nat) : List UInt8 := (List.range l).map fun k => UInt8.ofNat (x / 256 ^ k)

/-- Bootstrap payloads holding every instruction kind (tags 0 … 24, `Instruction` in
    `jam-bootstrap-service-common` 0.1.29), canonically encoded, then a 32-octet salt: the first
    with every `Option`, `bool` and choice in its second form and non-empty lists, the second in
    its first form with empty lists. Their refine runs put every instruction decoder in the code
    facts. -/
def allInstrPayloads : List (List UInt8) :=
  let h (b : Nat) : List UInt8 := List.replicate 32 (UInt8.ofNat b)
  let memo := List.replicate 128 9
  let q := (List.range 80).flatMap fun k => h k
  let a : List (List UInt8) := [
    [0] ++ h 1 ++ le 8 10 ++ le 8 11 ++ le 8 12 ++ le 8 13 ++ memo ++ [1, 3, 97, 98, 99] ++ le 8 14 ++ [1] ++ le 4 15,
    [1] ++ h 2 ++ le 8 20 ++ le 8 21,
    [2] ++ le 4 30 ++ le 8 31 ++ le 8 32 ++ memo,
    [3] ++ le 4 40,
    [4] ++ le 4 50 ++ h 3,
    [5, 2, 2, 1, 2, 0],
    [6] ++ h 4 ++ le 8 60,
    [7] ++ h 5 ++ le 8 70,
    [8] ++ le 4 80 ++ h 6 ++ [0],
    [9, 0],
    [10, 2, 1, 7, 0],
    [11] ++ le 4 1 ++ le 4 2 ++ le 4 3 ++ le 4 4 ++ [1] ++ le 4 5 ++ le 8 6,
    [12] ++ le 2 1 ++ q ++ le 4 7,
    [13, 1] ++ List.replicate 336 8,
    [14] ++ h 7,
    [15],
    [16],
    [17] ++ le 4 90 ++ [1, 2, 5, 6],
    [18, 1, 2, 3, 4],
    [19, 2, 1, 5, 0],
    [20] ++ le 8 3,
    [21] ++ le 8 42 ++ [2],
    [22, 0, 1] ++ h 8,
    [23],
    [24] ++ le 2 2 ++ [1] ++ h 9 ++ le 4 8]
  let b : List (List UInt8) := [
    [0] ++ h 1 ++ le 8 10 ++ le 8 11 ++ le 8 12 ++ le 8 13 ++ memo ++ [0] ++ le 8 14 ++ [0],
    [5, 0],
    [8] ++ le 4 80 ++ h 6 ++ [1],
    [10, 0],
    [11] ++ le 4 1 ++ le 4 2 ++ le 4 3 ++ le 4 4 ++ [0],
    [13, 0],
    [17] ++ le 4 90 ++ [0] ++ h 10,
    [18, 0],
    [19, 0],
    [22, 1],
    [24] ++ le 2 2 ++ [0] ++ le 4 8,
    [9, 1] ++ le 8 0 ++ le 8 4]
  [[UInt8.ofNat a.length] ++ a.flatten ++ h 0, [UInt8.ofNat b.length] ++ b.flatten ++ h 0]

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
  -- the last range: `Instruction::decode` from its tag dispatch on, error exits included
  fnRanges := [(68729, 69139), (31894, 32166), (58434, 58509), (32166, 32412), (40494, 40852), (41177, 44241),
    (20626, 22145)]
  -- `Vec`/`Option` decoding: the allocator's growth paths (`finish_grow`'s realloc branch,
  -- 33037–33122), the decoders' loops and their callees
  -- and refine's output encoding: `Instruction::encode_to`'s per-variant arms and their shared tails (17905–20398), the
  -- element loop and its dispatch (30073–30286), the length prefix (30977–31362) and
  -- `Vec<u8>::extend_from_slice` (58508–58615)
  fnRangesX := [(8, 482), (907, 2200), (2727, 3716), (23303, 25588), (32727, 33152), (35293, 36170),
    (50078, 50409), (70133, 70239), (17905, 20398), (30073, 30286), (30977, 31362), (58508, 58615)]
  -- `Instruction::encode_to` dispatches through its table at 67376 to the arms' jump-table entries
  jumpRangesX := [(17905, 20398)]
  -- refine's body, from its prologue (4568) to its return (6373), for `coder`, with what its handlers
  -- call that neither `Code` nor `CodeX` has: `drop_in_place::<Instruction>` (4046), `Import`'s
  -- collect loop (30766), the SDK's import-segment `fetch` (44677) and `foreign_historical_lookup` (49015)
  fnRangesR := [(4046, 6378), (30766, 30977), (44677, 44916), (49015, 49201)]
  -- accumulate (`Services/Bootstrap/Acc/README.md`, tier A): the entry 6378 … 15368, the inputs fetch
  -- and `AccumulateItem` decode, `BootstrapWorkOutput::decode`, the ring and results helpers, the
  -- storage wrappers and the allocator's remaining paths
  fnRangesA := [(5, 8), (550, 562), (638, 639), (758, 824), (904, 907), (2200, 2727), (3820, 4565), (6378, 15369),
    (22145, 22839), (22915, 22934), (23097, 23120), (23227, 23246), (25588, 26397), (28864, 29176),
    (30285, 31894), (32414, 32727), (33214, 34636), (34637, 35072), (36170, 36529), (38832, 38857),
    (39388, 39411), (39634, 40215), (40215, 40494), (40852, 41176), (44494, 44677), (44916, 45976),
    (46069, 46299), (46300, 47561), (47662, 48251), (48252, 48341), (48341, 49015), (49201, 49237), (49237, 49541),
    (49541, 49563), (49563, 49994), (55989, 56119), (58251, 58433), (58578, 58598)]
  -- logging (`Services/Bootstrap/Fmt/`): `alloc::fmt::format` (59375), `core::fmt` and the `String`
  -- sink, accumulate's tier C, and every function on refine's level-3 `Debug` line (6159 → 59375)
  fnRangesF := [(15369, 15435), (15949, 15977), (16544, 16572), (16726, 16754), (16908, 17351),
    (17465, 17696), (26397, 27570), (27601, 28165), (28197, 28347), (28378, 28737), (28739, 28864),
    (29675, 29975), (33152, 33211), (36529, 37156), (37158, 37312), (37352, 38704), (49995, 50076),
    (50830, 54577), (54744, 55968), (56340, 58251), (58615, 58878), (59375, 66380), (66488, 70131)]
  pathExtra := [(3, 0, 0x01234567, []), (3, 0, 0x89abcdef, [])]
  codeExtra := [(3, 0, 7, [2, 15, 15] ++ List.replicate 32 0)]
  codeOnly := allInstrPayloads.map fun y => (3, 0, 7, y)
  -- up to the end of `Instructions::decode`'s element loop
  codeOnlyStop := 562
  memcpySummary := true
  emptyCode := true
  lBound := 16777217

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

/-- As `go`, for an accumulate run (Ψ_A's context 𝕃²). -/
def goA (Q : Prepared) (f : HostFn AccCtx) (i : Nat) (gas : UInt64) (ch : Bool)
    (ω : Regs) (μ : Memory) (x : AccCtx) (acc : Array (Nat × Regs × Memory)) :
    Nat → Array (Nat × Regs × Memory)
  | 0 => acc
  | n + 1 =>
    if !(Q.valid && Q.prog.vInst i) then acc else
    let r := Q.step i gas ch ω μ
    let acc := acc.push (i, ω, μ)
    match r.status with
    | .cont => goA Q f r.pc r.gas r.charged r.regs r.mem x acc n
    | .host h =>
      let y := f h.toNat r.gas r.regs r.mem x
      match y.status with
      | .cont => goA Q f (Q.prog.next i) y.gas r.charged y.regs y.mem y.ctx acc n
      | _ => acc
    | _ => acc

/-- The traced accumulate of a service (`WITNESS_ACC=1`) for slot `t`, service id `s` and `n`
    inputs (each an incoming transfer of 5 with a zero memo), from instruction 5 with arguments
    ℰ(t, s, n), under Ψ_A's handler (`accHostFn`, `Params.full`). Inputs are passed in the refine
    shape (t, n, s, []). -/
def traceForAcc (code : ByteArray) (h : List UInt8) (Q : Prepared) (t n s : Nat) :
    Option (Array (Nat × Regs × Memory)) := do
  let acct0 : ServiceAccount := { codeHash := h, balance := 1000000000, minAccGas := 0, minMemoGas := 0 }
  let st : PartialState := { accounts := Std.ExtTreeMap.ofList [(s, acct0)], staging := [], authQueue := [], manager := 0, assigners := [], delegator := 0, registrar := 0, alwaysAcc := ∅ }
  let xfer : DeferredTransfer := { source := 9, dest := s, amount := 5, memo := ⟨(List.replicate 128 0).toArray⟩, gas := 1000000 }
  let inputs : List AccumulateInput := List.replicate n (.transfer xfer)
  let env : AccEnv := { params := .full, slot := t, entropy := List.replicate 32 0, inputs, code := code }
  let x := initImplications st s t (List.replicate 32 0)
  let a : ByteArray := ⟨(Codec.nat t ++ Codec.nat s ++ Codec.nat n).toArray⟩
  let (_, ω, μ) ← standardInit code a
  return goA Q (accHostFn env) 5 1000000000 false ω μ (x, x) #[] 300000

/-- Maximal runs of consecutive naturals in a sorted list, as [lo, hi). -/
def ranges (xs : List Nat) : List (Nat × Nat) :=
  xs.foldl (fun acc x => match acc with
    | (lo, hi) :: rest => if x == hi then (lo, hi + 1) :: rest else (x, x + 1) :: acc
    | [] => [(x, x + 1)]) [] |>.reverse

/-- The symbolic variables a class of inputs offers: `ext` (`segx`) adds the payload's first
    octet T and the reader position Q after the argument header. -/
def varNames (ext : Bool) (baseP : Nat × Nat × Nat × List UInt8) (acc : Bool := false) : List String :=
  if acc then ["TS", "S", "NI", "LA"]
  else if ext then (if baseP.2.2.2.isEmpty then ["Y", "S", "C", "I", "L", "Q"] else ["Y", "S", "C", "I", "L", "T", "Q"])
  else ["Y", "S", "C", "I", "L"]

/-- A variable's value for input `q = (c, i, s, y)`. -/
def pickVar (q : Nat × Nat × Nat × List UInt8) (v : String) : Nat :=
  let header := (Codec.nat q.1).length + (Codec.nat q.2.1).length + (Codec.nat q.2.2.1).length + (Codec.nat q.2.2.2.length).length
  match v with
  | "C" => q.1 | "I" => q.2.1 | "S" => q.2.2.1
  -- accumulate (`WITNESS_ACC=1`): the slot t and the input count n, in the refine shape (t, n, s, [])
  | "TS" => q.1 | "NI" => q.2.1
  | "LA" => (Codec.nat q.1).length + (Codec.nat q.2.2.1).length + (Codec.nat q.2.1).length
  | "L" => header + q.2.2.2.length + 32
  | "T" => (q.2.2.2.headD 0).toNat
  | "Q" => 2 ^ 32 - 2 ^ 16 - 2 ^ 24 + header
  | _ => q.2.2.2.length

/-- A value that equals an input parameter (`ext`: or a constant plus one or two of them) in every
    run of the class `allQ` (the base input first), as a Lean expression over the variables. -/
def matchVarG (ext : Bool) (names : List String) (allQ : List (Nat × Nat × Nat × List UInt8))
    (valBase : Nat) (valsOther : List Nat) (sx : Bool := false) (digits : Bool := false) : Option String := Id.run do
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
  -- `digits` (wild cuts): a variable's hex digits shifted away, v / 16^k, and its low digits v mod 16^k
  if digits then
    for v in names do
      for k in [1:9] do
        if let some 0 := fits (fun q => (pickVar q v / 16 ^ k : Int)) then return some s!"({v} / {16 ^ k})"
        if let some 0 := fits (fun q => (pickVar q v % 16 ^ k : Int)) then return some s!"({v} % {16 ^ k})"
  -- `sx` (`cut`): a variable sign-extended from 32 bits, 𝒳₄ (a 32-bit operation's result)
  if sx then
    for v in names do
      if let some 0 := fits (fun q => (PVM.Num.sext 4 (pickVar q v) : Int)) then return some s!"({v} + {v} / 2147483648 * 18446744069414584320)"
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
  symMem : List (Nat × Nat × String) := []
  deriving Inhabited

/-- Analyze steps `k0 + a … k0 + b − 1` of trace `tr`, against the other traces of the class
    (aligned at `k0`/their own join index) and their input parameters `(c, i, s, |y|)`. -/
def analyzeSeg (P : Program) (tr : Array (Nat × Regs × Memory))
    (others : Array (Array (Nat × Regs × Memory) × Nat)) (otherPs : Array (Nat × Nat × Nat × List UInt8))
    (k0 a b : Nat) (out : Bool) (baseP : Nat × Nat × Nat × List UInt8 := (3, 0, 7, [255]))
    (ext : Bool := false) (extra : List Nat := []) (staticW : List Nat := []) (cutMode : Bool := false) (allWords : Bool := false)
    (half : Bool := false) (wantS : List (Nat × Nat × String) := []) (acc : Bool := false) :
    IO SegInfo := do
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
    -- a read at an input-dependent address (a table indexed by an input): the hull of the class's
    -- addresses, so the readability fact covers every input's
    if let some r0 := m.reads.head? then
      let n := m.reads.length
      let addrs := others.toList.filterMap fun (t2, k2) => do
        let (pc2, regs2, mem2) ← t2[k2 + (k - k0)]?
        let ins2 ← P.decode pc2
        let m2 := P.exec pc2 ins2 regs2 mem2
        let r2 ← m2.reads.head?
        pure (r2 % 2 ^ 32)
      let a0 := r0 % 2 ^ 32
      if addrs.any (· != a0) then
        let lo := (a0 :: addrs).foldl min a0
        let hi := (a0 :: addrs).foldl max a0 + n
        for b in [lo:hi] do
          if !written.contains b && !rlist.contains b then rlist := b :: rlist
    for w in m.writes do
      let a := w % 2 ^ 32
      if !written.contains a then wlist := a :: wlist
      written := written.insert a
    -- `cut`: a `fetch` writes at most ω₉ octets at ω₇
    if cutMode then
      if let .oneImm .ecalli 2 := ins then
        for j in [0:regs[9]!.toNat] do
          let a := (regs[7]!.toNat + j) % 2 ^ 32
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
  let names := varNames ext baseP acc
  let allQ := baseP :: otherPs.toList
  let matchVar (valBase : Nat) (valsOther : List Nat) : Option String :=
    matchVarG ext names allQ valBase valsOther cutMode half
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
  let mut symMem : List (Nat × Nat × String) := []
  if ext then
    -- 8-octet words, and the 4-octet halves of those that hold no symbolic value whole (a `u32`)
    for n in (if half then [8, 4] else [8]) do
      let words := (((if allWords then wlist else live).map (fun a => a - a % n)).eraseDups.mergeSort).filter fun a =>
        (List.range n).all fun j => written.contains (a + j)
      for a in words do
        if n == 4 && symMem.any (fun (c, m, _) => c ≤ a && a < c + m) then continue
        if !((List.range n).all fun j => agreeMem B (a + j)) then
          let vb := Num.decodeLE (mB.readN a n)
          let vo := (others.toList).map fun (t2, k2) =>
            (t2[k2 + (B - k0)]?.map (fun x => Num.decodeLE (x.2.2.readN a n))).getD 0
          if let some e := matchVar vb vo then symMem := (a, n, e) :: symMem
  -- `out`: an input-dependent output octet, as an expression (e.g. a `u16` index's I % 256, I / 256)
  if ext && out then
    let dep := outBytes.filter fun b => !agreeMem B b && !(symMem.any fun (c, m, _) => c ≤ b && b < c + m)
    for a in dep do
      let n := 1
      do
        let vb := Num.decodeLE (mB.readN a n)
        let vo := (others.toList).map fun (t2, k2) =>
          (t2[k2 + (B - k0)]?.map (fun x => Num.decodeLE (x.2.2.readN a n))).getD 0
        match matchVar vb vo with
        | some v => symMem := (a, n, v) :: symMem
        | none => IO.eprintln s!"input-dependent output octets at {a} ({n})"
  -- words a later cut states symbolically (`wantS`) that this segment writes
  if ext then
    for (a, n, _) in wantS do
      if (List.range n).any (fun q => written.contains (a + q)) && !(symMem.any fun (c, m, _) => c == a && m == n) then
        let vb := Num.decodeLE (mB.readN a n)
        let vo := (others.toList).map fun (t2, k2) =>
          (t2[k2 + (B - k0)]?.map (fun x => Num.decodeLE (x.2.2.readN a n))).getD 0
        if let some e := matchVar vb vo then symMem := (a, n, e) :: symMem
  let inSym (b : Nat) : Bool := symMem.any fun (a, n, _) => a ≤ b && b < a + n
  -- `ext`: an octet of a word with an input-dependent written octet is not stated on its own
  let mixed (b : Nat) : Bool := ext && (List.range 8).any fun j =>
    let c := b - b % 8 + j
    written.contains c && !agreeMem B c
  let livePost := ((live ++ outBytes ++ extra.filter written.contains).eraseDups.mergeSort).filter fun b =>
    agreeMem B b && (!inSym b || extra.contains b)
  let vars := (vars0 ++ symMem.flatMap (fun (_, _, e) =>
    ((e.replace "(" "").replace ")" "" |>.splitOn " ").filter names.contains)).eraseDups
  let pcs := (List.range (B - A)).filterMap fun j => tr[A + j]?.map (·.1)
  return { A, B, pcA, pcB, vars, regFacts := regFacts.map (fun j => (j, rA[j]!.toNat)), symRegs, symLoads, wr, rr,
           loads := goodLoads.map (fun (a, k) => (a, k, (List.range k).map fun j => (mA.read (a + j)).toNat)),
           byteFacts := ((rlist.mergeSort).filter (fun a => agreeMem A a &&
             !(cutMode && symLoads.any fun (c, k, _) => c ≤ a && a < c + k))).map (fun a => (a, (mA.read a).toNat)),
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
  /-- The bound stated on S (`WITNESS_SBOUND=lo,hi`: lo ≤ S < hi), for a class of s by hex digits. -/
  sBound : String := "S < 4294967296"
  /-- Extra simp arguments for every generated step (`WITNESS_SIMP`). -/
  extraSimp : List String := []
  /-- `WITNESS_WILD=1`: a cut leaves unstated the live values that differ across the class and match
      no expression (data the rest only moves, such as formatted digits); a step that needs one for
      control or an address makes its proof fail. -/
  wild : Bool := false
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
  /-- `WITNESS_ACC=1`: the traced run is the service's accumulate (`traceForAcc`), and `cut` states
      its segments under `accContract` with the variables TS (slot), S (service id), NI (inputs). -/
  acc : Bool := false
  /-- The traces of the class: `traceFor`, or `traceForAcc` for accumulate. -/
  traceF : Nat → Nat → Nat → List UInt8 → Option (Array (Nat × Regs × Memory)) := fun _ _ _ _ => none
  /-- `WITNESS_VBOUND=V:lo,hi;…`: the bounds stated on further variables, as `sBound` for S. -/
  vBounds : List (String × String) := []

/-- `allocck`: the picoalloc model (`Services/Picoalloc/Model.lean`) against the binary. For each
    traced input, at every call of the allocator's entry points (`alloc` 40494, `dealloc` 40613,
    `realloc` 40701), the model runs from the state the memory holds at the call and is compared
    with the memory at the return: the result, the metadata and every chunk header from the base up. -/
def allocState (μ : Memory) : Picoalloc.State :=
  let A := 196792
  let rd (a n : Nat) : Nat := Num.decodeLE (μ.readN a n)
  { allocated := rd (A + 10048) 4, base := rd (A + 9728) 8, primary := rd (A + 10040) 8,
    secondary := fun p => rd (A + 9736 + 8 * p) 8, heads := fun b => rd (A + 4 * b) 4,
    hdr := fun a => ⟨rd a 4, rd (a + 4) 4, rd (a + 8) 4, rd (a + 12) 4⟩ }

def allocDiff (s t : Picoalloc.State) : List String := Id.run do
  let mut d : List String := []
  if s.allocated != t.allocated then d := s!"allocated {s.allocated} vs {t.allocated}" :: d
  if s.base != t.base then d := s!"base {s.base} vs {t.base}" :: d
  if s.primary % 2 ^ 64 != t.primary % 2 ^ 64 then d := s!"primary {s.primary} vs {t.primary}" :: d
  for p in [0:38] do
    if s.secondary p % 2 ^ 64 != t.secondary p % 2 ^ 64 then d := s!"secondary {p}: {s.secondary p} vs {t.secondary p}" :: d
  for b in [0:2432] do
    if s.heads b != t.heads b then d := s!"head {b}: {s.heads b} vs {t.heads b}" :: d
  -- the chunk chain from the base, up to the allocated space
  let mut c := t.base
  for _ in [0:100000] do
    if t.base == 0 || c ≥ t.base + 32 * t.allocated then break
    let hs := s.hdr c; let ht := t.hdr c
    if hs.prev != ht.prev || hs.size != ht.size then d := s!"hdr {c}: {repr hs} vs {repr ht}" :: d
    else if !Picoalloc.wordUsed ht.size && (hs.next != ht.next || hs.prevL != ht.prevL) then
      d := s!"free hdr {c}: {repr hs} vs {repr ht}" :: d
    let sz := Picoalloc.wordSize ht.size
    if sz == 0 then d := s!"zero-size chunk at {c}" :: d; break
    c := c + 32 * sz
  return d.reverse


/-- `WF`, computably, for testing it on traced states: the violations found. -/
def listWalk (s : Picoalloc.State) (a : Nat) : Nat → List Nat
  | 0 => []
  | f + 1 => if a = 0 then [] else a :: listWalk s (s.hdr a).next f

def wfCheck (s : Picoalloc.State) : List String := Id.run do
  let mut d : List String := []
  if s.base == 0 then return ["uninitialized"]
  if s.base % 32 != 0 then d := "base misaligned" :: d
  let cs := Picoalloc.walk s s.base s.top 200000
  -- tiles
  let mut a := s.base
  for c in cs do
    if c.addr != a then d := s!"gap at {a}" :: d
    if c.size == 0 then d := s!"empty chunk at {c.addr}" :: d
    a := c.addr + 32 * c.size
  if a != s.top then d := s!"chunks end at {a}, not {s.top}" :: d
  -- coalesced, prev
  for (c, e) in cs.zip (cs.drop 1) do
    if !c.used && !e.used then d := s!"adjacent free {c.addr} {e.addr}" :: d
    if (s.hdr e.addr).prev != c.size then d := s!"prev at {e.addr}: {(s.hdr e.addr).prev} vs {c.size}" :: d
  -- lists and bitmap
  for b in [0:Picoalloc.binCount] do
    let l := listWalk s (s.heads b) (cs.length + 1)
    if l.length > cs.length then d := s!"bin {b}: list does not end" :: d
    if l.eraseDups.length != l.length then d := s!"bin {b}: repeats" :: d
    let want := (cs.filter fun c => !c.used && Picoalloc.binDown c.size == b).map (·.addr)
    if l.length != want.length || !(want.all l.contains) then d := s!"bin {b}: list {l} vs free {want}" :: d
    if s.heads b != 0 && (s.hdr (s.heads b)).prevL != 0 then d := s!"bin {b}: head prevL" :: d
    for x in l do
      let nx := (s.hdr x).next
      if nx != 0 && (s.hdr nx).prevL != x then d := s!"bin {b}: back link at {nx}" :: d
    if ((s.secondary (b / 64)).testBit (b % 64)) != (s.heads b != 0) then d := s!"bit {b}" :: d
  for p in [0:38] do
    if s.primary.testBit p != (s.secondary p % 2 ^ 64 != 0) then d := s!"primary bit {p}" :: d
  if s.primary ≥ 2 ^ 38 then d := "primary has bits past 38" :: d
  for p in [0:38] do
    if s.secondary p ≥ 2 ^ 64 then d := s!"secondary {p} too wide" :: d
  -- space
  for c in cs do
    if c.used && c.addr + 32 * c.size > s.base + 32 * s.allocated then d := s!"used chunk {c.addr} past space" :: d
    if c.addr + 32 > s.base + 32 * s.allocated then d := s!"header {c.addr} past space" :: d
  return d.reverse

def mode_allocck (cx : Cx) : IO Unit := do
  let grow : Picoalloc.Grow := fun _ _ => true
  let salt := List.replicate 32 (0 : UInt8)
  let inputs : List (Nat × Nat × Nat × List UInt8) :=
    [cx.svc.base, cx.svc.emptyBase] ++ ((List.range 12).map fun n =>
      (3, 0, 7, (n.toUInt8 :: List.replicate n 15) ++ salt)) ++
    [(3, 0, 7, ([3, 3, 1, 2, 3, 4, 15, 15] : List UInt8) ++ salt)]
  let mut calls := 0
  let mut bad := 0
  for (c, i, sid, y) in inputs do
    let some tr := traceFor cx.code cx.h cx.acct cx.Q c i sid y | continue
    let arr := tr
    for k in [0:arr.size] do
      let some (pc, ω, μ) := arr[k]? | continue
      if pc != 40494 && pc != 40613 && pc != 40701 then continue
      -- the matching return: the first step at the caller's return address with ω₁ restored
      let ret := (ω.get 0).toNat; let sp := (ω.get 1).toNat
      let target := cx.P.jumpTable.getD (ret / 2 - 1) 0
      let some kr := (List.range (arr.size - k)).find? (fun j => j > 0 &&
          (match arr[k + j]? with
           | some (pc2, ω2, _) => pc2 == target && (ω2.get 1).toNat == sp
           | none => false))
        | IO.println s!"{pc} at {k}: no return found"; continue
      let some (_, ω', μ') := arr[k + kr]? | continue
      let s0 := allocState μ
      let after := allocState μ'
      let r7 := (ω.get 7).toNat; let r8 := (ω.get 8).toNat; let r9 := (ω.get 9).toNat; let r10 := (ω.get 10).toNat
      let units (b : Nat) : Nat := (b + 31) / 32
      let heapBase := 207008 - 32 -- refined below from the first initialisation
      let (res, model) : Option Nat × Option Picoalloc.State :=
        if pc == 40494 then
          match Picoalloc.alloc grow (if s0.base == 0 then after.base else s0.base) (units r8) (units r7) s0 with
          | some (q, s') => (some q, some s')
          | none => (none, none)
        else if pc == 40613 then (none, some (Picoalloc.free s0 r7))
        else
          match Picoalloc.realloc grow s0.base s0 r7 (units r9) (units r10) with
          | some (q, s', _) => (some q, some s')
          | none => (none, none)
      let _ := heapBase
      calls := calls + 1
      if (← IO.getEnv "ALLOCCK_V") == some "1" then
        IO.println s!"{pc} k={k} r7={r7} r8={r8} r9={r9} r10={r10} -> {(ω'.get 7).toNat}; changed={!(allocDiff s0 after).isEmpty}"
      let got := (ω'.get 7).toNat
      let rdiff := match res with
        | some q => if q != got then [s!"result {q} vs {got}"] else []
        | none => if pc == 40613 then [] else [s!"model failed, binary returned {got}"]
      let w0 := if s0.base == 0 then [] else wfCheck s0
      let w1 := wfCheck after
      let d := rdiff ++ (match model with | some m => allocDiff m after | none => []) ++
        (w0.map ("WF before: " ++ ·)) ++ (w1.map ("WF after: " ++ ·))
      if !d.isEmpty then
        bad := bad + 1
        IO.println s!"MISMATCH {pc} at step {k} (r7={r7} r8={r8} r9={r9} r10={r10}) input |y|={y.length}: {d.take 6}"
  IO.println s!"{calls} allocator calls checked, {bad} mismatches"

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
    IO.println s!"    : ∃ ω' μ', FreeStepsH p (refineContract env) {pcA} ω μ x {pcB} ω' μ' x {B - A} ∧"
    let regC := info.regPost.map (fun (j, v) =>
      match v with | some v => s!"ω'[{j}] = UInt64.ofNat {v}" | none => s!"ω'[{j}] = ω[{j}]") ++
      symPost.map fun (j, v) => s!"ω'[{j}] = UInt64.ofNat {v}"
    IO.println ("      (" ++ " ∧ ".intercalate regC ++ ") ∧")
    let memC := info.memPost.map fun (a, v) => s!"μ'.read {a} = {v}"
    IO.println ("      (" ++ (if memC.isEmpty then "True" else " ∧ ".intercalate memC) ++ ") ∧")
    if !info.symMem.isEmpty then
      IO.println ("      (" ++ " ∧ ".intercalate (info.symMem.map fun (a, n, e) => s!"μ'.readN {a} {n} = Num.encodeLE {n} {e}") ++ ") ∧")
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
  -- on a cut chain (`run … cut=NAME`), what `fetch` writes counts as written, as in the chain
  let cutM := cx.args.any (·.startsWith "cut=")
  return (← analyzeSeg cx.P cx.tr others otherPs 0 0 cx.n false (cx.c, cx.i, cx.sid, cx.y) (cutMode := cutM), others, otherPs)

set_option linter.unusedVariables false in
/-! ## Blobs as numbers (`blob`, `codecheck`) -/

/-- `0x…`. -/
def hexNat (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- The octets in chunks of 1024, each as a number, least significant first. -/
def chunkNats (b : ByteArray) : List Nat := (List.range ((b.size + 1023) / 1024)).map fun k =>
  Num.decodeLE (b.extract (1024 * k) (1024 * k + 1024)).toList

/-- The octets as one number, least significant first (`PVM.NatBlob`). -/
def natOfBytes (b : ByteArray) : Nat :=
  (chunkNats b).zipIdx.foldl (fun acc (c, k) => acc + (c <<< (8192 * k))) 0

/-- `blob`: `Services/<name>/Blob.lean`, the service's code preimage as a number. -/
def mode_blob (cx : Cx) : IO Unit := do
  let b := cx.bytes
  let terms := (chunkNats b).map hexNat
  IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {cx.svc.flag}blob` from {cx.svc.blob}.
  Do not edit by hand.
-/
import JAM.Theorems.NatBlob

/-!
# The {cx.svc.label} service's code preimage

`preimage` is the octets of `{cx.svc.blob}`, the base-256 digits of `N` (`PVM.NatBlob`),
least significant first, given as its 1024-octet `chunks`.
-/

namespace Services.{cx.svc.name}.Blob

/-- The preimage's octets in chunks of 1024, each as a number, least significant first. -/
def chunks : List Nat := [
  {",\n  ".intercalate terms}]

theorem chunks_lt : ∀ c ∈ chunks, c < 2 ^ 8192 := by decide +kernel

/-- The preimage's octets as one number, least significant first. -/
def N : Nat := PVM.NatBlob.ofChunks chunks

/-- The preimage's length in octets. -/
def size : Nat := {b.size}

/-- `{cx.svc.blob}`. -/
def preimage : List UInt8 := PVM.NatBlob.bytes N 0 size

end Services.{cx.svc.name}.Blob"

/-- Where the sections of a code preimage lie: the metadata prefix ℰ(|**m**|) at 0 (`mLen`, ending
    at `pos`), the standard program blob from `o1` (n1 octets) with section lengths `oLen`, `wLen`,
    heap pages `z`, stack `s` and PVM blob of `pLen` octets from `o2`; in that, ℰ(|**j**|) ending at
    `p1`, the jump-table width `jz`, ℰ(|**c**|) ending at `p2`, the code from `oc` and the bitmask
    from `om`. -/
structure Hdr where
  mLen : Nat
  pos : Nat
  o1 : Nat
  n1 : Nat
  oLen : Nat
  wLen : Nat
  z : Nat
  s : Nat
  pLen : Nat
  o2 : Nat
  jLen : Nat
  p1 : Nat
  jz : Nat
  cLen : Nat
  p2 : Nat
  oc : Nat
  om : Nat

def hdrOf (b : ByteArray) : Option Hdr := do
  let (mLen, pos) ← Blob.decodeNat? b 0
  let o1 := pos + mLen
  let le (o k : Nat) : Nat := Num.decodeLE (b.extract o (o + k)).toList
  let oLen := le o1 3
  let wLen := le (o1 + 3) 3
  let pLen := le (o1 + 11 + oLen + wLen) 4
  let o2 := o1 + 15 + oLen + wLen
  let pb := b.extract o2 (o2 + pLen)
  let (jLen, p1) ← Blob.decodeNat? pb 0
  let jz ← pb[p1]?.map UInt8.toNat
  let (cLen, p2) ← Blob.decodeNat? pb (p1 + 1)
  let oc := o2 + p2 + jLen * jz
  return { mLen, pos, o1, n1 := b.size - o1, oLen, wLen, z := le (o1 + 6) 2, s := le (o1 + 8) 3, pLen, o2,
           jLen, p1, jz, cLen, p2, oc, om := oc + cLen }

/-- The index a code fact is about, for sorting and windows (jump-table facts last). -/
def factKey (f : String) : Nat := match f.splitOn " " with
  | k :: v :: _ =>
    if k == ".instr" || k == ".blockStart" || k == ".block" then v.toNat!
    else if k == ".jumpTableSize" then 1000000000 else 1000000001 + v.toNat!
  | _ => 0

/-- The code facts in chunks each one kernel check can take within one refine: at most 4 facts
    about a stretch of at most 800 code indices, and each block's cost on its own. -/
def groupFacts (fs : List String) : List (List String) := Id.run do
  let mut out : Array (List String) := #[]
  let mut cur : Array String := #[]
  let mut lo := 0
  for f in fs do
    let k := factKey f
    if f.startsWith ".block " then
      if cur.size > 0 then out := out.push cur.toList; cur := #[]
      out := out.push [f]
    else
      if cur.size ≥ 3 || (cur.size > 0 && (k ≥ 1000000000) != (lo ≥ 1000000000)) ||
          (cur.size > 0 && k < 1000000000 && k > lo + 800) then
        out := out.push cur.toList; cur := #[]
      if cur.size == 0 then lo := k
      cur := cur.push f
  if cur.size > 0 then out := out.push cur.toList
  return out.toList

/-- Lean syntax for a simulation state. -/
def ppUnits (u : Units) : String := s!"⟨{u.alu}, {u.load}, {u.store}, {u.mul}, {u.div}⟩"
def ppRobState : RobState → String
  | .dec => ".dec" | .wait => ".wait" | .exe => ".exe" | .fin => ".fin" | .none => ".none"
def ppRobEntry (e : RobEntry) : String :=
  s!"⟨{ppRobState e.state}, {e.cycles}, {e.deps}, ⟨{e.regs.bits}⟩, {ppUnits e.units}⟩"
def ppSimState (x : SimState) : String :=
  let pc := match x.pc with | some i => s!"some {i}" | none => "none"
  s!"⟨{pc}, {x.cycle}, {x.decodeSlots}, {x.startSlots}, {ppUnits x.units}, [{", ".intercalate (x.rob.map ppRobEntry)}]⟩"

/-- The chunks k … k + m − 1 holding octets [lo, hi) of a blob, and the bits [lo, hi) of it. -/
def chunkRange (lo hi : Nat) : Nat × Nat := (lo / 1024, (hi + 1023) / 1024 - lo / 1024)
def bitChunkRange (lo hi : Nat) : Nat × Nat := (lo / 8192, (hi + 8191) / 8192 - lo / 8192)

def mode_codeRun (cx : Cx) : IO Unit := do
  let args := cx.args; let mode0 := cx.mode0; let empty := cx.empty; let mode := cx.mode; let n := cx.n; let bytes := cx.bytes
  let code := cx.code; let h := cx.h; let acct := cx.acct; let jb := cx.jb; let P := cx.P; let Q := cx.Q
  let c := cx.c; let i := cx.i; let sid := cx.sid; let y := cx.y; let pkg := cx.pkg; let a := cx.a
  let ω := cx.ω; let μ := cx.μ; let env := cx.env; let tr := cx.tr; let path := cx.path
  let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
  -- `codex` / `codexcheck`: as `code` / `codecheck`, for the facts of `fnRangesX` that the base facts
  -- lack, in the module `CodeX` (class `HasCodeX`), checked by `CodeXCheck.G*` and `CodeXOk`
  -- `codea` / `codeacheck`: the same for `fnRangesA`, in the module `CodeA` (class `HasCodeA`),
  -- leaving out what `Code` or `CodeX` already has
  -- `codef` / `codefcheck`: the same for `fnRangesF`, in the module `CodeF` (class `HasCodeF`),
  -- leaving out what `Code`, `CodeX` or `CodeA` already has
  let fmode := mode == "codef" || mode == "codefcheck"
  let rmode := mode == "coder" || mode == "codercheck"
  let amode := mode == "codea" || mode == "codeacheck" || fmode || rmode
  let xmode := mode == "codex" || mode == "codexcheck" || amode
  let E := if fmode then "F" else if rmode then "R" else if amode then "A" else "X"
  let rangesE := if fmode then cx.svc.fnRangesF else if rmode then cx.svc.fnRangesR else cx.svc.fnRangesA
  let mode := if mode == "codex" || mode == "codea" || mode == "codef" || mode == "coder" then "code"
    else if mode == "codexcheck" || mode == "codeacheck" || mode == "codefcheck" || mode == "codercheck" then "codecheck"
    else mode
  let CN := if xmode then s!"Code{E}" else "Code"
  let CC := if xmode then s!"Code{E}Check" else "CodeCheck"
  let HC := if xmode then s!"HasCode{E}" else "HasCode"
  let mut facts : Array String := #[]
  let mut lemmas : Array String := #[]
  let mut seen : List Nat := []
  -- `code`: the instructions on the base run's first n steps, and on the empty payload's whole run
  let (ec, ei, es, ey) := cx.svc.emptyBase
  let emptyRun : List (Nat × Regs × Memory) :=
    if (mode == "code" || mode == "codecheck") && cx.svc.emptyCode then ((traceFor code h acct Q ec ei es ey).map (·.toList)).getD [] else []
  let extraRuns : List (Nat × Regs × Memory) :=
    if mode == "code" || mode == "codecheck" then
      (cx.svc.codeExtra.flatMap fun (c2, i2, s2, y2) => ((traceFor code h acct Q c2 i2 s2 y2).map (·.toList)).getD []) ++
      cx.svc.codeOnly.flatMap fun (c2, i2, s2, y2) =>
        (((traceFor code h acct Q c2 i2 s2 y2).map (·.toList)).getD []).takeWhile (·.1 ≠ cx.svc.codeOnlyStop)
    else []
  let codePath := tr.toList.take n ++ emptyRun ++ extraRuns
  for (pc, regs, _) in codePath do
    if seen.contains pc then continue
    seen := pc :: seen
    let some ins := P.decode pc | continue
    facts := facts.push s!".instr {pc} ({leanInstr ins}) {P.next pc}"
    lemmas := lemmas.push s!"theorem d_{pc} \{p : ByteArray} \{P : Program} [h : {HC} p P] : deblob p {pc} = some P ∧ P.decode {pc} = some ({leanInstr ins}) ∧ P.next {pc} = {P.next pc} :=\n  h.ok.instr (by decide)"
    let bs (t : Nat) : Array String × Array String :=
      (#[s!".blockStart {t} {P.isBlockStart t}"],
       #[s!"@[pvm_code] theorem bs_{t} \{p : ByteArray} \{P : Program} [h : {HC} p P] : P.isBlockStart {t} = {P.isBlockStart t} := h.ok.blockStart (by decide)"])
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
  -- the basic block of every listed instruction: its start s, and e, the next block start
  let blockOf (pc : Nat) : Nat × Nat := Id.run do
    let st := P.blockStartOf pc
    let mut e := pc + 1
    while e < P.code.size && !P.isBlockStart e do e := e + 1
    return (st, e)
  for pc in seen do
    if (P.decode pc).isSome then
      let (st, e) := blockOf pc
      facts := facts.push s!".block {st} {e}"
  -- `codex` / `codea`: only the instructions of `fnRangesX` / `fnRangesA` that the facts before lack,
  -- with what they need: the instructions of `ranges` not in `seen0`, with what they need
  let extFacts (ranges : List (Nat × Nat)) (seen0 : List Nat) : Array String × List Nat := Id.run do
    let mut fx : Array String := #[]
    let mut sx : List Nat := []
    let seen := seen0
    for (lo, hi) in ranges do
      let mut pc := lo
      while pc < hi do
        if !seen.contains pc && !sx.contains pc then
          sx := pc :: sx
          if let some ins := P.decode pc then
            fx := fx.push s!".instr {pc} ({leanInstr ins}) {P.next pc}"
            let mut ts : List Nat := [P.next pc]
            match ins with
            | .oneOffset _ t | .regImmOffset _ _ _ t | .twoRegOffset _ _ _ t => if t ≥ 0 then ts := t.toNat :: ts
            | _ => pure ()
            for t in ts do fx := fx.push s!".blockStart {t} {P.isBlockStart t}"
            if let .regImmOffset .loadImmJump _ x _ := ins then
              let k := x.toNat / 2 - 1
              let t := P.jumpTable.getD k 0
              fx := fx.push s!".jumpTableSize {P.jumpTable.size}"
              fx := fx.push s!".jumpEntry {k} {t}"
              fx := fx.push s!".blockStart {t} {P.isBlockStart t}"
        pc := P.next pc
    for pc in sx do
      if (P.decode pc).isSome then
        let (st, e) := blockOf pc
        fx := fx.push s!".block {st} {e}"
    return (fx, sx)
  let mut baseFacts := facts
  if amode then
    let (fX, sX) := extFacts cx.svc.fnRangesX seen
    baseFacts := baseFacts ++ fX
    seen := seen ++ sX
  if fmode then
    let (fA, sA) := extFacts cx.svc.fnRangesA seen
    baseFacts := baseFacts ++ fA
    seen := seen ++ sA
  if xmode then
    let (fx, sx) := extFacts (if amode then rangesE else cx.svc.fnRangesX) seen
    -- `codea`: also every jump-table entry into `fnRangesA`. Accumulate also returns through
    -- addresses set by `load_imm` (then `jump`) and dispatches through tables in memory, neither of
    -- which names its entry in the instruction, so each entry whose target lies in the ranges is
    -- stated.
    -- `codex`: the entries into `jumpRangesX` that the base facts lack.
    let jr := if amode then rangesE else cx.svc.jumpRangesX
    let fx := Id.run do
      let mut fx := fx
      for k in [0:P.jumpTable.size] do
        let t := P.jumpTable.getD k 0
        if jr.any (fun (lo, hi) => lo ≤ t ∧ t < hi) && (amode || !baseFacts.contains s!".jumpEntry {k} {t}") then
          fx := fx.push s!".jumpTableSize {P.jumpTable.size}"
          fx := fx.push s!".jumpEntry {k} {t}"
          fx := fx.push s!".blockStart {t} {P.isBlockStart t}"
      return fx
    facts := fx
    seen := sx
  -- sorted by index, so each chunk of 64 reads a short stretch of the code (`codecheck`)
  let factsL := facts.toList.eraseDups.mergeSort (fun a b => factKey a ≤ factKey b)
  let idxOf (f : String) : Nat := (factsL.idxOf f)
  -- `facts` is split into chunks of 64, so each membership proof indexes two short lists
  let factGroups := groupFacts factsL
  let mut posOf : Std.HashMap String (Nat × Nat) := {}
  for (g, gi) in factGroups.zipIdx do
    for (f, fi) in g.zipIdx do posOf := posOf.insert f (gi, fi)
  -- facts = factChunks.flatten, factChunks = factGroups.flatten, 64 chunks to a group
  let memFact (k : Nat) : String :=
    let (c, j) := posOf.getD (factsL[k]!) (0, 0)
    s!"List.mem_flatten_of_mem (List.mem_flatten_of_mem (List.getElem_mem (l := factGroups) (n := {c / 64}) (by decide)) (List.getElem_mem (l := factGroup_{c / 64}) (n := {c % 64}) (by decide))) (List.getElem_mem (l := facts_{c}) (n := {j}) (by decide))"
  if mode == "codecheck" then
    let some hd := hdrOf bytes | IO.eprintln "codecheck: the blob does not parse"; return
    let o1 := hd.o1; let o2 := hd.o2; let oc := hd.oc; let mb := 8 * hd.om; let cLen := hd.cLen
    let csN := chunkNats bytes
    -- the view reading code indices [lo, hi) from the chunks that hold them
    let cvArgs (lo hi : Nat) : Nat × Nat × Nat × Nat :=
      let (kc, mc) := chunkRange (oc + lo) (oc + hi)
      let (km, mm) := bitChunkRange (mb + lo) (mb + hi)
      (kc, mc, km, mm)
    let cvS (lo hi : Nat) : String :=
      let (kc, mc, km, mm) := cvArgs lo hi
      s!"{kc} {mc} {km} {mm}"
    let cv (lo hi : Nat) : CodeView :=
      let (kc, mc, km, mm) := cvArgs lo hi
      NatBlob.cview csN oc mb cLen kc mc km mm
    let idsL := (jamHostCallIdsOf code).eraseDups.mergeSort
    -- read octets [lo, hi) of the blob from the chunks that hold them, not from N
    let rwN (lo hi : Nat) : String :=
      let (k, m) := chunkRange lo hi
      s!"simp (disch := omega) only [show N = ofChunks chunks from rfl, byte_ofChunks_window chunks chunks_lt {k} {m}, bytes_ofChunks_window chunks chunks_lt {k} {m}]"
    let (jk, jm) := chunkRange (o2 + hd.p2) (o2 + hd.p2 + hd.jLen * hd.jz)
    let mut out := ""
    out := out ++ "\n" ++ s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}codecheck {n}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.Code
import Services.{NS}.Blob
import PVM.Logic.FastCheck
import PVM.Theorems.HostIds

/-!
# {LBL}'s code facts, checked by the kernel

The code preimage `Services.{NS}.Blob.preimage` splits into its metadata and a standard program
blob (`split`), whose sections lie at the offsets its header gives (`jam`); its PVM blob parses to
`prog` (`parse`), which passes 𝔳_blob (`vBlob_ok`, as a chain of walks over the code) and every
fact of `Services.{NS}.Code.facts` (`chunk_ok_*` in `Services.{NS}.CodeCheck.G*`, a chunk of 64
facts at a time). So `checkCode_ok` (`Services.{NS}.CodeOk`): the blob passes `checkCode` for the
facts, by the kernel alone.

Every check is `decide +kernel` on arithmetic over the blob's 1024-octet chunks
(`Services.{NS}.Blob.chunks`), each reading only the chunks that hold the stretch of code it is about
(`PVM.NatBlob.cview`), and each small enough for one kernel run on chain: the walks, facts and
scans are in `Services.{NS}.CodeCheck.*`, and `Services.{NS}.CodeOk` puts them together.
-/

namespace Services.{NS}.CodeCheck

open PVM PVM.NatBlob Services.{NS}.Blob Services.{NS}.Code

theorem meta_len : Blob.decodeNat? (ba N 0 size) 0 = some ({hd.mLen}, {hd.pos}) := by
  simp only [Blob.decodeNat?, getElem?_ba, slice?_ba]
  {rwN 0 16}
  decide +kernel

/-- The code after the metadata. -/
theorem split : JAM.splitMetadata preimage = some (ba N {o1} {hd.n1}) := by
  have h := splitMetadata_bytes N 0 size meta_len (by decide)
  rw [show 0 + {hd.pos} + {hd.mLen} = {o1} from rfl, show size - {hd.pos} - {hd.mLen} = {hd.n1} from rfl] at h
  exact h

/-- The sections of the standard program blob (GP eq. `conditions`). -/
def jamBlob : JamBlob :=
  ⟨ba N {o1 + 11} {hd.oLen}, ba N {o1 + 11 + hd.oLen} {hd.wLen}, {hd.z}, {hd.s}, ba N {o2} {hd.pLen}⟩

theorem jam : JamBlob.parse? (ba N {o1} {hd.n1}) = some jamBlob :=
  jamParse?_ba N {o1} {hd.n1} (oLen := {hd.oLen}) (wLen := {hd.wLen}) (z := {hd.z}) (s := {hd.s}) (pLen := {hd.pLen})
    (by {rwN o1 (o1 + 16)}; decide +kernel) (by {rwN o1 (o1 + 16)}; decide +kernel)
    (by {rwN o1 (o1 + 16)}; decide +kernel) (by {rwN o1 (o1 + 16)}; decide +kernel)
    (by {rwN (o2 - 4) o2}; decide +kernel) (by decide)

theorem jtLen : Blob.decodeNat? (ba N {o2} {hd.pLen}) 0 = some ({hd.jLen}, {hd.p1}) := by
  simp only [Blob.decodeNat?, getElem?_ba, slice?_ba]
  {rwN o2 (o2 + 16)}
  decide +kernel

theorem codeLen : Blob.decodeNat? (ba N {o2} {hd.pLen}) {hd.p1 + 1} = some ({cLen}, {hd.p2}) := by
  simp only [Blob.decodeNat?, getElem?_ba, slice?_ba]
  {rwN o2 (o2 + 16)}
  decide +kernel

theorem jz_ok : byte N ({o2} + {hd.p1}) = {hd.jz} := by
  {rwN o2 (o2 + 16)}
  decide +kernel

/-- **j**, the dynamic jump table. -/
def jt : Array Nat :=
  ((List.range {hd.jLen}).map fun i => Num.decodeLE (bytes N ({o2} + {hd.p2} + i * {hd.jz}) {hd.jz})).toArray

/-- **j**, read from the chunks that hold it. -/
def jtW : Array Nat :=
  ((List.range {hd.jLen}).map fun i => Num.decodeLE (bytes (ofChunks ((chunks.drop {jk}).take {jm})) ({o2} + {hd.p2} + i * {hd.jz} - 1024 * {jk}) {hd.jz})).toArray

theorem jt_eq : jt = jtW := by
  unfold jt jtW
  refine congrArg List.toArray (List.map_congr_left (fun i hi => ?_))
  have := List.mem_range.1 hi
  exact congrArg Num.decodeLE (bytes_ofChunks_window chunks chunks_lt {jk} {jm} _ _ (by omega) (by omega))

/-- The program: **c**, **k** and **j** (GP §A.1). -/
def prog : Program := ⟨ba N {oc} {cLen}, bits N {mb} {cLen}, jt⟩

theorem parse : Blob.parse? (ba N {o2} {hd.pLen}) = some prog := by
  have h := parse?_ba N {o2} {hd.pLen} jtLen (by decide) jz_ok codeLen (by decide) (by decide +kernel)
  exact h

theorem prog_view : prog.view = view N {oc} {mb} {cLen} := view_eq N {oc} {mb} {cLen} jt

/-- The program's view, read from the chunks kc … kc + mc − 1 and km … km + mm − 1. -/
theorem prog_cview (kc mc km mm : Nat) : prog.view = cview chunks {oc} {mb} {cLen} kc mc km mm :=
  prog_view.trans (cview_eq chunks chunks_lt {oc} {mb} {cLen} kc mc km mm).symm

/-- The ids of every `ecalli` at an opcode position of the code. -/
def hostIds : List Nat := {idsL}
"
    out := out ++ s!"\nend Services.{NS}.CodeCheck\n"
    unless xmode do IO.FS.writeFile s!"Services/{NS}/CodeCheck.lean" ((out.drop 1).toString)
    IO.FS.createDirAll s!"Services/{NS}/{CC}"
    let modHead (what : String) : String := s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}codecheck {n}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.CodeCheck{if xmode then s!"\nimport Services.{NS}.Code{E}" else ""}

/-! # {what} -/

namespace Services.{NS}.{CC}

open PVM PVM.NatBlob Services.{NS}.Blob {if xmode then s!"Services.{NS}.CodeCheck Services.{NS}.Code{E}" else s!"Services.{NS}.Code"}
"
    let modEnd := s!"\nend Services.{NS}.{CC}\n"
    let V := s!"(view N {oc} {mb} {cLen})"
    let nest (xs : List String) (last : Option String) : String :=
      let ys := xs ++ (last.map ([·])).getD []
      match ys.reverse with
      | [] => "rfl"
      | z :: zs => zs.foldl (fun acc x => s!"({x}.trans {acc})") z
    -- no block starts in (s, e), BP indices to a theorem
    let BP := 12
    let bnoRanges (bs be : Nat) : List (Nat × Nat) :=
      (List.range ((be - bs - 1 + BP - 1) / BP)).map fun j => (bs + 1 + BP * j, min BP (be - (bs + 1 + BP * j)))
    let bnoPieces (c bs be : Nat) : String := String.join ((bnoRanges bs be).zipIdx.map fun ((a, len), j) =>
      s!"
theorem bno_{c}_{j} : ∀ k, {a} ≤ k → k < {a} + {len} → {V}.isBlockStart k = false := by
  have h : (cview chunks {oc} {mb} {cLen} {cvS (a - min a 32) (a + len + 40)}).noStartsF {a} {len} = true := by decide +kernel
  rw [cview_eq chunks chunks_lt] at h
  exact CodeView.noStartsF_sound _ (fun i => view_zeta_lt _ _ _ _ i) {a} {len} h
")
    let bnoCover (c bs be : Nat) : String :=
      let rs := bnoRanges bs be
      if rs.isEmpty then "(fun k h1 h2 => absurd h2 (by omega))"
      else
        let names := (List.range rs.length).map fun j => s!"bno_{c}_{j}"
        names.tail.foldl (fun acc x => s!"(range_cover {acc} {x})") names.head!
    let chunkPlain (c lo hi : Nat) : String := s!"
theorem chunk_{c} : facts_{c}.all (CodeFact.holdsV (cview chunks {oc} {mb} {cLen} {cvS lo hi}) jtW) = true := by
  decide +kernel

theorem chunk_ok_{c} : facts_{c}.all (·.holds prog) = true :=
  CodeFact.all_holds_of_view prog _ (prog_cview {cvS lo hi}) _ (by rw [show prog.jumpTable = jtW from jt_eq]; exact chunk_{c})
"
    -- 𝔳_blob, in walks of 60 instructions, 64 walks to a module
    let mut starts : Array Nat := #[]
    let mut pc := 0
    while pc < cLen do
      starts := starts.push pc
      pc := P.next pc
    let K := 40
    -- segments of at most K instructions and 110 code octets
    let mut segStarts : Array Nat := #[0]
    let mut si := 0
    while si < starts.size do
      let mut k := 0
      while k < K && si + k < starts.size && (k == 0 || (starts[si + k]?.getD cLen) - starts[si]! < 110) do k := k + 1
      si := si + k
      segStarts := segStarts.push si
    let nseg := segStarts.size - 1
    let WG := 64
    let nwg := (nseg + WG - 1) / WG
    let mut fuel := cLen + 1
    let mut walkGroups : Array String := #[]
    let mut imports : Array String := #[]
    for g in [0:nwg] do
      let mut ws := modHead s!"𝔳_blob of {LBL}'s code, walks {WG * g}–{min (WG * (g + 1)) nseg - 1}"
      let mut names : Array String := #[]
      let f0 := fuel
      let mut gi0 := 0
      let mut gj := 0
      for sgi in [WG * g:min (WG * (g + 1)) nseg] do
        let i0 := starts[segStarts[sgi]!]!
        let k := segStarts[sgi + 1]! - segStarts[sgi]!
        let j := starts[segStarts[sgi + 1]!]?.getD cLen
        if sgi == WG * g then gi0 := i0
        gj := j
        if (cv i0 (j + 64)).walkF k i0 != some j then IO.eprintln s!"codecheck: walk {sgi} does not reach {j}"
        ws := ws ++ s!"
theorem walk_{sgi} : {V}.vBlobAux {fuel} {i0} = {V}.vBlobAux {fuel - k} {j} := by
  have h : (cview chunks {oc} {mb} {cLen} {cvS i0 (j + 64)}).walkF {k} {i0} = some {j} := by decide +kernel
  rw [CodeView.walkF_eq _ (fun i => cview_zeta_lt chunks chunks_lt _ _ _ _ _ _ _ i), cview_eq chunks chunks_lt] at h
  exact CodeView.vBlobAux_walk _ {k} {i0} {j} {fuel} h (by decide)
"
        names := names.push s!"walk_{sgi}"
        fuel := fuel - k
      ws := ws ++ s!"
theorem walks_{g} : {V}.vBlobAux {f0} {gi0} = {V}.vBlobAux {fuel} {gj} :=
  {nest names.toList none}
"
      unless xmode do
        IO.FS.writeFile s!"Services/{NS}/CodeCheck/W{g}.lean" (ws ++ modEnd)
        imports := imports.push s!"Services.{NS}.CodeCheck.W{g}"
      walkGroups := walkGroups.push s!"walks_{g}"
    let vEnd := s!"(CodeView.vBlobAux_end _ {fuel} {cLen} (by decide) (by decide) rfl)"
    -- the facts, a chunk to a theorem, 64 chunks to a module
    let chunks := factGroups
    let FG := 64
    let nfg := (chunks.length + FG - 1) / FG
    let mut factGroupsL : Array (String × List Nat) := #[]
    for g in [0:nfg] do
      let mut gs := modHead s!"{LBL}'s code facts, chunks {FG * g}–{min (FG * (g + 1)) chunks.length - 1}"
      let cs := (List.range (min (FG * (g + 1)) chunks.length - FG * g)).map (FG * g + ·)
      for c in cs do
        let ch := chunks[c]!
        let ks := ch.filterMap fun f =>
          let k := factKey f
          if k ≥ 1000000000 then none
          else if f.startsWith ".block " then
            match f.splitOn " " with
            | _ :: a :: b :: _ => some (a.toNat!, b.toNat!)
            | _ => none
          else some (k, k)
        let (lo, hi) := match (ks.map (·.1)).min?, (ks.map (·.2)).max? with
          | some lo, some hi => (lo - min lo 32, hi + 40)
          | _, _ => (0, 1)
        let jumpish := ch.all (fun f => f.startsWith ".jumpEntry " || f.startsWith ".jumpTableSize ")
        match ch, jumpish with
        | [f], false =>
          if f.startsWith ".block " then
            -- a block's cost: 𝔛 a few transitions to a theorem, from state to state
            let (bs, be) := (ks.headD (0, 0))
            -- its terminator's static target, read from a second stretch of code
            let mut q := bs
            while P.next q < be do q := P.next q
            let tgt : Option Nat := match P.decode q with
              | some ins => (Instr.branchTarget? ins).bind fun t => if t ≥ 0 then some t.toNat else none
              | none => none
            let (kc, mc, km, mm) := cvArgs lo hi
            let (kc2, mc2) := match tgt with
              | some t => if t + 40 < lo || t ≥ hi then chunkRange (oc + t) (oc + t + 1) else (0, 0)
              | none => (0, 0)
            let V2 := NatBlob.cview2 csN oc mb cLen kc mc kc2 mc2 km mm
            let VS := s!"(cview2 chunks {oc} {mb} {cLen} {kc} {mc} {kc2} {mc2} {km} {mm})"
            let mut x := Sim.init bs
            let mut states : Array SimState := #[x]
            let mut links : Array Nat := #[]
            let mut cur := 0
            let mut budget := 0
            let mut done := false
            for _ in [0:100000] do
              match CodeView.Sim.transition V2 x with
              | some (.inl y) =>
                budget := budget + x.rob.length + 4
                cur := cur + 1
                x := y
                if budget ≥ 35 then
                  states := states.push x; links := links.push cur; cur := 0; budget := 0
              | some (.inr _) => done := true; break
              | none => break
            if !done then IO.eprintln s!"codecheck: block {bs} does not finish"
            if cur > 0 then states := states.push x; links := links.push cur
            let fuel0 := 256 * (cLen - bs + 2)
            let stName (j : Nat) : String := if j == 0 then s!"(Sim.init {bs})" else s!"bst_{c}_{j}"
            let mut bf := fuel0
            let mut lnames : Array String := #[]
            let mut fuels : Array Nat := #[]
            for j in [0:links.size] do
              fuels := fuels.push bf
              if j + 1 < states.size then
                gs := gs ++ s!"
def bst_{c}_{j + 1} : SimState := {ppSimState states[j + 1]!}
"
              gs := gs ++ s!"
theorem bsim_{c}_{j} : CodeView.Sim.run {V} {bf} {stName j} = CodeView.Sim.run {V} {bf - links[j]!} {stName (j + 1)} := by
  have h : CodeView.Sim.steps {VS} {links[j]!} {stName j} = some {stName (j + 1)} := by decide +kernel
  rw [cview2_eq chunks chunks_lt] at h
  exact CodeView.Sim.run_steps _ {links[j]!} _ _ {bf - links[j]!} h
"
              lnames := lnames.push s!"bsim_{c}_{j}"
              bf := bf - links[j]!
            fuels := fuels.push bf
            let z := stName links.size
            let zs := states[links.size]!
            -- the links 32 at a time, so no proof term nests too deep
            let mut segs : Array String := #[]
            for g in [0:(links.size + 31) / 32] do
              let a := 32 * g; let b := min (32 * (g + 1)) links.size
              gs := gs ++ s!"
theorem bseg_{c}_{g} : CodeView.Sim.run {V} {fuels[a]!} {stName a} = CodeView.Sim.run {V} {fuels[b]!} {stName b} :=
  {nest ((List.range (b - a)).map fun k => s!"bsim_{c}_{a + k}") none}
"
              segs := segs.push s!"bseg_{c}_{g}"
            lnames := segs
            gs := gs ++ s!"
theorem bend_{c} : CodeView.Sim.run {V} {bf} {z} = some {z} := by
  have h : CodeView.Sim.transition {VS} {z} = some (.inr {z}) := by decide +kernel
  rw [cview2_eq chunks chunks_lt] at h
  exact CodeView.Sim.run_final _ {z} {bf - 1} h

/-- ϱ^Δ of the block at {bs} is {max (zs.cycle - 3) 1} (GP eq. `gascostforblock`). -/
theorem bcost_{c} : {V}.blockCost {bs} ≤ stepCostCap := by
  rw [CodeView.blockCost_of_run {V} {bs} {z} {nest lnames.toList (some s!"bend_{c}")}]
  decide

theorem bstart_{c} : {V}.isBlockStart {bs} = true := by
  have h : (cview chunks {oc} {mb} {cLen} {cvS (bs - min bs 32) (bs + 40)}).isBlockStartF {bs} = true := by decide +kernel
  rw [CodeView.isBlockStartF_eq _ (fun i => cview_zeta_lt chunks chunks_lt _ _ _ _ _ _ _ i), cview_eq chunks chunks_lt] at h
  exact h
{bnoPieces c bs be}
theorem bstarts_{c} : CodeFact.blockStartsV {V} {bs} {be} = true :=
  CodeFact.blockStartsV_of _ {bs} {be} bstart_{c} {bnoCover c bs be}

theorem chunk_ok_{c} : facts_{c}.all (·.holds prog) = true := by
  simp only [facts_{c}, List.all_cons, List.all_nil, Bool.and_true, CodeFact.holds_block, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · rw [prog_view]; exact bstarts_{c}
  · rw [prog_view]; exact bcost_{c}
"
          else
            gs := gs ++ chunkPlain c lo hi
        | _, _ =>
          if jumpish then
            -- jump-table facts: each entry read directly (`getD_map_range`), not by walking **j**
            let mut names : Array String := #[]
            for (f, fi) in ch.zipIdx do
              let parts := f.splitOn " "
              if f.startsWith ".jumpEntry " then
                let k := parts[1]!; let t := parts[2]!
                gs := gs ++ s!"
theorem jtw_{c}_{fi} : jtW.getD {k} 0 = {t} := by
  rw [jtW, getD_map_range _ _ _ (by decide)]
  decide +kernel

theorem jte_{c}_{fi} : (CodeFact.jumpEntry {k} {t}).holds prog = true :=
  CodeFact.jumpEntry_holds prog {k} {t} ((congrArg (fun a : Array Nat => a.getD {k} 0) jt_eq).trans jtw_{c}_{fi} : jt.getD {k} 0 = {t})
"
              else
                gs := gs ++ s!"
theorem jte_{c}_{fi} : (CodeFact.jumpTableSize {parts[1]!}).holds prog = true :=
  CodeFact.jumpTableSize_holds prog {parts[1]!} (size_map_range _ _)
"
              names := names.push s!"jte_{c}_{fi}"
            gs := gs ++ s!"
theorem chunk_ok_{c} : facts_{c}.all (·.holds prog) = true := by
  simp only [facts_{c}, List.all_cons, List.all_nil, Bool.and_true, {", ".intercalate names.toList}]
"
          else gs := gs ++ chunkPlain c lo hi
      gs := gs ++ s!"
theorem chunks_{g} : factGroup_{g}.all (fun c => c.all (·.holds prog)) = true := by
  simp only [factGroup_{g}, List.all_cons, List.all_nil, Bool.and_true, {", ".intercalate (cs.map (s!"chunk_ok_{·}"))}]
"
      IO.FS.writeFile s!"Services/{NS}/{CC}/G{g}.lean" (gs ++ modEnd)
      imports := imports.push s!"Services.{NS}.{CC}.G{g}"
      factGroupsL := factGroupsL.push (s!"chunks_{g}", cs)
    -- the host-call ids: a scan of the code in stretches of 300 indices, 64 to a module
    let HS := 200
    let nh := (cLen + HS - 1) / HS
    let HG := 64
    let nhg := (nh + HG - 1) / HG
    let hostQ (a b : Nat) : String := s!"∀ i, {a} ≤ i → i < {b} → {V}.maskAt i = true →
    ∀ x, {V}.decode i = some (.oneImm .ecalli x) → x.toNat ∈ hostIds"
    let mut hostGroups : Array String := #[]
    for g in [0:nhg] do
      let mut hs := modHead s!"The host-call ids {LBL}'s code names, indices {HS * HG * g}–{min (HS * HG * (g + 1)) cLen - 1}"
      let mut names : Array String := #[]
      for k in [HG * g:min (HG * (g + 1)) nh] do
        let a := HS * k; let len := min HS (cLen - a)
        if !(cv a (a + len + 40)).hostScan idsL len a then IO.eprintln s!"codecheck: host scan {k} fails"
        hs := hs ++ s!"
theorem hosts_{k} : {hostQ a (a + len)} := by
  have h : (cview chunks {oc} {mb} {cLen} {cvS a (a + len + 40)}).hostScan hostIds {len} {a} = true := by decide +kernel
  rw [cview_eq chunks chunks_lt] at h
  exact CodeView.hostScan_sound _ _ _ _ h
"
        names := names.push s!"hosts_{k}"
      let ga := HS * HG * g; let gb := min (HS * HG * (g + 1)) cLen
      let cover := names.toList.tail.foldl (fun acc x => s!"(range_cover {acc} {x})") names[0]!
      hs := hs ++ s!"
theorem hostsG_{g} : {hostQ ga gb} :=
  {cover}
"
      unless xmode do
        IO.FS.writeFile s!"Services/{NS}/CodeCheck/H{g}.lean" (hs ++ modEnd)
        imports := imports.push s!"Services.{NS}.CodeCheck.H{g}"
      hostGroups := hostGroups.push s!"hostsG_{g}"
    let hcover := hostGroups.toList.tail.foldl (fun acc x => s!"(range_cover {acc} {x})") hostGroups[0]!
    if xmode then
      IO.FS.writeFile s!"Services/{NS}/Code{E}Ok.lean" (s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}code{E.toLower}check {n}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.CodeOk
" ++ String.join (imports.toList.map (s!"import {·}\n")) ++ s!"
/-!
# {LBL}'s further code facts hold of the vendored blob, by the kernel

`Services.{NS}.Code{E}Check.G*` check the facts of `Services.{NS}.Code{E}` a chunk at a time against
the program `Services.{NS}.CodeCheck` parses; with its 𝔳_blob (`CodeCheck.vBlob_ok`): `checkCode_ok`,
and so `hasCode{E}`: wherever the base facts hold, these do too.
-/

namespace Services.{NS}.Code{E}Check

open PVM PVM.NatBlob Services.{NS}.Blob Services.{NS}.Code{E}

/-- **The blob passes `checkCode` for the further code facts**, checked by the kernel. -/
theorem checkCode_ok : checkCode (ba N {o2} {hd.pLen}) facts = true :=
  checkCode_of_chunks CodeCheck.parse CodeCheck.vBlob_ok (by
    simp only [factChunks, factGroups, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      Bool.and_true, {", ".intercalate (factGroupsL.toList.map (·.1))}])

/-- The further code facts, wherever the base facts hold of the blob. -/
theorem hasCode{E} \{P : Program} (h : CodeOk (ba N {o2} {hd.pLen}) Code.facts P) :
    HasCode{E} (ba N {o2} {hd.pLen}) P :=
  HasCode{E}.of h checkCode_ok

end Services.{NS}.Code{E}Check
")
      return
    IO.FS.writeFile s!"Services/{NS}/CodeOk.lean" (s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}codecheck {n}` from {BLOB}.
  Do not edit by hand.
-/
" ++ String.join (imports.toList.map (s!"import {·}\n")) ++ s!"
/-!
# {LBL}'s code facts hold of the vendored blob, by the kernel

`Services.{NS}.CodeCheck` parses the blob; `Services.{NS}.CodeCheck.W*` walk 𝔳_blob, `G*` check
the facts a chunk at a time, and `H*` scan the host-call ids. Together: `vBlob_ok`,
`checkCode_ok` and `hostIds_ok`.
-/

namespace Services.{NS}.CodeCheck

open PVM PVM.NatBlob Services.{NS}.Blob Services.{NS}.Code

/-- 𝔳_blob(**c**, **k**, 0) (GP §A.1): the walks lead from 0 to the end of the code. -/
theorem vBlob_ok : prog.vBlob = true := by
  rw [Program.vBlob_view, prog_view, CodeView.vBlob]
  exact {nest walkGroups.toList (some vEnd)}

/-- **The blob passes `checkCode` for the code facts**, checked by the kernel. -/
theorem checkCode_ok : checkCode (ba N {o2} {hd.pLen}) facts = true :=
  checkCode_of_chunks parse vBlob_ok (by
    simp only [factChunks, factGroups, List.flatten_cons, List.flatten_nil, List.all_append, List.all_nil,
      Bool.and_true, {", ".intercalate (factGroupsL.toList.map (·.1))}])

/-- **The host-call ids the blob names** (`PVM.jamHostCallIdsOf`, GP §A.1, §A.5.2), by the kernel. -/
theorem hostIds_ok : ∀ n ∈ PVM.jamHostCallIdsOf (ba N {o1} {hd.n1}), n ∈ hostIds := by
  have hp : PVM.jamHostCallIdsOf (ba N {o1} {hd.n1}) = prog.hostCallIds := by
    rw [jamHostCallIdsOf_of jam]
    exact hostCallIdsOf_of parse
  rw [hp]
  apply prog.hostCallIds_sub
  intro i hi hm x hd
  rw [prog_view] at hm hd
  exact {hcover} i (Nat.zero_le _) (by simpa [prog] using hi) hm x hd

end Services.{NS}.CodeCheck
")
    return
  -- lemmas, regenerated from the fact strings with their indices
  let mut lemmasL : Array String := #[]
  for pc in seen.reverse do
    let some ins := P.decode pc | continue
    let fi := s!".instr {pc} ({leanInstr ins}) {P.next pc}"
    let k := idxOf fi
    let (bst, be) := blockOf pc
    let kb := idxOf s!".block {bst} {be}"
    let l := s!"theorem d_{pc} \{p : ByteArray} \{P : Program} [h : {HC} p P] : deblob p {pc} = some P ∧ P.decode {pc} = some ({leanInstr ins}) ∧ P.next {pc} = {P.next pc} ∧ P.blockCost (P.blockStartOf {pc}) ≤ stepCostCap :=\n  h.ok.instrCost (show CodeFact.instr {pc} ({leanInstr ins}) {P.next pc} ∈ facts from {memFact (k)})\n    (show CodeFact.block {bst} {be} ∈ facts from {memFact kb}) (by decide)\n\n@[pvm_code] theorem nx_{pc} \{p : ByteArray} \{P : Program} [h : {HC} p P] : P.next {pc} = {P.next pc} := (d_{pc} (p := p)).2.2.1"
    if !lemmasL.contains l then lemmasL := lemmasL.push l
  for f in factsL do
    if xmode && baseFacts.contains f then continue
    if f.startsWith ".jumpTableSize " then
      let m := (f.drop 15).toString
      lemmasL := lemmasL.push s!"@[pvm_code] theorem jts \{p : ByteArray} \{P : Program} [h : {HC} p P] : P.jumpTable.size = {m} := h.ok.jumpTableSize (show CodeFact.jumpTableSize {m} ∈ facts from {memFact (idxOf f)})"
    if f.startsWith ".jumpEntry " then
      let parts := (f.drop 11).toString.splitOn " "
      let k := parts[0]!; let t := parts[1]!
      lemmasL := lemmasL.push s!"@[pvm_code] theorem jte_{k} \{p : ByteArray} \{P : Program} [h : {HC} p P] : P.jumpTable.getD {k} 0 = {t} := h.ok.jumpEntry (show CodeFact.jumpEntry {k} {t} ∈ facts from {memFact (idxOf f)})"
    if f.startsWith ".blockStart " then
      let parts := (f.drop 12).toString.splitOn " "
      let t := parts[0]!; let b := parts[1]!
      lemmasL := lemmasL.push s!"@[pvm_code] theorem bs_{t} \{p : ByteArray} \{P : Program} [h : {HC} p P] : P.isBlockStart {t} = {b} := h.ok.blockStart (show CodeFact.blockStart {t} {b} ∈ facts from {memFact (idxOf f)})"
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
  let pathInputs := cx.svc.base :: cx.svc.emptyBase :: (cx.svc.segClass ++ cx.svc.segxExtra ++ cx.svc.emptyClass ++
    cx.svc.pathExtra ++ cx.svc.codeExtra)
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
  GENERATED by `lake exe genwitnesssteps {FLAG}code{if amode then E.toLower else ""} {n}` from {BLOB}.
  Do not edit by hand.
-/
{if xmode then s!"import Services.{NS}.Code" else "import JAM.Theorems.GrowHeap"}

/-!
# {if fmode then "Logging code facts" else if rmode then "Refine body code facts" else if amode then "Accumulate code facts" else if xmode then "Further code facts" else "Code facts"} of {LBL}

{if fmode then s!"Every instruction of {LBL}'s logging ranges (`fnRangesF`: `format!`, `core::fmt` and the
`String` sink) that none of `Code.facts`, `CodeX.facts` and `CodeA.facts` has, with the block starts,
blocks and jump-table entries they need (every entry into the ranges), kept apart so that adding them
rechecks nothing that uses only those. `Services.{NS}.CodeFOk` checks them against the blob by the
kernel (`CodeFCheck.checkCode_ok`, `hasCodeF`); `HasCodeF p P` assumes them." else if rmode then s!"Every instruction of {LBL}'s refine body (`fnRangesR`: its transform loop, handlers and output) that
neither `Code.facts` nor `CodeX.facts` has, with the block starts, blocks and jump-table entries they need
(every entry into the ranges), kept apart so that adding them rechecks nothing that uses only those.
`Services.{NS}.CodeROk` checks them against the blob by the kernel (`CodeRCheck.checkCode_ok`,
`hasCodeR`); `HasCodeR p P` assumes them." else if amode then s!"Every instruction of {LBL}'s accumulate ranges (`fnRangesA`) that neither `Code.facts` nor
`CodeX.facts` has, with the block starts, blocks and jump-table entries they need (every entry into
the ranges), kept apart so that adding them rechecks nothing that uses only those.
`Services.{NS}.CodeAOk` checks them against the blob by the kernel (`CodeACheck.checkCode_ok`,
`hasCodeA`); `HasCodeA p P` assumes them." else if xmode then s!"Every instruction of the further summarized functions (`fnRangesX`) that `Code.facts` lacks,
with the block starts, blocks and jump-table entries they need, kept apart from `Code.facts` so that
adding them rechecks nothing that uses only those. `Services.{NS}.CodeXOk` checks them against the
blob by the kernel (`CodeXCheck.checkCode_ok`, `hasCodeX`); `HasCodeX p P` assumes them." else s!"The code facts the proofs about {LBL} use: every instruction on the first {n} steps of its
refine path{if cx.svc.emptyCode then " and on the empty payload's refine path," else ""} and every instruction of the summarized functions (`fnRanges`), with the block
starts and jump-table entries they need. `checkCode` checks them against the blob
(`lake build {LBL}check`); `HasCode p P` assumes them."}
-/

namespace Services.{NS}.{CN}

open PVM

"
    let chunks := factGroups
    for (c, ch) in (List.range chunks.length).zip chunks do
      IO.println (s!"/-- Code facts, chunk {c}. -/\ndef facts_{c} : List CodeFact := [\n  " ++ ",\n  ".intercalate ch ++ "]\n")
    let ng := (chunks.length + 63) / 64
    for g in [0:ng] do
      IO.println (s!"/-- Chunks {64 * g}–{min (64 * (g + 1)) chunks.length - 1} of `facts`. -/\ndef factGroup_{g} : List (List CodeFact) := [" ++ ", ".intercalate (((List.range chunks.length).filter fun c => c / 64 == g).map fun c => s!"facts_{c}") ++ "]\n")
    IO.println ("/-- The groups of chunks of `facts`. -/\ndef factGroups : List (List (List CodeFact)) := [" ++ ", ".intercalate ((List.range ng).map fun g => s!"factGroup_{g}") ++ "]\n")
    IO.println "/-- The chunks of `facts`. -/\ndef factChunks : List (List CodeFact) := factGroups.flatten\n"
    IO.println s!"/-- The code facts the {LBL} proofs use. -/\ndef facts : List CodeFact := factChunks.flatten\n"
    IO.println s!"/-- The blob `p` deblobs to `P`, and `facts` hold of it. -/\nclass {HC} (p : outParam ByteArray) (P : Program) : Prop where\n  ok : CodeOk p facts P\n"
    if xmode then
      IO.println s!"/-- Where some facts hold of `P` and `checkCode` passes for these, these hold of `P` too. -/
theorem HasCode{E}.of \{p : ByteArray} \{P : Program} \{fs : List CodeFact} (h : CodeOk p fs P)
    (hx : checkCode p facts = true) : HasCode{E} p P := by
  obtain ⟨P', h'⟩ := checkCode_sound hx
  have e : P' = P := Option.some.inj (h'.parse.symm.trans h.parse)
  exact ⟨e ▸ h'⟩
"
    if amode then
      -- `codea`: the lemmas go in slices `CodeA/L*.lean` of 400 each, since one module holding them
      -- all needs more memory than a CI runner has; each slice imports only `CodeA`
      IO.println s!"\nend Services.{NS}.{CN}"
      IO.FS.createDirAll s!"Services/{NS}/{CN}"
      let sl := 400
      let nS := (lemmasL.size + sl - 1) / sl
      for k in [0:nS] do
        let part := (lemmasL.toList.drop (k * sl)).take sl
        IO.FS.writeFile s!"Services/{NS}/{CN}/L{k}.lean" (s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}code{E.toLower} {n}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.{CN}

/-! # Lemmas of `{CN}.facts`, slice {k} of {nS} -/

namespace Services.{NS}.{CN}

open PVM

" ++ "\n\n".intercalate part ++ s!"\n\nend Services.{NS}.{CN}\n")
      IO.FS.writeFile s!"Services/{NS}/{CN}All.lean" (s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}code{E.toLower} {n}` from {BLOB}.
  Do not edit by hand.
-/
" ++ String.join ((List.range nS).map fun k => s!"import Services.{NS}.{CN}.L{k}\n") ++ s!"
/-! # Every lemma of `{CN}.facts` -/
")
      return
    IO.println ("\n\n".intercalate lemmasL.toList)
    IO.println s!"\nend Services.{NS}.{CN}"
    return
  IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {FLAG}run {n}{((args.find? (·.startsWith "cut=")).map (" " ++ ·)).getD ""}` from {BLOB}.
  Do not edit by hand.
-/
import Services.{NS}.{if cx.svc.memcpySummary then "Memcpy" else "Code"}{((args.find? (·.startsWith "cut=")).map fun o => s!"\nimport Services.{NS}.{(o.drop 4).toString}").getD ""}

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
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 (initRegs L) μ ((∅, []) : RefineCtx) {endPc} ω' μ' x' {n} ∧
      PrefixPost L μ ω' μ' x' := by"
  -- `cut=NAME`: the proof from the cut chain NAME (`genwitnesssteps cut 0 NAME 0 N every=16 frame words`)
  let cutName := ((args.find? (·.startsWith "cut=")).map fun o => (o.drop 4).toString).getD ""
  let out (t : String) : IO Unit := if cutName == "" then IO.println t else pure ()
  if cutName != "" then
    let t ← IO.FS.readFile s!"Services/{NS}/{cutName}.lean"
    let some st := ((t.splitOn "theorem run").getD 1 "").splitOn ": ∃ ω'" |>.head? | throw (IO.userError "no run")
    let parts := ((((st.splitOn "(x : RefineCtx)").getD 1 "").splitOn "\n    (").drop 1).flatMap (·.splitOn ") (")
    let parts := "" :: parts
    let mut argsS : List String := ["henv", "hpar"]
    for q in parts.drop 1 do
      let nm := (q.splitOn " : ").headD ""
      let ty := (q.splitOn " : ").drop 1 |> " : ".intercalate
      let a := if nm == "henv" then "henv" else if nm == "hpar" then "hpar" else if nm == "L" then "L"
        else if nm == "hL" then "⟨hL.1, by omega⟩"
        else if nm.startsWith "hreg" then "(by simp [initRegs])"
        else if nm == "hhp" then "hμ.heapPages"
        else if nm.startsWith "hm_" then Id.run do
          let ps := (nm.drop 3).toString.splitOn "_"
          let c := ps[0]!.toNat!; let m := ps[1]!.toNat!
          let rds := ", ".intercalate ((List.range m).map fun q => s!"μ.read {c + q}")
          let rws := ", ".intercalate ((List.range m).map fun q =>
            let b := c + q
            match baseBytes.find? (·.1 == b) with
            | some (_, v) => s!"hμ.bytes {b} {v} (by decide)"
            | none => match pathBytes.find? (·.1 == b) with
              | some (_, v) => s!"hμ.path {b} {v} (by decide)"
              | none => s!"noStartOctet{b}")
          return s!"(by rw [show μ.readN {c} {m} = [{rds}] from rfl, {rws}])"
        else if nm.startsWith "hw_" then
          "(fun a h1 h2 => by first | exact hμ.stack a (by omega) (by omega) | exact hμ.heap a (by omega) (by omega))"
        else if nm.startsWith "hrd_" then
          "(fun a h1 h2 => by first | exact Memory.readable_of_writable (hμ.stack a (by omega) (by omega)) | exact Memory.readable_of_writable (hμ.heap a (by omega) (by omega)) | exact hμ.ro a (by omega) (by omega))"
        else s!"noStart_{nm}"
      let _ := ty
      argsS := argsS ++ [a]
    IO.println s!"  obtain ⟨ω', μ', hrun, hregs, hmem, hsym, hfr, hrdA, hrdm, hwrm, -⟩ :=
    {cutName}.run p P env (initRegs L) μ ((∅, []) : RefineCtx) {" ".intercalate argsS}
  refine ⟨ω', μ', _, hrun, ⟨?regs, ?bytes, ?args, ?argsRd, ?stk, ?hp, rfl, ?lw, ?ro, ?fr⟩⟩
  case regs =>
    clear hfr hrdA hrdm hwrm hmem hsym hrun
    simp [initRegs] at hregs
    simp [hregs]
  case bytes =>
    simp only [postBytes, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    simp [hmem]
  case args =>
    intro a h1 h2
    apply hfr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
      Nat.not_lt]
    omega
  case argsRd => intro a h1 h2; exact hrdA a (by omega)
  case stk => intro a h1 h2; exact hwrm a (hμ.stack a h1 h2)
  case hp => intro a h1 h2; exact hwrm a (hμ.heap a h1 h2)
  case lw =>
    simp only [lenAt, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    exact hsym
  case ro => intro a h1 h2; exact hrdm a (hμ.ro a h1 h2)
  case fr =>
    first
    | exact hfr
    | (intro a ha
       apply hfr
       simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
         Nat.not_lt] at ha ⊢
       omega)
"
  out s!"  obtain ⟨hL0, hLI⟩ := hL
  have hw := hμ.stack
  have hwh := hμ.heap
  have hr : ∀ a, {ω[1]!.toNat} - {jb.stackSize} ≤ a → a < {ω[1]!.toNat} → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hrh : ∀ a, {rwLo} ≤ a → a < {rwHi} → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwh a h1 h2)"
  for (a, b) in baseBytes do
    out s!"  have hb_{a} : μ.read {a} = {b} := hμ.bytes {a} {b} (by decide)"
  for (a, k) in baseLoads do
    let bytes := (List.range k).map fun j => (μ.read (a + j)).toNat
    let hbs := ", ".intercalate ((List.range k).map fun j => s!"hb_{a + j}")
    out s!"  have hbn_{a}_{k} : μ.readN {a} {k} = {bytes} := by\n    simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.map_append, Nat.reduceAdd, Nat.add_zero, {hbs}]"
  let stepLine (pc : Nat) (gs : String) : String := match P.decode pc with
    | some (.oneImm .ecalli 1) => Id.run do
      let some (_, regsAt, memAt) := tr.find? (·.1 == pc) | return ""
      let top := (growHeapCore regsAt memAt code).2.2.1
      let t := growTop (regsAt[7]!.toNat) top hB
      return s!"    apply FreeStepsH.growHeap env {t} (d_{pc} (p := p) (P := P)) henv (h := {top})\n      (by heap_pages hμ.heapPages) (by decide) (by decide) (by decide)\n      (by pvm_simp [growTop, initRegs, List.set_cons_succ, List.set_cons_zero, reg{gs}])\n      (by decide)"
    | some (.oneImm .ecalli _) =>
      s!"    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_host [hw, hr, hwh, hrh, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE, initRegs, List.set_cons_succ, List.set_cons_zero, growTop, setR7, reg{gs}]"
    | _ =>
      s!"    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [hpar, Params.full_encode, hw, hr, hwh, hrh, {", ".intercalate (baseLoads.toList.map fun (a, k) => s!"hbn_{a}_{k}")}{if baseLoads.isEmpty then "" else ", "}{", ".intercalate (baseBytes.toList.map fun (a, _) => s!"hb_{a}")}{if baseBytes.isEmpty then "" else ", "}initRegs, List.set_cons_succ, List.set_cons_zero, growTop, setR7, reg{gs}]"
  out s!"
  rw [show initRegs L = regsNF (initRegs L) [] from rfl]"
  let mut gs := ""
  if splices.isEmpty then
    out "  refine ⟨?ω, ?μ, ?x, ?h, ?post⟩\n  case h =>"
    for pc in path do out (stepLine pc "")
  else
    out s!"  suffices hs : ∃ ω' μ', FreeStepsH p (refineContract env) 0 (regsNF (initRegs L) []) μ ((∅, []) : RefineCtx) {endPc} ω' μ' ((∅, []) : RefineCtx) {n} ∧
      PrefixPost L μ ω' μ' ((∅, []) : RefineCtx) by
    obtain ⟨ω', μ', h, hp⟩ := hs
    exact ⟨ω', μ', _, h, hp⟩"
    let mut k := 0
    for s in [0:splices.size] do
      let (ks, kr) := splices[s]!
      let some (_, r, _) := tr[ks]? | break
      let ret := r[0]!.toNat
      let t := P.jumpTable.getD (ret / 2 - 1) 0
      out s!"  refine FreeStepsH.ex_trans (n₁ := {ks - k}) (n₂ := {n - ks}) (i₁ := {memBase}) (ω₁ := ?ω₁_{s}) (μ₁ := ?μ₁_{s}) ?pre{s} ?rest{s} (by decide)\n  case pre{s} =>"
      for j in [k:ks] do out (stepLine path[j]! gs)
      out s!"    exact FreeStepsH.refl
  refine FreeStepsH.bind_ex (memcpy_small_regs (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) _ _
    {ret} {t} {r[1]!.toNat} {r[7]!.toNat} {r[8]!.toNat} {r[9]!.toNat} ?m0_{s} ?m1_{s} ?m7_{s} ?m8_{s} ?m9_{s} (by decide)
    (by decide) ?mjt_{s} ?mbt_{s} (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?mwf_{s} ?mr_{s} ?mw_{s}) ?k{s}
    (n₂ := {n - kr}) (by decide)
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
    out "  refine ⟨?ω, ?μ, ?h, ?post⟩\n  case h =>"
    for j in [k:n] do out (stepLine path[j]! gs)
  out s!"    exact FreeStepsH.refl
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
"
  IO.println s!"/-! ## From Y's starting state -/

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
    ∃ ω' μ' x', FreeStepsH p (refineContract env) 0 ω μ ((∅, []) : RefineCtx) {endPc} ω' μ' x' {n} ∧
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
def mode_dis (cx : Cx) : IO Unit := do
    -- `dis LO HI`: the instructions at LO … HI − 1, decoded in order, with block starts marked
    let hi := (cx.args.getD 2 "0").toNat!
    let mut pc := cx.n
    while pc < hi do
      match cx.P.decode pc with
      | some ins => IO.println s!"{if cx.P.isBlockStart pc then "*" else " "} {pc} {leanInstr ins}"
      | none => IO.println s!"  {pc} ?"
      pc := cx.P.next pc

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
def varBinder (lb : Nat) (v : String) (sb : String := "S < 4294967296")
    (vb : List (String × String) := []) : String :=
  let bound := (vb.lookup v).getD <| match v with
    | "TS" => "TS < 4294967296" | "NI" => "NI < 4294967296" | "LA" => "3 ≤ LA ∧ LA ≤ 15"
    | "Y" => "1 ≤ Y ∧ Y ≤ 15" | "S" => sb | "C" => "C < 65536" | "L" => s!"0 < L ∧ L < {lb}"
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
def mode_cut (cx : Cx) (bsOv : Option (List Nat) := none) : IO Unit := do
  let args := cx.args; let tr := cx.tr; let P := cx.P
  let NS := cx.svc.name; let LBL := cx.svc.label; let BLOB := cx.svc.blob; let FLAG := cx.svc.flag
  let joinPc := cx.n
  -- refine or accumulate (`WITNESS_ACC=1`): the environment, context, contract, host tactic and
  -- code facts the generated steps use
  let envT := if cx.acc then "AccEnv" else "RefineHost.Env"
  let ctxT := if cx.acc then "AccCtx" else "RefineCtx"
  let contr := if cx.acc then "accContract env" else "refineContract env"
  let growL := if cx.acc then "FreeStepsH.growHeapAcc" else "FreeStepsH.growHeap"
  let hostT := if cx.acc then "pvm_host_acc" else "pvm_host"
  let parT := if cx.acc then "env.params = Params.full" else "env.fetch.params = Params.full"
  let codeImp := if cx.acc then s!"import Services.{cx.svc.name}.CodeX\nimport Services.{cx.svc.name}.CodeAAll\nimport Services.Bootstrap.Acc.HostSteps" else s!"import Services.{cx.svc.name}.Code"
  let codeOpen := if cx.acc then s!"Services.{cx.svc.name}.Code Services.{cx.svc.name}.CodeX Services.{cx.svc.name}.CodeA Services.Bootstrap.Acc" else s!"Services.{cx.svc.name}.Code"
  let hasC := if cx.acc then "[HasCode p P] [HasCodeX p P] [HasCodeA p P]" else "[HasCode p P]"
  let what := if cx.acc then "accumulate" else "refine"
  let name := args.getD 2 "cut"
  let opts := args.drop 3
  let out := opts.contains "out"
  -- `frame`: also carry, from the start, the frame (octets outside every write so far), the page
  -- access and the registers no segment writes, so the composed run states what `seg` states
  let frame := opts.contains "frame"
  -- `keep=j,…`: the start registers the caller knows; the others are dropped from the reads of
  -- the segments before their first write (a spill, say, whose value nothing uses)
  let keepO : Option (List Nat) := (opts.find? (·.startsWith "keep=")).map fun o =>
    (((o.drop 5).toString).splitOn ",").map String.toNat!
  let nums := (opts.filter fun o => o.all Char.isDigit).map String.toNat!
  let bs : List Nat := bsOv.getD <| match opts.find? (·.startsWith "every=") with
    | some e =>
      let N := ((e.drop 6).toString).toNat!
      let A := nums[0]!; let B := nums[1]!
      ((List.range ((B - A + N - 1) / N)).map (A + N * ·)) ++ [B]
    | none => nums
  -- `WITNESS_CLASS=c,i,s,k;…` replaces the class (k octets 255 of payload, or `c,i,s,k,b,f` as
  -- for `WITNESS_INPUT`), e.g. one per hex-digit
  -- count of s where the path depends on it
  let classOv := ((← IO.getEnv "WITNESS_CLASS").getD "").splitOn ";" |>.filterMap fun e =>
    match (e.splitOn ",").filterMap String.toNat? with
    | [t, s, n] => if cx.acc then some (t, n, s, []) else none
    | [c, i, s, k] => some (c, i, s, List.replicate k (255 : UInt8))
    | [c, i, s, k, b0, f] => some (c, i, s, (b0.toUInt8 :: List.replicate (k - 1) f.toUInt8).take k)
    | _ => none
  let classInputs : List (Nat × Nat × Nat × List UInt8) :=
    if !classOv.isEmpty then classOv
    else if cx.empty then cx.svc.emptyClass ++ cx.svc.emptyExtra else cx.svc.segClass ++ cx.svc.segxExtra
  let baseP := (cx.c, cx.i, cx.sid, cx.y)
  let align (t : Array (Nat × Regs × Memory)) : Option Nat :=
    (List.range t.size).find? (fun k => (t[k]?.map (·.1)) == some joinPc)
  let some k0 := align tr | IO.eprintln "join not reached"; return
  let mut others : Array (Array (Nat × Regs × Memory) × Nat) := #[]
  let mut otherPs : Array (Nat × Nat × Nat × List UInt8) := #[]
  for (c2, i2, s2, y2) in classInputs do
    let some t2 := cx.traceF c2 i2 s2 y2 | continue
    let some k2 := align t2 | IO.eprintln "join not reached"; return
    for j in [bs.head!:bs.getLast!+1] do
      if (tr[k0 + j]?.map (·.1)) != (t2[k2 + j]?.map (·.1)) then
        IO.eprintln s!"paths differ at +{j}"; return
    others := others.push (t2, k2)
    otherPs := otherPs.push (c2, i2, s2, y2)
  let names := varNames true baseP cx.acc
  let allQ := baseP :: otherPs.toList
  -- the value of register j / octet a at path step b (after PC), if the class agrees on it or it
  -- is one of the variables' expressions
  let regAt (b j : Nat) : Option String :=
    let vb := (tr[k0 + b]?.map (·.2.1[j]!.toNat)).getD 0
    let vo := others.toList.map fun (t2, k2) => (t2[k2 + b]?.map (·.2.1[j]!.toNat)).getD 0
    if vo.all (· == vb) then some (toString vb) else matchVarG true names allQ vb vo true cx.wild
  let octAt (b a : Nat) : Option Nat :=
    let vb := (tr[k0 + b]?.map (·.2.2.read a |>.toNat)).getD 0
    let vo := others.toList.map fun (t2, k2) => (t2[k2 + b]?.map (·.2.2.read a |>.toNat)).getD 0
    if vo.all (· == vb) then some vb else none
  let nseg := bs.length - 1
  -- host calls: each segment's (step, id), the heap's top at each cut, `fetch`'s pages
  let hostAt (k : Nat) : List (Nat × Nat) := (List.range (bs[k+1]! - bs[k]!)).filterMap fun j =>
    match tr[k0 + bs[k]! + j]? with
    | some (pc, _, _) => match P.decode pc with
      | some (.oneImm .ecalli h) => some (j, h.toNat)
      | _ => none
    | none => none
  let hasHost := (List.range nseg).any fun k => (hostAt k).any fun (_, h) => h == 1 || h == 2
  let hasGrow := (List.range nseg).any fun k => (hostAt k).any (·.2 == 1)
  let segGrow (k : Nat) : Bool := (hostAt k).any (·.2 == 1)
  let (hA, hB) := heapBounds cx.code
  let topAt (b : Nat) : Nat := match tr[k0 + b]? with
    | some (_, r, m) => (growHeapCore r m cx.code).2.2.1
    | none => 0
  let pageRanges (k : Nat) : List (Nat × Nat) := (hostAt k).filterMap fun (j, h) =>
    if h != 2 then none else match tr[k0 + bs[k]! + j]? with
      | some (_, r, _) =>
        let o := r[7]!.toNat; let l := r[9]!.toNat
        if l == 0 then none else some (o / 4096 * 4096, ((o + l - 1) / 4096 + 1) * 4096)
      | none => none
  let mut infos : Array SegInfo := Array.replicate nseg default
  let mut reads : Array (List Nat) := Array.replicate nseg []
  let mut writes : Array (Std.HashSet Nat) := Array.replicate nseg {}
  -- the state each cut needs, backward from the end
  let fin := (List.range 13).map (fun j => (tr[k0 + bs.getLast!]?.map (·.2.1[j]!.toNat)).getD 0)
  let outO := if out then (List.range fin[8]!).map (fin[7]! + ·) else []
  let whole ← analyzeSeg P tr others otherPs k0 bs.head! bs.getLast! out baseP true []
    (regsWritten cx (k0 + bs.head!) (k0 + bs.getLast!)) true (opts.contains "words") (half := cx.wild && out) (acc := cx.acc)
  let unch : List Nat := if frame then (List.range 13).filter (fun j => whole.regPost.any (· == (j, none))) else []
  let mut needR : List Nat := (if out then [0, 7, 8] else []) ++
    (if frame then whole.regPost.filterMap (fun (j, v) => v.map (fun _ => j)) ++ whole.symPost.map (·.1) else [])
  needR := needR.eraseDups
  let mut needO : List Nat := (outO ++ (if frame then whole.memPost.map (·.1) else [])).eraseDups.filter
    fun b => !(whole.symMem.any fun (a, n, _) => a ≤ b && b < a + n)
  let mut needS : List (Nat × Nat × String) := if frame || out then whole.symMem else []
  let mut needW : List (Nat × Nat) := []
  let mut needRd : List (Nat × Nat) := if out && fin[8]! > 0 then [(fin[7]!, fin[7]! + fin[8]!)] else []
  let mut sts0 : Array (List Nat × List Nat × List (Nat × Nat × String) × List (Nat × Nat) × List (Nat × Nat)) :=
    #[(needR, needO, needS, needW, needRd)]
  for kk in [0:nseg] do
    let k := nseg - 1 - kk
    let info ← analyzeSeg P tr others otherPs k0 bs[k]! bs[k+1]! false baseP true needO
      (regsWritten cx (k0 + bs[k]!) (k0 + bs[k+1]!)) true (half := cx.wild) (wantS := needS) (acc := cx.acc)
    let mut w : Std.HashSet Nat := {}
    for (lo, hi) in info.wr do
      for a in [lo:hi] do w := w.insert a
    infos := infos.set! k info
    writes := writes.set! k w
    let rd0 := regsRead cx (k0 + bs[k]!) (k0 + bs[k+1]!)
    let before := regsWritten cx (k0 + bs[0]!) (k0 + bs[k]!)
    reads := reads.set! k (match keepO with
      | some ks => rd0.filter fun j => ks.contains j || before.contains j
      | none => rd0)
    -- `wild`: drop from cut k + 1's state what segment k leaves inexpressible
    if cx.wild then
      let badR := needR.filter fun j =>
        info.wregs.contains j && !(info.regPost.any (fun (i, v) => i == j && v.isSome)) && !(info.symPost.any (·.1 == j))
      let badO := needO.filter fun a => w.contains a && !(info.memPost.any (·.1 == a))
      let badS := needS.filter fun (a, n, e) =>
        (List.range n).any (fun q => w.contains (a + q)) && !(info.symMem.any (· == (a, n, e)))
      if !(badR.isEmpty && badO.isEmpty && badS.isEmpty) then
        needR := needR.filter (!badR.contains ·)
        needO := needO.filter (!badO.contains ·)
        needS := needS.filter (!badS.contains ·)
        sts0 := sts0.set! (sts0.size - 1) (needR, needO, needS, needW, needRd)
    -- what segment k must leave: check it does
    for j in needR do
      if info.wregs.contains j && !(info.regPost.any (fun (i, v) => i == j && v.isSome)) && !(info.symPost.any (·.1 == j)) then
        let b := bs[k+1]!
        let vb := (tr[k0 + b]?.map (fun (x : Nat × Regs × Memory) => x.2.1[j]!.toNat)).getD 0
        let vo := others.toList.map fun ((t2, k2) : Array (Nat × Regs × Memory) × Nat) =>
          (t2[k2 + b]?.map (fun (x : Nat × Regs × Memory) => x.2.1[j]!.toNat)).getD 0
        throw (IO.userError s!"cut {k + 1}: segment {k} leaves register {j} input-dependent ({vb} :: {vo} for |y| = {allQ.map (fun (q : Nat × Nat × Nat × List UInt8) => q.2.2.2.length)}), and a later step reads it")
    for a in needO do
      if w.contains a && !(info.memPost.any (·.1 == a)) then
        throw (IO.userError s!"cut {k + 1}: segment {k} leaves octet {a} input-dependent, and a later step reads it")
    for (a, n, e) in needS do
      if (List.range n).any (fun q => w.contains (a + q)) && !(info.symMem.any (· == (a, n, e))) then
        throw (IO.userError s!"cut {k + 1}: segment {k} writes into the symbolic word at {a}, and a later step reads it")
    let rd := reads[k]!
    needR := (rd ++ needR.filter (fun j => !info.wregs.contains j)).eraseDups.mergeSort
    needO := (info.byteFacts.map (·.1) ++ needO.filter (fun a => !w.contains a)).eraseDups.mergeSort
    needS := (info.symLoads ++ needS.filter (fun (a, n, _) => !(List.range n).any (fun q => w.contains (a + q)))).eraseDups
    needW := (info.wr ++ pageRanges k ++ needW).eraseDups
    needRd := (info.rr ++ needRd).eraseDups
    sts0 := sts0.push (needR, needO, needS, needW, needRd)
  let stsR := sts0.reverse
  -- `wild`: the start state too states only what is expressible
  let mut sts := if !cx.wild then stsR else (List.range stsR.size).toArray.map fun k =>
    let (r, o, sy, wr, rr) := stsR[k]!
    (r.filter (fun j => (regAt bs[k]! j).isSome), o.filter (fun a => (octAt bs[k]! a).isSome), sy, wr, rr)
  -- `wild`: a symbolic word dropped at a cut stays dropped while no segment re-establishes it
  if cx.wild then
    for k in [1:sts.size] do
      let (r, o, sy, wr, rr) := sts[k]!
      let prev := sts[k-1]!.2.2.1
      let w := writes[k-1]!
      let sy' := sy.filter fun (a, n, e) =>
        prev.contains (a, n, e) ||
          ((List.range n).any (fun q => w.contains (a + q)) && infos[k-1]!.symMem.any (· == (a, n, e)))
      sts := sts.set! k (r, o, sy', wr, rr)
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
      let some e := regAt bs[k]! j | throw (IO.userError s!"cut {k}: register {j} there is input-dependent")
      vars0 := vars0 ++ exprVars names e
    for (_, _, e) in s do vars0 := vars0 ++ exprVars names e
  for info in infos do vars0 := vars0 ++ info.vars
  let vars := names.filter vars0.contains
  let varArgs := " ".intercalate (vars.flatMap fun v => [v, s!"h{v}"])
  let varBinders := " ".intercalate (vars.map (varBinder cx.svc.lBound · cx.sBound cx.vBounds))
  let segCond (k : Nat) : String :=
    let outW := " && ".intercalate (infos[k]!.wr.map fun (lo, hi) => s!"!(decide ({lo} ≤ a ∧ a < {hi}))")
    s!"decide (a < 4294967296){if outW == "" then "" else " && " ++ outW}"
  let fp := if frame then " ω₀ μ₀" else ""
  let fpB := if frame then " (ω₀ : Regs) (μ₀ : Memory)" else ""
  let frameFields (k : Nat) : List (String × String) :=
    if !frame then [] else if hasGrow then
      [("fr", s!"∀ a, C{k} a = true → μ.read a = μ₀.read a"),
       ("rdA", "∀ a, 2147483648 ≤ a → μ.readable a = μ₀.readable a"),
       ("rdm", "∀ a, μ₀.readable a = true → μ.readable a = true"),
       ("wrm", "∀ a, μ₀.writable a = true → μ.writable a = true")] ++ unch.map (fun j => (s!"uk{j}", s!"ω[{j}] = ω₀[{j}]"))
    else
      [("fr", s!"∀ a, C{k} a = true → μ.read a = μ₀.read a"), ("rdq", "∀ a, μ.readable a = μ₀.readable a"),
       ("wrq", "∀ a, μ.writable a = μ₀.writable a")] ++ unch.map (fun j => (s!"uk{j}", s!"ω[{j}] = ω₀[{j}]"))
  let envB := if hasHost then s!" (henv : heapBounds env.code = ({hA}, {hB})) (hpar : {parT})" else ""
  let envA := if hasHost then " henv hpar" else ""
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
    if hasGrow then fs := fs ++ [("hhp", s!"JAM.HeapPages μ {hA} {hB} {topAt b}")]
    return fs
  for k in [0:nseg + 1] do
    let (_, o, _, _, _) := sts[k]!
    for a in o do
      if (octAt bs[k]! a).isNone then throw (IO.userError s!"cut {k}: octet {a} there is input-dependent")
  let mut st := header "The state at each cut." ++ s!"
import PVM.Logic.Chase{if cx.extraSimp.isEmpty && !(cx.wild && out) then "" else "\nimport PVM.Logic.Words"}{if hasGrow then "\nimport JAM.Theorems.GrowHeap" else ""}

namespace Services.{NS}.{name}

open PVM

set_option maxRecDepth 100000

"
  if frame then
    st := st ++ "/-- The frame conditions: an address outside every write of the segments before a cut. -/\ndef C0 (a : Nat) : Bool := decide (a < 4294967296)\n\n"
    for k in [0:nseg] do
      st := st ++ s!"def C{k + 1} (a : Nat) : Bool := C{k} a && ({segCond k})\n\n"
  for k in [0:nseg + 1] do
    let fs := fieldsOf k ++ frameFields k
    st := st ++ s!"/-- The state at cut {k} (step {bs[k]!} after pc {joinPc}, pc {infos[min k (nseg - 1)]!.pcA}): what the rest of the path reads. -/
structure St{k} {" ".intercalate (vars.map (s!"({·} : Nat)"))}{fpB} (ω : Regs) (μ : Memory) : Prop where
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
    let mut sx := header s!"Steps {info.A} … {info.B - 1} of {LBL}'s {what}." ++ s!"
{codeImp}
import Services.{NS}.{name}.St

namespace Services.{NS}.{name}.S{k}

open PVM JAM {codeOpen} Services.{NS}.{name}

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- **Steps {info.A} … {info.B - 1} of {LBL}'s {what}** (pc {info.pcA} to pc {info.pcB}), from the
    registers they read and the octets they read first, to the values they leave. -/
theorem steps (p : ByteArray) (P : Program) {hasC} (env : {envT}) (ω : Regs) (μ : Memory)
    (x : {ctxT}){envB}"
    if hasGrow then sx := sx ++ s!"\n    (hhp : HeapPages μ {hA} {hB} {topAt bs[k]!})"
    for v in ivars do sx := sx ++ s!"\n    {varBinder cx.svc.lBound v cx.sBound cx.vBounds}"
    -- `wild`: only what cut k's state states
    let rdS := if cx.wild then rd.filter (sts[k]!.1.contains ·) else rd
    let symS := if cx.wild then info.symLoads.filter (sts[k]!.2.2.1.contains ·) else info.symLoads
    let regB := rdS.map fun j => (s!"hreg{j}", s!"ω[{j}] = UInt64.ofNat {(regAt bs[k]! j).getD "0"}")
    let symB := symS.map fun (a, n, e) => (s!"hbn_{a}_{n}", s!"μ.readN {a} {n} = Num.encodeLE {n} {e}")
    let wB := (info.wr ++ pageRanges k).eraseDups.map fun (lo, hi) => (s!"hw_{lo}_{hi}", s!"∀ a, {lo} ≤ a → a < {hi} → μ.writable a = true")
    let rB := info.rr.map fun (lo, hi) => (s!"hrd_{lo}_{hi}", s!"∀ a, {lo} ≤ a → a < {hi} → μ.readable a = true")
    let bB := info.byteFacts.map fun (a, v) => (s!"hb_{a}", s!"μ.read {a} = {v}")
    let binders := regB ++ symB ++ wB ++ rB ++ bB
    for (n, t) in binders do sx := sx ++ s!"\n    ({n} : {t})"
    sx := sx ++ s!"\n    : ∃ ω' μ', FreeStepsH p ({contr}) {info.pcA} ω μ x {info.pcB} ω' μ' x {info.B - info.A} ∧"
    -- the registers the next cut needs (and, with `frame`, those no segment writes)
    let postR := sts[k + 1]!.1 ++ unch
    let regC0 : List (Nat × String) := info.regPost.map (fun (j, v) =>
      match v with | some v => (j, s!"ω'[{j}] = UInt64.ofNat {v}") | none => (j, s!"ω'[{j}] = ω[{j}]")) ++
      info.symPost.map fun (j, v) => (j, s!"ω'[{j}] = UInt64.ofNat {v}")
    let regC := regC0.filter fun (j, _) => postR.contains j
    sx := sx ++ "\n      (" ++ (if regC.isEmpty then "True" else " ∧ ".intercalate (regC.map (·.2))) ++ ") ∧"
    let memC := info.memPost.map fun (a, v) => s!"μ'.read {a} = {v}"
    sx := sx ++ "\n      (" ++ (if memC.isEmpty then "True" else " ∧ ".intercalate memC) ++ ") ∧"
    if !info.symMem.isEmpty then
      sx := sx ++ "\n      (" ++ " ∧ ".intercalate (info.symMem.map fun (a, n, e) => s!"μ'.readN {a} {n} = Num.encodeLE {n} {e}") ++ ") ∧"
    let outW := " && ".intercalate (info.wr.map fun (lo, hi) => s!"!(decide ({lo} ≤ a ∧ a < {hi}))")
    sx := sx ++ s!"\n      (∀ a, (decide (a < 4294967296){if outW == "" then "" else " && " ++ outW}) = true → μ'.read a = μ.read a) ∧"
    let grow := segGrow k
    if grow then
      sx := sx ++ "\n      (∀ a, μ.readable a = true → μ'.readable a = true) ∧ (∀ a, μ.writable a = true → μ'.writable a = true) ∧\n      (∀ a, 2147483648 ≤ a → μ'.readable a = μ.readable a)"
    else
      sx := sx ++ "\n      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)"
    if hasGrow then sx := sx ++ s!" ∧\n      HeapPages μ' {hA} {hB} {topAt bs[k + 1]!}"
    sx := sx ++ " := by"
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
    let simpArgsH := ", ".intercalate ([regA, loadA, hws, hrs, factA].filter (· != "") ++
      (if hasGrow then ["setR7"] else []))
    let simpArgs := ", ".intercalate ([regA, loadA, hws, hrs, factA].filter (· != "") ++
      (if hasHost then ["hpar", "Params.full_encode"] else []) ++ (if hasGrow then ["setR7"] else []) ++ cx.extraSimp)
    sx := sx ++ "\n  rw [show ω = regsNF ω [] from rfl]\n  refine ⟨?ω', ?μ', ?run, ?post⟩\n  case run =>"
    for j in [0:info.pcs.length] do
      let pc := info.pcs[j]!
      match P.decode pc with
      | some (.oneImm .ecalli 1) =>
        let some (_, rg, mg) := tr[k0 + bs[k]! + j]? | pure ()
        let top := (growHeapCore rg mg cx.code).2.2.1
        let t := growTop rg[7]!.toNat top hB
        sx := sx ++ s!"\n    apply {growL} env {t} (d_{pc} (p := p) (P := P)) henv (h := {top})\n      (by heap_pages hhp) (by decide) (by decide) (by decide)\n      (by pvm_simp [growTop, reg, {simpArgs}])\n      (by decide)"
      | some (.oneImm .ecalli _) =>
        sx := sx ++ s!"\n    apply FreeStepsH.host_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in {hostT} [{simpArgsH}, PVM.Memory.writable_writeN, PVM.Memory.writable_setPages, List.range_succ, List.range_zero, List.nil_append, List.all_cons, List.all_nil, List.all_append, Bool.and_true, Bool.true_and, Nat.reduceDiv, PVM.Memory.writeN_nil, Num.length_encodeLE]"
      | _ =>
        sx := sx ++ s!"\n    apply FreeStepsH.step_decode (d_{pc} (p := p) (P := P))\n    · set_option maxHeartbeats 1000000 in pvm_simp [{simpArgs}]"
    let hpH := (if grow then ", ?rdA" else "") ++ (if hasGrow then ", ?hp" else "")
    if info.symMem.isEmpty then
      sx := sx ++ s!"\n    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?frame, ?rd, ?wr{hpH}⟩"
    else
      sx := sx ++ s!"\n    exact FreeStepsH.refl\n  case post =>\n    refine ⟨?regs, ?mem, ?smem, ?frame, ?rd, ?wr{hpH}⟩"
      sx := sx ++ "\n    case smem =>\n      " ++ (if info.symMem.length > 1 then "refine ⟨" ++ ", ".intercalate (info.symMem.map fun _ => "?_") ++ "⟩ <;>\n      " else "") ++ "simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,\n        PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32" ++ (if cx.wild && out then ", PVM.readN_writeN_encodeLE2_hi, PVM.readN_writeN_encodeLE2_lo]\n      all_goals first | (congr 1; split <;> omega) | simp only [PVM.Num.encodeLE, Nat.mod_mod, Nat.zero_div, PVM.ofNat_mod256]" else "]")
    sx := sx ++ s!"\n    case regs =>\n      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,\n        PVM.getD_some', List.lookup_nil, Option.getD_none, and_self, and_true, true_and{if regA == "" then "" else ", " ++ regA}{if hasGrow then ", setR7, PVM.set_regsNF, PVM.insertReg" else ""}]{if cx.wild then "\n      all_goals (try simp only [Nat.div_div_eq_div_mul, Nat.reduceMul])\n      all_goals (try (congr 1; split <;> omega))" else ""}"
    sx := sx ++ s!"\n    case mem =>\n      try and_intros\n      all_goals simp (disch := pvm_arith) only [PVM.Memory.read_writeN, PVM.reduceEncodeLE, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff,\n        Nat.reduceLT, and_true, true_and, and_false, false_and, ↓reduceIte, List.getElem!_cons_zero,\n        List.getElem!_cons_succ, UInt8.reduceOfNat, and_self, PVM.Num.encodeLE{if hasGrow then ", PVM.Memory.read_setPages" else ""}{if hasHost then ", hpar, Params.full_encode, List.drop_zero, List.take_of_length_le" else ""}] <;> chase_octet"
    -- accumulate: a `fetch` of the parameters leaves `env.params.encode` in memory, which `hpar` makes concrete
    let parFix := if cx.acc && (hostAt k).any (·.2 == 2) then "\n      try simp only [hpar, JAM.Params.full_encode]" else ""
    sx := sx ++ s!"\n    case frame =>\n      intro a ha\n      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,\n        not_and, Nat.not_lt] at ha{parFix}\n      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Num.length_encodeLE,\n        List.length_cons, List.length_nil, PVM.two32{if hasGrow then ", PVM.Memory.read_setPages" else ""}]"
    if grow then
      sx := sx ++ "\n    case rd =>\n      intro a ha\n      simp only [PVM.Memory.readable_writeN, PVM.Memory.readable_setPages]\n      split <;> simp_all"
      sx := sx ++ "\n    case wr =>\n      intro a ha\n      simp only [PVM.Memory.writable_writeN, PVM.Memory.writable_setPages]\n      split <;> simp_all\n"
    else
      sx := sx ++ "\n    case rd => intro a; simp only [PVM.Memory.readable_writeN]\n    case wr => intro a; simp only [PVM.Memory.writable_writeN]\n"
    if grow then
      sx := sx ++ "    case rdA =>\n      intro a ha\n      simp only [PVM.Memory.readable_writeN, PVM.Memory.readable_setPages]\n      first | (rw [if_neg (by simp only [PVM.pageSize]; omega)]) | (simp only [PVM.pageSize]; split <;> first | rfl | omega)\n"
    if hasGrow then sx := sx ++ s!"    case hp =>{if parFix.isEmpty then "" else " (try simp only [hpar, JAM.Params.full_encode]);"} first | exact hhp | heap_pages hhp\n"
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
          match info.symMem.findIdx? (fun (c, m, _) => c == a && m == len) with
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
      else if n == "hhp" then "hhp'"
      else if n.startsWith "hw_" then
        let parts := (n.drop 3).toString.splitOn "_"
        if grow then s!"fun a h1 h2 => hwr a ({rangeArg k true parts[0]!.toNat! parts[1]!.toNat!} a h1 h2)"
        else s!"fun a h1 h2 => (hwr a).trans ({rangeArg k true parts[0]!.toNat! parts[1]!.toNat!} a h1 h2)"
      else
        let parts := (n.drop 4).toString.splitOn "_"
        if grow then s!"fun a h1 h2 => hrd a ({rangeArg k false parts[0]!.toNat! parts[1]!.toNat!} a h1 h2)"
        else s!"fun a h1 h2 => (hrd a).trans ({rangeArg k false parts[0]!.toNat! parts[1]!.toNat!} a h1 h2)"
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
    let fproofs : List String := if !frame then [] else
      ["fun a ha => (hfr a (right_of_and ha)).trans (h.fr a (left_of_and ha))"] ++
      (if hasGrow then
        (if grow then ["fun a ha => (hrdA a ha).trans (h.rdA a ha)", "fun a ha => hrd a (h.rdm a ha)", "fun a ha => hwr a (h.wrm a ha)"]
         else ["fun a ha => (hrd a).trans (h.rdA a ha)", "fun a ha => (hrd a).trans (h.rdm a ha)", "fun a ha => (hwr a).trans (h.wrm a ha)"])
       else ["fun a => (hrd a).trans (h.rdq a)", "fun a => (hwr a).trans (h.wrq a)"]) ++
      unch.map (fun j => match regC.findIdx? (·.1 == j) with
        | some q => s!"r{q}.trans h.uk{j}" | none => "sorryNoUk")
    let proofs := proofs ++ fproofs
    let stepArgs := " ".intercalate ((if hasHost then ["henv", "hpar"] else []) ++ (if hasGrow then ["h.hhp"] else []) ++ ivars.flatMap (fun v => [v, s!"h{v}"]) ++ binders.map (argOf ·.1))
    sx := sx ++ s!"
/-- **Cut {k} to cut {k + 1}**: from the state `St{k}`, the steps reach `St{k + 1}`. -/
theorem run (p : ByteArray) (P : Program) {hasC} (env : {envT}) (ω : Regs) (μ : Memory)
    (x : {ctxT}){envB} {varBinders}{fpB} (h : St{k} {" ".intercalate vars}{fp} ω μ) :
    ∃ ω' μ', FreeStepsH p ({contr}) {info.pcA} ω μ x {info.pcB} ω' μ' x {info.B - info.A} ∧ St{k + 1} {" ".intercalate vars}{fp} ω' μ' := by
  obtain ⟨ω', μ', hrun, {pat rNames}, {pat mNames}, {if sNames.isEmpty then "" else pat sNames ++ ", "}hfr, hrd, hwr{if grow then ", hrdA" else ""}{if hasGrow then ", hhp'" else ""}⟩ :=
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

open PVM JAM {codeOpen}

set_option maxRecDepth 100000

/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**: the segments `S0` … `S{nseg - 1}`, composed. -/
theorem chain (p : ByteArray) (P : Program) {hasC} (env : {envT}) (ω : Regs) (μ : Memory)
    (x : {ctxT}){envB} {varBinders}{fpB} (h : St0 {" ".intercalate vars}{fp} ω μ) :
    ∃ ω' μ', FreeStepsH p ({contr}) {infos[0]!.pcA} ω μ x {infos[nseg - 1]!.pcB} ω' μ' x {bs[nseg]! - bs[0]!} ∧ St{nseg} {" ".intercalate vars}{fp} ω' μ' := by
"
  let mut cw := "ω"; let mut cm := "μ"; let mut ch' := "h"
  for k in [0:nseg] do
    ch := ch ++ s!"  obtain ⟨ω{k+1}, μ{k+1}, run{k+1}, h{k+1}⟩ := S{k}.run p P env {cw} {cm} x{envA} {varArgs}{fp} {ch'}\n"
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
    else [(s!"hN.{n}", (((t.replace "ω[" "ω'[").replace "μ." "μ'.").replace "HeapPages μ " "HeapPages μ' "))]
  ch := ch ++ s!"
/-- **Steps {bs[0]!} … {bs[nseg]! - 1} after pc {joinPc}**, from the facts the path reads before writing them. -/
theorem run (p : ByteArray) (P : Program) {hasC} (env : {envT}) (ω : Regs) (μ : Memory)
    (x : {ctxT}){envB}"
  for v in vars do ch := ch ++ s!"\n    {varBinder cx.svc.lBound v cx.sBound cx.vBounds}"
  for (n, t) in pre0 do ch := ch ++ s!"\n    ({n} : {t})"
  let startArgs := (if pre0.isEmpty && !frame then ["trivial"] else pre0.map (·.1)) ++
    (if frame then (if hasGrow then ["fun _ _ => rfl", "fun _ _ => rfl", "fun _ h => h", "fun _ h => h"]
      else ["fun _ _ => rfl", "fun _ => rfl", "fun _ => rfl"]) ++ unch.map (fun _ => "rfl") else [])
  if !frame then
    ch := ch ++ s!"\n    : ∃ ω' μ', FreeStepsH p ({contr}) {infos[0]!.pcA} ω μ x {infos[nseg - 1]!.pcB} ω' μ' x {bs[nseg]! - bs[0]!} ∧\n      " ++
      (if concl.isEmpty then "True" else " ∧ ".intercalate (concl.map (·.2))) ++ " := by"
    ch := ch ++ s!"\n  obtain ⟨ω', μ', hrun, hN⟩ :=\n    chain p P env ω μ x{envA} {varArgs} ⟨{", ".intercalate startArgs}⟩"
    ch := ch ++ s!"\n  exact ⟨ω', μ', hrun, {", ".intercalate (concl.map (·.1))}⟩\n\nend Services.{NS}.{name}\n"
  else
    -- as `seg` states it: the registers and live octets it leaves, its frame, unchanged access
    let regC := whole.regPost.map (fun (j, v) =>
      match v with
      | some v => (s!"ω'[{j}] = UInt64.ofNat {v}", s!"hN.hreg{j}")
      | none => (s!"ω'[{j}] = ω[{j}]", s!"hN.uk{j}")) ++
      whole.symPost.map fun (j, v) => (s!"ω'[{j}] = UInt64.ofNat {v}", s!"hN.hreg{j}")
    let memC := whole.memPost.map fun (a, v) =>
      match runAt nseg a with
      | some (c, m, j) => (s!"μ'.read {a} = {v}", s!"(Memory.read_of_readN hN.hm_{c}_{m} {j} (by decide))")
      | none => (s!"μ'.read {a} = {v}", "noRun")
    let symC := whole.symMem.map fun (a, n, e) => (s!"μ'.readN {a} {n} = Num.encodeLE {n} {e}", s!"hN.hbn_{a}_{n}")
    let ww := whole.wr
    let m := ww.length
    let outW := " && ".intercalate (ww.map fun (lo, hi) => s!"!(decide ({lo} ≤ a ∧ a < {hi}))")
    -- ha's conjuncts: the bound, then range i (1-based) of `ww`
    let lefts (n : Nat) (t : String) : String := (List.range n).foldl (fun acc _ => s!"(left_of_and {acc})") t
    let conj (i : Nat) : String := if i == 0 then lefts m "ha" else s!"(right_of_and {lefts (m - i) "ha"})"
    let segProof (k : Nat) : String :=
      let rs := infos[k]!.wr
      rs.foldl (fun acc (lo, hi) =>
        match ww.findIdx? (fun (l, h) => l ≤ lo && hi ≤ h) with
        | some q => s!"(and_true_of {acc} (not_mem_of_not_mem_cover {conj (q + 1)} (by decide) (by decide)))"
        | none => "noCover") (conj 0)
    let cProof := (List.range nseg).foldl (fun acc k => s!"(and_true_of {acc} {segProof k})") (conj 0)
    let grp (xs : List (String × String)) : String × String := match xs with
      | [] => ("True", "trivial")
      | [x] => x
      | xs => (" ∧ ".intercalate (xs.map (·.1)), "⟨" ++ ", ".intercalate (xs.map (·.2)) ++ "⟩")
    let (rT, rP) := grp regC
    let (mT, mP) := grp memC
    let symPart := if symC.isEmpty then ("", "") else
      let (sT, sP) := grp symC
      (s!"\n      ({sT}) ∧", s!"{sP}, ")
    ch := ch ++ s!"\n    : ∃ ω' μ', FreeStepsH p ({contr}) {infos[0]!.pcA} ω μ x {infos[nseg - 1]!.pcB} ω' μ' x {bs[nseg]! - bs[0]!} ∧"
    ch := ch ++ s!"\n      ({rT}) ∧\n      ({mT}) ∧{symPart.1}"
    ch := ch ++ s!"\n      (∀ a, (decide (a < 4294967296){if outW == "" then "" else " && " ++ outW}) = true → μ'.read a = μ.read a) ∧"
    if hasGrow then
      ch := ch ++ "\n      (∀ a, 2147483648 ≤ a → μ'.readable a = μ.readable a) ∧ (∀ a, μ.readable a = true → μ'.readable a = true) ∧"
      ch := ch ++ s!"\n      (∀ a, μ.writable a = true → μ'.writable a = true) ∧ JAM.HeapPages μ' {hA} {hB} {topAt bs[nseg]!} := by"
    else
      ch := ch ++ "\n      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by"
    ch := ch ++ s!"\n  obtain ⟨ω', μ', hrun, hN⟩ :=\n    chain p P env ω μ x{envA} {varArgs} ω μ ⟨{", ".intercalate startArgs}⟩"
    let accP := if hasGrow then "hN.rdA, hN.rdm, hN.wrm, hN.hhp" else "hN.rdq, hN.wrq"
    ch := ch ++ s!"\n  exact ⟨ω', μ', hrun, {rP}, {mP}, {symPart.2}fun a ha => hN.fr a {cProof}, {accP}⟩\n\nend Services.{NS}.{name}\n"
  IO.FS.writeFile s!"Services/{NS}/{name}.lean" ch
  IO.eprintln s!"{nseg} segments; the start state needs registers {sts[0]!.1} and {pre0.length} facts"
  if bsOv.isSome then IO.eprintln s!"cuts moved: steps {bs}"
where
  pat' (xs : List String) : String := match xs with
    | [] => "-" | [x] => x | xs => "⟨" ++ ", ".intercalate xs ++ "⟩"


/-- `cut`, moving cuts where the state cannot be stated (a live value that is input-dependent and
    no variable's expression): such a cut is dropped, joining its two segments, and the analysis
    retried. -/
def mode_cutAuto (cx : Cx) : IO Unit := do
  let opts := cx.args.drop 3
  let nums := (opts.filter fun o => o.all Char.isDigit).map String.toNat!
  let N : Option Nat := (opts.find? (·.startsWith "every=")).map fun e => ((e.drop 6).toString).toNat!
  let mut bs : List Nat := match N with
    | some N =>
      let A := nums[0]!; let B := nums[1]!
      ((List.range ((B - A + N - 1) / N)).map (A + N * ·)) ++ [B]
    | none => nums
  -- the cut that fails, from the error
  let failing (e : IO.Error) : Option Nat :=
    ((toString e).splitOn ":").head?.bind fun h => if h.startsWith "cut " then (h.drop 4).toString.toNat? else none
  -- first, drop the cuts whose state cannot be stated
  let mut moved := false
  let mut ok := false
  for _ in [0:bs.length] do
    try
      mode_cut cx (if moved then some bs else none)
      ok := true
      break
    catch e =>
      match failing e with
      | some k =>
        if k == 0 || k + 1 ≥ bs.length then throw e
        IO.eprintln s!"dropping cut {k} (step {bs[k]!}): {e}"
        bs := bs.eraseIdx k
        moved := true
      | none => throw e
  if !ok then throw (IO.userError "no cuts could be stated")
  -- then split the segments longer than N where a cut inside them can be stated, from the middle out
  let some N := N | return
  let mut changed := true
  let mut noSplit : List (Nat × Nat) := []
  while changed do
    changed := false
    let long := ((List.range (bs.length - 1)).filter fun q =>
      bs[q+1]! - bs[q]! > N && !noSplit.contains (bs[q]!, bs[q+1]!))
    let some q := long.head? | break
    let a := bs[q]!; let b := bs[q+1]!
    let mid := (a + b) / 2
    let cands := ((List.range (b - a)).flatMap fun d => [mid + d, mid - d - 1]).filter fun c => a < c && c < b
    let mut done := false
    for c in cands.eraseDups do
      let bs' := (bs.take (q + 1)) ++ [c] ++ (bs.drop (q + 1))
      try
        mode_cut cx (some bs')
        IO.eprintln s!"split [{a}, {b}) at {c}"
        bs := bs'; done := true; changed := true
        break
      catch _ => pure ()
    if !done then
      noSplit := noSplit ++ [(a, b)]
      changed := true
  -- write the final cuts' files
  mode_cut cx (some bs)
set_option maxHeartbeats 2000000 in
/-- `yclasses`: the payload lengths whose runs visit the same set of pcs (loops collapsed), for
    payloads of k octets 255 (k from a list of lengths up to 2^24), as maximal ranges of the scan. -/
def mode_yclasses (cx : Cx) : IO Unit := do
  let ks : List Nat := (List.range 600) ++ ((List.range 100).map (600 + 50 * ·)) ++
    ((List.range 40).map (5600 + 5000 * ·)) ++ [262144, 1048576, 4194304, 16777000]
  let mut prev : Option (List Nat) := none
  let mut start := 0
  let mut last := 0
  let mut sig := 0
  for k in ks do
    let some t := traceFor cx.code cx.h cx.acct cx.Q cx.c cx.i cx.sid (List.replicate k 255) | continue
    let pcs := (t.toList.map (·.1)).eraseDups.mergeSort
    if prev != some pcs then
      if prev.isSome then IO.println s!"class {sig}: |y| {start} … {last}"
      sig := sig + 1
      prev := some pcs; start := k
    last := k
  IO.println s!"class {sig}: |y| {start} … {last}"


def main (args0 : List String) : IO Unit := do
  -- `--service NAME` first selects the service (default witness)
  let (svc, args) : Svc × List String := match args0 with
    | "--service" :: nm :: rest => ((services.find? (fun s : Svc => s.label == nm)).getD witnessSvc, rest)
    | _ => (witnessSvc, args0)
  -- `seg0` / `segx0` / `cut0`: as `seg` / `segx` / `cut`, for the class of empty payloads
  let mode0 := args.headD "run"
  let empty := mode0 == "seg0" || mode0 == "segx0" || mode0 == "cut0"
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
  -- `WITNESS_INPUT=c,i,s,k` replaces the base input (k octets 255), `c,i,s,k,b,f` with payload
  -- b then k − 1 octets f
  let inp := ((← IO.getEnv "WITNESS_INPUT").getD "").splitOn ","
  let (c, i, sid, y) : Nat × Nat × Nat × List UInt8 := match inp.filterMap String.toNat? with
    | [c, i, s, k] => (c, i, s, List.replicate k 255)
    | [c, i, s, k, b0, f] => (c, i, s, (b0.toUInt8 :: List.replicate (k - 1) f.toUInt8).take k)
    | _ => if empty then svc.emptyBase else svc.base
  -- `WITNESS_PAYLOAD=<hex>` replaces the payload (exploration only)
  let y : List UInt8 := match (← IO.getEnv "WITNESS_PAYLOAD") with
    | some hx => ((List.range (hx.length / 2)).map fun k =>
        ((String.Pos.Raw.extract hx ⟨2 * k⟩ ⟨2 * k + 2⟩).foldl (fun n ch =>
          16 * n + (if ch.isDigit then ch.toNat - 48 else ch.toNat - 87)) 0).toUInt8)
    | none => y
  let pkg := mkPkg h sid (i + 1) (mkItem h sid y)
  let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat sid ++ Codec.var ⟨y.toArray⟩ ++ (Blake2b.hash256 ⟨pkg.encode.toArray⟩).toList).toArray⟩
  let some (_, ω, μ) := standardInit code a | return
  let env := mkEnv code sid i (Std.ExtTreeMap.ofList [(sid, acct)]) pkg
  let (tr, _, _, _, _) := go Q (toHostFn (RefineHost.dispatch env)) 0 1000000000 false ω μ (∅, []) #[] #[] 3000000
  let path := (tr.toList.take n).map (·.1)
  let sbE := ((← IO.getEnv "WITNESS_SBOUND").getD "").splitOn "," |>.filterMap String.toNat?
  let sBound := match sbE with
    | [lo, hi] => s!"{lo} ≤ S ∧ S < {hi}"
    | _ => "S < 4294967296"
  let extraSimp := ((← IO.getEnv "WITNESS_SIMP").getD "").splitOn "," |>.filter (· != "")
  let wild := (← IO.getEnv "WITNESS_WILD") == some "1"
  -- `WITNESS_ACC=1`: the traced run is the accumulate (`traceForAcc`), from `WITNESS_INPUT=t,s,n`
  -- (default t = 100, s = 7, n = 1), passed in the refine shape (t, n, s, [])
  let acc := (← IO.getEnv "WITNESS_ACC") == some "1"
  let (c, i, sid, y, tr) := if !acc then (c, i, sid, y, tr) else
    let (t, s, nI) := match inp.filterMap String.toNat? with
      | [t, s, nI] => (t, s, nI)
      | _ => (100, 7, 1)
    (t, nI, s, [], (traceForAcc code h Q t nI s).getD #[])
  let path := if acc then (tr.toList.take n).map (·.1) else path
  let traceF : Nat → Nat → Nat → List UInt8 → Option (Array (Nat × Regs × Memory)) :=
    if acc then fun t nI s _ => traceForAcc code h Q t nI s
    else fun c2 i2 s2 y2 => traceFor code h acct Q c2 i2 s2 y2
  let vBounds : List (String × String) := ((← IO.getEnv "WITNESS_VBOUND").getD "").splitOn ";" |>.filterMap fun e =>
    match e.splitOn ":" with
    | [v, r] => match (r.splitOn ",").filterMap String.toNat? with
      | [lo, hi] => some (v, s!"{lo} ≤ {v} ∧ {v} < {hi}")
      | _ => none
    | _ => none
  let cx : Cx := { svc, sBound, extraSimp, wild, args, mode0, empty, mode, n, bytes, code, h, acct, jb, P, Q, c, i, sid, y, pkg, a, ω, μ, env, tr, path, acc, traceF, vBounds }
  match mode with
  | "calls" => mode_calls cx
  | "allocck" => mode_allocck cx
  | "div" => mode_div cx
  | "cmp" => mode_cmp cx
  | "vals" => mode_vals cx
  | "valsx" => mode_valsx cx
  | "memcpy" => mode_memcpy cx
  | "post" => mode_post cx
  | "steps" => mode_steps cx
  | "dis" => mode_dis cx
  | "reads" => mode_reads cx
  | "seg" => mode_seg cx
  | "cut" => mode_cutAuto cx
  | "yclasses" => mode_yclasses cx
  | "blob" => mode_blob cx
  | _ => mode_codeRun cx
