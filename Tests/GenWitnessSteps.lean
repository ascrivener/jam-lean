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

/-- Function bodies whose code facts are emitted in full, for summaries: `memcpy` and the SDK's
    `u32` decoder. -/
def fnRanges : List (Nat × Nat) := [(186740, 187150), (184570, 184870)]

def main (args : List String) : IO Unit := do
  let mode := args.headD "run"
  let n := (args.getD 1 "39").toNat!
  let bytes ← IO.FS.readBinFile "services/witness/witness-service.jam"
  let some code := splitMetadata bytes.toList | return
  let h := (Blake2b.hash256 bytes).toList
  let acct : ServiceAccount := { codeHash := h, balance := 0, minAccGas := 0, minMemoGas := 0 }
  let some jb := JamBlob.parse? code | return
  let some P := Blob.parse? jb.code | return
  let Q := P.prepare
  let (c, i, sid, y) := (3, 0, 7, [255])
  let pkg := mkPkg h sid (i + 1) (mkItem h sid y)
  let a : ByteArray := ⟨(Codec.nat c ++ Codec.nat i ++ Codec.nat sid ++ Codec.var ⟨y.toArray⟩ ++ (Blake2b.hash256 ⟨pkg.encode.toArray⟩).toList).toArray⟩
  let some (_, ω, μ) := standardInit code a | return
  let env := mkEnv code sid i (Std.ExtTreeMap.ofList [(sid, acct)]) pkg
  let (tr, _, _, _, _) := go Q (toHostFn (RefineHost.dispatch env)) 0 1000000000 false ω μ (∅, []) #[] #[] 3000000
  let path := (tr.toList.take n).map (·.1)
  if mode == "calls" then
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
