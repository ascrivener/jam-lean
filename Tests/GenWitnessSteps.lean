import JAM
open PVM JAM

def go (Q : Prepared) (f : HostFn RefineCtx) (i : Nat) (gas : UInt64) (ch : Bool)
    (ω : Regs) (μ : Memory) (x : RefineCtx) (acc : Array (Nat × Regs)) (hosts : Array Nat) :
    Nat → Array (Nat × Regs) × Array Nat × Status × Regs × Memory
  | 0 => (acc, hosts, .panic, ω, μ)
  | n + 1 =>
    if !(Q.valid && Q.prog.vInst i) then (acc, hosts, .panic, ω, μ) else
    let r := Q.step i gas ch ω μ
    let acc := acc.push (i, ω)
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
  params := .tiny
  service := sid
  accounts := d
  lookupSlot := 10
  code := code
  exportOffset := 0
  fetch := { params := .tiny, package := some pkg, entropy := some (List.replicate 32 0),
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

def main (args : List String) : IO Unit := do
  let n := (args.headD "39").toNat!
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
  let mut facts : Array String := #[]
  let mut lemmas : Array String := #[]
  let mut seen : List Nat := []
  for (pc, regs) in tr.toList.take n do
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
  let factsL := facts.toList.eraseDups
  let idxOf (f : String) : Nat := (factsL.idxOf f)
  -- lemmas, regenerated from the fact strings with their indices
  let mut lemmasL : Array String := #[]
  for (pc, _) in tr.toList.take n do
    let some ins := P.decode pc | continue
    let fi := s!".instr {pc} ({leanInstr ins}) {P.next pc}"
    let k := idxOf fi
    let l := s!"theorem d_{pc} \{p : ByteArray} \{P : Program} [h : HasCode p P] : deblob p {pc} = some P ∧ P.decode {pc} = some ({leanInstr ins}) ∧ P.next {pc} = {P.next pc} :=\n  h.ok.instr (show CodeFact.instr {pc} ({leanInstr ins}) {P.next pc} ∈ facts from List.getElem_mem (l := facts) (n := {k}) (by decide))\n\n@[pvm_code] theorem nx_{pc} \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.next {pc} = {P.next pc} := (d_{pc} (p := p)).2.2"
    if !lemmasL.contains l then lemmasL := lemmasL.push l
  for f in factsL do
    if f.startsWith ".blockStart " then
      let parts := (f.drop 12).toString.splitOn " "
      let t := parts[0]!; let b := parts[1]!
      lemmasL := lemmasL.push s!"@[pvm_code] theorem bs_{t} \{p : ByteArray} \{P : Program} [h : HasCode p P] : P.isBlockStart {t} = {b} := h.ok.blockStart (show CodeFact.blockStart {t} {b} ∈ facts from List.getElem_mem (l := facts) (n := {idxOf f}) (by decide))"
  let endPc := (tr.toList.take n).getLast!.1
  let endPc := P.next endPc
  IO.println s!"/-
  GENERATED by `lake exe genwitnesssteps {n}` from services/witness/witness-service.jam.
  Do not edit by hand.
-/
import PVM.Logic.Steps

/-!
# The first {n} steps of witness's refine, proved symbolically

From Y's initial registers, with the argument length `L` arbitrary and memory arbitrary except
that the stack is writable, witness's code runs {n} gas-free steps from its entry point to the
first host call (the `ecalli 2` at {endPc}), assuming only the code facts `facts`, which
`checkCode` checks against the blob (`lake build witnesscheck`).

Each step is proved by `pvm_simp`; nothing here is evaluated by compiled code.
-/

namespace Services.Witness.Prefix

open PVM
"
  IO.println ("/-- The code facts these steps use. -/\ndef facts : List CodeFact := [\n  " ++ ",\n  ".intercalate factsL ++ "]\n")
  IO.println "/-- The blob `p` deblobs to `P`, and `facts` hold of it. -/\nclass HasCode (p : outParam ByteArray) (P : Program) : Prop where\n  ok : CodeOk p facts P\n"
  IO.println ("\n\n".intercalate lemmasL.toList)
  IO.println s!"
/-- Y's registers (GP eq. `registers`) for an argument of length `L`. -/
def initRegs (L : Nat) : Regs :=
  Vector.ofFn fun k => UInt64.ofNat (([{", ".intercalate ((ω.toList.map (·.toNat)).set 8 0 |>.map toString)}] : List Nat).set 8 L |>.getD k.val 0)

/-- The stack (2^32 − 2𝖹_Z − 𝖹_I − 𝖹_P·⌈s/𝖹_P⌉ to 2^32 − 2𝖹_Z − 𝖹_I) is writable. -/
def StackWritable (μ : Memory) : Prop :=
  ∀ a, {ω[1]!.toNat} - {jb.stackSize} ≤ a → a < {ω[1]!.toNat} → μ.writable a = true

theorem prefix_run (p : ByteArray) (P : Program) [HasCode p P] (μ : Memory) (L : Nat)
    (hw : StackWritable μ) : ∃ ω' μ', FreeSteps p 0 (initRegs L) μ {endPc} ω' μ' := by
  have hr : ∀ a, {ω[1]!.toNat} - {jb.stackSize} ≤ a → a < {ω[1]!.toNat} → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  unfold StackWritable at hw
  refine ⟨?ω, ?μ, ?h⟩
  case h =>"
  for pc in path do
    IO.println s!"    apply FreeSteps.step_decode (d_{pc} (p := p) (P := P))\n    · pvm_simp [hw, hr, initRegs, List.set_cons_succ, List.set_cons_zero]"
  IO.println s!"    exact FreeSteps.refl

/-- **The first {n} steps of witness's refine.** For any blob that passes `checkCode p facts`
    (the deployed witness blob does: `lake build witnesscheck`), the gas-free machine runs from the
    entry point to the first host call, for every argument length and every memory whose stack is
    writable. -/
theorem prefix_of_checkCode (p : ByteArray) (hc : checkCode p facts = true) :
    ∃ P, deblob p 0 = some P ∧ ∀ μ L, StackWritable μ →
      ∃ ω' μ', FreeSteps p 0 (initRegs L) μ {endPc} ω' μ' := by
  obtain ⟨P, hP⟩ := checkCode_sound hc
  haveI : HasCode p P := ⟨hP⟩
  exact ⟨P, (d_0 (p := p)).1, fun μ L hw => prefix_run p P μ L hw⟩

end Services.Witness.Prefix"
