import Tests.Vectors

/-!
# Vector runner (`lake build pvmtest`)

Runs every vector in `programs/`: each `run` step calls `PVM.psi` with the gas charged by the
model's own ϱ^Δ, and each `assert` step checks status, registers, pc, gas, page-fault address,
host-call number and memory.

Resuming follows the paper: after h̵ the next run starts at ı + 1 + skip(ı) (as in Ψ_H, GP
§A.6); after F or ∞ it restarts at ı. The charged flag ϱ̃ returned by Ψ is carried over.

The vectors report as `pc` the instruction that caused the exit, also on ∎ and ☇ where Ψ
itself returns 0; we compare it against `Result.exitPc` and keep Ψ's own value in `Result.pc`.
-/

namespace PVM.Tests

open Lean (Json)

/-- The machine state carried between steps of a vector. -/
structure VmState where
  pc : Nat
  gas : UInt64
  charged : Bool := false
  regs : Regs := Vector.replicate 13 0
  mem : Memory := .empty
  last : Option Result := none

/-- The vector's name for an exit status. -/
def statusName : Status → String
  | .cont => "continue"
  | .halt => "halt"
  | .panic => "panic"
  | .oog => "out-of-gas"
  | .fault _ => "page-fault"
  | .host _ => "ecalli"

/-- Compare memory: every listed chunk must match, and every non-zero octet of the model's
    memory must lie in a listed chunk. -/
def checkMemory (μ : Memory) (chunks : Array Json) : Except String Unit := do
  let mut covered : Std.HashSet Nat := {}
  for c in chunks do
    let a ← natField c "address"
    let bs ← bytesOf (← field c "contents")
    for k in [0:bs.size] do
      covered := covered.insert (a + k)
      let got := μ.read (a + k)
      if got != bs[k]! then die s!"memory[{a + k}] = {got}, expected {bs[k]!}"
  for (addr, v) in μ.bytes.toList do
    if v != 0 && !covered.contains addr then die s!"unexpected non-zero memory[{addr}] = {v}"

/-- Check an `assert` step against the last result. -/
def checkAssert (s : VmState) (a : Json) : Except String Unit := do
  let some r := s.last | die "assert before run"
  let st ← (← field a "status").getStr?
  if statusName r.status != st then die s!"status {statusName r.status}, expected {st}"
  let regs ← natArray (← field a "regs")
  for k in [0:13] do
    if (r.regs[k]!).toNat != regs[k]! then die s!"ω[{k}] = {r.regs[k]!}, expected {regs[k]!}"
  let pc ← natField a "pc"
  if r.exitPc != pc then die s!"pc {r.exitPc}, expected {pc}"
  let gas ← intField a "gas"
  if (r.gas.toNat : Int) != gas then die s!"gas {r.gas}, expected {gas}"
  if let .ok pf := natField a "page-fault-address" then
    match r.status with
    | .fault addr => if addr.toNat != pf then die s!"fault address {addr}, expected {pf}"
    | _ => die "expected a page fault"
  if let .ok h := natField a "hostcall" then
    match r.status with
    | .host id => if id.toNat != h then die s!"host call {id}, expected {h}"
    | _ => die "expected a host call"
  checkMemory r.mem (← (← field a "memory").getArr?)

/-- Run one vector. -/
def runVector (j : Json) : Except String Unit := do
  let p ← programOf j
  let mut s : VmState := { pc := ← natField j "initial-pc", gas := UInt64.ofInt (← intField j "initial-gas") }
  for stepJ in ← (← field j "steps").getArr? do
    let .obj kvs := stepJ | die "bad step"
    let some (kind, body) := kvs.toArray[0]? | die "empty step"
    match kind with
    | "run" =>
      let r := psi p s.pc s.gas s.charged s.regs s.mem
      let pc := match r.status with
        | .host _ => ((Blob.parse? p).map (·.next r.exitPc)).getD r.exitPc
        | _ => r.exitPc
      s := { s with pc, gas := r.gas, charged := r.charged, regs := r.regs, mem := r.mem, last := some r }
    | "assert" => checkAssert s body
    | "map" =>
      let a ← natField body "address"
      let len ← natField body "length"
      let w ← (← field body "is-writable").getBool?
      if a % pageSize != 0 || len % pageSize != 0 then die "unaligned map"
      s := { s with mem := s.mem.setPages (a / pageSize) (len / pageSize) (some (if w then .write else .read)) }
    | "write" =>
      let a ← natField body "address"
      let bs ← bytesOf (← field body "contents")
      s := { s with mem := s.mem.writeN a bs.toList }
    | "set-reg" =>
      let k ← natField body "reg"
      let v ← natField body "value"
      if h : k < 13 then s := { s with regs := s.regs.set k (UInt64.ofNat v) } else die "bad register"
    | other => die s!"unknown step {other}"

end PVM.Tests

open PVM.Tests in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "vendor/jamtestvectors/pvm/programs"
  let files ← jsonFiles dir
  let mut failed : Array String := #[]
  for f in files do
    let j ← readJson f
    match runVector j with
    | .ok () => pure ()
    | .error e =>
      IO.eprintln s!"FAIL {f.fileName.getD ""}: {e}"
      failed := failed.push (f.fileName.getD "")
  IO.println s!"pvmtest: {files.size - failed.size} of {files.size} vectors pass"
  return if failed.isEmpty && files.size > 0 then 0 else 1
