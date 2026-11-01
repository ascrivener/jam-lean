import Tests.Vectors

/-! Development aid: print every step of a vector's first run. -/

namespace PVM.Tests
open Lean (Json)

def traceVector (j : Json) (limit : Nat) : IO Unit := do
  let .ok p := programOf j | throw <| IO.userError "bad program"
  let some P := Blob.parse? p | throw <| IO.userError "parse failed"
  let .ok pc0 := natField j "initial-pc" | throw <| IO.userError "pc"
  let .ok g0 := intField j "initial-gas" | throw <| IO.userError "gas"
  let mut regs : Regs := Vector.replicate 13 0
  if let .ok steps := (do (← field j "steps").getArr?) then
    for s in steps do
      if let .ok b := field s "set-reg" then
        if let (.ok k, .ok v) := (natField b "reg", natField b "value") then
          if h : k < 13 then regs := regs.set k (UInt64.ofNat v)
  let mut i := pc0
  let mut gas := UInt64.ofInt g0
  let mut ch := false
  let mut mem : Memory := .empty
  for _ in [0:limit] do
    let ins := P.decode i
    let r := P.step i gas ch regs mem
    IO.println s!"{i}: {repr ins} -> {repr r.status} pc'={r.pc} gas={r.gas} ch={r.charged}"
    IO.println s!"    regs {r.regs.toList}"
    if r.status != .cont then return
    i := r.pc; gas := r.gas; ch := r.charged; regs := r.regs; mem := r.mem

end PVM.Tests

open PVM.Tests in
def main (args : List String) : IO Unit := do
  let f := args.headD ""
  traceVector (← readJson f) ((args.getD 1 "200").toNat!)
