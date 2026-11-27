import Tests.Vectors

/-!
# `pvmbench`: a long-running Ψ_H workload, for timing the fast interpreter

Runs the program of a gas-test vector (`vendor/jamtestvectors/pvm/gas-tests/*.json`) from ı = 0
with every page above 2^16 writable, a stack pointer near the top, and a host function that
continues at once. Prints the exit, the gas left and a digest of registers and memory, so two
builds can be compared for identical results.
-/

open PVM PVM.Tests Lean

def digest (r : HostRunResult Nat) : Nat := Id.run do
  let mut h : UInt64 := 1469598103934665603
  for v in r.regs.toArray do h := (h ^^^ v) * 1099511628211
  for (a, v) in r.mem.bytes.toList do
    h := (h ^^^ UInt64.ofNat a) * 1099511628211
    h := (h ^^^ v.toUInt64) * 1099511628211
  return h.toNat

def main (args : List String) : IO UInt32 := do
  let path := args.headD "vendor/jamtestvectors/pvm/gas-tests/prime-sieve.json"
  let gas := (args.getD 1 "100000000").toNat!
  let j ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let p ← IO.ofExcept (do bytesOf (← field j "program"))
  let μ := Memory.empty.setPages 16 (2 ^ 20 - 32) (some .write)
  let ω : Regs := (Vector.replicate 13 0).set 0 0xFFFF0000 |>.set 1 0xFEFE0000
  let f : HostFn Nat := fun _ g ω μ n => { status := .cont, gas := g, regs := ω, mem := μ, ctx := n + 1 }
  let t0 ← IO.monoMsNow
  let r := psiH p 0 (UInt64.ofNat gas) ω μ f 0
  let s := match r.status with
    | .halt => "halt" | .panic => "panic" | .oog => "oog" | .fault a => s!"fault {a}"
    | .host h => s!"host {h}" | .cont => "cont"
  IO.println s!"{path}: {s} pc {r.pc} gas used {gas - r.gas.toNat} host calls {r.ctx} digest {digest r}"
  let t1 ← IO.monoMsNow
  IO.println s!"time {t1 - t0} ms"
  return 0
