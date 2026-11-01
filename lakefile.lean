import Lake
open Lake DSL System

/-! Build configuration for the executable Lean model of the JAM PVM (Gray Paper v0.8.0).

* `lake build`           builds the model (`PVM`) and its theorems.
* `lake build pvmtest`   builds and runs the vector runner over `vendor/jamtestvectors/pvm/programs`.
* `lake build gascheck`  builds and runs the block gas checker over `programs/` and `gas-tests/`.
* `lake build Tests.Invocation`  kernel-checks the Ψ_H / Y / Ψ_M examples.

The vectors are fetched at the pinned commit by `scripts/fetch-vectors.sh`. -/

package «pvm-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PVM

/-- Shared helpers of the test executables. -/
lean_lib Tests where
  globs := #[.one `Tests.Vectors, .one `Tests.Invocation]

lean_exe «pvmtest-exe» where
  root := `Tests.PvmTest
  exeName := "pvmtest"

lean_exe «gascheck-exe» where
  root := `Tests.GasCheck
  exeName := "gascheck"

/-- The directory holding the pinned test vectors (`pvm/` of koute/jamtestvectors). -/
def vectorDir (pkg : Package) : FilePath := pkg.dir / "vendor" / "jamtestvectors" / "pvm"

/-- Build and run an executable over the vectors; a non-zero exit fails the build. -/
def runOnVectors (exeName : Lean.Name) (args : Array String) : FetchM (Job Unit) := do
  let some exe ← findLeanExe? exeName | error s!"no executable {exeName}"
  let job ← exe.exe.fetch
  job.mapM fun exeFile => do
    let out ← IO.Process.output { cmd := exeFile.toString, args := args }
    IO.print out.stdout
    IO.eprint out.stderr
    if out.exitCode != 0 then
      error s!"{exeName} failed (exit code {out.exitCode})"

/-- Run every vector in `programs/` (status, registers, pc, gas, page-fault address, memory). -/
target pvmtest pkg : Unit := do
  runOnVectors `«pvmtest-exe» #[(vectorDir pkg / "programs").toString]

/-- Compare the model's ϖ^Δ against every block cost in `programs/` and `gas-tests/`. -/
target gascheck pkg : Unit := do
  runOnVectors `«gascheck-exe»
    #[(vectorDir pkg / "programs").toString, (vectorDir pkg / "gas-tests").toString]

/-- Development aid: `lake exe pvmtrace <vector.json> [steps]`. -/
lean_exe pvmtrace where
  root := `Tests.Trace
