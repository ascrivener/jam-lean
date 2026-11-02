import Lake
open Lake DSL System

/-! Build configuration for the Lean model of the JAM PVM and Appendix B (Gray Paper v0.8.0).

* `lake build`           builds the model (`PVM`) and its theorems.
* `lake build pvmtest`   builds and runs the vector runner over `vendor/jamtestvectors/pvm/programs`.
* `lake build gascheck`  builds and runs the block gas checker over `programs/` and `gas-tests/`.
* `lake build Tests.Invocation`  kernel-checks the Ψ_H / Y / Ψ_M examples.
* `lake build Tests.LogicExample`  the worked for-all-inputs proof.

The vectors are fetched at the pinned commit by `scripts/fetch-vectors.sh`. -/

package «jam-lean» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib PVM

/-- Appendix B and the protocol terms it needs, built on `PVM`. -/
@[default_target]
lean_lib JAM

/-- Results about specific services' deployed code, built on `JAM`. -/
@[default_target]
lean_lib Services

/-- Shared helpers of the test executables. -/
lean_lib Tests where
  globs := #[.one `Tests.Vectors, .one `Tests.Invocation, .one `Tests.LogicExample,
    .one `Tests.Blake2bTest, .one `Tests.HostGeneralTest, .one `Tests.JamJson,
    .one `Tests.KeccakTest, .one `Tests.RefineTest]

lean_exe «pvmtest-exe» where
  root := `Tests.PvmTest
  exeName := "pvmtest"

lean_exe «codectest-exe» where
  root := `Tests.CodecTest
  exeName := "codectest"

lean_exe «acctest-exe» where
  root := `Tests.AccumulateTest
  exeName := "acctest"

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

/-- The Gray Paper v0.8.0 JAM vectors (davxy/jam-test-vectors `v0.8.0`), fetched by
    `scripts/fetch-jam-vectors.sh`. -/
def jamVectorDir (pkg : Package) : FilePath := pkg.dir / "vendor" / "jam-test-vectors"

/-- Encode the work-package family and compare with the codec vectors. -/
target codectest pkg : Unit := do
  runOnVectors `«codectest-exe» #[(jamVectorDir pkg / "codec" / "tiny").toString]

/-- Run the accumulation STF on every accumulate vector (tiny). -/
target acctest pkg : Unit := do
  runOnVectors `«acctest-exe» #[(jamVectorDir pkg / "stf" / "accumulate" / "tiny").toString]

/-- Compare the model's ϖ^Δ against every block cost in `programs/` and `gas-tests/`. -/
target gascheck pkg : Unit := do
  runOnVectors `«gascheck-exe»
    #[(vectorDir pkg / "programs").toString, (vectorDir pkg / "gas-tests").toString]

lean_exe «witnesscheck-exe» where
  root := `Tests.WitnessCheck
  exeName := "witnesscheck"

/-- Check that the vendored witness blob names only `Services.Witness.ids`. -/
target witnesscheck pkg : Unit := do
  runOnVectors `«witnesscheck-exe» #[(pkg.dir / "services" / "witness" / "witness-service.jam").toString]

/-- Development aid: `lake exe pvmtrace <vector.json> [steps]`. -/
lean_exe pvmtrace where
  root := `Tests.Trace
