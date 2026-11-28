import Tests.Examples.Basic
import Tests.Examples.Pilot
import Tests.Examples.STF


/-!
# Worked examples for the companion book (`lake build examples-exe`)

Runs selected model functions on chosen test vectors and writes what they compute, as JSON, to
`docs/site/examples/<name>.json`. The book's `{example "<name>"}` block (`docs/site/Companion/Example.lean`)
renders each file as a box: which vector and parameters, the inputs, and a table of values before →
after. Every computed (after) value is the model's own result; before and input values are read
from the vector. The generator fails unless the vector's expected output matches. It uses the comparison the vector's
test suite uses (the harnesses in `Tests.SafroleHarness`, `Tests.AccumulateHarness` and `Tests.PvmHarness`).

```
lake build examples-exe && .lake/build/bin/examples [OUT_DIR]   # default docs/site/examples
```

CI regenerates the files and fails when they differ from the committed ones
(`scripts/check-examples.sh`), so the book's examples always show what the current model computes.

The vectors: davxy/jam-test-vectors `v0.8.0` (`scripts/fetch-jam-vectors.sh`), run with the tiny
chain the tests use (`JAM.V080.tiny080`), and koute/jamtestvectors `pvm/programs`
(`scripts/fetch-vectors.sh`). The `Example` type and the formatting helpers are in `Tests/Examples/Basic.lean`; the generators
are in topic modules (`Tests/Examples/Pilot.lean`, …). To add examples, write functions returning an
`Example` in a topic module and register its list in `examples` below (see `docs/site/README.md`,
"Worked examples").
-/

namespace JAM.Tests.Examples

/-- Every example, one list per topic module (`Tests/Examples/*.lean`). A new topic module adds
    its import above and its list here. -/
def examples : List (IO Example) := List.flatten [
  pilot,
  stf]

end JAM.Tests.Examples

open JAM.Tests.Examples in
def main (args : List String) : IO UInt32 := do
  let out : System.FilePath := args.headD "docs/site/examples"
  IO.FS.createDirAll out
  for mk in examples do
    let e ← mk
    let file := out / s!"{e.name}.json"
    IO.FS.writeFile file ((Lean.toJson e).pretty 100 ++ "\n")
    IO.println s!"examples: wrote {file}"
  return 0
