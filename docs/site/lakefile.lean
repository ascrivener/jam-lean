import Lake
open Lake DSL

/-! The jam-lean documentation site (Adam, 2026-11-27):

* API reference pages built by doc-gen4 for the `PVM`, `JAM` and `JamCrypto` libraries;
* *A companion to the Gray Paper*, a Verso book (`Companion`) that sets the paper's equations next
  to the Lean definitions, read from the model's source, and the theorems about them.

This is a separate Lake package: the model, JamCrypto and the executables stay core+Std, and the
root lakefile never resolves doc-gen4. Nothing outside `docs/site/` imports anything here.

```
cd docs/site
lake build PVM:docs JAM:docs JamCrypto:docs   # HTML in .lake/build/doc
lake exe companion --output _book              # the companion's HTML in _book/
```

`scripts/build-site.sh` assembles the Pages site (`_site/api/`). -/

package «jam-docs»

require «jam-lean» from "../.."

/-- doc-gen4 at the tag matching the toolchain (leanprover/lean4:v4.36.0-rc1). -/
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.36.0-rc1"

/-- Verso at the tag matching the toolchain. -/
require verso from git "https://github.com/leanprover/verso" @ "v4.36.0-rc1-patch1"

/-- *A companion to the Gray Paper*: the chapters, in the order of GP v0.8.1's sections. -/
lean_lib Companion where
  leanOptions := #[⟨`autoImplicit, false⟩]
  extraDepTargets := #[`modelHighlights]

/-- Renders the companion to HTML: `lake exe companion --output DIR`. -/
lean_exe companion where
  root := `CompanionMain

/-- SubVerso's semantically highlighted JSON (the `highlighted` module facet, from the `subverso`
    package Verso requires) for the model modules the companion quotes with `{leanSource}`. -/
target modelHighlights : Unit := do
  -- Every module a chapter quotes with `{leanSource}`: a missing one fails the book's build.
  let mods := #[`JAM.Safrole, `JAM.Disputes, `JAM.Assurances, `JAM.Reports, `JAM.Statistics,
    `JAM.Shuffle, `PVM.Machine, `PVM.Gas, `PVM.Memory,
    `JAM.Work, `JAM.Refine, `JAM.Segments, `JAM.Guarantee, `JAM.Auditing, `JAM.BestChain,
    `JAM.Theorems.BestChain]
  let jobs ← mods.mapM fun m => do
    let some mod ← findModule? m | error s!"modelHighlights: no module {m}"
    fetch <| mod.facet `highlighted
  return (Job.mixArray jobs).map fun _ => ()
