import Lake
open Lake DSL

/-! The jam-lean documentation site (Adam, 2026-11-27): API reference pages built by doc-gen4 for
the `PVM`, `JAM` and `JamCrypto` libraries.

This is a separate Lake package: the model, JamCrypto and the executables stay core+Std, and the
root lakefile never resolves doc-gen4. Nothing outside `docs/site/` imports anything here.

```
cd docs/site
lake build PVM:docs JAM:docs JamCrypto:docs   # HTML in .lake/build/doc
```

`scripts/build-site.sh` assembles the Pages site (`_site/api/`). -/

package «jam-docs»

require «jam-lean» from "../.."

/-- doc-gen4 at the tag matching the toolchain (leanprover/lean4:v4.36.0-rc1). -/
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.36.0-rc1"
