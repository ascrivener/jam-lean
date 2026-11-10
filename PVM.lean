import PVM.Basic
import PVM.Tables
import PVM.Blob
import PVM.Instr
import PVM.Memory
import PVM.Exec
import PVM.Gas
import PVM.Machine
import PVM.Fast
import PVM.Invocation
import PVM.Theorems.Blob
import PVM.Theorems.Decode
import PVM.Theorems.Host
import PVM.Theorems.Termination
import PVM.Theorems.Invocation
import PVM.Theorems.HostIds
import PVM.Theorems.InitMem
import PVM.Logic.Free
import PVM.Logic.Host
import PVM.Logic.Invariant
import PVM.Logic.Det
import PVM.Logic.Code
import PVM.Logic.Attr
import PVM.Logic.Bits
import PVM.Logic.Steps
import PVM.Logic.Chase
import PVM.Logic.StepsH
import PVM.Logic.Words
import PVM.Logic.Go
import PVM.Logic.GasBound
import PVM.SymExec.Trace

/-!
# An executable model of the JAM PVM (Gray Paper v0.8.0, Appendix A)

* `PVM.Blob`     — deblob, 𝔳_blob, 𝔳_inst, skip, ζ, ϖ, 𝔏 (§A.1–A.3)
* `PVM.Instr`    — typed instructions and decoding (§A.5 operand definitions)
* `PVM.Exec`     — the mutation tables (§A.4–A.5)
* `PVM.Memory`   — RAM and ε^μ (eq. `pvmmemory`, §A.4)
* `PVM.Gas`      — the gas cost model ϱ^Δ (§A.9–A.10)
* `PVM.Machine`  — Ψ₁ and Ψ (§A.1, §A.4)
* `PVM.Invocation` — Ψ_H, Y and Ψ_M (§A.6–A.8)
* `PVM.Tables`   — generated from the paper's LaTeX: opcodes, T, the gas cost table
* `PVM.Theorems` — host calls and their ids, termination and Ψ's and Ψ_H's equations, decoding, blobs
-/
