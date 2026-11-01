import PVM.Basic
import PVM.Tables
import PVM.Blob
import PVM.Instr
import PVM.Memory
import PVM.Exec
import PVM.Gas
import PVM.Machine
import PVM.Theorems.Blob
import PVM.Theorems.Decode
import PVM.Theorems.Host
import PVM.Theorems.Termination

/-!
# An executable model of the JAM PVM (Gray Paper v0.8.0, Appendix A)

* `PVM.Blob`     — deblob, 𝔳_blob, 𝔳_inst, skip, ζ, ϖ, 𝔏 (§A.1–A.3)
* `PVM.Instr`    — typed instructions and decoding (§A.5 operand definitions)
* `PVM.Exec`     — the mutation tables (§A.4–A.5)
* `PVM.Memory`   — RAM and ε^μ (eq. `pvmmemory`, §A.4)
* `PVM.Gas`      — the gas cost model ϱ^Δ (§A.9–A.10)
* `PVM.Machine`  — Ψ₁ and Ψ (§A.1, §A.4)
* `PVM.Tables`   — generated from the paper's LaTeX: opcodes, T, the gas cost table
* `PVM.Theorems` — host calls, termination and Ψ's equation, decoding, blobs
-/
