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
import PVM.Theorems.BlobLimits
import PVM.Theorems.GasFuel
import PVM.Theorems.ExecForms
import PVM.Logic.Free
import PVM.Logic.Host
import PVM.Logic.Invariant
import PVM.Logic.Det
import PVM.Logic.Dead7
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
import PVM.SymExec.Loop

/-!
# An executable model of the JAM PVM (Gray Paper v0.8.1, Appendix A)

* `PVM.Blob`     — deblob, $\mathfrak{v}_{\text{blob}}$, $\mathfrak{v}_{\text{inst}}$, skip, $\zeta$, $\varpi$, $\mathfrak{L}$ (§A.1–A.3)
* `PVM.Instr`    — typed instructions and decoding (§A.5 operand definitions)
* `PVM.Exec`     — the mutation tables (§A.4–A.5)
* `PVM.Memory`   — RAM and $\varepsilon^\mu$ (eq. `pvmmemory`, §A.4)
* `PVM.Gas`      — the gas cost model $\varrho^\Delta$ (§A.9–A.10)
* `PVM.Machine`  — $\Psi_1$ and $\Psi$ (§A.1, §A.4)
* `PVM.Invocation` — $\Psi_H$, $Y$ and $\Psi_M$ (§A.6–A.8)
* `PVM.Fast`     — fast compiled forms of $\Psi$, $\Psi_H$, $\Psi_M$, the ALU, the parsers, $Y$ and $\varrho^\Delta$, each proved equal to the spec and used by compiled code (`@[csimp]`; `docs/fast-paths.md`)
* `PVM.Tables`   — generated from the paper's LaTeX: opcodes, $T$, the gas cost table
* `PVM.Theorems` — host calls and their ids, termination and $\Psi$'s and $\Psi_H$'s equations, decoding, blobs,
  the gas simulation's fuel (`GasFuel`) and the unreachable defaults of $\Psi_1$ (`ExecForms`)
-/
