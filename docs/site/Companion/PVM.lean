import VersoManual
import Companion.Source
import Companion.Docstring
import PVM.Machine
import PVM.Theorems.Termination
import PVM.Theorems.GasFuel
import PVM.Theorems.ExecForms

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix A: the PVM's single step" =>
%%%
tag := "pvm"
shortTitle := "A. PVM step"
file := "pvm-step"
%%%

Appendix A of GP v0.8.1 defines the Polkadot Virtual Machine. $`\Psi` runs a program, and each of its
steps is $`\Psi_1`, the single-step transition of §A.4. A step does three things, in this order:

* it charges gas for the current basic block, if the block has not been charged yet;
* it checks the memory the instruction reads and writes ($`\varepsilon^\mu`);
* it applies the instruction's regular execution, given by the mutation tables of §A.5.

This chapter puts each part of the paper's definition next to the model's.

# Ψ₁
%%%
tag := "pvm-step"
%%%

$$`\Psi_1 \colon (\mathfrak{p}, \mathbf{k}, \mathbf{j}, \imath, \varrho, \tilde\varrho, \varphi, \mu) \mapsto (\varepsilon^*, \imath^*, \varrho^*, \tilde\varrho^*, \varphi^*, \mu^*) \qquad \text{(A.7)}`

The result is {api}`PVM.StepResult`, and the function is {api}`PVM.Program.step`. A
{api}`PVM.Program` holds the code $`\mathbf{c}`, the bitmask $`\mathbf{k}` and the jump table $`\mathbf{j}`, so they need not be passed
separately. The paper writes the registers as $`\varphi`; the model's code calls them `ω`.

{leanSource PVM.Program.step}

$`\Psi` calls $`\Psi_1` only at a valid instruction, so in practice the decode always succeeds. The `getD`
default only keeps $`\Psi_1` total, and the following theorem shows it is never reached:

{mathdoc PVM.Program.step_decode}

# The gas stage
%%%
tag := "pvm-gas"
%%%

Gas for a whole basic block is charged before the block's first instruction runs. $`\tilde\varrho` records that
the current block has been paid for:

$$`\left(\varepsilon^{\varrho}, \varrho^*, \tilde\varrho'\right) = \begin{cases} (\blacktriangleright, \varrho, \top) & \text{when } \tilde\varrho = \top \\ (\blacktriangleright, \varrho - \varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)), \top) & \text{otherwise when } \varrho \ge \varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)) \\ (\infty, \varrho, \bot) & \text{otherwise} \end{cases} \qquad \text{(A.8)}`

{leanSource PVM.Program.chargeGas}

The block cost $`\varrho^\Delta` (eq. (A.54), `gascostforblock`) is the number of cycles a simulated out-of-order CPU
needs to retire the whole block, minus 3, and at least 1:

$$`\varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \imath) = \max\left(\mathbf{x}^{\text{final}}_{c} - 3,\, 1\right) \qquad \text{(A.54)}`

$$`\text{where } \mathbf{x}^{\text{final}} = \mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathbf{x}^{\text{init}}),\; \mathbf{x}^{\text{init}} = \left(\imath, 0, 4, 5, (4, 4, 4, 1, 1), []\right)`

{leanSource PVM.Program.blockCost?}

The simulation $`\mathfrak{X}` is run with fuel, because Lean needs every function to terminate. The theorems
below show that the fuel never runs out, and that the total {api}`PVM.Program.blockCost` agrees
with the paper's $`\varrho^\Delta` at every block $`\Psi` charges:

{mathdoc PVM.Sim.run_fuel_eq}

{mathdoc PVM.Program.blockCost_eq_of_deblob}

# Memory exceptions
%%%
tag := "pvm-memory"
%%%

Let $`\mathbf{r}` and $`\mathbf{w}` be the indices that an instruction reads and writes. The memory-access exception is
the following:

$$`\varepsilon^{\mu} = \begin{cases} \blacktriangleright & \text{when } \mathbf{x} = \emptyset \\ \text{☇} & \text{when } \min(\mathbf{x}) \bmod 2^{32} < 2^{16} \\ \Finv \times \mathsf{Z}_P \left\lfloor \min(\mathbf{x}) \bmod 2^{32} \div \mathsf{Z}_P \right\rfloor & \text{otherwise} \end{cases}`

$$`\text{where } \mathbf{x} = \left\{ x \;\middle|\; x \in \mathbf{r} \wedge x \bmod 2^{32} \notin \mathbb{V}_\mu \;\vee\; x \in \mathbf{w} \wedge x \bmod 2^{32} \notin \mathbb{V}^*_\mu \right\} \qquad \text{(A.9)}`

{leanSource PVM.memoryException}

The model computes $`\mathbf{r}` and $`\mathbf{w}` together with the regular execution. Each row of the mutation tables
in {api}`PVM.Program.exec` returns the indices it reads and writes (`Mutation.reads`, `Mutation.writes`).

# The final state and the charged flag
%%%
tag := "pvm-final"
%%%

$$`\left(\varepsilon^*, \imath^*, \varphi^*, \mu^*\right) = \begin{cases} (\varepsilon^{\varrho}, \imath, \varphi, \mu) & \text{when } \varepsilon^{\varrho} \ne \blacktriangleright \\ (\varepsilon^{\mu}, \imath, \varphi, \mu) & \text{otherwise when } \varepsilon^{\mu} \ne \blacktriangleright \\ (\varepsilon, \imath', \varphi', \mu') & \text{otherwise} \end{cases} \qquad \text{(A.10)}`

$$`\tilde\varrho^* = \begin{cases} \bot & \text{when } \tilde\varrho' = \bot \vee \left(\mathbf{c}_{\imath} \in T \wedge \varepsilon^* \in \{\blacktriangleright\} \cup \{\hbar\} \times \mathbb{N}_R\right) \\ \top & \text{otherwise} \end{cases} \qquad \text{(A.11)}`

{leanSource PVM.Program.finalState}

$`\tilde\varrho^*` is the `charged` field in {api}`PVM.Program.step`. A terminator that continues, or makes a
host call, clears the flag, so the next block is charged when it starts.

# Ψ terminates

$`\Psi` iterates $`\Psi_1` until the step's result is not $`\blacktriangleright`. The paper does not say why this terminates. The
model gives a measure: every block charge costs at least one unit of gas, and between charges $`\imath`
increases or a terminator clears $`\tilde\varrho`. With this measure, $`\Psi` is a total function, {api}`PVM.psi`.

{mathdoc PVM.step_measure_lt}

{mathdoc PVM.psi_eq_runFuel}

# Readings chosen
%%%
tag := "pvm-readings"
%%%

These points are recorded in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues) (note 5 is under [paper and vectors](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#paper-and-vectors)):

* *Note 3, §A.4.* The prose says that a RAM index below $`2^{16}` always panics, "regardless of the
  apparent (in)accessibility". The formula for $`\varepsilon^\mu` considers only inaccessible indices. The model
  follows the formula ({api}`PVM.memoryException`).
* *Note 2, §A.10, the branch cost.* The gas model's $`\mathfrak{b}` reads $`\zeta` at the branch
  target $`\imath + \mathcal{Z}(\dots)`, which can be negative, where $`\zeta` is undefined. The
  model reads a negative index as 0 (`trap`), like an index past the end of $`\mathbf{c}`
  ({api}`PVM.Program.zetaInt`, used by {api}`PVM.Program.branchCost`).
* *Note 1, §A.10.* The gas model's $`\mathfrak{P}_S` compares $`\varphi_A = \varphi_D`, which, read literally, compares
  register values. The gas model has no values, so the model compares the indices $`r_A = r_D`.
* *Note 5.* $`\Psi` returns $`\imath = 0` on $`\blacksquare` and ☇, while the test vectors report the instruction that exited.
  The model follows the paper (`PVM.Result.pc`).
