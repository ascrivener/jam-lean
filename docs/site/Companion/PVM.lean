import VersoManual
import Companion.Source
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

Appendix A of GP v0.8.1 defines the Polkadot Virtual Machine. Ψ runs a program, and each of its
steps is Ψ₁, the single-step transition of §A.4. A step does three things, in this order:

* it charges gas for the current basic block, if the block has not been charged yet;
* it checks the memory the instruction reads and writes (ε^μ);
* it applies the instruction's regular execution, given by the mutation tables of §A.5.

This chapter puts each part of the paper's definition next to the model's.

# Ψ₁
%%%
tag := "pvm-step"
%%%

$$`\Psi_1 \colon (\mathbf{p}, \mathbf{k}, \mathbf{j}, \imath, \varrho, \tilde\varrho, \omega, \mu) \mapsto (\varepsilon^*, \imath^*, \varrho^*, \tilde\varrho^*, \omega^*, \mu^*)`

The result is {name}`PVM.StepResult`, and the function is {name}`PVM.Program.step`. A
{name}`PVM.Program` holds the code 𝐜, the bitmask 𝐤 and the jump table 𝐣, so they need not be passed
separately.

{leanSource PVM.Program.step}

Ψ calls Ψ₁ only at a valid instruction, so in practice the decode always succeeds. The `getD`
default only keeps Ψ₁ total, and the following theorem shows it is never reached:

{docstring PVM.Program.step_decode}

# The gas stage
%%%
tag := "pvm-gas"
%%%

Gas for a whole basic block is charged before the block's first instruction runs. ϱ̃ records that
the current block has been paid for:

$$`\left(\varepsilon^{\varrho}, \varrho^*, \tilde\varrho'\right) = \begin{cases} (\blacktriangleright, \varrho, \top) & \text{when } \tilde\varrho = \top \\ (\blacktriangleright, \varrho - \varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)), \top) & \text{otherwise when } \varrho \ge \varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)) \\ (\infty, \varrho, \bot) & \text{otherwise} \end{cases}`

{leanSource PVM.Program.chargeGas}

The block cost ϱ^Δ (eq. `gascostforblock`) is the number of cycles a simulated out-of-order CPU
needs to retire the whole block, minus 3, and at least 1:

$$`\varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \imath) = \max\left(\mathbf{x}^{\text{final}}_{c} - 3,\, 1\right)`

$$`\text{where } \mathbf{x}^{\text{final}} = \mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathbf{x}^{\text{init}}),\; \mathbf{x}^{\text{init}} = \left(\imath, 0, 4, 5, (4, 4, 4, 1, 1), []\right)`

{leanSource PVM.Program.blockCost?}

The simulation 𝔛 is run with fuel, because Lean needs every function to terminate. The theorems
below show that the fuel never runs out, and that the total {name}`PVM.Program.blockCost` agrees
with the paper's ϱ^Δ at every block Ψ charges:

{docstring PVM.Sim.run_fuel_eq}

{docstring PVM.Program.blockCost_eq_of_deblob}

# ε^μ: memory exceptions
%%%
tag := "pvm-memory"
%%%

Let 𝐫 and 𝐰 be the indices that an instruction reads and writes. The memory-access exception is
the following:

$$`\varepsilon^{\mu} = \begin{cases} \blacktriangleright & \text{when } \mathbf{x} = \emptyset \\ \text{☇} & \text{when } \min(\mathbf{x}) \bmod 2^{32} < 2^{16} \\ \text{F} \times \mathsf{Z}_P \left\lfloor \min(\mathbf{x}) \bmod 2^{32} \div \mathsf{Z}_P \right\rfloor & \text{otherwise} \end{cases}`

$$`\text{where } \mathbf{x} = \left\{ x \;\middle|\; x \in \mathbf{r} \wedge x \bmod 2^{32} \notin \mathbb{V}_\mu \;\vee\; x \in \mathbf{w} \wedge x \bmod 2^{32} \notin \mathbb{V}^*_\mu \right\}`

{leanSource PVM.memoryException}

The model computes 𝐫 and 𝐰 together with the regular execution. Each row of the mutation tables
in {name}`PVM.Program.exec` returns the indices it reads and writes (`Mutation.reads`, `Mutation.writes`).

# The final state and ϱ̃\*
%%%
tag := "pvm-final"
%%%

$$`\left(\varepsilon^*, \imath^*, \omega^*, \mu^*\right) = \begin{cases} (\varepsilon^{\varrho}, \imath, \omega, \mu) & \text{when } \varepsilon^{\varrho} \ne \blacktriangleright \\ (\varepsilon^{\mu}, \imath, \omega, \mu) & \text{otherwise when } \varepsilon^{\mu} \ne \blacktriangleright \\ (\varepsilon, \imath', \omega', \mu') & \text{otherwise} \end{cases}`

$$`\tilde\varrho^* = \begin{cases} \bot & \text{when } \tilde\varrho' = \bot \vee \left(\mathbf{c}_{\imath} \in T \wedge \varepsilon^* \in \{\blacktriangleright\} \cup \{\hbar\} \times \mathbb{N}_R\right) \\ \top & \text{otherwise} \end{cases}`

{leanSource PVM.Program.finalState}

ϱ̃\* is the `charged` field in {name}`PVM.Program.step`. A terminator that continues, or makes a
host call, clears the flag, so the next block is charged when it starts.

# Ψ terminates

Ψ iterates Ψ₁ until the step's result is not ▸. The paper does not say why this terminates. The
model gives a measure: every block charge costs at least one unit of gas, and between charges ı
increases or a terminator clears ϱ̃. With this measure, Ψ is a total function, {name}`PVM.psi`.

{docstring PVM.step_measure_lt}

{docstring PVM.psi_eq_runFuel}

# Readings chosen
%%%
tag := "pvm-readings"
%%%

These points are recorded in the model's
[upstream candidates](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md):

* *Note 3, §A.4.* The prose says that a RAM index below 2^16 always panics, "regardless of the
  apparent (in)accessibility". The formula for ε^μ considers only inaccessible indices. The model
  follows the formula ({name}`PVM.memoryException`).
* *Note 2, the branch target.* A branch target ı + 𝒵(…) can be negative, and ζ is undefined there.
  In the model a negative target is never the start of a basic block, so the branch panics
  ({name}`PVM.Program.branch`).
* *Note 1, §A.10.* The gas model's 𝔓\_S compares ω\_A = ω\_D, which, read literally, compares register
  values. The gas model has no values, so the model compares the indices r\_A = r\_D.
* *Note 5.* Ψ returns ı = 0 on ∎ and ☇, while the test vectors report the instruction that exited.
  The model follows the paper (`PVM.Result.pc`).
