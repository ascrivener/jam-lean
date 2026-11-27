import VersoManual
import Companion.Source
import Companion.Docstring
import PVM.Machine
import PVM.Invocation
import PVM.Theorems.Blob
import PVM.Theorems.BlobLimits
import PVM.Theorems.Decode
import PVM.Theorems.Termination
import PVM.Theorems.GasFuel
import PVM.Theorems.ExecForms
import PVM.Theorems.Host
import PVM.Theorems.HostIds
import PVM.Theorems.Invocation
import PVM.Theorems.InitMem
import JAM.Theorems.HostGas

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix A: the Polkadot Virtual Machine" =>
%%%
tag := "pvm"
shortTitle := "A. PVM"
file := "pvm-step"
%%%

Appendix A of GP v0.8.1 defines the Polkadot Virtual Machine (PVM), the machine on which JAM runs
the code of services and authorizers. The appendix has ten sections, and this chapter follows them in order:

* §A.1, the machine $`\Psi`, which runs a program blob $`\mathfrak{p}` until it exits, and $`\text{deblob}`,
  which splits the blob into code, opcode bitmask and jump table;
* §A.2–§A.3, the skip distance between instructions and the basic blocks;
* §A.4, the single step $`\Psi_1`, with its gas charge, its memory checks and the jump rules;
* §A.5, the instruction tables: how each instruction's operands are decoded and what it does;
* §A.6–§A.8, the host-call loop $`\Psi_H`, the standard program initialization $`Y` and the
  argument invocation $`\Psi_M`, which the invocations of Appendix B are built on;
* §A.9–§A.10, the gas cost model: the cost of a basic block is the number of cycles a simulated
  CPU needs to run it.

The paper writes the 13 registers as $`\varphi` and the RAM as $`\mu`. In the model's code the
registers are `ω`, and register values are `UInt64` (the paper's $`\mathbb{N}_R = \mathbb{N}_{2^{64}}`). Equation numbers
are those printed in the v0.8.1 release of the paper.

The modules are `PVM/Blob.lean` (§A.1–§A.3), `PVM/Machine.lean` (§A.1, §A.4), `PVM/Instr.lean`
and `PVM/Exec.lean` (§A.5), `PVM/Memory.lean` (the RAM), `PVM/Invocation.lean` (§A.6–§A.8) and
`PVM/Gas.lean` (§A.9–§A.10). Their full API is on the
[doc-gen4 pages](https://ascrivener.github.io/jam-lean/api/PVM/Machine.html).

# The machine Ψ and deblob (§A.1)
%%%
tag := "pvm-psi"
%%%

$`\Psi` repeats the single step $`\Psi_1` until the step's exit reason is not $`\blacktriangleright`
("continue"). Before every step the blob is deblobbed afresh at the current $`\imath`, so an
instruction counter that is not a valid instruction panics:

$$`\Psi \colon (\mathfrak{p}, \imath, \varrho, \tilde\varrho, \varphi, \mu) \mapsto \begin{cases} \Psi(\mathfrak{p}, \imath', \varrho', \tilde\varrho', \varphi', \mu') & \text{when } \varepsilon = \blacktriangleright \\ (\varepsilon, 0, \varrho', \bot, \varphi', \mu') & \text{when } \varepsilon \in \{\text{☇}, \blacksquare\} \\ (\varepsilon, \imath, \varrho', \tilde\varrho', \varphi, \mu) & \text{otherwise} \end{cases}`

$$`\text{where } (\varepsilon, \imath', \varrho', \tilde\varrho', \varphi', \mu') = \begin{cases} \Psi_1(\mathbf{c}, \mathbf{k}, \mathbf{j}, \imath, \varrho, \tilde\varrho, \varphi, \mu) & \text{when } (\mathbf{c}, \mathbf{k}, \mathbf{j}) = \text{deblob}(\mathfrak{p}, \imath) \\ (\text{☇}, \imath, \varrho, \tilde\varrho, \varphi, \mu) & \text{otherwise} \end{cases} \qquad \text{(A.1)}`

Its type is
$`(\mathbb{B}, \mathbb{N}_R, \mathbb{N}_G, \{\bot, \top\}, \llbracket\mathbb{N}_R\rrbracket_{13}, \mathbb{M}) \to (\{\blacksquare, \text{☇}, \infty\} \cup \{\Finv, \hbar\} \times \mathbb{N}_R, \mathbb{N}_R, \mathbb{N}_G, \{\bot, \top\}, \llbracket\mathbb{N}_R\rrbracket_{13}, \mathbb{M})`.
The exit reasons are a regular halt $`\blacksquare`, a panic ☇, running out of gas $`\infty`, a page
fault $`\Finv` with the address that faulted, and a host call $`\hbar` with the host-call identifier.
The model's {api}`PVM.Status` has one constructor for each, plus `cont` for $`\blacktriangleright`.

The model's $`\Psi` is {api}`PVM.psi`. Lean requires every function to terminate, and the paper's
$`\Psi` is a plain recursion, so the model runs the steps with a fuel bound, {api}`PVM.runFuel`, and
proves the bound is never reached (the last section of this chapter, {ref "pvm-terminates"}[Ψ terminates]):

{leanSource PVM.runFuel}

{leanSource PVM.psi}

The following theorem states that `psi` satisfies the paper's recursive equation (A.1), case by case:

{mathdoc PVM.psi_eq}

Two direct consequences: $`\Psi` never returns $`\blacktriangleright`, and it never returns more gas than it was given.

{mathdoc PVM.psi_status_ne_cont}

{mathdoc PVM.psi_gas_le}

## deblob
%%%
tag := "pvm-deblob"
%%%

$`\text{deblob}` (eq. (A.2), `deblob`) decodes a program blob into the instruction data
$`\mathbf{c}`, the opcode bitmask $`\mathbf{k}` and the dynamic jump table $`\mathbf{j}`, and checks
that the program is well formed and that $`\imath` is a valid instruction:

$$`\text{deblob}(\mathfrak{p}, \imath) = \begin{cases} (\mathbf{c}, \mathbf{k}, \mathbf{j}) & \text{when } \exists!\, \mathbf{c} \in \mathbb{B}_{:\mathsf{Z}_C}, \mathbf{k} \in \mathbb{b}, \mathbf{j} \in \llbracket\mathbb{N}_R\rrbracket_{:\mathsf{Z}_J} : \\ & \quad \mathfrak{p} = \mathcal{E}(|\mathbf{j}|) \frown \mathcal{E}_1(z) \frown \mathcal{E}(|\mathbf{c}|) \frown \mathcal{E}_z(\mathbf{j}) \frown \mathcal{E}(\mathbf{c}) \frown \mathcal{E}(\mathbf{k}),\ z \le 4 \wedge \mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, 0) \wedge \mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath) \\ \nabla & \text{otherwise} \end{cases}`

$$`\mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, \imath) = \begin{cases} \top & \text{when } \imath > 0 \wedge \imath = |\mathbf{k}| \\ \bot & \text{otherwise when } \imath + 1 + \text{skip}(\imath) = |\mathbf{k}| \wedge \mathbf{c}_\imath \notin T \\ \mathfrak{v}_{\text{blob}}(\mathbf{c}, \mathbf{k}, \imath + 1 + \text{skip}(\imath)) & \text{otherwise when } \mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath) \\ \bot & \text{otherwise} \end{cases}`

$$`\mathfrak{v}_{\text{inst}}(\mathbf{c}, \mathbf{k}, \imath) = |\mathbf{k}| = |\mathbf{c}| \wedge \imath < |\mathbf{k}| \wedge \mathbf{k}_\imath = 1 \wedge \mathbf{c}_\imath \in U \qquad \text{(A.2)}`

So $`\mathfrak{v}_{\text{blob}}` walks the program from index 0, one instruction at a time, and accepts it only if
every instruction is valid and the last one is a block terminator ($`T`, below). The limits
$`\mathsf{Z}_C = 2^{25}` on the code and $`\mathsf{Z}_J = 2^{24}` on the jump table are new in v0.8.1.

The model splits deblob into the parse of the encoding, {api}`PVM.Blob.parse?`, and the two checks:

{leanSource PVM.deblob}

{leanSource PVM.Blob.parse?}

{leanSource PVM.Program.vInst}

{leanSource PVM.Program.vBlobAux}

$`\mathfrak{v}_{\text{blob}}` is again a recursion, here on an index that increases at every call, so the model gives it
$`|\mathbf{k}| + 1` units of fuel ({api}`PVM.Program.vBlob`). More fuel would not change the answer, and every program that parses
respects the v0.8.1 limits:

{mathdoc PVM.Program.vBlob_eq}

{mathdoc PVM.Blob.parse?_limits}

# Skip, ζ and basic blocks (§A.2–§A.3)
%%%
tag := "pvm-blocks"
%%%

Instructions have variable length, and the bitmask $`\mathbf{k}` marks the octets of $`\mathbf{c}` that start an
instruction. $`\text{skip}(i)` is the number of octets, minus one, to the next instruction's opcode, and
$`\zeta` is $`\mathbf{c}` padded with zeroes, so reading past the end of the code reads 0 (the opcode of `trap`):

$$`\text{skip} \colon \mathbb{N} \to \mathbb{N},\quad i \mapsto \min(24,\ j \in \mathbb{N} : (\mathbf{k} \frown [1, 1, \dots])_{i + 1 + j} = 1) \qquad \text{(A.3)}`

$$`\zeta \equiv \mathbf{c} \frown [0, 0, \dots] \qquad \text{(A.4)}`

{leanSource PVM.Program.skip}

{leanSource PVM.Program.zeta}

{mathdoc PVM.Program.skip_le}

The block-termination opcodes $`T` are `trap`, `fallthrough`, the jumps, the load-and-jumps and the
branches (22 opcodes); $`U` is the set of all valid opcodes (139 of them). The basic blocks start at
0 and after every terminator, provided an instruction starts there, and $`\mathfrak{L}(\imath)` is the start of the
block containing $`\imath`:

$$`\varpi \equiv \left(\{0\} \cup \{n + 1 + \text{skip}(n) \mid n \in \mathbb{N}_{|\mathbf{c}|} \wedge \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in T\}\right) \cap \{n \mid \mathbf{k}_n = 1 \wedge \mathbf{c}_n \in U\} \qquad \text{(A.5)}`

$$`\mathfrak{L} \colon \mathbb{N}_R \to \mathbb{N}_R,\quad \imath \mapsto \max(j \in \varpi : j \le \imath) \qquad \text{(A.6)}`

The model's $`T` and $`U` ({api}`PVM.terminatorOpcodes`, {api}`PVM.validOpcodes`) are in `PVM/Tables.lean`,
which is generated from the paper's LaTeX source by a script; CI regenerates it from the pinned
paper and fails on any difference.

{leanSource PVM.Program.isBlockStart}

{leanSource PVM.Program.blockStartOf}

`isBlockStart` searches for the terminator $`n` only in the 25 octets before the candidate (since
$`\text{skip}(n) \le 24`). The theorem below shows that this is exactly membership in $`\varpi`:

{mathdoc PVM.Program.isBlockStart_iff}

# The single step Ψ₁ (§A.4)
%%%
tag := "pvm-step"
%%%

$`\Psi_1`, the single-step transition, does three things, in this order:

* it charges gas for the current basic block, if the block has not been charged yet;
* it checks the memory the instruction reads and writes ($`\varepsilon^\mu`);
* it applies the instruction's regular execution, given by the instruction tables of §A.5.

$$`\Psi_1 \colon (\mathfrak{p}, \mathbf{k}, \mathbf{j}, \imath, \varrho, \tilde\varrho, \varphi, \mu) \mapsto (\varepsilon^*, \imath^*, \varrho^*, \tilde\varrho^*, \varphi^*, \mu^*) \qquad \text{(A.7)}`

The result is {api}`PVM.StepResult`, and the function is {api}`PVM.Program.step`. A
{api}`PVM.Program` holds the code $`\mathbf{c}`, the bitmask $`\mathbf{k}` and the jump table $`\mathbf{j}`, so they need not be passed
separately.

{leanSource PVM.Program.step}

$`\Psi` calls $`\Psi_1` only at a valid instruction, so in practice the decode always succeeds. The `getD`
default only keeps $`\Psi_1` total, and the following theorem shows it is never reached:

{mathdoc PVM.Program.step_decode}

## The gas stage
%%%
tag := "pvm-gas"
%%%

Gas for a whole basic block is charged before the block's first instruction runs. $`\tilde\varrho` records that
the current block has been paid for:

$$`\left(\varepsilon^{\varrho}, \varrho^*, \tilde\varrho'\right) = \begin{cases} (\blacktriangleright, \varrho, \top) & \text{when } \tilde\varrho = \top \\ (\blacktriangleright, \varrho - \varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)), \top) & \text{otherwise when } \varrho \ge \varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \mathfrak{L}(\imath)) \\ (\infty, \varrho, \bot) & \text{otherwise} \end{cases} \qquad \text{(A.8)}`

{leanSource PVM.Program.chargeGas}

The block cost $`\varrho^\Delta` (eq. (A.54), `gascostforblock`) is the number of cycles a simulated out-of-order CPU
needs to retire the whole block, minus 3, and at least 1. It is defined in §A.9, below
({ref "pvm-gasmodel"}[the gas cost model]).

## Memory exceptions
%%%
tag := "pvm-memory"
%%%

The RAM $`\mu \in \mathbb{M}` holds $`2^{32}` octets $`\mu_{\mathbf{v}}` and an access mode per page of
$`\mathsf{Z}_P = 2^{12}` octets, $`\mu_{\mathbf{a}}`: read-only $`R`, writable $`W` or inaccessible $`\emptyset` (GP §4.7).
$`\mathbb{V}_\mu` is the set of readable indices and $`\mathbb{V}^*_\mu` the set of writable ones. The model's
{api}`PVM.Memory` keeps both as finite maps, with absent octets reading as 0 and absent pages
inaccessible; indices wrap modulo $`2^{32}` (the paper's $`\mu^\circlearrowleft`).

{leanSource PVM.Memory}

Let $`\mathbf{r}` and $`\mathbf{w}` be the indices that an instruction reads and writes. The memory-access exception is
the following:

$$`\varepsilon^{\mu} = \begin{cases} \blacktriangleright & \text{when } \mathbf{x} = \emptyset \\ \text{☇} & \text{when } \min(\mathbf{x}) \bmod 2^{32} < 2^{16} \\ \Finv \times \mathsf{Z}_P \left\lfloor \min(\mathbf{x}) \bmod 2^{32} \div \mathsf{Z}_P \right\rfloor & \text{otherwise} \end{cases}`

$$`\text{where } \mathbf{x} = \left\{ x \;\middle|\; x \in \mathbf{r} \wedge x \bmod 2^{32} \notin \mathbb{V}_\mu \;\vee\; x \in \mathbf{w} \wedge x \bmod 2^{32} \notin \mathbb{V}^*_\mu \right\} \qquad \text{(A.9)}`

{leanSource PVM.memoryException}

The model computes $`\mathbf{r}` and $`\mathbf{w}` together with the regular execution. Each row of the instruction tables
in {api}`PVM.Program.exec` returns the indices it reads and writes (`Mutation.reads`, `Mutation.writes`).

## The final state and the charged flag
%%%
tag := "pvm-final"
%%%

$$`\left(\varepsilon^*, \imath^*, \varphi^*, \mu^*\right) = \begin{cases} (\varepsilon^{\varrho}, \imath, \varphi, \mu) & \text{when } \varepsilon^{\varrho} \ne \blacktriangleright \\ (\varepsilon^{\mu}, \imath, \varphi, \mu) & \text{otherwise when } \varepsilon^{\mu} \ne \blacktriangleright \\ (\varepsilon, \imath', \varphi', \mu') & \text{otherwise} \end{cases} \qquad \text{(A.10)}`

$$`\tilde\varrho^* = \begin{cases} \bot & \text{when } \tilde\varrho' = \bot \vee \left(\mathbf{c}_{\imath} \in T \wedge \varepsilon^* \in \{\blacktriangleright\} \cup \{\hbar\} \times \mathbb{N}_R\right) \\ \top & \text{otherwise} \end{cases} \qquad \text{(A.11)}`

{leanSource PVM.Program.finalState}

$`\tilde\varrho^*` is the `charged` field in {api}`PVM.Program.step`. A terminator that continues, or makes a
host call, clears the flag, so the next block is charged when it starts.

Unless an instruction says otherwise, its regular execution continues at the next instruction and
changes nothing:

$$`\varepsilon = \blacktriangleright,\quad \imath' = \imath + 1 + \text{skip}(\imath),\quad \varphi' = \varphi,\quad \mu' = \mu \qquad \text{except as indicated} \qquad \text{(A.12)}`

This is `dflt` in {api}`PVM.Program.exec`, below.

## Numbers: signs, bits and sign extension

The instruction tables use a few conversions between $`n`-octet naturals and integers or bit
strings. $`\mathcal{Z}_n` reads an $`n`-octet natural as a signed integer and $`\mathcal{Z}_n^{-1}` goes back:

$$`\mathcal{Z}_{n \in \mathbb{N}} \colon \mathbb{N}_{2^{8n}} \to \mathbb{Z}_{-2^{8n-1} \dots 2^{8n-1}},\quad a \mapsto \begin{cases} a & \text{when } a < 2^{8n-1} \\ a - 2^{8n} & \text{otherwise} \end{cases} \qquad \text{(A.13)}`

$$`\mathcal{Z}^{-1}_{n \in \mathbb{N}} \colon \mathbb{Z}_{-2^{8n-1} \dots 2^{8n-1}} \to \mathbb{N}_{2^{8n}},\quad a \mapsto (2^{8n} + a) \bmod 2^{8n} \qquad \text{(A.14)}`

$`\mathcal{B}_n` and $`\overleftarrow{\mathcal{B}}_n` (eqs. (A.15)–(A.18)) give the bits of a natural, least or most significant
first, with their inverses. The model works with single bits, {api}`PVM.Num.bit` and {api}`PVM.Num.ofBits`.
Immediates are stored in as few octets as possible and sign-extended to 64 bits by $`\mathcal{X}_n`:

$$`\mathcal{X}_{n \in \{0, 1, 2, 3, 4, 8\}} \colon \mathbb{N}_{2^{8n}} \to \mathbb{N}_R,\quad x \mapsto x + \left\lfloor \frac{x}{2^{8n-1}} \right\rfloor (2^{64} - 2^{8n}) \qquad \text{(A.19)}`

{leanSource PVM.Num.signed}

{leanSource PVM.Num.unsigned}

{leanSource PVM.Num.sext}

## Jumps

A static jump must land on the start of a basic block, a conditional branch must have both its
targets on block starts (whether or not it is taken), and a dynamic jump goes through the jump table,
with addresses that are the table index plus one, times $`\mathsf{Z}_A = 2`:

$$`\text{sjump}(b) \implies (\varepsilon, \imath') = \begin{cases} (\text{☇}, \imath) & \text{when } b \notin \varpi \\ (\blacktriangleright, b) & \text{otherwise} \end{cases} \qquad \text{(A.20)}`

$$`\text{branch}(b, C) \implies (\varepsilon, \imath') = \begin{cases} (\text{☇}, \imath) & \text{when } b \notin \varpi \vee \imath + 1 + \text{skip}(\imath) \notin \varpi \\ (\blacktriangleright, \imath + 1 + \text{skip}(\imath)) & \text{otherwise when } \neg C \\ (\blacktriangleright, b) & \text{otherwise} \end{cases} \qquad \text{(A.21)}`

$$`\text{djump}(a) \implies (\varepsilon, \imath') = \begin{cases} (\blacksquare, \imath) & \text{when } a = 2^{32} - 2^{16} \\ (\text{☇}, \imath) & \text{otherwise when } a = 0 \vee a > |\mathbf{j}| \cdot \mathsf{Z}_A \vee a \bmod \mathsf{Z}_A \ne 0 \vee \mathbf{j}_{(a / \mathsf{Z}_A) - 1} \notin \varpi \\ (\blacktriangleright, \mathbf{j}_{(a / \mathsf{Z}_A) - 1}) & \text{otherwise} \end{cases} \qquad \text{(A.22)}`

A dynamic jump to $`2^{32} - 2^{16}` halts the machine. That is the value $`Y` puts in $`\varphi_0` (eq. (A.47)), so a
dynamic jump to the initial value of $`\varphi_0` halts.

{leanSource PVM.Program.sjump}

{leanSource PVM.Program.branch}

{leanSource PVM.Program.djump}

# The instruction tables (§A.5)
%%%
tag := "pvm-instructions"
%%%

§A.5 lists every instruction in thirteen tables, one per *argument format*. Each table starts with
an equation that says how the operands are decoded from the octets after the opcode, and each row
gives an opcode $`\zeta_\imath`, a name and the instruction's mutations (its exceptions to eq. (A.12)).
The skip length is

$$`\ell \equiv \text{skip}(\imath) \qquad \text{(A.23)}`

and register operands are read from the low and high nibbles of the octets after the opcode, capped
at 12. For example, instructions with two registers and one immediate (§A.5.10) decode as

$$`r_A = \min(12, (\zeta_{\imath+1}) \bmod 16),\quad r_B = \min\left(12, \left\lfloor \frac{\zeta_{\imath+1}}{16} \right\rfloor\right),\quad l_X = \min(4, \max(0, \ell - 1)),\quad \nu_X \equiv \mathcal{X}_{l_X}\left(\mathcal{E}^{-1}_{l_X}(\zeta_{\imath+2 \dots+ l_X})\right) \qquad \text{(A.32)}`

with $`\varphi_A \equiv \varphi_{r_A}`, $`\varphi'_A \equiv \varphi'_{r_A}`, and likewise for $`B`. Offsets are relative to $`\imath`; for one offset (§A.5.5)

$$`l_X = \min(4, \ell),\quad \nu_X \equiv \imath + \mathcal{Z}_{l_X}\left(\mathcal{E}^{-1}_{l_X}(\zeta_{\imath+1 \dots+ l_X})\right) \qquad \text{(A.27)}`

The model keeps decoding and execution apart. {api}`PVM.Instr` has one constructor per format, carrying
the opcode and the decoded operands; {api}`PVM.Program.decode` follows the format equations, and
{api}`PVM.Program.exec` the rows. The thirteen formats, with the equation that decodes their operands and
their opcodes, are:

* §A.5.1, no arguments (opcodes 0–2): `trap`, `fallthrough`, `unlikely`. Constructor `Instr.noArgs`.
* §A.5.2, one immediate, eq. (A.24) (opcode 10): `ecalli`, the host call. `Instr.oneImm`.
* §A.5.3, one register and one extended-width immediate, eq. (A.25) (20): `load_imm_64`. `Instr.regExtImm`.
* §A.5.4, two immediates, eq. (A.26) (30–33): `store_imm_u8` … `store_imm_u64`. `Instr.twoImm`.
* §A.5.5, one offset, eq. (A.27) (40): `jump`. `Instr.oneOffset`.
* §A.5.6, one register and one immediate, eq. (A.28) (50–62): `jump_ind`, `load_imm`, the direct loads and stores. `Instr.regImm`.
* §A.5.7, one register and two immediates, eq. (A.29) (70–73): `store_imm_ind_*`. `Instr.regTwoImm`.
* §A.5.8, one register, one immediate and one offset, eq. (A.30) (80–90): `load_imm_jump` and the `branch_*_imm`. `Instr.regImmOffset`.
* §A.5.9, two registers, eq. (A.31) (100–110): `move_reg`, the bit counts, the sign and zero extensions and `reverse_bytes`. `Instr.twoReg`.
* §A.5.10, two registers and one immediate, eq. (A.32) (120–161): the indirect loads and stores and the ALU operations with an immediate. `Instr.twoRegImm`.
* §A.5.11, two registers and one offset, eq. (A.33) (170–175): the register-register branches. `Instr.twoRegOffset`.
* §A.5.12, two registers and two immediates, eq. (A.34) (180): `load_imm_jump_ind`. `Instr.twoRegTwoImm`.
* §A.5.13, three registers, eq. (A.35) (190–230): the three-register ALU operations. `Instr.threeReg`.

The opcode enumerations and the format of each opcode are generated from the paper, like $`T` and $`U`.

{leanSource PVM.Instr}

{leanSource PVM.Program.decode}

{mathdoc PVM.Program.decode_opcode}

## Execution

{api}`PVM.Program.exec` gives each decoded instruction its regular execution: $`\varepsilon`, $`\imath'`, $`\varphi'`, $`\mu'`, and the
indices $`\mathbf{r}` and $`\mathbf{w}` it reads and writes. Loads and stores share two helpers, `load` and `store`,
which read or write $`n` octets little-endian at an address and record the indices; jumps go
through `sjump`, `branch` and `djump`. For example, the rows of §A.5.6 for `load_u16`, `load_i16` and
`store_u16` are

$$`\varphi'_A = \mathcal{E}^{-1}_2(\mu^\circlearrowleft_{\nu_X \dots+ 2}),\qquad \varphi'_A = \mathcal{X}_2\left(\mathcal{E}^{-1}_2(\mu^\circlearrowleft_{\nu_X \dots+ 2})\right),\qquad \mu'^\circlearrowleft_{\nu_X \dots+ 2} = \mathcal{E}_2(\varphi_A \bmod 2^{16})`

and `load_imm_jump` (opcode 80) and `jump_ind` (opcode 50) are

$$`\text{sjump}(\nu_Y),\ \varphi'_A = \nu_X \qquad\qquad \text{djump}((\varphi_A + \nu_X) \bmod 2^{32})`

{leanSource PVM.Program.exec}

The arithmetic of the ALU formats is in separate functions, one per format, each a transcription
of its table: {api}`PVM.Exec.twoRegAlu` (§A.5.9), {api}`PVM.Exec.twoRegImmAlu` (§A.5.10) and
{api}`PVM.Exec.threeRegAlu` (§A.5.13); the branch conditions are {api}`PVM.Exec.regImmBranchCond` (§A.5.8)
and {api}`PVM.Exec.twoRegBranchCond` (§A.5.11). The model computes over $`\mathbb{N}` and $`\mathbb{Z}` as the paper does,
reading a register with `toNat` and writing the result back (every result is already in
$`\mathbb{N}_{2^{64}}`). Some rows of §A.5.13, for example:

$$`\texttt{add\_32}\colon\ \varphi'_D = \mathcal{X}_4((\varphi_A + \varphi_B) \bmod 2^{32})`

$$`\texttt{div\_s\_32}\colon\ \varphi'_D = \begin{cases} 2^{64} - 1 & \text{when } b = 0 \\ \mathcal{Z}^{-1}_8(a) & \text{when } a = -2^{31} \wedge b = -1 \\ \mathcal{Z}^{-1}_8(\text{rtz}(a \div b)) & \text{otherwise} \end{cases} \quad \text{where } a = \mathcal{Z}_4(\varphi_A \bmod 2^{32}),\ b = \mathcal{Z}_4(\varphi_B \bmod 2^{32})`

$$`\texttt{rem\_s\_64}\colon\ \varphi'_D = \begin{cases} 0 & \text{when } \mathcal{Z}_8(\varphi_A) = -2^{63} \wedge \mathcal{Z}_8(\varphi_B) = -1 \\ \mathcal{Z}^{-1}_8(\text{smod}(\mathcal{Z}_8(\varphi_A), \mathcal{Z}_8(\varphi_B))) & \text{otherwise} \end{cases}`

{leanSource PVM.Exec.threeRegAlu}

Signed division rounds towards zero, and the signed remainder takes the sign of the numerator:

$$`\text{smod} \colon (\mathbb{Z}, \mathbb{Z}) \to \mathbb{Z},\quad (a, b) \mapsto \begin{cases} a & \text{when } b = 0 \\ \text{sgn}(a) \cdot (|a| \bmod |b|) & \text{otherwise} \end{cases} \qquad \text{(A.36)}`

$$`\text{rtz} \colon \mathbb{Z} \to \mathbb{Z},\quad x \mapsto \begin{cases} \lceil x \rceil & \text{when } x < 0 \\ \lfloor x \rfloor & \text{otherwise} \end{cases} \qquad \text{(A.37)}`

{leanSource PVM.Num.smod}

{leanSource PVM.Num.divRtz}

The paper writes the sign-extending loads in two ways: in §A.5.6 as $`\mathcal{X}_n(\dots)` and in §A.5.10 as
$`\mathcal{Z}^{-1}_8(\mathcal{Z}_n(\dots))`. The model keeps each form as written and proves that they agree:

{mathdoc PVM.Program.exec_loadIndI}

# Host calls: Ψ_H (§A.6)
%%%
tag := "pvm-host"
%%%

`ecalli` stops $`\Psi` with $`\hbar \times h`. $`\Psi_H^*` runs $`\Psi`, hands each host call to a handler $`f`, and resumes
after the `ecalli` if the handler continues:

$$`\Psi_H^* \colon (\mathfrak{p}, \imath, \varrho, \tilde\varrho, \varphi, \mu, f, \mathfrak{x}) \mapsto \begin{cases} (\varepsilon', \imath', \varrho', \tilde\varrho', \varphi', \mu', \mathfrak{x}) & \text{when } \varepsilon' \in \{\blacksquare, \text{☇}, \infty\} \cup \{\Finv\} \times \mathbb{N}_R \\ \Psi_H^*(\mathfrak{p}, \imath'', \varrho'', \tilde\varrho', \varphi'', \mu'', f, \mathfrak{x}'') \text{ where } \imath'' = \imath' + 1 + \text{skip}(\imath') & \text{when } \varepsilon' = \hbar \times h \wedge (\blacktriangleright, \varrho'', \varphi'', \mu'', \mathfrak{x}'') = f(h, \varrho', \varphi', \mu', \mathfrak{x}) \\ (\varepsilon'', \imath', \varrho'', \tilde\varrho', \varphi'', \mu'', \mathfrak{x}'') & \text{when } \varepsilon' = \hbar \times h \wedge (\varepsilon'', \varrho'', \varphi'', \mu'', \mathfrak{x}'') = f(h, \varrho', \varphi', \mu', \mathfrak{x}) \wedge \varepsilon'' \in \{\text{☇}, \infty\} \end{cases}`

$$`\text{let } (\varepsilon', \imath', \varrho', \tilde\varrho', \varphi', \mu') = \Psi(\mathfrak{p}, \imath, \varrho, \tilde\varrho, \varphi, \mu) \qquad \text{(A.38)}`

$$`\Psi_H(\mathfrak{p}, \imath, \varrho, \varphi, \mu, f, \mathfrak{x}) \equiv \Psi_H^*(\mathfrak{p}, \imath, \varrho, \bot, \varphi, \mu, f, \mathfrak{x}) \qquad \text{(A.39)}`

$$`\Omega\langle X \rangle \equiv (\mathbb{N}, \mathbb{N}_G, \llbracket\mathbb{N}_R\rrbracket_{13}, \mathbb{M}, X) \to (\{\blacktriangleright, \text{☇}, \infty\}, \mathbb{N}_G, \llbracket\mathbb{N}_R\rrbracket_{13}, \mathbb{M}, X) \qquad \text{(A.40)}`

A handler of type $`\Omega\langle X \rangle` is the model's {api}`PVM.HostFn`; its context $`X` is whatever the invocation needs
(Appendix B, {ref "invocations"}[the next chapter]). Since v0.8.1 a handler can only continue, panic
or run out of gas; it cannot halt the machine.

{leanSource PVM.HostFn}

{leanSource PVM.psiHFuel}

{leanSource PVM.psiHStar}

{leanSource PVM.psiH}

$`\Psi_H^*` is again a plain recursion. It terminates when the handler never returns more gas than it was
given ({api}`PVM.HostFn.GasNonIncreasing`). The handlers of all three invocations of Appendix B have this
property ({api}`JAM.isAuthHostFn_gasNonIncreasing`, {api}`JAM.refineHostFn_gasNonIncreasing`,
{api}`JAM.AccHost.accHostFn_gasNonIncreasing`). Each
continuing host call happens at a lower value of the measure that bounds $`\Psi`. For such handlers the
model's fuel is always enough, and `psiHStar` satisfies the paper's equation (A.38):

{mathdoc PVM.psiHStar_eq}

Two theorems about the host calls a program can make: $`\Psi` exits with $`\hbar \times h` only at an `ecalli` whose
immediate is $`h`, and so every such $`h` is among the immediates of the `ecalli` instructions in the
program's code ({api}`PVM.hostCallIdsOf`):

{mathdoc PVM.psi_host}

{mathdoc PVM.psi_hostId_mem}

# Standard program initialization: Y (§A.7)
%%%
tag := "pvm-init"
%%%

A JAM program blob $`\mathfrak{j}` holds a PVM blob $`\mathfrak{p}` together with the initial contents of RAM: read-only
data $`\mathbf{o}`, read-write data $`\mathbf{w}`, a number $`z` of extra heap pages and a stack size $`s`, after an opaque
metadata section $`\mathbf{m}`. $`Y` decodes it and lays out the RAM and the registers for argument data $`\mathbf{a}`:

$$`Y \colon (\mathbb{B}, \mathbb{B}_{:\mathsf{Z}_I}) \to (\mathbb{B}, \llbracket\mathbb{N}_R\rrbracket_{13}, \mathbb{M})?,\quad (\mathfrak{j}, \mathbf{a}) \mapsto \begin{cases} (\mathfrak{p}, \varphi, \mu) & \text{when } \exists!\, (\mathfrak{p}, \mathbf{o}, \mathbf{w}, z, s) \text{ which satisfy equations (A.42) and (A.45)} \\ \emptyset & \text{otherwise} \end{cases} \qquad \text{(A.41)}`

$$`\text{let } \mathcal{E}(\updownarrow\mathbf{m}) \frown \mathcal{E}_3(|\mathbf{o}|) \frown \mathcal{E}_3(|\mathbf{w}|) \frown \mathcal{E}_2(z) \frown \mathcal{E}_3(s) \frown \mathbf{o} \frown \mathbf{w} \frown \mathcal{E}_4(|\mathfrak{p}|) \frown \mathfrak{p} = \mathfrak{j} \qquad \text{(A.42)}`

$$`\mathsf{Z}_Z = 2^{16},\quad \mathsf{Z}_I = 2^{24} \qquad \text{(A.43)}`

$$`\text{let } P(x \in \mathbb{N}) \equiv \mathsf{Z}_P \left\lceil \frac{x}{\mathsf{Z}_P} \right\rceil,\quad Z(x \in \mathbb{N}) \equiv \mathsf{Z}_Z \left\lceil \frac{x}{\mathsf{Z}_Z} \right\rceil \qquad \text{(A.44)}`

$$`5\mathsf{Z}_Z + Z(|\mathbf{o}|) + Z(|\mathbf{w}| + z\mathsf{Z}_P) + Z(s) + \mathsf{Z}_I \le 2^{32} \qquad \text{(A.45)}`

The RAM has four sections, each starting on a zone of $`\mathsf{Z}_Z` octets and separated by at least one
unmapped zone; everything else is inaccessible:

$$`\forall i \in \mathbb{N}_{2^{32}} : ((\mu_{\mathbf{v}})_i, (\mu_{\mathbf{a}})_{\lfloor i / \mathsf{Z}_P \rfloor}) = \begin{cases} (\mathbf{o}_{i - \mathsf{Z}_Z}, R) & \text{when } \mathsf{Z}_Z \le i < \mathsf{Z}_Z + |\mathbf{o}| \\ (0, R) & \text{when } \mathsf{Z}_Z + |\mathbf{o}| \le i < \mathsf{Z}_Z + P(|\mathbf{o}|) \\ (\mathbf{w}_{i - (2\mathsf{Z}_Z + Z(|\mathbf{o}|))}, W) & \text{when } 2\mathsf{Z}_Z + Z(|\mathbf{o}|) \le i < 2\mathsf{Z}_Z + Z(|\mathbf{o}|) + |\mathbf{w}| \\ (0, W) & \text{when } 2\mathsf{Z}_Z + Z(|\mathbf{o}|) + |\mathbf{w}| \le i < 2\mathsf{Z}_Z + Z(|\mathbf{o}|) + P(|\mathbf{w}|) + z\mathsf{Z}_P \\ (0, W) & \text{when } 2^{32} - 2\mathsf{Z}_Z - \mathsf{Z}_I - P(s) \le i < 2^{32} - 2\mathsf{Z}_Z - \mathsf{Z}_I \\ (\mathbf{a}_{i - (2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I)}, R) & \text{when } 2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I \le i < 2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I + |\mathbf{a}| \\ (0, R) & \text{when } 2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I + |\mathbf{a}| \le i < 2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I + P(|\mathbf{a}|) \\ (0, \emptyset) & \text{otherwise} \end{cases} \qquad \text{(A.46)}`

$$`\forall i \in \mathbb{N}_{13} : \varphi_i = \begin{cases} 2^{32} - 2^{16} & \text{when } i = 0 \\ 2^{32} - 2\mathsf{Z}_Z - \mathsf{Z}_I & \text{when } i = 1 \\ 2^{32} - \mathsf{Z}_Z - \mathsf{Z}_I & \text{when } i = 7 \\ |\mathbf{a}| & \text{when } i = 8 \\ 0 & \text{otherwise} \end{cases} \qquad \text{(A.47)}`

So $`\varphi_1` is the top of the stack, $`\varphi_7` and $`\varphi_8` point at the arguments, and $`\varphi_0` is the return address
that halts (eq. (A.22)). In the model's code the paper's $`P` and $`Z` are {api}`PVM.roundPage` and {api}`PVM.roundZone`.

{leanSource PVM.standardInit}

{leanSource PVM.validJamBlob?}

{leanSource PVM.initialMemory}

{leanSource PVM.initialRegs}

The model sets page access first and then writes the three data sections. The two theorems below
read the result back, page by page and octet by octet, in the shape of eq. (A.46):

{mathdoc PVM.initialMemory_pages}

{mathdoc PVM.initialMemory_read}

# Argument invocation: Ψ_M (§A.8)
%%%
tag := "pvm-args"
%%%

$`\Psi_M` is what the three invocations of Appendix B call: initialize with $`Y`, run $`\Psi_H`, and read the
output from the RAM range that $`\varphi_7` and $`\varphi_8` name when the program halts:

$$`\Psi_M \colon (\mathbb{B}, \mathbb{N}_R, \mathbb{N}_G, \mathbb{B}_{:\mathsf{Z}_I}, \Omega\langle X \rangle, X) \to (\mathbb{N}_G, \mathbb{B} \cup \{\text{☇}, \infty\}, X)`

$$`(\mathfrak{j}, \imath, \varrho, \mathbf{a}, f, \mathfrak{x}) \mapsto \begin{cases} (0, \text{☇}, \mathfrak{x}) & \text{when } Y(\mathfrak{j}, \mathbf{a}) = \emptyset \\ R(\varrho, \Psi_H(\mathfrak{p}, \imath, \varrho, \varphi, \mu, f, \mathfrak{x})) & \text{when } Y(\mathfrak{j}, \mathbf{a}) = (\mathfrak{p}, \varphi, \mu) \end{cases}`

$$`\text{where } R \colon (\varrho, (\varepsilon, \imath', \varrho', \varphi', \mu', \mathfrak{x}')) \mapsto \begin{cases} (u, \infty, \mathfrak{x}') & \text{when } \varepsilon = \infty \\ (u, \mu'_{\varphi'_7 \dots+ \varphi'_8}, \mathfrak{x}') & \text{when } \varepsilon = \blacksquare \wedge \mathbb{N}_{\varphi'_7 \dots+ \varphi'_8} \subseteq \mathbb{V}_{\mu'} \\ (u, [], \mathfrak{x}') & \text{when } \varepsilon = \blacksquare \wedge \mathbb{N}_{\varphi'_7 \dots+ \varphi'_8} \not\subseteq \mathbb{V}_{\mu'} \\ (u, \text{☇}, \mathfrak{x}') & \text{otherwise} \end{cases} \quad \text{where } u = \varrho - \varrho' \qquad \text{(A.48)}`

The first component is the gas used. The output {api}`PVM.InvOutput` is a blob, ☇ or $`\infty`; a page fault
ends as ☇ (the "otherwise" case).

{leanSource PVM.psiM}

{leanSource PVM.invocationResult}

# The gas cost model (§A.9)
%%%
tag := "pvm-gasmodel"
%%%

The cost of a basic block is the number of cycles that a simplified out-of-order CPU needs to run
it. The simulation state $`\mathbb{S}` (eq. (A.49)) holds the next instruction to decode $`\imath` (or $`\emptyset` once a
terminator has been decoded), a cycle counter $`c`, the decode slots $`d` left in this cycle, the number
$`e` of instructions that may still start in this cycle, the free execution units $`t` and the reorder
buffer $`\mathbf{r}`. A reorder-buffer entry $`\mathbb{R}` (eq. (A.50)) has a state (DEC, WAIT, EXE, FIN or $`\emptyset`),
the cycles left $`c`, the entries it depends on $`p`, the registers it clobbers $`r`, and the execution
units it uses $`t`. Units are counted per kind, $`\mathbb{E} = (A, L, S, M, D)` (eq. (A.51): ALU, load, store,
multiply, divide), with memberwise arithmetic and comparison (eqs. (A.52), (A.53)).

{mathdoc PVM.SimState}

{mathdoc PVM.RobEntry}

{leanSource PVM.Units}

$`\check{s}` and $`\check{r}`, the source and destination registers of an instruction, are every register that its row in §A.5
reads or writes, whether or not it would at run time; `ecalli` has neither, and the destination of
the four `cmov` instructions also counts as a source ({api}`PVM.Instr.srcRegs`, {api}`PVM.Instr.dstRegs`).

The block cost runs the simulation $`\mathfrak{X}` from an initial state and takes its final cycle count:

$$`\varrho^{\Delta}(\mathbf{c}, \mathbf{k}, \imath) = \max\left(\mathbf{x}^{\text{final}}_{c} - 3,\, 1\right)`

$$`\text{where } \mathbf{x}^{\text{final}} = \mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathbf{x}^{\text{init}}),\; \mathbf{x}^{\text{init}} = \left(\imath, 0, 4, 5, (4, 4, 4, 1, 1), []\right) \qquad \text{(A.54)}`

{leanSource PVM.Program.blockCost?}

Each transition of $`\mathfrak{X}` decodes an instruction if it can, else starts one that is ready, else stops if
nothing is left, else advances a cycle:

$$`\mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathbf{x}) = \begin{cases} \mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathfrak{X}'(\mathbf{c}, \mathbf{k}, \mathbf{x})) & \text{when } \mathbf{x}_\imath \ne \emptyset \wedge \check{d}(\mathbf{c}, \mathbf{k}, \mathbf{x}_\imath) \le \mathbf{x}_d \wedge l < 32 \\ \mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathfrak{X}''(\mathbf{x})) & \text{otherwise when } \mathfrak{S}(\mathbf{x}) \ne \emptyset \wedge \mathbf{x}_e > 0 \\ \mathbf{x} & \text{otherwise when } \mathbf{x}_\imath = \emptyset \wedge l = 0 \\ \mathfrak{X}(\mathbf{c}, \mathbf{k}, \mathfrak{X}'''(\mathbf{x})) & \text{otherwise} \end{cases}`

$$`\text{where } l = |[r \mid r \mathrel{\hat\in} \mathbf{x}_{\mathbf{r}}, r_s \ne \emptyset]| \qquad \text{(A.55)}`

{leanSource PVM.Sim.transition}

The four steps:

* $`\mathfrak{X}'` (eq. (A.56)) sends `move_reg` to $`\mathfrak{X}^{\text{mov}}` (eq. (A.57)), which only renames registers in the
  reorder buffer, and every other instruction to $`\mathfrak{X}^{\text{dec}}` (eq. (A.58)), which appends a DEC entry
  whose dependencies are the entries that clobber one of its source registers. After a terminator,
  $`\mathbf{x}_\imath` becomes $`\emptyset`.
* $`\mathfrak{X}''` (eq. (A.59)) starts the entry $`\mathfrak{S}(\mathbf{x})`: it becomes EXE and takes its execution units.
* $`\mathfrak{S}` (eq. (A.60)) picks the first WAIT entry whose units are free and whose dependencies have no
  cycles left:

$$`\mathfrak{S}(\mathbf{x}) = \begin{cases} \emptyset & \text{when } s = \emptyset \\ \min(s) & \text{otherwise} \end{cases} \quad \text{where } s = \left\{ j \in \mathbb{N}_{|\mathbf{x}_{\mathbf{r}}|} \;\middle|\; \mathbf{x}_{\mathbf{r}}[j]_s = \text{WAIT} \wedge \mathbf{x}_{\mathbf{r}}[j]_t \le \mathbf{x}_t \wedge (\forall k \in \mathbf{x}_{\mathbf{r}}[j]_p : \mathbf{x}_{\mathbf{r}}[k]_c = 0) \right\} \qquad \text{(A.60)}`

* $`\mathfrak{X}'''` (eq. (A.61)) advances one cycle: it resets the decode and start slots, frees the units of
  entries finishing this cycle, retires every leading entry that is FIN or $`\emptyset`, moves DEC to WAIT and
  finished EXE entries to FIN, and counts down the cycles of running entries.

{leanSource PVM.Sim.decodeStep}

{leanSource PVM.Sim.decodeMove}

{leanSource PVM.Sim.decodeInstr}

{leanSource PVM.Sim.readyToStart}

{leanSource PVM.Sim.startStep}

{leanSource PVM.Sim.cycleStep}

The paper's $`\mathfrak{X}` is a recursion with no stated bound. The model runs it with fuel,
$`256 \cdot (|\mathbf{c}| - \imath + 2)` transitions ({api}`PVM.Sim.fuel`), and proves that the fuel always suffices (more fuel gives
the same result), and that for every block $`\Psi` charges the simulation finishes, so the total
{api}`PVM.Program.blockCost` is the paper's $`\varrho^\Delta` there:

{mathdoc PVM.Sim.run_fuel_eq}

{mathdoc PVM.Program.blockCost?_isSome_of_deblob}

{mathdoc PVM.Program.blockCost_eq_of_deblob}

# The gas cost tables (§A.10)
%%%
tag := "pvm-gastables"
%%%

§A.10 gives, for every instruction, the cycles $`\check{c}` it needs, the decode slots $`\check{d}` and the execution
units $`\check{x} = (\check{x}_A, \check{x}_L, \check{x}_S, \check{x}_M, \check{x}_D)`. Most cells are numbers; four are functions. $`\mathfrak{P}` depends
on whether the destination overlaps a source register, $`\mathfrak{P}_S` (for the non-immediate shifts and
rotates) only on the first source register, $`\mathfrak{m}` is the cost of memory accesses (used by the loads), and $`\mathfrak{b}` the cost of a branch:

$$`\mathfrak{P}(a, b, \mathbf{c}, \mathbf{k}, \imath) = \begin{cases} a & \text{when } \check{s}(\mathbf{c}, \mathbf{k}, \imath) \cap \check{r}(\mathbf{c}, \mathbf{k}, \imath) \ne \emptyset \\ b & \text{otherwise} \end{cases} \qquad \text{(A.62)}`

$$`\mathfrak{P}_S(a, b, \mathbf{c}, \mathbf{k}, \imath) = \begin{cases} a & \text{when } \varphi_A = \varphi_D \\ b & \text{otherwise} \end{cases} \qquad \text{(A.63)}`

$$`\mathfrak{m} \equiv 25 \qquad \text{(A.64)}`

$$`\mathfrak{b}(\mathbf{c}, \imath) = \begin{cases} 1 & \text{when } \{\zeta_{\imath + 1 + \text{skip}(\imath)}, \zeta_{\imath_{\text{target}}}\} \cap \{\texttt{unlikely}, \texttt{trap}\} \ne \emptyset \\ 20 & \text{otherwise} \end{cases} \qquad \text{(A.65)}`

For example, `move_reg` costs $`(0, 1, 0, 0, 0, 0, 0)`, `add_64` costs $`(1, \mathfrak{P}(1, 2), 1, 0, 0, 0, 0)`, the
loads $`(\mathfrak{m}, 1, 1, 1, 0, 0, 0)`, the branches $`(\mathfrak{b}, 1, 1, 0, 0, 0, 0)` and the divisions and remainders
$`(60, 4, 1, 0, 0, 0, 1)`, in the order $`(\check{c}, \check{d}, \check{x}_A, \check{x}_L, \check{x}_S, \check{x}_M, \check{x}_D)`.

The table itself is {api}`PVM.costRow?`, generated from the paper with the other tables. It keeps each
cell as written ({api}`PVM.CostExpr`); {api}`PVM.Program.evalCost` evaluates a cell for one instruction:

{leanSource PVM.Program.evalCost}

{leanSource PVM.Program.branchCost}

# Ψ terminates
%%%
tag := "pvm-terminates"
%%%

$`\Psi` iterates $`\Psi_1` until the step's result is not $`\blacktriangleright`. The paper does not say why this terminates. The
model gives a measure: every block charge costs at least one unit of gas, and between charges $`\imath`
increases or a terminator clears $`\tilde\varrho`. With this measure, $`\Psi` is a total function, {api}`PVM.psi`.

{mathdoc PVM.step_measure_lt}

{mathdoc PVM.psi_eq_runFuel}

# Readings chosen
%%%
tag := "pvm-readings"
%%%

Most of these points are recorded in the model's
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
* *Note 13, §A.6.* $`\Psi_H^*` need not terminate: a handler that returns more gas than it was given can
  make it recurse forever. The model proves termination for handlers that never add gas, which
  covers the handlers of all three invocations of Appendix B; for any other handler, `psiHStar` returns ☇ when its fuel
  runs out.
* *Note 17, §A.7.* $`Y` takes arguments $`\mathbf{a} \in \mathbb{B}_{:\mathsf{Z}_I}`, and the paper does not say what happens to a longer
  argument. The model returns $`\emptyset` ({api}`PVM.validJamBlob?`), so $`\Psi_M` panics.
* *§A.8.* $`\Psi_H` returns seven components, including the flag $`\tilde\varrho`, while $`R` in eq. (A.48) takes six. The
  model reads $`R` as ignoring the flag ({api}`PVM.invocationResult`).
* *`neg_add_imm_32`, §A.5.10.* $`\varphi'_A = \mathcal{X}_4((\nu_X + 2^{32} - \varphi_B) \bmod 2^{32})` is computed over $`\mathbb{Z}`: $`\varphi_B` may exceed
  $`2^{32}`, making the intermediate value negative, and the model takes the mathematical (non-negative)
  remainder ({api}`PVM.Exec.twoRegImmAlu`).
