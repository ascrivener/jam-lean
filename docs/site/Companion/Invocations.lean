import VersoManual
import Companion.Source
import Companion.Paper
import Companion.Docstring
import JAM.Host.General
import JAM.Refine
import JAM.Accumulate
import JAM.Theorems.HostGas
import JAM.Theorems.Confinement
import PVM.Theorems.Invocation

/-
Model modules quoted with `{leanSource}` here (each must be in `modelHighlights`):
`JAM.Host.General`, `JAM.Refine`, `JAM.Accumulate`.
-/

open Verso.Genre Manual
open Companion
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Appendix B: PVM invocations and host calls" =>
%%%
tag := "invocations"
shortTitle := "B. Invocations"
file := "invocations"
%%%

*In the paper:* {gpchapter}`sec:virtualmachineinvocations`.

*In brief.* The protocol runs service code at three points, and this appendix defines each:
Is-Authorized, which runs a work-package's authorization code to decide whether the package may use
a core ({ref "authorization"}[§8], {ref "work"}[§14]); Refine, which does a work-item's computation
in-core ({ref "work"}[§14]); and Accumulate, which lets a service fold refined results into its
on-chain state ({ref "accumulation"}[§12]). Each one starts a PVM ({ref "pvm"}[Appendix A]) with its
arguments and answers its host calls. The host functions are the program's only way to reach
anything beyond its own registers and memory: reading and writing storage, fetching its inputs,
exporting segments, creating services, transferring funds, and more. Each has a gas cost and reports
its outcome in a register, often as one of a few result codes. For example, when a service's code
calls read for a storage item, the host function copies the value into the program's memory and
returns its length, or the code NONE if there is no such item.

*Key terms:*

* $`\Psi_I`, $`\Psi_R` and $`\Psi_A`, the Is-Authorized, Refine and Accumulate invocations.
* $`\Psi_M`, the argument invocation that each of them uses ({ref "pvm"}[Appendix A]).
* $`\Omega_\square`, the host functions, one for each host-call identifier.

Appendix B of GP v0.8.1 defines the three places where the protocol runs a PVM program: the
Is-Authorized invocation $`\Psi_I` (§B.2), the Refine invocation $`\Psi_R` (§B.3) and the Accumulate
invocation $`\Psi_A` (§B.4). Each one runs a standard program blob with $`\Psi_M`, the argument
invocation, which calls $`\Psi_H` to run the machine and to hand each host call to a dispatcher
$`F`. The dispatcher maps the host-call identifier to a host function $`\Omega_\square` (§B.5).

$`\Psi_H`, the standard program initialization $`Y` and $`\Psi_M` are in {ref "pvm"}[Appendix A] of v0.8.1
(§A.6–§A.8), so they are in the {ref "pvm"}[Appendix A chapter]. This chapter covers what Appendix B
adds: the result constants, the three invocations with their dispatchers, and every host function.

The model's code for this appendix is in three modules: `JAM/Host/General.lean` (the general host
functions and the rules they share), `JAM/Refine.lean` ($`\Psi_I`, $`\Psi_R` and the refine host
functions) and `JAM/Accumulate.lean` ($`\Psi_A` and the accumulate host functions).

Throughout, $`\varphi` is the 13 registers, $`\varrho` the gas, $`\mu` the RAM and $`\mathfrak{x}`
the invocation context. A host function's results are written with a star: $`\varepsilon^*`,
$`\varrho^*`, $`\varphi^*`, $`\mu^*`, $`\mathfrak{x}^*`. In the model's code the registers are
called `ω`.

# Result constants (§B.1)
%%%
tag := "invocations-constants"
%%%

Host functions report most outcomes through $`\varphi'_7`. The paper's constants are:

* $`\mathtt{NONE} = 2^{64} - 1`: the item does not exist.
* $`\mathtt{WHAT} = 2^{64} - 2`: name unknown.
* $`\mathtt{OOB} = 2^{64} - 3`: the inner PVM memory index given for reading or writing is not accessible.
* $`\mathtt{WHO} = 2^{64} - 4`: index unknown.
* $`\mathtt{FULL} = 2^{64} - 5`: storage full, or resource already allocated.
* $`\mathtt{CORE} = 2^{64} - 6`: core index unknown.
* $`\mathtt{CASH} = 2^{64} - 7`: insufficient funds.
* $`\mathtt{LOW} = 2^{64} - 8`: gas limit too low.
* $`\mathtt{HUH} = 2^{64} - 9`: the operation is invalid.
* $`\mathtt{OK} = 0`: general success.

Inner PVM invocations (the `invoke` host call) have their own codes: $`\mathtt{HALT} = 0`,
$`\mathtt{PANIC} = 1`, $`\mathtt{FAULT} = 2`, $`\mathtt{HOST} = 3` and $`\mathtt{OOG} = 4`.

In the model these are the definitions of the namespace `JAM.Result` ({api}`JAM.Result.NONE`,
{api}`JAM.Result.WHAT`, …) and `JAM.RefineHost` ({api}`JAM.RefineHost.HALT`, …), as naturals.

# The Is-Authorized invocation (§B.2)
%%%
tag := "invocations-isauth"
%%%

$`\Psi_I` runs a work-package's authorization code on core $`c`. It is stateless: its only host calls
are `gas`, `grow_heap` and `fetch`.

{transcribed "B.1" "3bb9b7d0c8"}

$$`\Psi_I \colon \left\lgroup \mathbb{P}, \mathbb{N}_{\mathsf{C}} \right\rgroup \to \left\lgroup \mathbb{B} \cup \mathbb{E}, \mathbb{N}_G \right\rgroup, \quad (\mathbf{p}, c) \mapsto \begin{cases} (\texttt{BAD}, 0) & \text{if } \mathbf{p}_\mathbf{u} = \emptyset \\ (\texttt{BIG}, 0) & \text{otherwise if } |\mathbf{p}_\mathbf{u}| > \mathsf{W}_A \\ (\mathbf{r}, u) & \text{otherwise} \end{cases} \qquad \text{(B.1)}`

$$`\text{where } (u, \mathbf{r}, \emptyset) = \Psi_M(\mathbf{p}_\mathbf{u}, 0, \mathsf{G}_I, \mathcal{E}_2(c), F, \emptyset)`

{gpeq "B.2"}

$$`\text{where } \varphi' = \varphi \text{ except } \varphi'_7 = \mathtt{WHAT}`

$`\mathbf{p}_\mathbf{u}` is the authorization code: the historical lookup, in the service
$`\mathbf{p}_h`, of the code hash $`\mathbf{p}_u` at the lookup anchor ({ref "work"}[§14.3]). The model computes it
from an explicit account state $`\mathbf{d}`, the state the paper draws on implicitly:

{leanSource JAM.WorkPackage.authCode}

{leanSource JAM.psiI}

The dispatcher, and the case for an identifier it does not know, shared with $`\Psi_R`:

{leanSource JAM.RefineHost.dispatchI}

{leanSource JAM.RefineHost.unknown}

# The Refine invocation (§B.3)
%%%
tag := "invocations-refine"
%%%

$`\Psi_R` refines one work item. It can make a historical lookup, export segments, and create and
run inner PVM instances. The historical lookup $`\Omega_H` is meant to give the same result whatever the state of the chain,
at any time when auditing may occur (less than two epochs after accumulation). The lookup anchor may
be up to $`\mathsf{L}` timeslots before the recent history, so the expunge period $`\mathsf{D}` adds a safety
margin of eight hours:

{gpeq "B.3"}

An inner PVM instance holds a program blob, its RAM, its instruction counter, the gas-charged flag
of the current basic block, and the handle of the program module it came from:

{gpeq "B.4"}

{leanSource JAM.InnerPvm}

The refine context is $`(\mathbf{m}, \mathbf{c}, \mathbf{e})`: the inner instances by identifier, the
compiled program modules by handle, and the exported segments. All three start empty.

{leanSource JAM.RefineCtx}

$`\Psi_R` takes the core $`c`, the item index $`i`, the work-package $`p`, the authorizer trace
$`\mathbf{r}`, the import segments $`\overline{\mathbf{i}}` of every item and the export offset
$`\varsigma`. It draws implicitly on a recent account state $`\delta`:

{transcribed "B.5" "f6f3a96977"}

$$`\Psi_R \colon \left\lgroup \mathbb{N}_{\mathsf{C}}, \mathbb{N}, \mathbb{P}, \mathbb{B}, \llbracket\llbracket\mathbb{J}\rrbracket\rrbracket, \mathbb{N} \right\rgroup \to \left\lgroup \mathbb{B} \cup \mathbb{E}, \llbracket\mathbb{J}\rrbracket, \mathbb{N}_G \right\rgroup \qquad \text{(B.5)}`

$$`(c, i, p, \mathbf{r}, \overline{\mathbf{i}}, \varsigma) \mapsto \begin{cases} (\texttt{BAD}, [], 0) & \text{if } w_s \notin \mathcal{K}(\delta) \vee \mathfrak{j} = \emptyset \\ (\texttt{BIG}, [], 0) & \text{otherwise if } |\mathfrak{j}| > \mathsf{W}_C \\ (\mathbf{o}, [], u) & \text{otherwise if } \mathbf{o} \in \{\infty, \text{☇}\} \\ (\mathbf{o}, \mathbf{e}, u) & \text{otherwise} \end{cases}`

$$`\begin{aligned} \text{where } & w = p_\mathbf{w}[i],\quad \mathfrak{j} = \Lambda(\delta[w_s], (p_\mathbf{c})_t, w_c),\quad \mathbf{a} = \mathcal{E}(c, i, w_s, {\updownarrow} w_\mathbf{y}, \mathcal{H}(p)) \\ \text{and } & (u, \mathbf{o}, (\mathbf{m}, \mathbf{c}, \mathbf{e})) = \Psi_M(\mathfrak{j}, 0, w_g, \mathbf{a}, F, (\emptyset, \emptyset, [])) \end{aligned}`

The model passes $`\delta` as the argument `d`, and the extrinsic data $`\overline{\mathbf{x}}` that
`fetch` serves as the argument `extrinsics` (see the readings below):

{leanSource JAM.psiR}

The dispatcher $`F` (eq. {eq}`B.6`) gives `gas`, `grow_heap` and `fetch` the refine arguments
($`\mathbf{p}`, the zero hash in place of entropy, $`\mathbf{r}`, $`i`, $`\overline{\mathbf{i}}`,
$`\overline{\mathbf{x}}`) and adds the refine functions with identifiers 7 to 15. Any other identifier
is charged $`\mathsf{M}_\emptyset` and answered with $`\varphi'_7 = \mathtt{WHAT}`, as in {eq}`B.2`.
In the model, the fixed arguments are collected in {api}`JAM.RefineHost.Env`:

{leanSource JAM.RefineHost.dispatch}

# The Accumulate invocation (§B.4)
%%%
tag := "invocations-accumulate"
%%%

The accumulate context is a pair of implications $`(\mathbf{x}, \mathbf{y}) \in \mathbb{L}^2`: the
regular dimension $`\mathbf{x}` and the exceptional dimension $`\mathbf{y}`, which only `checkpoint`
changes. An implication holds the accumulating service $`s`, the partial state $`\mathbf{e}`, the
services whose accounts were modified $`\mathbf{w}`, the next free service identifier $`i`, the
deferred transfers $`\mathbf{t}`, the yield $`y` and the provisions $`\mathbf{p}`:

{gpeq "B.7"}

{gpeq "B.8"}

{leanSource JAM.Implications}

{leanSource JAM.Implications.self}

$`\Psi_A` first credits the service with the incoming deferred transfers, then runs its code with
entry point 5:

{transcribed "B.9" "0a03907597"}

$$`\Psi_A \colon (\mathbf{e}, t, s, g, \mathbf{i}) \mapsto \begin{cases} (\mathbf{e}, \mathbf{w} \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} \{\}, \mathbf{t} \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} [], y \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} \emptyset, u \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} 0, \mathbf{p} \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} []) & \text{if } s \notin \mathcal{K}(\mathbf{e}_\mathbf{d}) \\ (\mathbf{e} \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} \mathbf{s}, \mathbf{w}, \mathbf{t} \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} [], y \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} \emptyset, u \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} 0, \mathbf{p} \mathrel{\genfrac{}{}{0pt}{3}{\blacktriangleright}{\blacktriangleright}} []) & \text{otherwise if } \mathfrak{j} = \emptyset \vee |\mathfrak{j}| > \mathsf{W}_C \\ C(\Psi_M(\mathfrak{j}, 5, g, \mathcal{E}(t, s, |\mathbf{i}|), F, I(\mathbf{s}, \mathbf{w}, s)^2)) & \text{otherwise} \end{cases} \qquad \text{(B.9)}`

$$`\begin{aligned} \text{where } & \mathfrak{j} = \mathbf{e}_\mathbf{d}[s]_\mathbf{c} \\ \text{and } & \mathbf{s} = \mathbf{e} \text{ except } \mathbf{s}_\mathbf{d}[s]_b = \mathbf{e}_\mathbf{d}[s]_b + \textstyle\sum_{r \in \mathbf{x}, r_u = \bot} r_a,\; \mathbf{s}_\mathbf{d}[s]_x = \mathbf{e}_\mathbf{d}[s]_x + \textstyle\sum_{r \in \mathbf{x}, r_u = \top} r_a \\ \text{and } & \mathbf{w} = \{ s \mid r \in \mathbf{x} \},\quad \mathbf{x} = [ i \mid i \mathrel{\mathrlap{<}{-}} \mathbf{i}, i \in \text{𝕥} ] \end{aligned}`

Here $`b` is the balance and $`x` the supervisor balance of an account, and $`r_u` says whether a
transfer goes to the supervisor balance. In the model, {api}`JAM.psiA` forms $`\mathbf{s}` and
$`\mathbf{w}`, and {api}`JAM.psiARun` does the rest. $`\Psi_M` takes its gas in $`\mathbb{N}_G`,
but $`g` can exceed $`2^{64} - 1` (see {ref "accumulation-readings"}[note v0.8.1-A61]); the model
runs $`\Psi_M` with $`\min(g, 2^{64} - 1)`:

{leanSource JAM.psiA}

{leanSource JAM.psiARun}

The initial implications, and `check`, which finds the first identifier in a sequence that is not
already a service:

{gpeq "B.10"}

{gpeq "B.13"}

{leanSource JAM.initImplications}

{leanSource JAM.checkId}

`checkId` takes fuel because Lean needs every function to terminate; it is given
$`|\mathbf{e}_\mathbf{d}| + 1` steps.

The dispatcher $`F` (eq. {eq}`B.11`) has the general functions `gas`, `grow_heap` and `fetch` (with the
entropy $`\eta'_0` and the inputs $`\mathbf{i}`), and the accumulate functions with identifiers 3 to 6
and 16 to 29. Unknown identifiers are handled as in {eq}`B.2`:

{leanSource JAM.AccHost.dispatch}

The collapse $`C` (eq. {eq}`B.12`) keeps the exceptional dimension $`\mathbf{y}` when the machine ran out
of gas or panicked. Otherwise it keeps $`\mathbf{x}`, and an output $`\mathbf{o} \in \mathbb{H}` (32 octets)
becomes the yield:

{gpeq "B.12"}

In the model, $`C` is the final `match o with` of {api}`JAM.psiARun`.

# Host functions (§B.5)
%%%
tag := "invocations-host"
%%%

## The rules every host function shares

Each host function maps $`(\varrho, \varphi, \mu, \mathfrak{x}, \dots)` to
$`(\varepsilon^* \in \{\blacktriangleright, \text{☇}, \infty\}, \varrho^* \in \mathbb{N}_G, \varphi^*, \mu^*, \mathfrak{x}^*)`.
It costs $`g` gas, given in its row of the paper's tables. If there is not enough gas, the result is
$`\infty`, all the gas is used, and registers, memory and context are unchanged:

{gpeq "B.14"}

{gpeq "B.15"}

{gpeq "B.17"}

The model applies these rules in one place, {api}`JAM.charged`, which every host function calls with
its $`g` and a body that gives the "except as indicated" part. A body starts from
$`(\blacktriangleright, \varrho - g, \varphi, \mu, \mathfrak{x})`:

{leanSource JAM.charged}

{leanSource JAM.HostOut}

Gas that depends on a size $`\ell` in octets is charged at a rate $`L` per 1024 octets:

{gpeq "B.16"}

{leanSource JAM.memGas}

The gas constants $`\mathsf{M}_\square` are numbers from the paper's list of constants. The model's
`JAM/Constants.lean` is generated from that list (the paper's `definitions.tex`), and CI regenerates it
and fails on any difference. So $`\mathsf{M}_G` is {api}`JAM.Constants.CgasG`, $`\mathsf{M}_\emptyset`
is {api}`JAM.Constants.Cgasunknown`, and so on.

Several functions end the same way: they compute a value $`\mathbf{v}` (an octet string, $`\emptyset`
if there is none, or $`\nabla` if an input could not be read), and copy part of it to memory:

$$`f = \min(f_0, |\mathbf{v}|), \quad l = \min(z, |\mathbf{v}| - f), \quad (\varepsilon', \varphi'_7, \mu'_{o \dots+ l}) \equiv \begin{cases} (\text{☇}, \varphi_7, \mu_{o \dots+ l}) & \text{if } \mathbf{v} = \nabla \vee \mathbb{N}_{o \dots+ l} \not\subseteq \mathbb{V}^*_\mu \\ (\blacktriangleright, \mathtt{NONE}, \mu_{o \dots+ l}) & \text{otherwise if } \mathbf{v} = \emptyset \\ (\blacktriangleright, |\mathbf{v}|, \mathbf{v}_{f \dots+ l}) & \text{otherwise} \end{cases}`

The paper writes this out in each of `fetch`, `historical_lookup`, `lookup`, `read` and `info`
(`fetch` and `info` have no $`\nabla` case). The model writes it once, as {api}`JAM.writeValue`, and
each of those functions passes its own $`o`, $`f_0` and $`z`:

{leanSource JAM.writeValue}

In the entries below, "in" names the registers a function reads, "out" what it sets, and the outcomes
are listed in the paper's order: the first that applies is the result. Where a function names a
service by a register, the value $`2^{64} - 1` means the caller's own service, except in `eject` and `assign`, where
the service is taken as given, and in `bless`, where it keeps the current holder.

## General functions (§B.5.1)
%%%
tag := "invocations-general"
%%%

These leave the context unchanged.

*`gas` = 0*, $`\Omega_G(\varrho, \varphi, \mu, \mathfrak{x})`.
$`g = \mathsf{M}_G`. Out: $`\varphi'_7 = \varrho^*`, the gas left after the charge.

{leanSource JAM.hostGas}

*`grow_heap` = 1*, $`\Omega_{\text{♊}}(\varrho, \varphi, \mu, \mathfrak{x}, \mathfrak{j})`. In:
$`\varphi_7`, the page the heap should reach. The heap's first page $`a` and its bound $`b` come from the
program blob $`\mathfrak{j}` (its read-only data $`\mathbf{o}` and stack size $`s`, eq. {eq}`A.42`), and
$`h = a + c` is the current top, where $`c` counts the writable pages in $`\mathbb{N}_{a \dots b}`:

$$`a = \frac{2\mathsf{Z}_Z + Z(|\mathbf{o}|)}{\mathsf{Z}_P}, \quad b = \frac{2^{32} - 3\mathsf{Z}_Z - \mathsf{Z}_I - Z(s)}{\mathsf{Z}_P}, \quad \varphi'_7 \equiv \begin{cases} h & \text{if } \varphi_7 \le h \vee \varphi_7 > b \\ \varphi_7 & \text{otherwise} \end{cases}, \quad (\mu'_\mathbf{a})_{a \dots \varphi'_7} \equiv [\mathrm{W}, \dots, \mathrm{W}], \quad g \equiv \mathsf{M}_{\text{♊},c} + (\varphi'_7 - h) \cdot \mathsf{M}_{\text{♊},p}`

{leanSource JAM.heapBounds}

{leanSource JAM.growHeapCore}

{leanSource JAM.hostGrowHeap}

*`fetch` = 2*, $`\Omega_Y(\varrho, \varphi, \mu, \mathfrak{x}, p, n, \mathbf{r}, i, \overline{\mathbf{i}}, \overline{\mathbf{x}}, \mathbf{i})`.
In: $`\varphi_{10}` selects an item, $`\varphi_{11}` and $`\varphi_{12}` index into it, and
$`[o, f_0, z] = \varphi_{7 \dots+ 3}` say where and how much to copy. Out: $`\varphi'_7` and memory, by the
shared tail above. The items, by $`\varphi_{10}`: 0, the protocol constants; 1, the entropy $`n`;
2, the authorizer trace $`\mathbf{r}`; 3 and 4, an extrinsic of any item or of item $`i`; 5 and 6, an
import segment of any item or of item $`i`; 7 to 13, the work-package, its authorization configuration
and token, its context, the summaries of its items, one item's summary and one item's payload; 14 and
15, all the accumulation inputs or one of them. An argument that is $`\emptyset` in the invocation,
an index out of range, or any other $`\varphi_{10}` gives $`\mathbf{v} = \emptyset`, so $`\varphi'_7 = \mathtt{NONE}`.
$`g \equiv \mathsf{M}_{Y,\varphi_{10},c} + \mathcal{G}(\mathsf{M}_{Y,\varphi_{10},\ell}, z)` when
$`\varphi_{10} < 16`, and $`\mathsf{M}_{Y,\emptyset}` otherwise.

{leanSource JAM.FetchContext}

{leanSource JAM.fetchValue}

{leanSource JAM.hostFetch}

## Refine functions (§B.5.2)
%%%
tag := "invocations-refine-functions"
%%%

These work on the refine context:

{gpeq "B.18"}

*`historical_lookup` = 7*, $`\Omega_H(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{c}, \mathbf{e}), s, \mathbf{d}, t)`.
In: $`\varphi_7` names the service, the 32-octet hash is at $`h = \varphi_8`; then
$`o = \varphi_9`, $`f_0 = \varphi_{10}`, $`z = \varphi_{11}`. $`\mathbf{v}` is the historical lookup
$`\Lambda(\mathbf{a}, t, \mu_{h \dots+ 32})`: $`\nabla` if the hash is not readable, $`\emptyset` if
there is no such service. $`g \equiv \mathsf{M}_{H,c} + \mathcal{G}(\mathsf{M}_{H,\ell}, z)`.

{leanSource JAM.RefineHost.historicalLookup}

*`export` = 8*, $`\Omega_E(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{c}, \mathbf{e}), \varsigma)`.
In: $`p = \varphi_7`, $`z = \min(\varphi_8, \mathsf{W}_G)`. The segment is $`\mu_{p \dots+ z}` zero-padded to
$`\mathsf{W}_G` octets. Outcomes: ☇ if $`\mathbb{N}_{p \dots+ z} \not\subseteq \mathbb{V}_\mu`;
$`\mathtt{FULL}` if $`\varsigma + |\mathbf{e}| \ge \mathsf{W}_X`; otherwise the segment is appended to
$`\mathbf{e}` and $`\varphi'_7 = \varsigma + |\mathbf{e}|`, its index. $`g \equiv \mathsf{M}_E`.

{leanSource JAM.RefineHost.exportSeg}

*`compile` = 9*, $`\Omega_\Gamma(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{c}, \mathbf{e}), s, \mathbf{d}, t)`.
In: $`[m, p, l, f, i] = \varphi_{7 \dots+ 5}`. For $`m = 0` the program blob is $`\mu_{p \dots+ l}`;
for $`m = 1` it is the part $`\mathbf{h}_{f^* \dots+ l^*}` of the historical lookup $`\mathbf{h}` of the
hash at $`p`, in service $`\mathbf{d}[s]` ($`i = 2^{64} - 1`) or $`\mathbf{d}[i]`. Let $`\mathbf{H}`
be the handles in use (the keys of $`\mathbf{c}` and the handles of the instances in $`\mathbf{m}`).
Outcomes: $`\mathtt{FULL}` if $`|\mathbf{H}| \ge 128`; ☇ if the source is not readable;
$`\mathtt{NONE}` if $`m = 1` and there is no such service or no preimage; $`\mathtt{HUH}` if there is no blob or
$`\text{deblob}(\mathbf{p}, 0) = \nabla`; otherwise the blob is stored under the least handle
$`k \notin \mathbf{H}`, and $`\varphi'_7 = k`. $`g \equiv \mathsf{M}_{\Gamma,\mathrm{m},c} + \mathcal{G}(\mathsf{M}_{\Gamma,\mathrm{m},\ell}, l)`
for $`m = 0`, $`\mathsf{M}_{\Gamma,\mathrm{d},c} + \mathcal{G}(\mathsf{M}_{\Gamma,\mathrm{d},\ell}, l)` for
$`m = 1`, and $`\mathsf{M}_{\Gamma,\mathrm{m},c}` otherwise.

{leanSource JAM.RefineHost.compileBlob}

{leanSource JAM.RefineHost.compile}

*`machine` = 10*, $`\Omega_M(\varrho, \varphi, \mu, (\mathbf{m}, \mathbf{c}, \mathbf{e}))`. In:
$`[h, i] = \varphi_{7 \dots+ 2}`: instantiate module $`h` at instruction $`i`, with empty RAM and the
charged flag $`\bot`. Outcomes: $`\mathtt{FULL}` if $`|\mathbf{m}| \ge 63`; $`\mathtt{WHO}` if
$`h \notin \mathcal{K}(\mathbf{c})`; $`\mathtt{HUH}` if $`\text{deblob}(\mathbf{c}[h], i) = \nabla`;
otherwise the instance gets the least free identifier $`n`, and $`\varphi'_7 = n`. $`g \equiv \mathsf{M}_M`.

{leanSource JAM.RefineHost.machine}

*`peek` = 11*, $`\Omega_P`. In: $`[n, o, s, z] = \varphi_{7 \dots+ 4}`: copy $`z` octets from address
$`s` of instance $`n` to address $`o` of our RAM. Outcomes: ☇ if
$`\mathbb{N}_{o \dots+ z} \not\subseteq \mathbb{V}^*_\mu`; $`\mathtt{WHO}` if there is no instance $`n`;
$`\mathtt{OOB}` if its RAM is not readable there; otherwise $`\mathtt{OK}`.
$`g \equiv \mathsf{M}_{P,c} + \mathcal{G}(\mathsf{M}_{P,\ell}, z)`.

{leanSource JAM.RefineHost.peek}

*`poke` = 12*, $`\Omega_O`. In: $`[n, s, o, z] = \varphi_{7 \dots+ 4}`: copy $`z` octets from address
$`s` of our RAM to address $`o` of instance $`n`. Outcomes: ☇ if
$`\mathbb{N}_{s \dots+ z} \not\subseteq \mathbb{V}_\mu`; $`\mathtt{WHO}` if there is no instance $`n`;
$`\mathtt{OOB}` if its RAM is not writable there; otherwise $`\mathtt{OK}`.
$`g \equiv \mathsf{M}_{O,c} + \mathcal{G}(\mathsf{M}_{O,\ell}, z)`.

{leanSource JAM.RefineHost.poke}

*`pages` = 13*, $`\Omega_Z`. In: $`[n, p, c, r] = \varphi_{7 \dots+ 4}`: set the $`c` pages from page
$`p` of instance $`n` to mode $`r`. Modes 0, 1 and 2 zero the pages and make them inaccessible,
read-only or writable; modes 3 and 4 make them read-only or writable and keep their contents.
Outcomes: $`\mathtt{WHO}` if there is no instance $`n`; $`\mathtt{HUH}` if $`r > 4`, $`p < 16` or
$`p + c \ge 2^{32} / \mathsf{Z}_P`; $`\mathtt{HUH}` if $`r > 2` and one of the pages is inaccessible;
otherwise $`\mathtt{OK}`. $`g` is $`\mathsf{M}_{Z,f,c} + c \cdot \mathsf{M}_{Z,f,p}` for $`r = 0`,
$`\mathsf{M}_{Z,a,c} + c \cdot \mathsf{M}_{Z,a,p}` for $`r \in \{1, 2\}`,
$`\mathsf{M}_{Z,s,c} + c \cdot \mathsf{M}_{Z,s,p}` for $`r \in \{3, 4\}`, and $`\mathsf{M}_{Z,i}`
otherwise.

{leanSource JAM.RefineHost.setPagesMode}

{leanSource JAM.RefineHost.pages}

*`invoke` = 14*, $`\Omega_K`. In: $`[n, o] = \varphi_{7, 8}`. The 112 octets at $`o` hold the inner
gas $`g_R` and the inner registers $`\mathbf{w}`, $`\mathcal{E}_8(g_R) \frown \mathcal{E}_8(\mathbf{w})`.
Instance $`n` runs under $`\Psi` from its instruction counter and charged flag; afterwards its gas and
registers are written back to the same 112 octets, and its RAM, charged flag and instruction counter
are stored (after a host call the counter moves past the `ecalli`, $`i' + \text{skip}(i') + 1`).
Outcomes: ☇ if $`\mathbb{N}_{o \dots+ 112} \not\subseteq \mathbb{V}^*_\mu`; $`\mathtt{WHO}` if there is
no instance $`n`; otherwise $`\varphi'_7` is $`\mathtt{HOST}`, $`\mathtt{FAULT}`, $`\mathtt{OOG}`,
$`\mathtt{PANIC}` or $`\mathtt{HALT}` by the inner exit, with $`\varphi'_8` the host-call identifier
($`\mathtt{HOST}`) or the fault address ($`\mathtt{FAULT}`). The cost includes the inner gas, and the
inner gas left over is returned:

$$`g \equiv \mathsf{M}_K + g_R, \qquad \varrho^* \equiv \max(\varrho - g, 0) + \begin{cases} 0 & \text{if } \mathbf{w} = \nabla \vee n \notin \mathcal{K}(\mathbf{m}) \vee \varrho < g \\ g'_R & \text{otherwise} \end{cases}`

{leanSource JAM.RefineHost.invoke}

*`expunge` = 15*, $`\Omega_X`. In: $`[m, n] = \varphi_{7, 8}`. For $`m = 0`, remove instance $`n` and
return its instruction counter in $`\varphi'_7`; for $`m = 1`, remove module $`n` and return
$`\mathtt{OK}`. $`\mathtt{WHO}` if there is no such instance or module; $`\mathtt{HUH}` for any other
$`m`. $`g \equiv \mathsf{M}_X`.

{leanSource JAM.RefineHost.expunge}

## Accumulate functions (§B.5.3)
%%%
tag := "invocations-accumulate-functions"
%%%

These work on the accumulate context, and change only the regular dimension $`\mathbf{x}` (except
`checkpoint`):

{gpeq "B.19"}

$`\mathbf{d} = (\mathbf{x}_\mathbf{e})_\mathbf{d}` is the accounts of the current partial state. Many
functions ask that the caller $`\mathbf{x}_s` be the service $`d` it changes or that service's effective
supervisor $`\mathbf{d}[d]_e` ({ref "accounts"}[§9.5]): in the model, {api}`JAM.AccHost.mayModify`. A function that changes
service $`d`'s account adds $`d` to $`\mathbf{x}_\mathbf{w}`.

{leanSource JAM.AccHost.mayModify}

*`lookup` = 3*, $`\Omega_L`. In: $`\varphi_7` names the service, the hash is at $`h = \varphi_8`; then
$`o = \varphi_9`, $`f_0 = \varphi_{10}`, $`z = \varphi_{11}`. $`\mathbf{v}` is the preimage
$`\mathbf{a}_\mathbf{p}[\mu_{h \dots+ 32}]`. $`g \equiv \mathsf{M}_{L,c} + \mathcal{G}(\mathsf{M}_{L,\ell}, z)`.

*`read` = 4*, $`\Omega_R`. In: $`\varphi_7` names the service, the key is $`\mu_{k_O \dots+ k_Z}` with
$`[k_O, k_Z, o] = \varphi_{8 \dots+ 3}`; then $`f_0 = \varphi_{11}` and $`z = v_Z = \varphi_{12}`.
$`\mathbf{v}` is the storage value $`\mathbf{a}_\mathbf{s}[\mathbf{k}]`.
$`g \equiv \mathsf{M}_{R,c} + \mathcal{G}(\mathsf{M}_{R,\mathrm{k},\ell}, k_Z) + \mathcal{G}(\mathsf{M}_{R,\mathrm{v},\ell}, v_Z)`.

*`info` = 6*, $`\Omega_I`. In: $`\varphi_7` names the service; $`o = \varphi_8`,
$`f_0 = \varphi_9`, $`z = \varphi_{10}`. $`\mathbf{v}` is the encoding of the account's code hash,
supervisor and its creation slot, balances, threshold, gas limits, octets, items, gratis offset,
creation and last-accumulation slots and parent. $`g \equiv \mathsf{M}_I`.

The paper lists `lookup`, `read` and `info` with the accumulate functions. They only read the context,
so the model writes them in `JAM/Host/General.lean`, taking the caller's account $`\mathbf{x}_\mathbf{s}` and
$`\mathbf{d}`:

{leanSource JAM.namedAccount}

{leanSource JAM.hostLookup}

{leanSource JAM.hostRead}

{leanSource JAM.infoValue}

{leanSource JAM.hostInfo}

*`write` = 5*, $`\Omega_W`. In: $`\varphi_7` names the service $`d`; the key is at
$`[k_O, k_Z] = \varphi_{8 \dots+ 2}` and the value at $`[v_O, v_Z] = \varphi_{10 \dots+ 2}`. An empty value
deletes the key. Outcomes: ☇ if key or value is not readable; $`\mathtt{WHO}` if $`d` is not a service;
$`\mathtt{HUH}` unless $`\mathbf{x}_s \in \{d, \mathbf{d}[d]_e\}`; $`\mathtt{FULL}` if afterwards
$`d`'s threshold exceeds its balance plus supervisor balance, or its items or octets leave
$`\mathbb{N}_{2^{32}}` or $`\mathbb{N}_{2^{64}}`; otherwise $`\varphi'_7` is the length of the previous
value ($`\mathtt{NONE}` if there was none).
$`g \equiv \mathsf{M}_{W,c} + \mathcal{G}(\mathsf{M}_{W,\mathrm{k},\ell}, k_Z) + \mathcal{G}(\mathsf{M}_{W,\mathrm{v},\ell}, v_Z)`.

{leanSource JAM.AccHost.write}

*`bless` = 16*, $`\Omega_B`. In: $`[m, a, v, r, o, n] = \varphi_{7 \dots+ 6}`: the new manager $`m`,
assigners (at $`a`, 4 octets per core), delegator $`v`, registrar $`r`, and $`n` always-accumulate
entries (at $`o`, 12 octets each). The value $`2^{64} - 1` keeps a role, or the whole assigner list or
always-accumulate set, as it is; an assigner entry $`2^{32} - 1` keeps that core's assigner. The manager
may set anything; any other caller may only hand on the roles it holds and must leave everything else
as it is. Outcomes: ☇ if a list is not readable; $`\mathtt{HUH}` if the caller may not make the change,
or the always-accumulate list repeats a service; $`\mathtt{WHO}` if $`m'`, $`v'` or $`r'` is not in
$`\mathbb{N}_S`; otherwise $`\mathtt{OK}`. $`g \equiv \mathsf{M}_{B,c} + n \cdot \mathsf{M}_{B,\ell}`.

{leanSource JAM.AccHost.bless}

*`assign` = 17*, $`\Omega_A`. In: $`[c, o, a] = \varphi_{7 \dots+ 3}`: set core $`c`'s authorizer queue
to the $`\mathsf{Q}` hashes at $`o`, and its assigner to $`a`. Outcomes: ☇ if the queue is not readable;
$`\mathtt{CORE}` if $`c \ge \mathsf{C}`; $`\mathtt{HUH}` unless the caller is core $`c`'s assigner;
$`\mathtt{WHO}` if $`a \notin \mathbb{N}_S`; otherwise $`\mathtt{OK}`. $`g \equiv \mathsf{M}_A`.

{leanSource JAM.AccHost.assign}

*`designate` = 18*, $`\Omega_D`. In: $`[o, z] = \varphi_{7 \dots+ 2}`: set the staging validator keys to
the $`z` keys of 336 octets at $`o`. Outcomes: ☇ if they are not readable; $`\mathtt{HUH}` if
$`z \notin \mathbb{V}` or the caller is not the delegator; otherwise $`\mathtt{OK}`.
$`g \equiv \mathsf{M}_{D,c} + z \cdot \mathsf{M}_{D,\ell}`.

{leanSource JAM.AccHost.designate}

*`checkpoint` = 19*, $`\Omega_C`. $`\mathbf{y}' \equiv \mathbf{x}` and $`\varphi'_7 \equiv \varrho^*`:
the exceptional dimension becomes the current regular one. $`g \equiv \mathsf{M}_C`.

{leanSource JAM.AccHost.checkpoint}

*`new` = 20*, $`\Omega_N(\varrho, \varphi, \mu, (\mathbf{x}, \mathbf{y}), t)`. In: $`\varphi_7` names
the funding service $`s`; $`[i, x, o] = \varphi_{8 \dots+ 3}` are the desired identifier, the mode and
the address of 60 octets holding the new account's code hash $`c`, request length $`l`, gas limits
$`g` and $`m` and gratis offset $`f`. The new account's threshold is paid from $`s`'s balance
($`x \in \{0, 2\}`) or supervisor balance ($`x \in \{1, 3\}`), and lands in the new account's balance
($`x \in \{0, 1\}`) or supervisor balance ($`x \in \{2, 3\}`). Its supervisor and parent are the caller.
The registrar may choose an identifier $`i < \mathsf{S}`; otherwise the new account takes
$`\mathbf{x}_i`, and $`\mathbf{x}_i` moves on to
$`\text{check}(\mathsf{S} + (\mathbf{x}_i - \mathsf{S} + 42) \bmod (2^{32} - \mathsf{S} - 2^8))`.
Outcomes: ☇ if the 60 octets are not readable; $`\mathtt{HUH}` if $`l \notin \mathbb{N}_P`;
$`\mathtt{WHO}` if $`s` is not a service; $`\mathtt{HUH}` if $`x > 3`, the caller may not draw on the
chosen balance, or $`f \ne 0` and the caller is not the manager; $`\mathtt{CASH}` if $`s` cannot pay;
$`\mathtt{FULL}` if the registrar's chosen identifier is taken; otherwise $`\varphi'_7` is the new
identifier. $`g \equiv \mathsf{M}_N`.

{leanSource JAM.AccHost.new}

*`supervisor` = 29*, $`\Omega_V`. In: $`\varphi_7` names service $`d`, $`\varphi_8` service $`u`:
$`d`'s supervisor becomes $`u`, recorded with $`u`'s creation slot. Outcomes: $`\mathtt{WHO}` unless both
are services; $`\mathtt{HUH}` unless the caller is $`d`'s effective supervisor; otherwise $`\mathtt{OK}`.
$`g \equiv \mathsf{M}_V`.

{leanSource JAM.AccHost.supervisor}

*`upgrade` = 21*, $`\Omega_U`. In: $`\varphi_7` names service $`d`; $`[o, a, m] = \varphi_{8 \dots+ 3}`:
the new code hash (at $`o`) and gas limits. Outcomes: ☇ if the hash is not readable; $`\mathtt{WHO}` if
$`d` is not a service; $`\mathtt{HUH}` unless $`\mathbf{x}_s \in \{d, \mathbf{d}[d]_e\}`; otherwise
$`\mathtt{OK}`. $`g \equiv \mathsf{M}_U`.

{leanSource JAM.AccHost.upgrade}

*`transfer` = 22*, $`\Omega_T`. In: $`\varphi_7` names the source $`s` and $`\varphi_8` the destination
$`d`; $`[x, a, l, o] = \varphi_{9 \dots+ 4}` are the mode, amount, gas limit and memo address. Modes
$`x \in \{0, 2\}` debit $`s`'s balance and $`\{1, 3\}` its supervisor balance; $`x \in \{0, 1\}` credit
$`d`'s balance and $`\{2, 3\}` its supervisor balance. With $`o = 0` the credit is immediate; otherwise a
deferred transfer carrying the memo $`\mu_{o \dots+ \mathsf{W}_T}` and gas limit $`l` is appended to
$`\mathbf{x}_\mathbf{t}`. Outcomes: ☇ if the memo is not readable; $`\mathtt{WHO}` unless both are
services; $`\mathtt{HUH}` if $`x > 3` or the caller may not make the debit or the credit;
$`\mathtt{LOW}` if $`o \ne 0` and $`l` is below $`d`'s minimum memo gas; $`\mathtt{CASH}` if the
source's balances after the transfer, $`\mathbf{d}'[s]`, go negative or below its threshold; otherwise
$`\mathtt{OK}`. $`g \equiv \mathsf{M}_T + t`, where $`t = l` for a deferred transfer that succeeds and
0 otherwise.

{leanSource JAM.AccHost.transferCode}

{leanSource JAM.AccHost.transfer}

*`eject` = 23*, $`\Omega_J(\varrho, \varphi, \mu, (\mathbf{x}, \mathbf{y}), t)`. In: $`d = \varphi_7`.
Remove service $`d` and credit its balance and supervisor balance to the caller. Outcomes:
$`\mathtt{WHO}` if $`d` is not a service; $`\mathtt{HUH}` if $`d` is the caller, the caller is not
$`d`'s effective supervisor, $`d` was created at $`t`, or $`d`'s item count $`\mathbf{d}[d]_i` is not 0; otherwise
$`\mathtt{OK}`. $`g \equiv \mathsf{M}_J`.

{leanSource JAM.AccHost.eject}

*`query` = 24*, $`\Omega_Q`. In: $`\varphi_7` names the service; $`[o, z] = \varphi_{8, 9}`: the request
for the hash at $`o` with length $`z`. Outcomes: $`\mathtt{HUH}` if $`z \notin \mathbb{N}_P`; ☇ if the
hash is not readable; $`\mathtt{WHO}` if there is no such service; otherwise the request's history
of up to three timeslots, packed into $`\varphi'_7` and $`\varphi'_8`: $`(\mathtt{NONE}, 0)` with no
request, $`(0, 0)` for $`[]`, $`(1 + 2^{32}x, 0)` for $`[x]`, $`(2 + 2^{32}x, y)` for $`[x, y]` and
$`(3 + 2^{32}x, y + 2^{32}z)` for $`[x, y, z]`. $`g \equiv \mathsf{M}_Q`.

{leanSource JAM.AccHost.query}

*`solicit` = 25*, $`\Omega_S(\varrho, \varphi, \mu, (\mathbf{x}, \mathbf{y}), t)`. In: $`\varphi_7` names
service $`d`; $`[o, z] = \varphi_{8, 9}`. A new request starts with history $`[]`; a request with
history $`[x, y]` becomes $`[x, y, t]`. Outcomes: $`\mathtt{HUH}` if
$`z \notin \mathbb{N}_P`; ☇ if the hash is not readable; $`\mathtt{WHO}` if $`d` is not a service;
$`\mathtt{HUH}` unless $`\mathbf{x}_s \in \{d, \mathbf{d}[d]_e\}`, or if the request is in any other
state; $`\mathtt{FULL}` under the same footprint conditions as `write`; otherwise $`\mathtt{OK}`.
$`g \equiv \mathsf{M}_S`.

{leanSource JAM.AccHost.solicit}

*`forget` = 26*, $`\Omega_F(\varrho, \varphi, \mu, (\mathbf{x}, \mathbf{y}), t)`. In: as `solicit`. By the
request's history: $`[]` removes the request; $`[x, y]` with $`y < t - \mathsf{D}` removes the request
and the preimage; $`[x]` becomes $`[x, t]`; $`[x, y, w]` with $`y < t - \mathsf{D}` becomes $`[w, t]`.
Outcomes: as `solicit`, with $`\mathtt{HUH}` for any other history, and no $`\mathtt{FULL}`.
$`g \equiv \mathsf{M}_F`.

{leanSource JAM.AccHost.forget}

*`yield` = 27*, $`\Omega_{\text{♉}}`. In: $`o = \varphi_7`. Outcomes: ☇ if the 32 octets at $`o` are not
readable; otherwise $`\mathbf{x}'_y` is that hash and $`\varphi'_7 = \mathtt{OK}`. $`g \equiv \mathsf{M}_{\text{♉}}`.

{leanSource JAM.AccHost.yield}

*`provide` = 28*, $`\Omega_{\text{♈}}`. In: $`\varphi_7` names service $`s`; the preimage is
$`\mathbf{i} = \mu_{o \dots+ z}` with $`[o, z] = \varphi_{8, 9}`. Outcomes: $`\mathtt{HUH}` if
$`z \notin \mathbb{N}_P`; ☇ if $`\mathbf{i}` is not readable; $`\mathtt{WHO}` if $`s` is not a service;
$`\mathtt{HUH}` unless $`s`'s request for $`(\mathcal{H}(\mathbf{i}), z)` has history $`[]`;
$`\mathtt{HUH}` if $`(s, \mathbf{i})` is already provided; otherwise $`(s, \mathbf{i})` is added to
$`\mathbf{x}_\mathbf{p}` and $`\varphi'_7 = \mathtt{OK}`.
$`g \equiv \mathsf{M}_{\text{♈},c} + \mathcal{G}(\mathsf{M}_{\text{♈},\ell}, z)`.

{leanSource JAM.AccHost.provide}

## Logging

GP v0.8.1 defines no logging host function. A program that makes a host call with an identifier
outside the tables above gets the dispatcher's last case: it is charged $`\mathsf{M}_\emptyset` and
$`\varphi'_7 = \mathtt{WHAT}`, and nothing else changes.

# What is proved
%%%
tag := "invocations-theorems"
%%%

*The dispatchers never add gas.* Every host function charges $`g \ge 0`. The one that hands gas back,
`invoke`, returns only what is left of the $`g_R` it charged, because $`\Psi` never ends with more gas
than it started with ({api}`PVM.psi_gas_le`). The model proves this for the dispatchers of all three
invocations, using the property {api}`PVM.HostFn.GasNonIncreasing`:

{mathdoc PVM.HostFn.GasNonIncreasing}

{mathdoc JAM.accHostFn_gasNonIncreasing}

{mathdoc JAM.refineHostFn_gasNonIncreasing}

{mathdoc JAM.isAuthHostFn_gasNonIncreasing}

With these, {api}`PVM.psiHStar_eq` applies to all three invocations: for a handler that does not add
gas, the model's $`\Psi_H^*` satisfies the paper's defining equation (see the {ref "pvm"}[Appendix A chapter]).

*What a service's host calls can reach.* $`\Psi` only stops for the host-call identifiers of the
program's own `ecalli` instructions, so the host calls a service can make are fixed by its code. Two
consequences are proved, about the identifiers {api}`PVM.jamHostCallIdsOf` reads off a standard
program blob without running it:

{mathdoc PVM.jamHostCallIdsOf}

{mathdoc JAM.reachingIds}

{mathdoc JAM.NoSupervisee}

{mathdoc JAM.Outside}

{mathdoc JAM.psiA_confined}

{mathdoc JAM.psiR_noExports}

# Readings chosen
%%%
tag := "invocations-readings"
%%%

These points are recorded in the model's
[notes on the paper](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues):

* *Note 18, $`\Psi_R`.* The dispatcher passes the extrinsic data $`\overline{\mathbf{x}}` to `fetch`,
  but $`\Psi_R`'s arguments do not include it; the account state is implicit too. The model takes
  both as arguments of {api}`JAM.psiR` (`extrinsics` and `d`), and {api}`JAM.psiI` takes the account
  state the same way.
* *Note 20, `pages`.* The row defines only $`(\varphi'_7, \mathbf{m}')`, with no $`\varepsilon'`. The
  model uses the default $`\varepsilon' = \blacktriangleright` of {eq}`B.17`: `pages` never panics
  ({api}`JAM.RefineHost.pages`).
* *Note v0.8.1-A19, `new` and check.* $`\text{check}` {eq}`B.13` tests $`i \notin \mathcal{K}(\mathbf{e}_\mathbf{d})`
  against the state passed to $`\Psi_A`, but `new` uses it in the middle of an invocation. The model
  checks against the current accounts $`(\mathbf{x}_\mathbf{e})_\mathbf{d}` ({api}`JAM.AccHost.new`);
  the two differ only if the sequence meets an identifier created or ejected earlier in the same
  invocation.
* *Note v0.8.1-A20, `new` by the registrar.* With the registrar choosing $`i < \mathsf{S}` equal to
  the funding service $`s`, the paper's $`\mathbf{d}'` sets $`\mathbf{d}'[i']` to the new account and
  also changes $`\mathbf{d}'[s]`'s balance, which conflict. The model tests $`\mathtt{CASH}` on $`s`'s
  own balances, then answers $`\mathtt{FULL}`.

* *Note v0.8.1-A36, a missing work item.* $`\Psi_R` reads $`w = p_\mathbf{w}[i]` without saying what happens when the
  package has no item $`i`. The model answers $`(\texttt{BAD}, [], 0)`, as for a missing service.
