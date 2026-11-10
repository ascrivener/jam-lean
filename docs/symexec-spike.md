# Spike: a verified symbolic executor for PVM code

Status: feasibility spike, not adopted. Whether to switch method is Adam's decision.
Code: the generic executor is in `PVM/SymExec/` (imported by `PVM.lean`). The Bootstrap code table and the Bootstrap stretches are in `Services/Bootstrap/SymExec/` (imported by `Services.lean`). Both are in the default build. Generators: `PVM/SymExec/gen_*.py`. The spike's BTail1 demo instances (`BTail1S0`, `BTail1S0to32`, `BTail1Cuts`) were measurement scaffolding; they were removed when the migrated BTail1 chain superseded them, and remain in git history.

## Short answer

**It works, and it is fast.** One Lean function runs a stretch of PVM code over a symbolic state.
Its soundness against `Program.freeStep` / `FreeStepsH` (GP v0.8.0 §A.4–A.5) is proved once.
Each stretch is then one theorem closed by `decide +kernel`: the kernel evaluates a Boolean check.
There is no `native_decide`, no `bv_decide` and no `sorry`. The axioms are only `propext`,
`Classical.choice` and `Quot.sound`.

* **Same statement.** `PVM.SymExec.BTail1S0.run` has a statement definitionally equal to
  `Services.Bootstrap.BTail1.S0.run` (checked with `rfl` on the types).
* **Symbolic memory.** `PVM.SymExec.FixedZ.z1` and `.z2` have statements definitionally equal to
  `Services.Bootstrap.Decode.Fixed.z1` and `.z2`. These are hand-written stretches with a symbolic
  stack pointer `A`, a symbolic output slot `O`, a disjointness hypothesis between them, frame
  conditions, and a final return to a symbolic address. The executor proves them in ≈1.5 s net,
  against ≈10.8 s for the hand-written proofs.
* **Longer stretches.** `PVM.SymExec.BTail1S0to32.run` proves `St0 → St32` of BTail1: 512 steps,
  pc 35202 to pc 68840, with function calls and returns through the jump table. That replaces the
  32 generated files `S0` … `S31` with one check.
* **Kernel speed.** The kernel evaluates the executor at about 6–7.5 ms per PVM step. Cost grows
  linearly from 16 to 512 steps.
* **Against the generated proofs.** On the same 512 steps, checking takes about 30× less time
  (5.9 s against 173 s) and the source is 8.5× smaller (76 KB against 645 KB). Both can improve
  further (see the plan).

**Recommendation: pursue it in phases.** Symbolic memory (base + offset addresses with frame
conditions) is now prototyped and stays fast and sound; see "Symbolic memory" below.

Phase 1 (2–3 days) lets the executor take over the
straight-line and concrete-branch stretches the generator now emits. Each later phase widens what
it covers, and each can stop independently. Loops keep their hand-written invariants.

## What was built

| File | Lines | What it is |
|---|---|---|
| `PVM/SymExec/Core.lean` | 468 | Symbolic values `SVal`, affine addresses `Aff`, state `SState`, `sstep`, `srun` (the executor) |
| `PVM/SymExec/Sound.lean` | 1049 | `sstep_sound`, `srun_sound`: soundness against `Program.exec` / `freeStep` / `FreeStepsH` |
| `PVM/SymExec/Check.lean` | 320 | `check` (run, then compare with a target spec and a frame), `check_sound`, `ret_step` |
| `PVM/SymExec/FixedZ.lean` | 166 | `Decode.Fixed.z1` / `z2` by the executor: symbolic stack pointer and output slot (hand-written) |
| `PVM/SymExec/gen_stretch.py` | 202 | Prototype generator: turns `St_k`/`St_l`, the segment files and the code facts into a check |
| `PVM/SymExec/BTail1S0.lean` | 218 | St0 → St1 (16 steps): the replacement of `BTail1/S0.lean` |
| `PVM/SymExec/BTail1S0to32.lean` | 875 | St0 → St32 (512 steps): replaces `S0` … `S31` |

**Design.**

* **Values** (`SVal`) are terms over named naturals (S, C, I, L) and the start registers and memory.
  The paper's own mutation functions are nodes: `twoRegImmAlu`, `threeRegAlu` and `twoRegAlu` of
  §A.5.9, §A.5.10 and §A.5.13. So every ALU instruction is supported with **no per-operation
  proof**: soundness is by construction. Smart constructors fold literals and drop `mod`s that the
  bounds of the named naturals show do nothing.
* **Addresses** are affine (`Aff`): a literal, or ρ_k + d with an integer offset d. Named naturals
  have lower and upper bounds, so every address has an interval. Two regions are disjoint when they
  share a base and their offsets say so, when their intervals say so, or when a declared separation
  says so. A separation is a hypothesis of the stretch, such as `O + 12 ≤ A - 12 ∨ A + 56 ≤ O`.
* **Memory** is a list of cells `μ_{a…+n} = ℰ_n(v)` at affine addresses, plus a list of dirty
  regions; anything not dirty reads as at the start.
  * A store keeps the parts of a literal cell it does not overwrite, as fragments.
  * A load finds an exact cell, or assembles literal octets from several cells, or reads the start
    memory.
  * Readable and writable ranges are static, because stores do not change pages. Each access is
    checked against them, so ε^μ = ▸ is proved.
* **Code** is a search tree of `d_i` facts, plus the needed `bs_i` and `jte_k` facts and `jts`.
  It comes from the existing code facts (`HasCode`), so nothing new is trusted.
* **Check** runs exactly `k` steps from the start pc and requires the end pc. It compares
  registers and cells with the target `St` up to `mod`, and requires every write to lie inside
  the frame (the next `C_k` ranges).

**Instructions covered now.** All ALU instructions; loads and stores at a concrete base plus an
offset (§A.5.10), and at absolute addresses (§A.5.6, unsigned loads); `store_imm_ind_*`;
`load_imm`; `load_imm_64`; `jump`; `load_imm_jump`; `fallthrough`; `unlikely`; branches (§A.5.8,
§A.5.11) whose condition evaluates to a literal; and `jump_ind` / `load_imm_jump_ind` through the
jump table.

**Returns.** A return through the jump table to a symbolic address (`ret` with
**j**_{ret/2−1} = t) is one generic lemma, `ret_step`, applied after the check.

**Not covered.** Host calls, `trap`/halt exits (`FreeRunH`), `store_imm_*` at absolute addresses,
symbolic branch conditions, addresses with two symbolic terms (base + index·stride), regions of
symbolic length, and table reads at a symbolic index. On any of these `srun`
returns `none`, `check` is `false`, and nothing is proved. Soundness never depends on coverage.

## Measurements

The machine has 4 cores and 15 GB of RAM. Every figure is one `lake env lean <file>` run, with
the dependencies already built. Loading the imports alone (Code facts, St) takes **1.2 s and
1.65 GB**. Times marked "net" subtract that load.

### Kernel cost of the check (the key unknown; first iteration, concrete addresses)

| Stretch | Steps | Kernel `decide` | Per step |
|---|---:|---:|---:|
| St0→St1 | 16 | 103 ms | 6.4 ms |
| St0→St2 | 32 | 184 ms | 5.8 ms |
| St0→St4 | 64 | 458 ms | 7.2 ms |
| St0→St8 | 128 | 765 ms | 6.0 ms |
| St0→St16 | 256 | 1.6 s | 6.3 ms |
| St0→St32 | 512 | 3.84 s | 7.5 ms |

Before the code table became a search tree, the instruction lookup was a linear scan. The kernel
then took 11.9 s for 512 steps, growing roughly quadratically. The tree fixed that.

### Against the generated proofs

| | Generated (`BTail1/S*.lean`) | Executor |
|---|---|---|
| St0→St1 (16 steps): wall time | 30.2 s (29 s net) | 1.9 s (0.7 s net) |
| St0→St1: source | 122 lines, 22 KB | 218 lines, 15 KB |
| St0→St32 (512 steps): wall time | 211 s over 32 files (≈173 s net) | 7.1 s (5.9 s net), one file |
| St0→St32: source | 3,790 lines, 645 KB (32 files) | 875 lines, 76 KB |
| Peak RSS | 1.72–1.83 GB per file (≈0.1–0.2 GB over imports) | 1.70 GB (16 steps), 1.82 GB (128), 1.99 GB (256), 2.38 GB (512) |

Notes on the table:

* S0 is the slowest generated segment, because of its 24 per-octet hypotheses. S1–S31 take
  4–10 s each. Even so, the executor is about **30× faster per step** across S0–S31.
* Memory per check grows with stretch length: +0.73 GB at 512 steps. Chunks of 128–256 steps keep
  it under +0.35 GB.
* About 485 of the 875 lines in `BTail1S0to32.lean` are the instruction tree, which is the same
  data as `Code.lean`. About 100 more lines are the bridge between `St` structures and specs.
  Phase 1 removes both (see the plan), leaving about 250 lines of target data for 512 steps. That
  is **≈25× less source**, and it involves no recompilation-sensitive per-step text.
* In the 512-step file, the bridge's `omega` over about 100 frame ranges takes 2.8 s, more than
  half the non-kernel time. A Boolean frame check removes it.

### Symbolic memory (second iteration)

Addresses became affine for this round. The same check now also decides disjointness from bounds
and declared separations.

| | Hand-written (`Decode/Fixed.lean`, `pvm_go`) | Executor (`FixedZ.lean`) |
|---|---|---|
| `z1` + `z2` (9 + 15 steps, symbolic A and O): wall time | 11.9 s (≈10.8 s net) | 2.65 s (≈1.5 s net); the kernel checks take ≈0.2–0.3 s, the rest is the bridge to the hypotheses |
| Source | 63 lines (statements and proofs) | 166 lines (spec data and bridge, written by hand) |
| Peak RSS | 1.88 GB | 1.71 GB |

* By hand, the executor is not shorter. The win is speed, and that the proof does not depend on
  the instruction text. A generator or tactic that reads the spec from the hypotheses would remove
  most of those lines.
* What the affine generality costs: the 512-step BTail1 check now takes 5.9 s in the kernel
  (11.6 ms per step), against 3.8 s (7.5 ms per step) in the concrete-address version. Growth is
  still linear, and the whole file takes 9.1 s against 211 s for the generated files.
* Soundness covers everything above; nothing is assumed beyond what each stretch's hypotheses
  state.

## Answers to the questions

**1. Can the kernel evaluate it fast enough without `native_decide`?** Yes. It runs at about
6–7.5 ms per step, linearly up to 512 steps. The generated proofs cost about 300 ms per step (S1–S31)
and about 1.8 s per step (S0). Two things matter for speed: lookups must be logarithmic (a tree,
not a list), and the state must not grow with the trace (dirty ranges are deduplicated).

**2. Prototype on an existing stretch.** Done twice.

* `BTail1S0.run` has exactly `S0.run`'s statement (`St0 → ∃ ω' μ', FreeStepsH … 16 ∧ St1`), so it
  can replace `S0` in the `BTail1.chain` composition.
* `BTail1S0to32.run` proves `St0 → St32` in one step. It replaces `S0` … `S31` and the first 31
  links of `chain`.
* Going further, St0→St48 runs for 572 steps and then stops at a load at a symbolic address:
  `load_u8 r10, [71060 + (S & 15)]`, a hex-digit table. This is the first construct the prototype
  does not cover.

**3. Comparison.** See the tables above. On the same stretch, checking is about 30× faster, the
source is about 8.5× smaller now (about 25× with phase 1), and the extra memory is moderate.
Recompiling the binary changes only the data: the code facts, the cut states and the pcs. The
generic proofs stay the same.

**4. Cost to cover the rest** (working days, one session):

| Item | Cost | Notes |
|---|---|---|
| Rest of the instruction set Bootstrap uses | 1 | `store_imm_*` absolute, signed absolute loads; same pattern as the existing cases |
| `trap`/halt/fault exits (`FreeRunH`, e.g. the run to the trap at 6377 in `EmptyPayload`) | 1 | `srun` ends on a non-▸ status; soundness via `FreeExit` |
| Integration (phase 1) | 2–3 | One shared code tree for the whole binary, proved once from `HasCode`. `St_k` defined as `Spec` data, so no bridge. A Boolean frame check. The generator emits only cut specs. A `#eval` diagnostic for failing checks (I used one in the spike) |
| Symbolic branch conditions | 2–3 | Decide comparisons from the named naturals' bounds (cheap and common); otherwise fork on the condition and return both paths as hypotheses |
| Symbolic memory | **done for base + offset** (≈1 day); 2–4 more | Done: affine addresses, bounds, offset disjointness, declared separations, symbolic frames (`FixedZ`). Remaining: base + index·stride (loop indices), regions of symbolic length (`[S0, S1)`), table reads at a bounded symbolic index |
| Host calls under contracts (`refineContract`, `accContractK`) | 3–5 | `srun` stops at `ecalli` and the stretch splits there. Each contract lemma is lifted once to a symbolic transformer: fresh named naturals for the outputs, its memory frame as dirty ranges. Cost depends on how uniform the contracts' post-conditions are |
| Loops | 5–10 | Hand invariants remain. The executor proves the body, from invariant state to invariant state with a symbolic counter. That needs the linear-arithmetic normal form of the memory item and a proved normaliser |

**5. Recommendation: pursue it in phases.**

* **Phase 1, about 1 week: integration plus the remaining instructions and exits.** This alone
  can replace most of the generated `S*` files for straight-line and concrete-branch code, at about
  30× less checking time and about 25× less source.
* **Phase 2, about 1 week: bounds-decided branches and symbolic table and offset addressing.**
  This removes the blocker found at St0→St48 and the like.
* **Phase 3, 1–2 weeks: host-call contracts, then loop bodies.**

Each phase is independently useful, and the generated files can remain wherever the executor does
not yet reach. Mixing is free, because both produce the same `FreeStepsH` / `St_k` statements.

If only one thing is done, do phase 1. It is where most of the 561k generated lines and most of
the CI time come from, and the risk is low: the soundness proof is done, and coverage failures
show up as a `false` check, never as an unsound proof.

## Phase 1 (in progress)

Integration work, on branch `claude/symexec-phase1`:

* **One shared code table per binary** (`Services/Bootstrap/SymExec/Prog.lean`, generated by
  `PVM/SymExec/gen_prog.py`).
  * It holds every instruction fact (5,421), block start (5,581) and jump-table entry (260) of
    `Services.Bootstrap.Code` as search trees.
  * `hyp : ProgHyp p P prog` is proved once from the code facts' `d_i`, `bs_i`, `jte_k` and `jts`.
  * The file is 11k lines, generated, and checks once in ≈20 s.
  * Stretch files no longer carry any code data.
* **Cut states as data** (`PVM/SymExec/Cut.lean`).
  * A `Cut` lists registers, cells, readable and writable regions, and the frame (the regions
    written since the chain's start). `Cut.Holds vals μ₀ c ω μ` is what it asserts.
  * `seg_sound` turns one Boolean `segCheck` into `A.Holds → ∃ …, FreeStepsH … ∧ B.Holds`.
  * `segCheck` also checks the frames and regions as Booleans, so a segment needs no bridge proof
    and no `omega`.
  * Example: `Services/Bootstrap/SymExec/BTail1Cuts.lean` covers 512 steps of BTail1 as two 256-step segments.
    It is 51 lines and checks in 7.7 s.
* **Exits and returns.** `trap_exit` (☇), `halt_exit` (∎ through `jump_ind` to 2^32 − 2^16) and
  `ret_step` (a return through **j** to a symbolic address) close a chain.
* **Instructions.** Added `store_imm_*` at an absolute address, and signed loads at an absolute
  address (`load_i8/16/32`). The latter use 𝒳_n; `sext_eq` proves that equals 𝒵⁻¹_8(𝒵_n(·)) on
  loaded values. BParams uses one at pc 56090.
* **Simplification.** The zero-extension idiom now normalises to v when the bounds allow:
  `add_imm_32 0` of v < 2^31, and `shlo_r_imm_64 s` of `shlo_l_imm_64 s` of w with w·2^s < 2^64
  (`zextRule`).
* **Branches decided by bounds.** A branch against an immediate on a symbolic value is followed
  when the value's bounds decide it. This covers unsigned comparisons only. Example:
  `branch_eq_imm r, 0` with 1 ≤ ρ_k is never taken. The rules are in `scond` and `decideCond`.
* **Diagnostics.** `PVM/SymExec/Trace.lean`: `#eval traceSeg …` reports the first step the
  executor cannot follow, or the target facts that do not entail. It uses the same tests as the
  check, so it reports nothing on a check the kernel accepts.

## Generator interface

What a generator (e.g. `genwitnesssteps`) should emit to target the executor.

**Per binary**, regenerated on every recompile: the module `gen_prog.py` produces, i.e. `prog : Prog`
and `hyp : ProgHyp p P prog` from the binary's code facts. The code facts must include:
* every instruction the stretches visit;
* `isBlockStart` for every branch or jump target and every branch's fall-through successor;
* the jump-table entries reached, and |**j**| (`jts`).

**Per chain**, i.e. per path through the binary:
* `vals`: the named naturals, in order (e.g. `[S, C, I, L]`), with exclusive upper bounds `ub` and
  lower bounds `lb`. Proofs `BHold vals ub` and `LBHold vals lb` come from the chain's hypotheses.
* `sep`: pairs of regions declared disjoint, each proved from a hypothesis. A pair has the form
  `((⟨some k, d⟩, n), (⟨some k', d'⟩, n'))`.
* One `cut_i : Cut` per cut point:
  * `regs`: pairs `(r, v)` with `r < 13`;
  * `cells`: `(address, width, value)`;
  * `rd`, `wr`: regions, each `(address, length)`;
  * `frame`: every region written since the chain's start, cumulative. A cut's frame must cover the
    previous cut's frame.
  * Values must be closed: `.const n`, `.var k`, `.addr ⟨some k, d⟩`, or `.const (Num.decodeLE
    [bytes])` for literal octets. Addresses are `⟨none, n⟩` (literal) or `⟨some k, d⟩`
    (ρ_k + d, with d an integer).
* One theorem per segment. Its statement is
  `cut_a.Holds vals μ₀ ω μ → ∃ ω' μ', FreeStepsH p R start ω μ x tgt ω' μ' x k ∧ cut_b.Holds vals μ₀ ω' μ'`.
  Its proof is one line:
  `seg_sound (lb := lb) (sep := sep) (by decide +kernel) (Prog.hyp (p := p) (P := P)) hB hLB hsep h x`.
* Composition is `FreeStepsH.trans`. A chain ends with `trap_exit`, `halt_exit` or `ret_step`.

**Where to cut.**
* A segment can be as long as the executor can follow it. Keep each check to 128–256 steps, so its
  memory stays around +0.3 GB.
* A chain must also be cut wherever the executor cannot follow: host calls, branches on symbolic
  conditions, table reads at a symbolic index, base + index·stride addresses, and regions of
  symbolic length. A hand-written summary takes over there; its pre- and post-conditions are
  stated as, or converted to and from, `Cut.Holds`.

**Debugging.** `#eval traceSeg prog ub lb sep cut_a cut_b start tgt k`.

**Migration.** The existing `St_k` structures and their downstream uses (`S_k.run`, `chain`) can be
kept by generating `St_k` as an abbreviation for `cut_k.Holds …`, or by adapter lemmas.
`BTail1S0.lean` shows such a bridge, generated against today's `St` structures.

## Risks and caveats

* **No coverage diagnostics.** When a check is `false`, `decide +kernel` gives no reason. The fix
  is an `#eval` tracer over the same executor; the spike used one, and it found each gap in
  minutes. Phase 1 should ship it.
* **Memory grows with stretch length** (+0.73 GB at 512 steps). Keep checks to 128–256 steps, or
  split at existing cuts.
* **`decide +kernel` sends the whole evaluation to the kernel.** That is the point. The kernel's
  `Nat` literals are GMP-backed, so constant folding is cheap. The elaborator never evaluates the
  check.
* **Trust is unchanged.** The executor adds no axioms and no trusted code. Its soundness rests on
  the same `Program.exec`, `freeStep` and code facts as the existing proofs.
* **The prototype generator reads the existing generated files.** It is a spike tool. A real one
  would come from `genwitnesssteps`'s own trace data.
* **No discrepancies found.** The spike found no paper/vector or model/binary disagreement, so
  `docs/upstream-candidates.md` is unchanged.
