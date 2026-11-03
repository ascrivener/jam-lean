# jam-lean

An executable Lean 4 model of JAM from the
[Gray Paper](https://github.com/gavofyork/graypaper) **v0.8.0**: the Polkadot Virtual Machine
(Appendix A, library `PVM`), and Appendix B with the protocol terms it needs (library `JAM`, in
progress). The PVM is checked against the PVM test vectors of
[koute/jamtestvectors](https://github.com/koute/jamtestvectors) (branch `master_pvm_initial`,
commit `6bf3768e5b37bbe4ca5d6e1306284ecb27c0198f`, directory `pvm/`); `JAM` against
[davxy/jam-test-vectors](https://github.com/davxy/jam-test-vectors) `v0.8.0`.

It is meant for proofs as well as evaluation: everything is total, decoding is kept separate from
execution, memory is an extensional finite map, and the theorems use only `propext`,
`Classical.choice` and `Quot.sound`. The model depends only on Lean core and `Std` (toolchain
`v4.36.0-rc1`).

## Scope

Two libraries, each bounded by the Gray Paper (v0.8.0):

* **`PVM`: exactly Appendix A**, all of it and nothing more: §A.1–A.5 (deblob, decoding,
  instruction semantics, memory, Ψ₁, Ψ), §A.6–A.8 (Ψ_H, Y, Ψ_M) and §A.9–A.10 (the gas model).
  Results are exactly the paper's tuples. From outside Appendix A it uses only what Appendix A
  references: the integer and bit-sequence encodings of Appendix C, the RAM and register
  definitions of §4.7, and constants. `PVM/Logic/` holds proof rules about this model; it adds no
  semantics.
* **`JAM`: Appendix B (in progress)**, built on `PVM`, with the protocol terms Appendix B needs:
  the codec (Appendix C), ℋ = Blake2b-256 (§3.8), work packages, items, digests and reports
  (§11, §14), service accounts (§9), ℋ_K = Keccak-256 and the binary Merkle root (Appendix E).
  It has the general host functions (`gas`, `grow_heap`, `fetch`, `lookup`, `read`, `write`,
  `info`), the 13 accumulate host functions, Ψ_A, and the accumulation state transition of §12
  (Δ_1, Δ_*, Δ_+, the ready queue and history, statistics, and the output root); and the refine
  host functions (`historical_lookup`, `export`, `machine`, `peek`, `poke`, `pages`, `invoke`,
  `expunge`), Ψ_R and Ψ_I. Protocol and gas
  constants are generated from `definitions.tex` (`scripts/gen_constants.py`, drift-checked in CI);
  the test vectors' tiny chain is `Params.tiny`. A proof about pure PVM programs imports only `PVM` and trusts nothing from `JAM`.

A third library, **`Services`**, holds results about specific services' deployed code, built on
`JAM`; nothing in `PVM` or `JAM` depends on it.

Test-vector conventions (`map`/`write`/`set-reg` steps, how runs resume, the exit index the vectors
call `pc`) live in `Tests/`, not in the model.

## Results

| Check | Result |
| --- | --- |
| `programs/` vectors (status, registers, pc, gas, fault address, host call, memory) | **364 / 364** pass, with gas charged by the model's own ϱ^Δ |
| Block costs in `programs/` | **5,123 / 5,123** correct |
| Block costs in `gas-tests/` (doom, pinky, prime-sieve) | **39,737 / 39,737** correct |
| Model's ϖ against the blocks the vectors list | identical in all 367 programs |
| `JAM` codec: work-package family vs. GP v0.8.0 codec vectors | **6 / 6** match |
| `JAM` Blake2b-256 vs. `hashlib` and RFC 7693 | **13 / 13** match |
| `JAM` general host functions, hand-written cases | **30 / 30** pass |
| `JAM` Keccak-256 / SHA3-256 vs. `hashlib` and standard vectors | **15 / 15** match |
| `JAM` refine host functions, Ψ_R and Ψ_I, hand-written cases (no vectors exist) | **59 / 59** pass, 2 more kernel-checked |
| `witness-service.jam`'s host-call ids within those `Services.Witness` assumes (`lake build witnesscheck`) | **pass** |
| The real witness binary's refine on 7 malformed payloads gives `Rejected(BadPayload)` (`lake build witnessrun`; a test, not a proof) | **7 / 7** |
| Accumulation STF (§12) vs. GP v0.8.0 accumulate vectors (tiny) | **61 / 63** pass; the 2 others are `bless_from_non_manager`, which the vectors' changelog lists as departing from GP 0.8.0 |

## Building and running

```bash
lake build                            # the model and its theorems
lake env lean scripts/CheckAxioms.lean   # axiom audit of every PVM declaration
scripts/fetch-vectors.sh              # pinned vectors into vendor/jamtestvectors
lake build pvmtest                    # run every vector in programs/
lake build gascheck                   # compare ϱ^Δ with every block cost
scripts/check-tables.sh               # regenerate PVM/Tables.lean from the pinned paper and diff
```

`pvmtest` and `gascheck` are Lake targets that build an executable and run it; a failing vector
fails the build. `lake exe pvmtrace <vector.json> [steps]` prints a step-by-step trace.

## Layout

| Module | Contents | Paper |
| --- | --- | --- |
| `PVM/Basic.lean` | registers, 𝒵, 𝒵⁻¹, 𝒳, ℰ_l, bit functions, rtz, smod | §A.4–A.5, eqs. `signedfunc`, `signedextension`, `bitsfunc` |
| `PVM/Blob.lean` | deblob, 𝔳_blob, 𝔳_inst, skip, ζ, U, T, ϖ, 𝔏 | §A.1–A.3, eqs. `skip`, `instructions` |
| `PVM/Instr.lean` | the typed `Instr` and `Program.decode` | operand definitions of §A.5.1–A.5.13 |
| `PVM/Exec.lean` | the mutation tables: (ε, ı', ω', μ') and **r**, **w** | §A.4–A.5, sjump, branch, djump (eq. `jumptablealignment`) |
| `PVM/Memory.lean` | RAM as `Std.ExtTreeMap`s, read-after-write lemmas, ε^μ | §4.7 eq. `pvmmemory`, §A.4 |
| `PVM/Gas.lean` | š, ř, 𝔓, 𝔓_S, 𝔪, 𝔟 and the simulation 𝔛 (𝔛', 𝔛^mov, 𝔛^dec, 𝔛'', 𝔖, 𝔛''') | §A.9–A.10, eq. `gascostforblock` |
| `PVM/Machine.lean` | Ψ₁ (`Program.step`) and Ψ (`psi`) | §A.1, §A.4 |
| `PVM/Invocation.lean` | host-call handlers 𝔉_X, Ψ_H (`psiH`, `psiHStar`), Y (`standardInit`), Ψ_M (`psiM`) | §A.6–A.8, eqs. `conditions`, `memlayout`, `registers` |
| `PVM/Tables.lean` | **generated**: opcode enumerations per argument format, U, T, 𝔪, the gas cost table | §A.3, §A.5, §A.10 |
| `PVM/Theorems/*.lean` | the theorems below | |
| `Tests/` | vector runner, gas checker, tracer, kernel-checked invocation examples | |
| `scripts/gen_tables.py` | LaTeX → `PVM/Tables.lean` | |

### The generated table

`scripts/gen_tables.py` reads `text/pvm.tex` and emits `PVM/Tables.lean`: the opcode numbers,
names and argument formats from the instruction tables, the terminator set T from §A.3, 𝔪, and
each row (č, ď, x̌_A, x̌_L, x̌_S, x̌_M, x̌_D) of the gas cost table with the paper's macros
expanded. Cells stay symbolic (`const`, `overlap` = 𝔓, `overlapShift` = 𝔓_S, `memory` = 𝔪,
`branch` = 𝔟) and are evaluated per instruction in `PVM/Gas.lean`. The script rejects anything it
does not recognise, and checks that the cost table and the instruction tables name the same
instructions. CI regenerates the file from the pinned paper and fails on any difference. Because
the opcode enumerations are generated too, a renamed or renumbered instruction in the paper breaks
the build of the semantics rather than drifting silently.

## Theorems

* **Host calls** (`PVM/Theorems/Host.lean`). `exec_status_eq_host_iff`: an instruction's mutation
  yields h̵ × h iff it is `ecalli` with immediate h. `step_host` lifts this to Ψ₁ and `psi_host`
  to Ψ: if Ψ exits with h̵ × h, the program deblobs at the exit index and the instruction there
  decodes to `ecalli` with immediate h.
* **A program's host calls are bounded by its own `ecalli` immediates**
  (`PVM/Theorems/HostIds.lean`). `hostCallIdsOf` scans a blob without running it.
  `psi_hostId_mem`: every h̵ × h Ψ returns has h in that set. `psiHStar_congr` and `psiM_congr`:
  running a program under two host handlers that agree on those ids gives the same result, so a
  service's behaviour cannot depend on, and it can never invoke, any host function it does not
  name. For a concrete blob the set is checked by `decide +kernel` without executing anything.
* **Ψ is the paper's Ψ** (`PVM/Theorems/Termination.lean`). `psi` runs with fuel `stepBound`;
  `runFuel_stepBound_isSome` shows the fuel never runs out, and `psi_eq` shows `psi` satisfies
  the paper's recursive definition of Ψ (deblob, Ψ₁, then the case split on ε) exactly. The
  measure (`runMeasure`, `step_measure_lt`) is 2n·ϱ + (ϱ̃ ? n + |**c**| − ı : 0) with
  n = |**c**| + 1: a charge costs at least one gas, a terminator clears ϱ̃, and any other
  instruction moves ı forward (`exec_pc_of_not_terminator`). `psi_status_ne_cont`: Ψ never
  returns ▸.
* **Ψ_H is the paper's Ψ_H\*** (`PVM/Theorems/Invocation.lean`). For any handler that never
  returns more gas than it was given (`HostFn.GasNonIncreasing`, true of every host function in
  the paper), `psiHStar_eq` shows `psiHStar` satisfies GP §A.6's recursive definition, and
  `psiHFuel_stable` that its fuel never runs out. The key fact, `psi_host_measure`: resuming after
  a host call is strictly lower in `runMeasure` than where the run started, because `ecalli` is
  not a terminator, so the flag stays set and ı moves forward.
* **Ψ never adds gas** (`PVM/Theorems/Termination.lean`). `psi_gas_le`: the gas Ψ returns is at
  most the gas it was given (`Program.step_gas_le` for one step).
* **The protocol's host functions never add gas** (`JAM/Theorems/HostGas.lean`).
  `accHostFn_gasNonIncreasing`, `refineHostFn_gasNonIncreasing` and
  `isAuthHostFn_gasNonIncreasing`: the dispatchers of Ψ_A, Ψ_R and Ψ_I are
  `HostFn.GasNonIncreasing`, so `psiHStar_eq` applies to all three invocations: their Ψ_H runs
  never exhaust the fuel and are the paper's Ψ_H exactly. Each host function charges g ≥ 0 by the
  common rules (`charged_gas_le`); `invoke`, the one that hands gas back, returns only what the
  inner Ψ left of the g_R it charged (`invoke_gas`, from `psi_gas_le`).
* **Context invariants** (`PVM/Theorems/HostIds.lean`). `psiM_ctx_inv`: if every host call a
  blob names preserves a property of the context, Ψ_M's final context has it. Only the blob's own
  `ecalli` ids matter.
* **Confinement** (`JAM/Theorems/Confinement.lean`). `psiA_confined`: if a service's code names
  none of `bless`, `assign`, `designate`, `new`, `eject`, `provide`, Ψ_A for it leaves every other
  account, the staging set, the authorizer queue and the privileged services as they were, and
  provides nothing. `psiR_noExports`: code that does not name `export` exports no segments.
* **Y's RAM, region by region** (`PVM/Theorems/InitMem.lean`). `initialMemory_pages` and
  `initialMemory_read`: the access of every page and the octet at every address of the memory Y
  builds, as a case split on the section, for any blob. With them a proof can start from Y's
  memory knowing only a blob's section sizes and the octets it reads.
* **`grow_heap` in symbolic runs** (`JAM/Theorems/GrowHeap.lean`). `HeapPages μ a b h`: in
  ℕ_{a…b} the writable pages are exactly those below h. `growHeapCore_eq` gives Ω_♊'s heap top
  from it without counting, and `FreeStepsH.growHeap` takes a whole `grow_heap` step under
  `refineContract`.
* **Witness's refine, first steps** (`Services/Witness/Prefix.lean`, generated by
  `lake exe genwitnesssteps run 702`, drift-checked in CI). `prefix_from_Y`: for a JAM blob with the
  deployed section sizes and read data octets (`layoutOk`) whose PVM code passes
  `checkCode p facts` (the vendored witness blob does both, by `witnesscheck`), any arguments Y
  accepts, and any refine environment whose code has the same heap bounds and whose parameters are
  the paper's full chain (`Params.full`), the gas-free machine runs 702 steps from Y's starting
  state: the SDK's entry, the heap allocator's initialization with both of its `grow_heap` calls,
  its size-class bitmap search and allocations, through function returns by `jump_ind`, the
  `fetch` of the protocol parameters (122 octets, `Params.full_encode`) and the code after it, up to
  the first read of the argument octets. The generator reports where the path first reads the
  arguments.
  The memory the path needs (`StartMem`, including the heap's pages and four octets of the
  read-write data) is proved of Y's RAM (`startMem_initial`).
* **Function summaries** (`Services/Witness/Memcpy.lean`). `memcpy_small`: the compiler's `memcpy`
  in witness, for fewer than 16 octets, from any destination, source and stack pointer and any
  return address the jump table resolves: it writes its stack frame, copies the octets, and
  returns with ω₀, ω₁, ω₅, ω₆, ω₇ unchanged. The byte loop is proved by induction on the count
  (`memcpy_loop`), with symbolic addresses. The code facts, for the path and for whole function
  bodies, are generated into `Services/Witness/Code.lean` (`lake exe genwitnesssteps code 702`).
* **The SDK's `u32` decoder, summarized** (`Services/Witness/DecodeU32.lean`). `decodeU32`: for
  a reader `{ptr, len}` whose octets at `ptr` are ℰ(n) (GP (C), the general natural encoding) for
  any n < 2^32, within `len`, the decoder at 184570 returns ω₇ = 0 and ω₈ = n with the reader
  advanced past ℰ(n), the callee-saved registers restored, and memory unchanged outside its stack
  frames and the reader (`DecodeOk`). It covers every encoding width (1 to 5 octets) by one
  theorem per class, with `memcpy_small` for the copy; the leading-ones count of the symbolic
  prefix octet uses bit lemmas (`PVM/Logic/Bits.lean`), and sign-extended octets are kept folded
  (`sx8`) so no 2^64-size constant sits next to a symbolic value in a checked term.
* **Segment theorems for the bad-payload path** (`Services/Witness/ErrTail0.lean` … `ErrTail4`,
  generated by `lake exe genwitnesssteps seg 74620 a b ErrTailk`). Witness's `Op::decode` jumps to
  74620 for an empty payload or a tag ≥ 12; from there the path is the same for every payload of
  1 to 15 octets. Each segment is a standalone theorem: from any state with the register values
  and memory octets it reads (only those every such payload agrees on, found by tracing several
  inputs), the machine reaches the segment's end with the registers and octets it sets, memory
  unchanged outside what it writes, and the same page access. The first 1300 of the path's 1543
  steps are proved, each segment in one to three minutes.
* **The witness service** (`Services/Witness.lean`). The witness bounty market
  (ascrivener/witness at 71e585a), built with `cargo jam-build` 0.1.29, is vendored as
  `services/witness/witness-service.jam`. Its code names host calls 0–6, 9, 11–14, 18, 20, 21, 24
  and 100 only. `accumulate_confined`: accumulating witness changes nothing outside its own account,
  for every state, input and gas. `refine_noExports`: its refine exports nothing. The theorems are
  kernel-checked for any code naming only those ids; that the vendored blob names only those ids is
  checked by compiled code (`lake build witnesscheck`), since kernel evaluation over a 223 kB blob is
  out of reach for now.
* **A fast Ψ that is the paper's Ψ** (`PVM/Fast.lean`). `psi` re-deblobs the program on every step
  and re-simulates gas on every block charge, as the paper writes it. `psiFast` parses once and
  memoizes block costs. `psi_eq_psiFast : psi = psiFast` is registered with `@[csimp]`, so compiled
  code (including every test runner) executes `psiFast`, while the kernel and every theorem see
  `psi`.
* **Memory** (`PVM/Memory.lean`). `read_write`, `read_write_self`, `read_write_of_ne`,
  `read_writeN_at`, `readN_writeN` (read after a multi-octet write of at most 2^32 octets), and
  that writes leave page access unchanged.
* **Decoding** (`PVM/Theorems/Decode.lean`). `decode_opcode`: a decoded instruction's opcode is
  ζ_ı.
* **Blobs and blocks** (`PVM/Theorems/Blob.lean`). `skip_le` (skip ≤ 24); `isBlockStart_iff` and
  `followsTerminator_iff`: the bounded search used for ϖ is exactly the paper's set
  comprehension; `vBlobAux_fuel`, `vBlob_eq`: 𝔳_blob's fuel is sufficient.

`Tests/Invocation.lean` checks hand-assembled programs through Y, Ψ_H and Ψ_M (echo, host calls
that change registers and context, out-of-gas, traps, invalid blobs, unreadable output, Y's
memory layout and registers) by `decide +kernel`: the Lean kernel evaluates the whole model
itself. No test vectors cover these layers at the pinned commit.

`scripts/CheckAxioms.lean` collects the axioms of every declaration in the `PVM` namespace and
fails on anything but `propext`, `Classical.choice` and `Quot.sound` (so on `sorryAx`, and on
the axioms `native_decide` and `bv_decide` introduce). CI also greps for `sorry`, `partial def`,
`implemented_by`, `native_decide` and `bv_decide`.

## Reasoning about programs (`PVM/Logic/`)

Theorems and proof rules about the Appendix A model; nothing here adds semantics.

* **Gas abstraction** (`Logic/Free.lean`). `Program.freeStep` is Ψ₁ without its gas stage, and
  `FreeRun` the big-step runs of that gas-free machine. `psi_freeRun`: every Ψ run that does not end
  in ∞ is a `FreeRun` with the same exit reason, registers and memory. Gas only ever stops a run
  early, so properties of the form "if it finishes, then …" can ignore gas, basic blocks and the
  cost model entirely.
* **Abstract hosts** (`Logic/Host.lean`). A host contract `HostRel` says what a host call may do;
  `FreeRunH` is gas-free Ψ_H under a contract. `psiHStar_freeRunH` and `psiM_free`: every Ψ_H / Ψ_M
  run, under any handler that respects the contract and does not add gas, that does not end in ∞
  is such a run. Proofs therefore hold for every handler meeting the contract.
* **Invariant rules** (`Logic/Invariant.lean`). `FreeRun.of_invariant` and `FreeRunH.of_invariant`:
  an invariant that holds initially and is preserved by each step (and by each host call the
  contract allows) constrains every way the run can end.
* **Determinism** (`Logic/Det.lean`). `FreeRun.det`, `FreeRunH.det`: gas-free runs from one
  state end the same way (under contracts where one pins down the other). `psiM_of_freeRunH`:
  exhibiting *one* gas-free run from Y's initial state determines Ψ_M's result: it is that run's
  output, or ∞. A proof about what a service computes can therefore construct a single run and
  leave gas to a separate bound.
* **Code facts** (`Logic/Code.lean`). `checkCode p fs` checks, in one `Bool`, that a blob passes
  𝔳_blob and a list of facts about it: the decoded instruction and ı + 1 + skip(ı) at given
  indices, block starts, jump-table entries. `checkCode_sound` turns it into those facts, with
  `deblob p i = some P`. A theorem about a large program takes `checkCode p fs = true` as its one
  hypothesis about the bytes, whatever evaluates it.
* **Stepping** (`Logic/Steps.lean`). `FreeSteps`: chains of gas-free steps, which compose and end
  in a `FreeRun`. `FreeSteps.step_decode` takes one step at an index whose instruction a code fact
  gives; the `pvm_simp` tactic computes that step's effect with symbolic register and memory
  contents (unfolding the mutation, reducing concrete arithmetic, deciding ε^μ from memory-access
  hypotheses) and fixes the next state by `rfl`. Memory lemmas for it: reading back a write,
  reading a disjoint range, ℰ⁻¹(ℰ_n(v)) = v mod 2^(8n).
* **Through host calls** (`Logic/StepsH.lean`). `FreeStepsH`: chains through ordinary steps and
  through host calls whose outcome a contract allows; they compose and end in a `FreeRunH`.
  `FreeStepsH.host_decode` takes an `ecalli` step. For refine, `JAM.refineContract`
  (`JAM/Theorems/RefineContract.lean`) is the dispatcher's graph on the ids whose non-∞ outcome
  does not depend on the gas left (`grow_heap`, `fetch`, unknown ids such as `log`), and
  `refineContract_pins` proves it pins down the real handler, as `psiM_of_freeRunH` requires.
  The `pvm_host` tactic computes such a step.
* **Worked example** (`Tests/LogicExample.lean`). A three-instruction countdown loop.
  `countdown_spec`: for every initial register file with ω₀ = 2^32 − 2^16, every memory and every
  amount of gas, Ψ either runs out of gas or halts with ω₈ = 0. The proof uses `psi_freeRun`, a
  program-counter invariant, and one lemma per instruction. Each lemma unfolds `exec` on the
  decoded instruction and is checked in about a second.

## Toward proofs about what services compute

The confinement theorems use only *which* host calls a service's code can make. Proving what it
*computes* means following its code. The first target is witness's refine on a malformed payload:
for every core, item index, service id and work package whose item payload does not decode as an
`Op` (empty, or a first octet ≥ 12), Ψ_R outputs ℰ(`Rejected(BadPayload)`) = [12, 0]. `witnessrun`
checks this on fixed inputs. Tracing those runs shows what a proof for all inputs involves:

* **The path is short**: about 2,400–2,900 instructions (1,500–1,600 distinct) for short payloads,
  with host calls `fetch`, `grow_heap`, `grow_heap`, `fetch`, `log`. The SDK reads the payload
  through `fetch`, so the proof goes through Ω_Y.
* **It depends on the inputs only through a few branches**: the lengths of the varint encodings of
  c, i and s, and the payload length, which drives a copy loop (43,349 steps for 20,000 octets)
  and extra `grow_heap` calls.

The plan (`Logic/Det.lean`, `Logic/Code.lean` and `Logic/Steps.lean` are its first pieces;
`Services/Witness/Prefix.lean` runs it on the first 39 instructions, at about 0.15 s each):

1. **Program access the kernel can afford.** The kernel cannot evaluate over a 217 kB `ByteArray`.
   For now the facts the proof uses are one hypothesis, `checkCode p fs = true`, evaluated by
   compiled code in CI (as `witnesscheck` does for the host-call ids). A kernel check over a
   representation it evaluates quickly (GMP-backed `Nat`s) can discharge the same hypothesis
   later without changing the theorem.
2. **Symbolic execution**, proved sound against Ψ₁: registers and memory as terms over the
   inputs, a path condition, case splits at the input-dependent branches.
3. **Summaries** for loops and library code (the copy loop first), proved once by induction and
   used in place of their code.
4. The theorem, as one gas-free run lifted to Ψ_R with `psiM_of_freeRunH` ("[12, 0] or ∞"),
   then a gas bound.

Staging: the first statement fixes a one-octet payload with first octet ≥ 12, leaving c, i, s and
ℋ(p) arbitrary. The traced path shows those only reach the SDK's varint decoder and are then
stored, while the payload length also sets the sizes the heap allocator works with; a one-octet
payload keeps the allocator's state concrete. Empty and longer payloads follow.

## Notes on the paper and the vectors

Where the paper is ambiguous, the model follows the paper's formal definition and the choice is
noted here and in a comment at the definition.

1. **𝔓_S compares ω_A = ω_D** (§A.10), which read literally compares register *values*; the gas
   model has no values, so we compare the register indices r_A = r_D. The equal-register case
   occurs 226 times in the vectors' blocks and every cost matches.
2. **𝔟 at a negative branch target.** 𝔟 reads ζ at ı_target, and ı_target = ı + 𝒵(…) can be
   negative, where ζ is undefined. We read it as 0 (`trap`), like indices past the end of **c**.
   No branch in any vector has a target outside [0, |**c**|), so this is untested.
3. **RAM below 2^16** (§A.4). The prose says the machine "always panics … regardless of the
   apparent (in)accessibility", but the formula for ε^μ only considers *inaccessible* indices, so
   an accessible index below 2^16 does not panic. We follow the formula. No vector maps a page
   below 2^16, so the two readings are not distinguished.
4. **Three-register r_D = min(12, ζ_{ı+2})**, not mod 16. No vector has ζ_{ı+2} ≥ 16.
5. **The exit pc.** Ψ returns ı = 0 on ∎ and ☇; the vectors report the exiting instruction.
   `Result` is exactly Ψ's tuple, so the test harness recomputes the exiting instruction
   (`Tests.exitIndex`).
6. **Register writes on halt and panic.** Ψ returns ω' on ∎ and ☇, so `load_imm_jump` and
   `load_imm_jump_ind` set ω_A even when their jump halts or panics. The vectors agree (6 vectors
   fail without it).
7. **T excludes `unlikely` and `ecalli`**, so after a host call ϱ̃ stays set and the resumed run
   is not charged again. The vectors agree: no block starts after either, and the multi-step
   `ecalli` vectors charge each block once.
8. **`cmov_iz`/`cmov_nz` read ω_D** (and `cmov_*_imm` read ω_A) in š, and **`move_reg`
   renames** in 𝔛^mov. The vectors test both: dropping ω_D breaks 10 block costs, treating
   `move_reg` as an ordinary instruction breaks 65.
9. **`neg_add_imm_32`** is (ν_X + 2^32 − ω_B) mod 2^32 over ℤ: ω_B can exceed 2^32, so the
   intermediate is negative and the modulus is the mathematical one. (An early version of this
   model truncated in ℕ; `riscv_rv64ui_subw` caught it.)
10. **ε^μ takes min(**x**) before reducing mod 2^32**, as written; this only matters for accesses
    that wrap around 2^32.
11. **Coverage gap.** No vector contains `cmov_nz_imm` (opcode 148).
12. **Gas types in Ψ_H.** The handler type 𝔉_X returns gas in ℕ_G, but Ψ_H's result is typed
    ℤ_G and the host functions compute ϱ − g, which is negative when they run out. We follow 𝔉_X
    (gas in ℕ_G); Ψ_M only uses max(ϱ', 0), so nothing downstream sees the difference yet.
13. **Ψ_H need not terminate.** The paper's Ψ_H* recurses after every host call; a handler that
    returns more gas than it was given can keep it running forever. We prove termination (and the
    paper's equation) for handlers that do not add gas, which includes the dispatchers of Ψ_A, Ψ_R
    and Ψ_I (`JAM/Theorems/HostGas.lean`); for others `psiHStar` stops with ☇ after its fuel.
14. **Y's fit condition is vacuous.** With 3-, 3-, 2- and 3-octet length fields, |**o**|, |**w**|,
    z𝖹_P and s are bounded so that 5𝖹_Z + Q(|**o**|) + Q(|**w**| + z𝖹_P) + Q(s) + 𝖹_I is at most
    about 2^28.3 < 2^32. We check it anyway.
15. **Accumulate vectors and GP 0.8.0.** The vectors' CHANGELOG lists behaviour that departs from
    GP 0.8.0, following later Gray Paper PRs. We follow the paper and list the affected vectors in
    `Tests/AccumulateTest.lean` (`knownDeviations`); CI fails if any other vector fails or if a
    listed one starts to pass. Currently: `bless_from_non_manager-1` and `-2` (`bless` from a
    non-manager: GP 0.8.0 answers `HUH`, the vectors accept it). The other listed departures
    (`grow_heap` running out of gas, its address limit, program size limits) are not exercised by
    any vector. The `log` host call (JIP-1, not in the paper) is an unknown host call, 1000 gas.
16. **Sets are sets.** Terms the paper types as sets or dictionaries use extensional types, so no
    order or multiplicity is observable: `OctetSet` (`Std.ExtTreeSet`) for the prerequisites p, the
    ready-queue dependency sets, P(**r**) and each entry of the accumulated history ξ; `OctetDict`
    (`Std.ExtTreeMap`) for the segment-root lookup l; `Provisions` for the provisions **p** of 𝕃.
    Iteration is in ascending order, which is the order set and dictionary encodings use.
17. **Y's argument bound.** The paper types **a** ∈ 𝔹_{:𝖹_I}; for longer arguments we return ∅.
18. **Ψ_R's extrinsics.** The refine dispatcher passes x̄ to `fetch`, built from the **x** with
    (ℋ(**x**), |**x**|) ∈ w_x, but Ψ_R's arguments do not include that data. `psiR` takes x̄ as an
    argument. Likewise Ψ_R and Ψ_I draw on an account state **d** the paper leaves implicit; both
    take it as an argument.
19. **Code that is not ℰ(↕**m**, **c**).** Ψ_R and **p**_c (§14.3) split the looked-up preimage as
    ℰ(↕**m**, **c**) without saying what happens if it does not have that form. We treat it like a
    missing preimage: BAD. Likewise an item index i ≥ |p_w| gives BAD.
20. **`pages` gives no ε'.** Ω_Z's row defines only (ω'_7, **m**'); with the common rules it
    continues (▸) in every case, including WHO and HUH.

## Caveats

* **𝔛's termination is not proved.** The simulation runs with fuel `256 · (|**c**| − ı + 2)`
  transitions. Across every block of the vectors it needs at most 54 transitions per instruction
  and under 5% of the fuel. `Program.blockCost?` returns `none` if the fuel runs out, and the gas
  checker treats that as a failure; `Program.blockCost` (used by Ψ₁) falls back to 1.
* **Totality fallbacks that valid programs never reach**: Ψ₁ reads an undecodable octet as
  `trap` (Ψ only calls Ψ₁ where 𝔳_inst holds), and ϱ^Δ evaluates to 1 if 𝔛 meets an opcode
  outside U.
* **Kernel evaluation is slow.** Concrete runs can be checked by the kernel, but the model
  follows the paper literally: it re-deblobs the program on every step and re-runs the gas
  simulation on every block charge. A 200-iteration two-instruction loop takes about 45 s of
  kernel time. Proved-equivalent fast paths (parse once, cache block costs) are the obvious next
  step before checking real services this way.
* **Types.** ı is a `Nat` rather than ℕ_R; gas is a `UInt64` (ℕ_G). Immediates are stored
  sign-extended as `UInt64`, offsets as `Int`.
* **Test harness.** The vectors' `map`, `write` and `set-reg` steps and the resumption rule
  (ı + 1 + skip(ı) after h̵ as in Ψ_H, the same ı after F or ∞) are harness conventions outside
  Ψ. The test executables use `Lean.Data.Json` from the Lean core distribution; the model itself
  imports only `Init` and `Std`.

## Provenance

Written from the Gray Paper and the test vectors only. No other PVM or JAM implementation was
consulted.
