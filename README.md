# jam-lean

An executable Lean 4 model of JAM from the
[Gray Paper](https://github.com/gavofyork/graypaper) **v0.8.0**: the Polkadot Virtual Machine
(Appendix A, library `PVM`), and Appendix B with the protocol terms it needs (library `JAM`, in
progress). The PVM is checked against the PVM test vectors of
[koute/jamtestvectors](https://github.com/koute/jamtestvectors) (branch `master_pvm_initial`,
commit `6bf3768e5b37bbe4ca5d6e1306284ecb27c0198f`, directory `pvm/`); `JAM` against
[davxy/jam-test-vectors](https://github.com/davxy/jam-test-vectors) `v0.8.0`.

**What's proven:** [`docs/whats-proven.md`](docs/whats-proven.md) summarises the theorems about real
service binaries (witness, and Parity's bootstrap service with its picoalloc heap allocator), their
assumptions, the trust base, the model/binary disagreements found, and how to reproduce it all.

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
  the codec (Appendix C) with its decoder ℰ⁻¹, blocks, headers and extrinsics, ℋ = Blake2b-256
  (§3.8), work packages, items, digests and reports (§11, §14), service accounts (§9), ℋ_K = Keccak-256 and the binary Merkle root (Appendix E).
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
| `JAM` codec (Appendix C): every GP v0.8.0 codec vector (headers, blocks, all extrinsics, the work-package family), encoded from JSON and round-tripped through ℰ⁻¹ | **15 / 15** tiny, **15 / 15** full |
| `JAM` Blake2b-256 vs. `hashlib` and RFC 7693 | **13 / 13** match |
| `JAM` general host functions, hand-written cases | **30 / 30** pass |
| `JAM` Keccak-256 / SHA3-256 vs. `hashlib` and standard vectors | **15 / 15** match |
| `JAM` SHA-512 vs. FIPS 180-2 examples and `hashlib`; the VRF output Y of one trace block against its η'_0 | **9 / 9** match; **1 / 1** |
| `JAM` refine host functions, Ψ_R and Ψ_I, hand-written cases (no vectors exist) | **59 / 59** pass, 2 more kernel-checked |
| `witness-service.jam`'s host-call ids within those `Services.Witness` assumes (`lake build witnesscheck`) | **pass** |
| The real witness binary's refine on 7 malformed payloads gives `Rejected(BadPayload)` (`lake build witnessrun`; a test, not a proof) | **7 / 7** |
| `JAM` state trie M (Appendix D) vs. GP v0.8.0 trie vectors (keys cut to 31 octets, note 27); state-key constructor C, hand-written | **11 / 11** roots match; **4 / 4** |
| `JAM` Fisher–Yates shuffle ℱ with 𝒬_l (Appendix F) vs. GP v0.8.0 shuffle vectors | **8 / 8** match |
| `JAM` erasure coding ℰ_C / ℛ over GF(2¹⁶) (Appendix H) vs. GP v0.8.0 erasure vectors | data shards match in **12 / 12** (6 tiny, 6 full); parity shards follow a different convention in all 12 (note 28), which the test reproduces exactly; ℛ recovers the paper's code in all 12 |
| Accumulation STF (§12) vs. GP v0.8.0 accumulate vectors (tiny) | **61 / 63** pass; the 2 others are `bless_from_non_manager`, which the vectors' changelog lists as departing from GP 0.8.0 |
| Recent-history STF (§7: β_H, the accumulation-output belt β_B) vs. `stf/history` (`lake build historytest`) | **4 / 4** tiny, **4 / 4** full |
| Authorization STF (§8: the pool α from the queue φ') vs. `stf/authorizations` (`lake build authtest`) | **3 / 3** tiny, **3 / 3** full |
| Validator statistics (§13.1: π_V, π_L) vs. `stf/statistics` (`lake build statstest`) | **4 / 4** tiny, **4 / 4** full |
| Preimage STF (§12.4) and its service statistics (§13.2 provision counts) vs. `stf/preimages` (`lake build preimagestest`) | **8 / 8** tiny, **8 / 8** full |
| Disputes STF (§10: verdicts, culprits, faults, ψ', ρ^‡ and H_O) vs. `stf/disputes` (`lake build disputestest`; Ed25519 verification is a parameter, note 29) | **29 / 29** tiny, **31 / 31** full |
| Assurances STF (§11.2: the available reports **R** and ρ after assurances) vs. `stf/assurances` (`lake build assurancestest`; signatures as in note 29) | **11 / 11** tiny, **11 / 11** full |
| Reports STF (§11.3–§11.5: guarantor assignments M and M*, guarantee validity, ρ', G and the reported packages) and core and service statistics (§13.2) vs. `stf/reports` (`lake build reportstest`; signatures as in note 29) | **44 / 44** tiny, **48 / 48** full |
| Safrole STF (§6: τ, η, key rotation, γ_Z, γ_S, γ_A, H_E, H_W) vs. `stf/safrole` (`lake build safroletest`), with the Bandersnatch primitives as an oracle read from the vectors (note 31) | **21 / 21** tiny, **25 / 25** full |

## Building and running

```bash
lake build                            # the model and its theorems
lake env lean scripts/CheckAxioms.lean   # axiom audit of every PVM declaration
scripts/fetch-vectors.sh              # pinned vectors into vendor/jamtestvectors
lake build pvmtest                    # run every vector in programs/
lake build gascheck                   # compare ϱ^Δ with every block cost
scripts/check-tables.sh               # regenerate PVM/Tables.lean from the pinned paper and diff
scripts/fetch-jam-vectors.sh          # GP v0.8.0 JAM vectors into vendor/jam-test-vectors
lake build historytest authtest       # the recent-history and authorization STF vectors (tiny and full)
lake build statstest preimagestest    # the statistics and preimage STF vectors (tiny and full)
lake build disputestest assurancestest reportstest  # disputes, assurances and reports STF vectors
lake build safroletest                # the Safrole STF vectors (tiny and full)
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
| `PVM/Logic/Words.lean`, `PVM/Logic/Go.lean` | service-independent tools for summaries: ℰ and little-endian words as octet lists, misaligned word splices, folded loads (`rdN`, `sxw`, `sx8`); `pvm_go` steps a run through generated code facts | (C) |
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
  from it without counting, and `FreeStepsH.growHeapK` takes a whole `grow_heap` step under
  `refineContractK cap`, for a growth whose cost 275 + 121 a page fits in `cap`
  (`FreeStepsH.growHeap`: under `refineContract`, so at most 14 pages).
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
* **What the first 702 steps leave** (`Services/Witness/Prefix.lean`, `PrefixPost`). The generated
  prefix theorem now also states the state at pc 43276:
  - registers: ω₆ = ω₇ = L (the argument length), the rest concrete;
  - the octets later steps read (`postBytes`), and the words holding L (`lenAt`);
  - the arguments and their read access unchanged;
  - the stack and heap writable;
  - the refine context unchanged.
  The facts come from the segment analysis over inputs of every width, including a 300-octet
  payload so that L's octets are not mistaken for constants.
* **The front end's segments** (`Services/Witness/Front1.lean` … `Front4.lean`, generated by
  `genwitnesssteps segx`). This is the code between the summarized calls from step 775 to
  `Op::decode`'s error jump at 74620:
  - after the `u32` decodes of i and of s;
  - after the decode of |y|, through the payload's allocation (275 steps);
  - after the payload copy, through the tag check.

  `segx` extends the segment analysis with:
  - the payload's first octet T (here 12 ≤ T < 256) and the reader position Q after the header;
  - values that are a constant plus one or two variables (Y + 32, Q + Y, …);
  - 8-octet words left holding such values;
  - start registers limited to those the preceding summary guarantees (`keep=`);
  - facts the steps need, proved by `omega` from the bounds (the allocator's size class
    (Y + 31) / 32 = 1);
  - more inputs (service ids ≥ 2^31, i = 1, a 3-octet c), so that no value they happen to share
    is stated.
* **The core-index decode** (`Services/Witness/DecodeC.lean`). From pc 43276 (step 702 of
  refine), witness decodes the core index c from its arguments with the SDK's natural-number
  decoder inlined, checks c < 2^16 and calls the `u32` decoder for the next argument.
  `decodeC` proves this for every c < 2^16, with one case for each width of ℰ(c): 0, 1–127,
  2 octets and 3 octets. Witness takes the core index as a `u16` and rejects larger values,
  which no refine call passes (cores < 341).
* **Witness's Ψ_R rejects a bad tag** (`Services/Witness/PsiR.lean`, `psiR_badTag`). The statement
  is about Ψ_R itself (GP eq. `refinvocation`). Take a work item whose service's code, looked up
  historically, is a blob with the deployed layout that passes `checkCode` for witness's code facts
  (`lake build witnesscheck` checks both of the vendored blob), refined with the full-chain
  parameters. Then for every core index c < 2^16, item index i < 2^16, service id < 2^32, and
  payload of 1 to 15 octets whose first octet is at least 12, Ψ_R's result is
  ℰ(`Rejected(BadPayload)`) = [12, 0], or ∞. It is built from three lifts:
  - `run_badTag`, the gas-free run below;
  - `PsiRLift.psiR_of_run`, Ψ_R's code lookup, its arguments ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ↕y ⌢ ℋ(p), and
    Y's start;
  - `Lift.psiM_of_run`, from `psiM_of_freeRunH`, the dispatcher's contract, and the halting step
    `halt_43609`.

  `checkCode` and the layout are hypotheses here; `Rejects.refine_rejects` discharges them for the
  vendored blob in the kernel. The theorem depends on propext, Classical.choice and Quot.sound only.
* **Witness rejects a bad tag, end to end** (`Services/Witness/BadPayload.lean`, `run_badTag`).
  For every core index c < 2^16, item index i < 2^16, service id s < 2^32, payload y of 1 to 15
  octets whose first octet (the `Op` tag) is at least 12, and 32-octet hash h, the gas-free machine
  runs from Y's registers, over a starting memory that holds the arguments, to the halting step
  with ω₇ = 206816, ω₈ = 2 and the octets [12, 0] there: `Rejected(BadPayload)`. The run is
  chained from the following pieces:
  - the prefix;
  - the core-index decode;
  - the `u32` decodes of i, s and |y|;
  - the front segments;
  - the payload copy;
  - the error tail `ErrTail.run` (`Op::decode` jumps to 74620 for a tag ≥ 12; generated by
    `cut` over the wider class of inputs, below).

  Every piece's hypotheses (about 400 facts in all: registers, octets, words, access ranges) are
  discharged by `chase` (`PVM/Logic/Chase.lean`). It traces each fact back through the earlier
  pieces' post-states and frames to the prefix's post-state and the starting octets. The error
  tail is its own generated theorem (`ErrTail.run`, `genwitnesssteps cut`), from the 94 facts it
  reads at 74620.
* **The empty payload's tail** (`EmptyTail.run`, generated by `cut0`). The empty payload reaches
  74620 by a different route and takes 1445 steps from there to the same halt and output [12, 0]
  (here at ω₇ = 206752).
* **Witness rejects the empty payload** (`Services/Witness/EmptyPayload.lean`, `run_empty`;
  `Services/Witness/PsiREmpty.lean`, `psiR_empty`). The same chain as `run_badTag` up to the
  decode of |y| = 0, then the empty path's front segment `EFront3` (`genwitnesssteps cut0 … frame`) and
  `EmptyTail.run`, lifted to Ψ_R by `psiR_of_run` with the output at 206752.
* **Milestone A′** (`PsiREmpty.psiR_rejects`). Under the hypotheses above, for every core index
  c < 2^16, item index i < 2^16, service id < 2^32 and payload that is empty or of 1 to 15 octets
  whose first octet is at least 12, Ψ_R's result is ℰ(`Rejected(BadPayload)`) = [12, 0], or ∞.
  It depends on propext, Classical.choice and Quot.sound only.
* **Milestone A′, exactly** (`PsiREmpty.psiR_rejects_exact`, with `psiR_badTag_exact` and
  `psiR_empty_exact`). With a refine gas limit of at least `gasBound` = 4001 · (8192 + 2000) =
  40,782,192 (under 1% of the full chain's 5 · 10⁹), the "or ∞" goes: Ψ_R's result is exactly
  ℰ(`Rejected(BadPayload)`) = [12, 0]. The bound is (N + 1)(M + H): the path takes at most N = 4000
  steps, each in a basic block costing at most M = `stepCostCap` = 2^13 (each step of a counted
  chain carries its block's bound, from the code facts' `.block` entries), and each host call costs
  at most H = `hostCostMax` = 2000 (`fetch` of the parameters costs 390, `log` 1000).
* **The deployed witness binary rejects malformed payloads, by the kernel alone**
  (`Services/Witness/Rejects.lean`, `refine_rejects`). Milestone A′ exactly, for the code preimage
  that *is* `services/witness/witness-service.jam` (`Services.Witness.Blob.preimage`): no hypothesis
  about the code is left. Its sections (`CodeCheck.split`, `CodeCheck.jam`), 𝔳_blob and the 3,800
  code facts (`CodeCheck.checkCode_ok`), the costs of the 344 blocks the path visits, the section
  sizes and data octets the path reads (`layout_ok`) and the heap bounds (`heap_ok`) are all checked
  by the kernel. That is possible because the blob is a number to the kernel (`PVM.NatBlob`): octet
  j is ⌊N / 2^(8j)⌋ mod 256, computed with the kernel's arbitrary-precision arithmetic, and each check
  reads its stretch of the code from a window cut out of N once (`NatBlob.wview`). The model's
  code-reading definitions are repeated over a `CodeView` (`PVM/Logic/View.lean`, equal by `rfl`),
  𝔳_blob is checked as a chain of walks (`PVM/Logic/FastCheck.lean`), and the generated
  `Services/Witness/CodeCheck.lean` (`genwitnesssteps codecheck`) holds the checks. The theorem
  depends on propext, Classical.choice and Quot.sound only.
* **Kernel checks sized for one refine.** witness-lean attests a declaration in one refine (about
  55 ms of nanoda), and a long kernel reduction cannot be split for it. So the generated checks are
  small: 𝔳_blob in walks of at most 40 instructions, the code facts 3 to a check, the host-call scan
  200 indices at a time, block starts 12 indices at a time, and each block's cost as a chain of
  simulation links between explicit states (`CodeView.Sim.steps`, `run_steps`). The blob is a list
  of 1024-octet chunks (`NatBlob.ofChunks`), and every check reads only the chunks it needs
  (`NatBlob.cview`, `byte_ofChunks_window`), so none rebuilds the 223 kB number. Profiled with
  nanoda (`scripts/nanoda-profile.sh`), witness's whole code check is about 16,800 declarations,
  1.6 × 10¹³ gas in all, none over a refine (the heaviest 54 ms).
* **The witness service** (`Services/Witness.lean`). The witness bounty market
  (ascrivener/witness at 71e585a), built with `cargo jam-build` 0.1.29, is vendored as
  `services/witness/witness-service.jam`. Its code names host calls 0–6, 9, 11–14, 18, 20, 21, 24
  and 100 only. `accumulate_confined`: accumulating witness changes nothing outside its own account,
  for every state, input and gas. `refine_noExports`: its refine exports nothing. Both hold for any
  code naming only those ids, and `Services/Witness/Confined.lean` states them for the vendored
  binary itself: the kernel scans every opcode position of its code for `ecalli`
  (`CodeCheck.hostIds_ok`), so `Confined.accumulate_confined` and `Confined.refine_noExports` have no
  hypothesis about the code and depend on propext, Classical.choice and Quot.sound only
  (`lake build witnesscheck` remains as a compiled cross-check).
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

## A second service: Parity's bootstrap service

To check that the tooling is not witness-specific, it also runs on Parity's JAM bootstrap service
(`services/bootstrap`, built unmodified from the published crate, with the same SDK version as
witness). Its refine decodes a list of instructions and returns them; its accumulate runs them
with host calls for storage, service creation and transfers.

* **One generator, per-service configuration.** `genwitnesssteps --service bootstrap …` takes the
  blob, the base input and the classes of inputs from a per-service `Svc`. Witness is the
  default, and its generated files are unchanged.
* **Code facts and their check:** `Services/Bootstrap/Code.lean` (the 7,463-step refine of an
  empty instruction list, plus `memcpy`), checked by `lake build bootstrapcheck`.
* **Prefix:** `Services/Bootstrap/Prefix.lean`, the first 600 steps of its refine (both `fetch`
  calls, both heap growths and two `memcpy` calls) with what they leave, proved from Y's starting
  state for any argument length, as for witness.
* **Shared summaries:** `memcpy` is instruction-for-instruction the same code in both blobs
  (at 186740 in witness, 68729 in bootstrap), so `Services/Bootstrap/Memcpy.lean` is witness's
  proof with the pcs moved, checked again by the kernel. The SDK's decoders and the allocator
  are not shared: the compiler specializes them differently in each service, so their summaries
  are per binary.
* **Summaries used by the generated runs.** For a service with a `memcpy` summary, the generated
  prefix does not step through `memcpy` calls of fewer than 16 octets whose arguments are the same
  in every traced run: it splits the run there (`FreeStepsH.ex_trans`), applies
  `memcpy_small_regs` (`FreeStepsH.bind_ex`), and continues from the return with the registers
  it guarantees. Bootstrap's prologue makes 31 `memcpy` calls before it reads its arguments
  (step 3455); 29 of them are under 16 octets.
* **Refine on an empty payload** (`Services/Bootstrap/PsiREmpty.lean`, `psiR_empty`): for every
  c < 2^16, i < 2^16 and service id < 2^32, Ψ_R's result is ☇ (panic) or ∞. The decode of
  `Instructions` fails and the service's `unwrap` traps at 6377.
* **Refine on an empty instruction list** (`Services/Bootstrap/NoInstr.lean`, `psiR_noinstr`): for
  every c < 2^16, i < 2^16, service id < 2^32 and 32-octet salt, with the payload
  ℰ(`Instructions { instructions: [], salt }`) = [0] ⌢ salt, Ψ_R's result is
  ℰ(`BootstrapWorkOutput { instructions: [], work_item_index: i }`) = [0] ⌢ ℰ₂(i), or ∞. The run
  is composed as follows:
  * `NoInstrArgs` covers the prefix and the argument decodes.
  * `NoInstrHead` copies the payload to the heap and reads the hash.
  * `NoInstrTail1` … `NoInstrTail8` handle the log of s; each one is generated for a different
    number of hex digits of s.
  * `NoInstrFinish` reads the salt, encodes the output and halts.

  The generator's `out` mode states each output octet that depends on the input as an expression
  in it (i mod 256 and i / 256 here).

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
* **Enough gas** (`Logic/GasBound.lean`). The converse of `psiM_of_freeRunH`'s "or ∞":
  `psiM_of_stepsH` says that from Y's state, a chain of at most n steps (`FreeStepsH … n`) to a
  halting step gives Ψ_M exactly that halt's output, given at least (n + 1)(M + H) gas, every step's
  block costing at most M = `stepCostCap` (`CostOk`, which each step of the chain carries) and every host call the
  contract allows costing at most H and doing what the contract says with that much gas
  (`HostCostLe`). Each continuing Ψ₁ step with ϱ ≥ M is the gas-free step (`step_eq_of_gas`), and
  Ψ_H* then follows the chain step by step (`psiHStar_of_steps`). `FreeStepsH` carries the bound:
  each step and host call counts one, `pad` and `mono` loosen it, and generated chains state their
  exact step count. `refineContract` allows a call only as the dispatcher answers it with
  `hostCostMax` gas, which `refineContract_cost` turns into `HostCostLe`: each gas-independent call
  charges a fixed cost (`RefineHost.dispatch_cost`). `refineContractK cap` is the same contract
  with any cap (`refineContract` is it at `hostCostMax`; `refineContractK_pins`,
  `refineContractK_cost`), and a chain under `refineContract` lifts to any larger cap
  (`refineContract_le`, `FreeStepsH.weaken`).
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
   The facts the proof uses are one hypothesis, `checkCode p fs = true`, which the kernel checks of
   the vendored witness blob over a representation it evaluates quickly, the blob as one number
   (`PVM.NatBlob`, `Services/Witness/CodeCheck.lean`).
2. **Symbolic execution**, proved sound against Ψ₁: registers and memory as terms over the
   inputs, a path condition, case splits at the input-dependent branches.
3. **Summaries** for loops and library code (the copy loop first), proved once by induction and
   used in place of their code.
4. The theorem, as one gas-free run lifted to Ψ_R with `psiM_of_freeRunH` ("[12, 0] or ∞"),
   then a gas bound.

Staging: the first statement fixes a one-octet payload with first octet ≥ 12, leaving c, i, s and
ℋ(p) arbitrary. The traced path shows those only reach the SDK's varint decoder and are then
stored, while the payload length also sets the sizes the heap allocator works with; a one-octet
payload keeps the allocator's state concrete. Empty payloads and payloads of up to 15 octets
follow (milestone A′, `psiR_rejects`).

## Checking on chain: witness-lean

[witness-lean](https://github.com/ascrivener/witness-lean) checks Lean proofs on JAM, in witness's
refine, with an independent kernel (nanoda), one batch of declarations per refine. To be attested
there, each declaration has to check within one refine (5×10⁹ gas, about 50–60 ms of native
nanoda time). Lean's own build times say nothing about this: the tactics never go on chain, only
the terms they leave.

Two scripts measure it, with a witness-lean checkout (`WITNESS_LEAN`, `cargo build --release -p
lean-host` and `cargo jam-build --out-dir out` run there), lean4export at its pinned commit for this
toolchain (`LEAN4EXPORT`), and for gas a witness checkout with witness-sim built (`WITNESS`):

```bash
scripts/nanoda-profile.sh OUT Services.Witness.PsiREmpty Services.Witness.PsiREmpty.psiR_rejects
```

```bash
scripts/nanoda-gas.sh OUT Services.Witness.PsiREmpty.psiR_rejects
```

The first exports the declarations' closure, converts it to witness-lean's nodes and checks every
node with nanoda natively, reporting each one's time against a refine. The second plans the
batches with witness-lean's planner and runs the ones holding the named declarations in
witness-sim's PolkaVM, which charges PolkaJam's gas.

Measured on `psiR_rejects` (milestone A′), 2026-11-04, nanoda as vendored by witness-lean at
`a3ef25a`:

| | |
|---|---|
| Nodes | 18,571, all accepted by nanoda: an independent kernel agrees with Lean's on all of A′ |
| Statements, proofs | 16 MB, 115 MB |
| Checking in all | 101 s natively, about 8×10¹² gas |
| Over one refine | 36 nodes; the heaviest `run_badTag` (16.7 s, and it overflows a 64 MB stack), `prefix_run` (7.4 s, a 10 MB proof), the 260-step segments (0.75–1.2 s each) |
| A generated segment of 20 steps | 47 ms natively; attested in witness-sim at 3.4×10⁹ gas, of which about 1×10⁹ loads its 2,136 trusted nodes |
| 40 / 80 steps | 93 ms / 314 ms |

So each symbolic step costs about 2.3 ms of nanoda time, and a node holds about 20 steps.

**Paths cut to fit** (`genwitnesssteps cut PC name A B every=N`). The generator cuts a path into
segments of at most N steps and names the state at each cut: `St k` is a structure of the facts
the rest of the path reads there (the registers read before written, the octets as runs within
8-octet words, symbolic words, and merged page-access ranges), worked out backward from the end.
Segment k is two declarations: `steps`, the symbolic run from the registers and octets it reads
(as `seg`), and `run : St k → ∃ run, St (k+1)`, which takes `steps`' arguments from `St k` by
projection, carries every fact the segment doesn't touch across its frame (`readN_of_frame`,
a decided address condition), and rebuilds the words it writes from `steps`' post-octets
(`readN_cons`). `chain` composes the segments by transitivity alone; no fact is re-derived.
The registers a segment reads come from the instructions' operands (GP §A.5), so a cut's state
needs only what is read: the error tail's start needs ω₁, ω₅, ω₆ and 94 facts, against twelve
registers and 342 facts before. Measured for the error tail at N = 16 (97 segments):

| | |
|---|---|
| Heaviest `steps` (natively, in witness-sim) | 62 ms, 3.7×10⁹ gas |
| Heaviest `run` | 48 ms, 3.0×10⁹ gas |
| `chain` (97 segments) | 36 ms, 3.5×10⁹ gas |
| `run`, the 94-fact statement | 1.3×10⁹ gas |
| The tail in all | 12.9 s natively; 12,914 nodes, most of them the states' field projections |

Three options make `cut` a drop-in for a `segx` segment inside a composition:

- `frame`: each state also carries, from the chain's start (ω₀, μ₀), the frame (`fr`: every
  octet outside the writes of the segments so far, under the condition `C k`, built segment by
  segment), unchanged page access, and the registers no segment writes. The chain's `run` then
  states what `segx` would: the registers and live octets it leaves, its frame in `seg`'s form
  (converted with `not_mem_of_not_mem_cover`), and unchanged access.
- `keep=j,…`: the start registers the caller knows. Static reads overcount (a spill whose value
  nothing uses), so the others are dropped from the reads of the segments before their first
  write; a segment that did need one would fail to check.
- Cuts move: where a cut's state cannot be stated (a live value that is input-dependent and no
  variable's expression, such as a partly computed varint), the cut is dropped, joining its two
  segments, and the analysis retried.

`Front3`, `Front4` and `EFront3` are generated this way (18, 5 and 4 segments). A cut's values
may also be a variable sign-extended from 32 bits (𝒳₄, a 32-bit operation's result: the service id
in `Front4`), stated in the form `pvm_simp` leaves, `S + S / 2^31 · (2^64 − 2^32)`.
 The
model, the code facts and core are already small enough. What has to change is the shape of the
generated proofs: segments of about 20 steps, and compositions that don't re-derive every
hypothesis with `chase` (`run_badTag` discharges about 400 facts in one term).

The compositions (`run_badTag`, `run_empty`) are written by hand and call the generated chains'
`run`s with one `?_` per fact, each discharged by `chase`; `scripts/fix_holes.py FILE Name…` sets
those counts after a chain is regenerated.

**What is not cut.** The hand-written proofs that are still over one refine (the compositions, the
`decodeU32`/`decodeC`/`memcpy` summaries, `initialMemory_read`, `baseBytes_cases`) are left to
witness-lean's judgment splitting, which checks one heavy declaration over many refines by
attesting the kernel's judgments in pieces that cite each other (`lean-host judgments`; see
witness-lean's `docs/design/heavy-declarations.md`). On `run_badTag` it plans 352 ops of at most
2.7×10⁹ gas over 151 rounds. Cutting is preferred where a generator can do it: the cut chains
attest in one round with no extra data, and need nothing beyond the kernel.

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
21. **Authorization's F(c) binds g only in its condition** (§8): α[c] ⊖ {(g_w)_a} names a g that
    is quantified only in the case "∃ g ∈ E_G : (g_w)_c = c". We read it as that guarantee's
    authorizer (E_G has at most one guarantee per core). All authorizations vectors agree.
22. **Recent history** (§7) follows the paper as written: β_H^† corrects the last state root, the
    new entry has state root ℍ_0 and super-peak ℳ_R(β_B'), and β_B' = 𝒜(β_B, r, ℋ_K). The
    vectors give r = ℳ_B(**s**, ℋ_K) directly (`accumulate_root`) and agree throughout.
23. **Validator statistics** (§13.1). Three points the paper leaves loose:
    * The guarantee count tests κ'_v ∈ G, but G (eq. `guarantorsig`) holds Ed25519 keys. We
      compare (κ'_v)_e.
    * On an epoch change the fresh accumulator is written [(0, …), …] with no length. We use
      |κ'|, which |π_V'| = |κ'| (eq. `activityspec`) requires.
    * π_V^† credits assurances over N_{|κ|}, which we take as |π_V|.

    G itself is an argument: computing it needs the guarantor assignments M or M*, which need
    entropy and λ' that the vectors do not carry. The test builds G from κ' and each credential's
    validator index. The vectors agree with all three readings, including the full-size
    `stats_epoch_change_with_set_resize-1`, where the set shrinks from 1023 to 6 validators.
24. **The service provision sum** (§13.2) is written ∑_{(s, **d**) ∈ E_P}(1, |**d**|) inside
    ∀ s ∈ **s**. Read literally as a fresh binding, it would give every service the whole
    extrinsic's count. We read s as already bound, so the sum covers that service's pairs only.
    `preimages_order_check-3` provides to two services and agrees. The statistics vectors cover
    only validator records, and the preimages vectors only the provision counts. Core
    statistics and the refinement and accumulation parts of service records are modelled
    (`coreStats`, `serviceStats`) but untested here.
25. **Preimage errors.** The paper says E_P must be ordered and unique and every pair providable,
    but it names no errors and gives no order between the two checks. We check ordering first
    and use the vectors' names (`preimages_not_sorted_unique`, `preimage_unneeded`). Pairs are
    ordered by service, then by the data octets lexicographically. On an error, the vectors keep
    the prior state; the paper makes such a block invalid.
26. **ℰ on Booleans.** Appendix C defines no encoding of {⊤, ⊥}, which appears in a verdict's
    judgments and in faults (𝔼_D). We encode ⊤ as 1 and ⊥ as 0 (ℰ of the indicator, by the
    notation section's ⊤ = 1, ⊥ = 0) and decode only those two octets. The codec vectors agree.
27. **Trie keys are 31 octets; the vectors' are 32.** State keys are 𝔹_31 (§D.1) and L stores
    exactly 31 octets of key, but `trie/trie.json` gives 32-octet keys. The test passes the first
    31 octets to M, after checking that no two keys of a case share them; all 11 roots then
    match, so the vectors' last octet never matters.
28. **Erasure coding: the vectors pad the message polynomial to a power of two.** §H.3 interpolates
    p of degree < d = R(v) through the d message words at 0̃ … (d−1)~ and gives validator i ≥ d the
    word p(ĩ). Every erasure vector (tiny and full) instead takes p of degree < n = 2^⌈log₂ d⌉
    through the message words and zeroes at d̃ … (n−1)~, and gives validator i ≥ d the word at
    (n + i − d)~. The data shards agree; the parity shards differ. We follow the paper, and
    `Tests/ErasureTest.lean` lists all 12 vectors in `knownDeviations`. For each it checks that the
    vectors' convention, built from the model's own interpolation, reproduces every shard, and
    that ℛ recovers the paper's code from two different shard subsets. CI fails if any vector
    departs in another way or starts to match.

    *Where the convention comes from.* No Gray Paper release describes it. From v0.3.3, the first
    with "The Generator Polynomial", to v0.8.0, that subsection says degree < d (341 before the
    rate became R(v) in v0.8.0) and points d̃ …; v0.1.1–v0.3.2 give no polynomial, only "the same
    transform as done by the algorithm of" Lin, Chung and Han (2014), which §H still cites. The
    vectors' own documentation (`erasure/README.md`, the schema, the CHANGELOG) says nothing about
    the layout. It is the layout of power-of-two additive-FFT encoders in that paper's line: the
    documentation of the `reed-solomon-simd` crate (a Leopard-RS derivative) describes its
    "low rate" mode, used when there are more recovery than original shards, as "Original shards
    fit into a single chunk which is padded with zero-filled shards if needed. Recovery shards are
    generated in chunks", chunks being the next power of two of the original count, which is the
    convention above. Only documentation was consulted, not any implementation's code; the vectors do
    not say which implementation produced them. The paper's text, which is explicit, is what the
    model follows.

29. **Disputes** (§10).
    * *Signatures are a parameter.* The model does not implement Ed25519: `JAM.disputesTransition` takes a
      `Crypto` (`JAM/Crypto.lean`) whose `edVerify` stands for s ∈ 𝕍̄_k⟨m⟩. The test runner's
      oracle is read from each vector's expected output: when it is `bad_signature`, every
      signature is rejected, otherwise every one is accepted. So these tests check everything
      except signature validity itself: a `bad_signature` vector only confirms that the
      transition rejects when verification fails.
    * *Errors and their order.* The paper names no errors and gives no order between the
      conditions. We use the vectors' names, and check in the order of §10.2: verdicts ordered
      and unique; for each verdict its age, the order of its judgments, their count
      ⌊2/3·|**k**|⌋ + 1, each judge index and signature, then "not already judged" and V
      defined; then culprits, then faults, then the faults that good verdicts need.
    * *Faults.* The condition r ∈ ψ_B' ⇔ r ∉ ψ_G' ⇔ v is read as a chain of two equivalences:
      the report is in exactly one of ψ_B' and ψ_G', and v = ⊤ exactly when it is bad. Read as
      ((r ∈ ψ_B' ⇔ r ∉ ψ_G') ⇔ v), a ⊤ fault on a good report would pass.
    * *Offender keys.* **k** = {i_e | i ∈ λ ∪ κ} ∖ ψ_O. A key outside **k** is reported as
      `offender_already_reported` when it is in ψ_O, and as `bad_guarantor_key` (culprits) or
      `bad_auditor_key` (faults) otherwise. κ and λ are the prior sets, as the paper writes them.
    * A bad verdict needs no culprits in GP 0.8.0, and the vectors agree
      (`progress_with_bad_verdict_without_culprits-1`). On an error the vectors keep the prior
      state; the paper makes such a block invalid.

30. **Assurances** (§11.2). Signatures are checked through `Crypto.edVerify`, with the test oracle
    of note 29. The paper names no errors and gives no order between the conditions; each
    assurance is checked in turn, in the order §11.2.1 states them: the anchor H_P, the assurer
    index (a_v ∈ ℕ_{|κ|}) and order, the signature, then the bits. A core is cleared when its
    report is in **R**, compared by encoding. A stale report that is still assigned may be
    assured and made available; the paper allows it (ρ^‡[c] ≠ ∅ is all a set bit needs) and the
    vectors agree (`assurances_for_stale_report-1`).

31. **Safrole** (§6).
    * *Cryptography is a parameter.* The model implements no Bandersnatch arithmetic. `JAM.safrole`
      takes a `Crypto` (`JAM/Crypto.lean`) whose `bsRingRoot`, `bsRingVerify` and `bsRingOut` stand
      for O, 𝔹̄°_r⟨c⟩⟨m⟩ and Y of a Ring VRF proof (Appendix G). `bsVerify` and `bsOut` stand for
      the IETF VRF and are used only by `JAM.sealValid`, the header's seal and entropy-source
      conditions. The transition takes Y(H_V) as an input, as the vectors give it.
    * *What the vector tests check.* `Tests/SafroleTest.lean` builds a closed-world oracle per
      chain from the vectors themselves. The vectors' tickets carry only (entry index, proof).
      Since **n** ⊆ γ_A', each accepted ticket's identifier is read from the posterior γ_A'.
      `bsRingVerify` is then true exactly on the (γ_Z', `$jam_ticket_seal` ⌢ η_2' ⌢ e, proof)
      triples of accepted tickets, and `bsRingOut` maps those proofs to their identifiers.
      `bsRingRoot` maps the Bandersnatch keys of each epoch change's γ_P' to its γ_Z'.
      The tests therefore check everything in §6 except the cryptography: rotation and Φ, η, F, Z,
      the markers, the merge into γ_A', and the extrinsic's conditions. They also check that the
      model passes the right root, context and keys to the primitives; feeding η_1' for η_2', or ι
      for Φ(ι), fails the suite. They do not check that any proof, ring root or identifier is
      cryptographically right. "Valid" here means "accepted by some vector". The `bad_ticket_proof`
      vectors reuse an accepted proof with a different entry index, so the oracle rejects them.
    * *Errors and their order.* The paper names no errors and gives no order between the
      conditions. We use the vectors' names, and check the timeslot (H_T > τ, §5), then |E_T|
      (eq. `enforceticketlimit`), then each entry index and then each proof (eq.
      `ticketsextrinsic`), then the order of **n**, then its disjointness from γ_A, then
      **n** ⊆ γ_A'. Every error vector gets the vectors' error with this order. No vector submits a
      ticket that is valid but falls outside γ_A' (`useless_ticket` here), so that condition is
      untested.
    * *The order on identifiers.* The paper orders tickets by y ∈ ℍ without defining an order on
      ℍ. We compare the octet sequences lexicographically; the vectors agree.
    * *The entry index in a context.* `$jam_ticket_seal` ⌢ η_2' ⌢ e appends a natural number to an
      octet sequence. We append it as one octet (e < n ≤ 2𝖤/6 + 1 < 256). Under the oracle this
      is only checked to be the same convention in the extrinsic and in the oracle's tables.

32. **Reports (guarantees)** (§11.3–§11.5).
    * *Inputs outside the state.* Two inputs are arguments of `JAM.guarantees`: the pipeline's
      package set ⋃ K(β_H's **p**) ∪ ⋃ ξ ∪ **q** ∪ **a** (computed by `knownPackages`; the vectors
      give it as `known_packages`), and the ancestor-set condition on lookup anchors, which needs
      the last 𝖫 headers. The vectors carry no ancestor set, so the test takes the condition to
      hold. The vectors' `recent_blocks` is taken as β_H^†.
    * *Errors and their order.* The paper names no errors and gives no order between the
      conditions. We use the vectors' names and check: the extrinsic's core order; then per
      guarantee its credential and timeslot, the signers (index, assignment, active core, key,
      signature), the report's shape (1 ≤ |r_d| ≤ 𝖨, dependencies ≤ 𝖩, size ≤ 𝖶_R), the erasure
      shards, the core free, the authorizer, the services and gas; then duplicates within the
      extrinsic; then per report its anchor, lookup anchor, novelty, segment-root lookup,
      prerequisites and code hashes. The segment-root lookup is checked before the prerequisites:
      a lookup key in neither the extrinsic nor β also fails the dependency condition, and the
      vectors call it an invalid lookup (`segment_root_lookup_invalid-1`).
    * *Split conditions.* The paper writes **c**_v = r_c < |κ'|/3 as one condition; we report
      `wrong_assignment` and `bad_core_index` separately. The anchor condition asks for one
      y ∈ β_H^† matching hash, state root, super-peak and slot; a context whose hash matches no
      entry is `anchor_not_recent`, otherwise the first field that matches no such entry is named.
    * *Banned keys.* Φ (eq. `blacklistfilter`) replaces an offender's key with the null key, whose
      signatures the paper rejects like any other bad signature. We report a signer with the null
      key as `banned_validator` before checking its signature.
    * *Guarantor assignments.* R takes x mod |**c**|/3 and P uses ⌊i/3⌋; when |κ'| is not a
      multiple of 3, |**c**|/3 is read as ⌊|**c**|/3⌋. M* reads κ' or λ' from the epoch of τ' − 𝖱,
      taken as 0 when τ' < 𝖱. The full-chain vectors with a shrunk set agree.
    * The reporters G and the incoming reports' core and service statistics (π_C', π_S' of
      §13.2) are checked too, with no available reports, assurances, preimages or accumulation.

33. **Block import Υ** (§4, §5, Appendix D).
    * *Composition.* `JAM.importBlock` (`JAM/BlockImport.lean`) composes the section transitions
      along GP eq. `transitionfunctioncomposition`: disputes, Safrole (with ψ'_O), assurances,
      guarantees (with κ', λ', η', ψ'_O and β_H^†), accumulation of **R**, recent history with θ',
      preimages (checked against the prior δ, integrated into δ^‡), authorizations from φ', and
      statistics. The STFs are used unchanged; `AccResult` gained a field `outputs` holding θ',
      which `accumulate` computed but did not return. σ is `JAM.State` and T, M_σ are
      `State.serialize` and `State.root` (`JAM/State.lean`).
    * *Header conditions* (§5): H_P is the hash of the last retained header, H_R = M_σ(σ), H_X as in
      eq. `extrinsichash`, H_O, H_E and H_W equal to the markers the transitions produce,
      H_I < |κ'|, and `sealValid` for the seal and entropy source. The wall-clock bound is not
      checked. The ancestor set 𝒜 of §11.4.1 is the retained headers together with the block's own
      header, so that a lookup anchor can be the parent; the paper does not say whether 𝒜 includes
      the block being imported.
    * *Serialization.* ρ's entries are serialized with the whole guarantee (r, t, **a**) and then
      ℰ_4 of the timestamp, as in C(10); the traces agree. The core and service statistics π_C, π_S
      use the general natural encoding ℰ for every field, gas included; the traces agree, while
      Appendix D says numeric state terms use fixed-length encodings by the size of the term.
    * *The trace runner* (`Tests/TraceTest.lean`, `lake build tracetest` after
      `scripts/fetch-trace-vectors.sh`). Trace states are raw key-values. A storage key is hashed
      in C(s, h), so a raw state with storage cannot be decoded into 𝔸 (whose storage is keyed by
      the original keys). The runner decodes only the genesis state (preimages and requests are
      recognised by hashing) and keeps the model's own σ from there, comparing T(σ') and M_σ(σ')
      with every post-state. Cryptography: every signature, VRF and ring proof is accepted (the
      blocks are known valid); Y is the Bandersnatch VRF specification's output hash, SHA-512 of the
      suite string, 3, the 32-octet output point and 0, cut to 32 octets (`JAM/Sha512.lean`, FIPS 180-4). This follows the output-hash convention of the Bandersnatch VRF specification, which GP Appendix G defers to; it is beyond the paper's text. Only the runner's `Crypto` instance uses it: `JAM.Crypto` stays a parameter and no STF changed; O
      is answered from (γ_P, γ_Z) of the states already seen, as every state has γ_Z = O(γ_P).

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
