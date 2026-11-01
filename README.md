# pvm-lean

An executable Lean 4 model of the JAM Polkadot Virtual Machine, written from the
[Gray Paper](https://github.com/gavofyork/graypaper) **v0.8.0** (Appendix A, `text/pvm.tex`) and
checked against the PVM test vectors of
[koute/jamtestvectors](https://github.com/koute/jamtestvectors) (branch `master_pvm_initial`,
commit `6bf3768e5b37bbe4ca5d6e1306284ecb27c0198f`, directory `pvm/`).

It is meant for proofs as well as evaluation: everything is total, decoding is kept separate from
execution, memory is an extensional finite map, and the theorems use only `propext`,
`Classical.choice` and `Quot.sound`. The model depends only on Lean core and `Std` (toolchain
`v4.36.0-rc1`).

## Scope

The boundary is **Appendix A of the Gray Paper, all of it and nothing more**: §A.1–A.5 (deblob,
decoding, instruction semantics, memory, Ψ₁, Ψ), §A.6–A.8 (Ψ_H, Y, Ψ_M) and §A.9–A.10 (the gas
model). Results are exactly the paper's tuples. From outside Appendix A the model uses only what
Appendix A itself references: the integer and bit-sequence encodings of Appendix C, the RAM and
register definitions of §4.7, and constants. Host functions, service accounts and the refine,
accumulate and is-authorized invocations (Appendix B) belong in a separate package that depends on
this one. Test-vector conventions (`map`/`write`/`set-reg` steps, how runs resume, the exit index
the vectors call `pc`) live in `Tests/`, not in the model.

## Results

| Check | Result |
| --- | --- |
| `programs/` vectors (status, registers, pc, gas, fault address, host call, memory) | **364 / 364** pass, with gas charged by the model's own ϱ^Δ |
| Block costs in `programs/` | **5,123 / 5,123** correct |
| Block costs in `gas-tests/` (doom, pinky, prime-sieve) | **39,737 / 39,737** correct |
| Model's ϖ against the blocks the vectors list | identical in all 367 programs |

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
    paper's equation) for handlers that do not add gas; for others `psiHStar` stops with ☇ after
    its fuel.
14. **Y's fit condition is vacuous.** With 3-, 3-, 2- and 3-octet length fields, |**o**|, |**w**|,
    z𝖹_P and s are bounded so that 5𝖹_Z + Q(|**o**|) + Q(|**w**| + z𝖹_P) + Q(s) + 𝖹_I is at most
    about 2^28.3 < 2^32. We check it anyway.
15. **Y's argument bound.** The paper types **a** ∈ 𝔹_{:𝖹_I}; for longer arguments we return ∅.

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
