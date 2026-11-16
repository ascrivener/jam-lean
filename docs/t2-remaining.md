# T2: the remaining work (map, 2026-11-16)

What still stands between `main` and a T2 statement (`accumulate_spec`, `docs/bootstrap-target.md`)
stated with named hypotheses. Written by Handlers A (7th session) from the Handlers and Acc READMEs,
T2 inputs' handoff (`claude/bootstrap-t2-inputs-wip`, Acc/README.md) and `docs/HANDOFF.md`.

The final theorem is `∀ f, Impl p (accContractS env) env AccAbort (Spec.accumulate C t) Halts` from
instruction 5, then `psiA_of_impl` (`Acc/Impl/Lift.lean`, on main). Every row below contributes one
`Impl` piece or one ingredient of that statement.

Sizes: **S** is under a session, **M** is one to three sessions, **L** is more than three. "Hyp?" says
whether a named hypothesis (listed in the docstring and in `docs/whats-proven.md`, as CLAUDE.md
allows) could stand in for the item for now.

## Done (on main, or proved on a branch with a PR open or next)

| Piece | Where |
|---|---|
| `Impl`, `Impl.bind`/`pre`/`forIn`, `accContractS`, the lift `psiA_of_impl`, `ASem` | main, `Acc/Impl/` |
| Start, 5 → 6501 (`start_to_6501`), and `acc_log_line` (6501 → 6630) | main |
| `inputs_decode` (6630 → 6674; ≤ 89 inputs, blobs ≤ 16384 octets: G3) | main |
| SDK wrappers `get` / `set` / `remove` (Q18) | main, `Acc/Wrappers/` |
| `on_transfer` as `Impl … (onTransfer …)` (`tr_impl`) | `claude/bootstrap-t2-inputs-wip`, PR #222 |
| Items-loop pieces: `items_end`, `items_halt`, `op_pre`, `op_mid`, Disp, Head | inputs WIP |
| `ParamStatics` established by the prologue (`start_to_6429_statics`) | `claude/bootstrap-t2-statics` (PR after #222) |
| Row 8, `add_recent` as `Impl … (addRecent …)` | PR #224 |
| Row 9, `results_init` as `Impl` of the empty results write and `checkpoint` | `claude/bootstrap-t2-handlers-a-row9` (PR after #224) |

## Remaining

| # | Item | Prerequisites | Natural owner | Size | Hyp? |
|---|---|---|---|---|---|
| R1 | **Items-loop skeleton**: `Impl.forIn` over the inputs at loop head 6766 (frame sp as at 6674); transfer arm → `tr_impl`; work-error arm (skip, 15191); end → `items_halt` | `tr_impl` (#222); an operand-arm summary (R2) | T2 inputs | M | No (it is the spine) |
| R2 | **Operand arm composition**: item log line (6955, `item_fmt_site`), output decode (R3), row 8, row 9, instruction loop (R5), row 11 (R7), the operand's drops (15191) back to 6766 | R3, R5, R7; rows 8 and 9 | T2 inputs or Handlers A | M | Partly: each sub-piece can be a hypothesis while it lands |
| R3 | **Output decode** at 7073 (`BootstrapWorkOutput::decode`, `Vec<Instruction>` at sp − 1160, then the `u16` item) under HeapHost: success, Exhausts, and the decode-error branch (→ ☇) | frame-base `ElemOkF`/`Loop` (T1 decoders); HeapHost decoders | Vec / Decode-HeapHost (`claude/decode-heaphost`, paused) | L | Yes for the error branch (decided: an open obligation, local premise allowed); the success path could also be a hypothesis ("decodes to `Dec.output`") |
| R4 | **Results representation** `ResultsAt μ rp n rs`: the `Vec<Result>` at [sp+456] (144-octet items, count [sp+464]) built by the instruction loop, related to the spec's `results : List Result` | agreement on the item layout (the 144-octet `WorkExecResult`-like enum; tag octet, payload) | whoever owns R5 (Handlers A) | S–M | It is a definition, not a hypothesis; needs agreeing first |
| R5 | **Instruction loop** 8490 … 15032: per instruction the log line (`format!` 59375, `log`), the dispatch, the handler (R6) to the shared tail 14278, the result pushed onto the results Vec (growth: R8), the `Checkpoint` instruction's early results write (8650 → 8710, via 36170: R7) | R4, R6, R8; `Impl.forIn` | Handlers A (loop itself unowned today) | L | The per-instruction log lines (G4) can be fmt hypotheses, like `LogFmt` |
| R6 | **Handlers as `Impl … (onInstr C now i)`**, one per instruction (≈ 24 tags). Today only segment summaries exist, under `accContractK`/`Q` (Upgrade, Checkpoint, Designate, Assign, LookedUp, AssignForGasCost-empty, Panic); none is an `Impl`. To do: lift those to `accContractS`/`Impl`, then the rest: CreateService, Transfer (G1 `gas`), Zombify, Eject, DeleteItems, Solicit, Forget, Lookup, Import/Export, Bless, Yield, Provide, LookedUp, Imported, Exported, RandomStorageAccumulate, Benchmark (G5), AssignForGasCost (non-empty) | the wrappers (main); the Designate/Assign allocation side (#150); fmt summaries for each handler's `format!` (log-sites table in Acc/README.md; formatters 37897, 37996, 38706, Lookup/Exported/Import ones unidentified); the Encode arms for `Result` payloads (R9) | Handlers A (+ fmt for log sites) | L (the biggest item) | Yes per handler: "the handler at tag k implements `onInstr` … or aborts for `AccAbort`". Log sites already are hypotheses (`ArgsAt`, frame-only) |
| R7 | **Row 11**: 15032 … 15198, `store key (encodeResults results)` unless a `Zombify` (Q4), via 36170 for general n (the loop 36346, per item byte 255 → [1, e] else [0] ++ 36299), then the drops (33214 ret 558/560, 28864 ret 564, deallocs 15166 / 15185) and back to 6766 | R4; R8; R9 (36299); RO table at 68264 (R10); `res_head`/`res_free` generalised from n = 0 | Handlers A | M (given R8, R9) | Yes: 36299 per item as a hypothesis "appends `Result.encode r` or Exhausts" |
| R8 | **HeapHost growing writer** (`extend`/`prefix` with realloc under `HeapHost`, accumulate's counterpart of refine's `BufH`/`EncMH` under `refineContractK`). Needed because `Result.encode` of `.data`/`.dataVec` is unbounded, and for the results Vec's pushes in R5. Also lifts G3 (≤ 89 inputs, ≤ 16384-octet blobs) | refine's WriterGrow/EncMH as a template; allocator realloc lemmas (main) | Vec / Decode-HeapHost session | M–L | Yes, as a named "writer step" hypothesis; but it would sit under many lemmas, so proving it is preferable |
| R9 | **36299, the `Result` encoder**: dispatch through the i32 table at 68264 to the arms 30374 / 30512 / 30433 / 30438 / 30392 / 30567 / 30640 (tags 0–6) | R8 (for `.data`, `.dataVec`); R10 | Handlers A or Vec | M | Yes (per-arm or whole-encoder hypothesis) |
| R10 | **RO-data facts** for accumulate: the table at 68264 … 68291, key-size words 68680 … 68704, `set`'s error table 69056 / 69072, keys/templates in rodata | `VendoredFacts`/`FmtRO`-style definition (T1); an accumulate `roBytes` check (`Acc/RoData.lean`, `accRoBytes`) and `KeepsRO` | T1 (definition) + T2 inputs (carriage) | S–M | Yes: already carried as hypotheses (decided: allowed until step 10 of `bootstrap-target.md`) |
| R11 | **Frames keep the statics** (decided: Adam approved option (a)) 196616 … 196791 through `TrPost` and the fmt hypotheses (`KeyFmt`, `Utf8Call`, `LogFmt`), so `ParamStatics` reaches row 8 | decided (a): strengthen the three frames and thread the region through | T2 inputs | S | Yes (ParamStatics is already a premise; this discharges it) |
| R12 | **`AccAbort` and `ValuesFit`**: `AccAbort` = heap exhaustion (alloc null, > 2³⁷ − 32, Exhausts) and named quirks (Q18 remove-on-FULL panics; `orPanic` FULL is a spec panic, not an abort); the WF predicate `ValuesFit` (< 2⁶³) and its consequences (`StoreFit` for every intermediate context) | the list of trap addresses from every summary (36528, 34070, 32584, 47977, 3820, 4002, 15362, 15363, 34178, 48047 …) | T2 inputs | S | No (definitions) |
| R13 | **Remaining `get` band** 2³⁶ ≤ \|w\| + 31 ≤ 2³⁷ − 32 (32-bit unit count sign-extends) | allocator lemma "a request ≥ 2³¹ units returns null, keeping the context" | Vec / allocator | S | Yes (or excluded by `ValuesFit`-style bound) |
| R14 | **G1 `gas`** (0) at 11330 and 13011 (Transfer, CreateService) and **G5** Benchmark's `checkpoint` (11889) | the Acc/README.md G1 proposal; `accContractS`'s 0/18 case | Handlers A (with R6) | S each | No (small) |
| R15 | **The end** 15215 … 15359: halt with (ω₇, ω₈) = (0, 0) as `Halts` | — | T2 inputs (`items_halt` exists) | S | No |
| R16 | **Final composition and statement**: chain start → `inputs_decode` → R1 → `Halts`, pick one gas cap ≥ every summary's bound (2²⁷ for the allocator), discharge `ParamStatics` (statics branch), state `accumulate_spec` with its named hypotheses, list them in `docs/whats-proven.md` | everything above | T2 inputs (or parent's pick) | M | — |

## Plan B (Adam, decision 23, 2026-11-16): a T2 skeleton with named hypotheses

T2 is stated soon, with the plumbing proved and these named hypotheses (each in the theorem's
docstring and in `docs/whats-proven.md`, stated minimally and close to `Spec`, so that each can be
proved later without changing T2):
- **R6, per handler:** "the handler at tag k implements `onInstr C now i`, or aborts for `AccAbort`",
  for every tag except what is already proved (rows 8 and 9, the wrappers);
- **R3, the output decode's success path;**
- **R9, the results encoder 36299, per item:** "appends `Result.encode r`, or exhausts";
- **R8, the HeapHost writer step;**
- the per-instruction log lines (G4) as Fmt hypotheses, like `LogFmt`.

Interfaces (parent, 2026-11-16):
- `InstrRep : Spec.Instr → List UInt8 → Memory → Prop` (the 232-octet slot and its heap buffers) is a
  parameter shared by the R3 and R6 hypotheses, with a copy/frame field in the bundle (equivalent to
  ∃ InstrRep with R3 ∧ R6, so nothing is weakened). **Obligation:** T1's per-kind `Rep`s (`kindRep`,
  `AssignRep`, `BlessRep`, …) discharge it.
- The Debug log lines of the instruction (8772) and the result (the tail at 14278) are G4 Fmt
  hypotheses, stated by Handlers A, minimal and frame-only like `LogFmt`, and listed in
  `docs/whats-proven.md`.
- R5's result is the contract R2 consumes: from 8493 with `InstrRep` for each item, `ResultsVec []` and
  `HeapCtxC`, `Impl` of the spec's instruction loop, post at 15028 / 15050 with `ResultsVec results`,
  [sp+160] = 1 ↔ a `Zombify` is present, `HeapCtxC` keeping old chunks, and the frame.

Split: Handlers A does R4 (`ResultsAt`), R5 (the instruction loop as `Impl.forIn` against the
per-handler hypotheses) and R7 (row 11 against the R8/R9 hypotheses). T2 inputs does R1, R2, R12,
R15 and R16 (the final statement). R2's operand arm consumes R5's and R7's results; the interfaces
are agreed through the parent.

## Named hypotheses the statement would carry, as things stand

Already accepted or decided: `ValuesFit` (< 2⁶³); `ParamStatics` (an obligation, proved on the
statics branch); RO-data facts (R10); the fmt hypotheses `KeyFmt`, `Utf8Call`, `LogFmt` and the
handlers' log-site `ArgsAt` (with `ExhaustsP`); the output decode's failure branch (R3, an open
obligation); `RingFits` (2·𝖢·𝖨 < 2³², implied by `apply()`'s checks plus 𝖨 > 0).

Candidates if Adam wants T2 stated before R3/R6/R8/R9 are proved (each is a new assumption, so
his call): per-handler `Impl` hypotheses (R6), the `Result` encoder 36299 (R9), the HeapHost writer
step (R8), and the output decode's success path (R3).

## Critical path

R8 (HeapHost writer) unblocks R9, R7 and R5's pushes, and lifts G3. R4 should be agreed before R5
and R7 start. R6 is the largest body of work and parallelises per handler. R1/R2/R16 compose and can
proceed against hypotheses for R3/R5/R7.
