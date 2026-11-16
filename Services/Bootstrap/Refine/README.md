# Bootstrap T1 (refine): handoff

State of the work on bootstrap's `refine` (T1), written for the next session to pick up.
Everything cites Gray Paper v0.8.0 via the docstrings of the files named here; the spec side is
`Spec.refine` and `exportSeg` in `JAM/Refine.lean`.

## Current state (2026-11-16, read this first)

**On `main`:** `Refine/Milestone.lean` `refine_milestone` (#197, with the `Fmt.FmtRO` conjunct of
`VendoredFacts` from #207), T1c's first milestone M1. Ψ_R against `Spec.refine` for payloads of 1 ≤ n < 128
well-formed instructions, each passed through (`Kinds.MFixed`) or `ExportSegs`, with |y| + 48 ≤ 2^24.
- Named hypotheses: `VendoredFacts` (layoutOk, the three read-only tables and `FmtRO`; step 10) and `FmtHyps`
  (`ArgsLineOk` 4742, `ExportFmtOk` 5744, `DebugLineOk` 6159 for `Top.DRm`; the fmt summaries).
- Third outcome: `ExhaustsHeap` alone. That the run then ends in ☇ with no exports is a recorded obligation
  (`docs/bootstrap-target.md`, M1).
- Stack: the Fmt hypotheses and the frame lemmas take `S0 + 7560 ≤ M` (refine's real stack below its frame).
- Everything in the old "PAUSED 2026-11-14" list has landed (#179, #181, #182, #188, #197, #207).

**In progress:** the rest of M1 (T1c), on `claude/bootstrap-t1-m1-wip`. The plan went to the coordinator
on 2026-11-15:
- **A. n ≥ 128** for the existing kinds. The multi-octet length prefix, `Vec<Instruction>::decode`'s batches
  after the second (a loop over `finish_grow` batches), the loop's `LayP.hn`, and the exit encoder via
  `encode_okMH_big`. None of the Fmt hypotheses has n < 128 built in, so this only weakens `hn`.
- **B. The variable-width pass-through kinds** (`CreateService`, `DeleteItems`, `Bless`, `Assign`,
  `Designate`, `Provide`, `LookedUp`, `Imported`, `RandomStorageAccumulate`, `AssignForGasCost`). Each kind's
  `ElemOkAFC` from the Decode session's `*_elem_big`, the inner chunks in `Kp`, the heap encoder arms
  (`EncOkMH`), and the output drop of heap variants (`DropOut.NoDrop` generalised).
- **C. Eager `Lookup`** (host 7 is gas-free on main; handler 5278–5427, wrapper 49015, format at 5398).
- **D. `Import`** (fetch wrapper 44677, collect loop 30766; a missing segment traps, so `Spec.refine`
  panics).
- **E. The allocation-failure ☇ obligation.**

**Progress on A (2026-11-16):** A1–A3 done for 1 ≤ n ≤ 2²¹, as `RunMixedG.run_mixedG` (`run_mixed` for any
length prefix ℰ(n) and output ℰ(n) ⌢ encodings ⌢ ℰ₂(w)). Builds, axioms clean.
- `DecodeHeadG.headG`: `Instructions::decode`'s head for any n < 2^32 (general `decodeU32`).
- `DecodeVecN.w1G`, `v2gG`: the grow step between batches. Batches: 70, then min(remaining, length) (70, 70, 140,
  280, …); each later batch grows the buffer to length + batch by `finish_grow` → `realloc`.
- `DecodeVecNC`: `BInv`, `batch_step`, `batches`, `first_batch`, `vec_exit`, `vec_allC` (= `vec_anyC` for any
  1 ≤ n < 2^32, with `hbig`: 232 n < 2^30 − 64). `hbatch` is gone: OkFD's unused `es.length < 128` was dropped
  (Decode/LoopAPassC.lean, approved option (i); noted in Decode/README.md).
- `DecodeCG.decode_allC`: `decode_oneC` for any n (headG + vec_allC).
- `PassLoop.LayP.hn` is now n ≤ 2²¹ (was n < 128); `Entry.entry`, `Body.body`, `ExportElem.push` take n ≤ 2²¹.
- Exit encoder: `ExitEnc.enc_run` now runs `Encode.EncMD.encode_okMD_big` (no growth: |ℰ(n)| ≤ 4 for n ≤ 2²¹, so the
  232 n + 6 octets suffice for `EncOk` elements of ≤ 232 octets). Its output is ℰ(n) ⌢ out ⌢ ℰ₂(w), and the chain
  enc_run → exit_run → body → run_fixed/run_mixed/from4680/refine_core takes `[HasCodeA p P]`.
  `ExitEnc.out_small` turns that back into n :: … for n < 128, so `run_fixed`, `run_mixed` and `refine_milestone`
  keep their statements.
- **Open: where n ≤ 2²¹ comes from** (asked the coordinator, 2026-11-16). Every bound traces to
  `ReallocCall.realloc_call`'s hr1 (request < 2^25 − 1 units = 2^30 octets), which runs through the whole Alloc
  realloc chain. It is needed by: decode's realloc (232 n < 2^30 − 64, implied by n ≤ 2²¹); the output `grow_one`
  (`pass_elem_grow`'s len ≤ 2²¹); and, for part B's heap elements, `encode_okMH_big`'s `cap ≤ capBound` (2^28) and
  `hbig`. The payload bound |y| ≤ 2^24 allows n up to 2^24. Model side: the heap is 1 GiB (`maxSize`), so requests
  of ≥ 2^25 units fail in `growInplace` and `alloc`. `alloc_call` already covers sizes up to 2^36. What's missing is the
  binary's `realloc_impl` null path for 2^25 ≤ units < 2^32. Options sent: (a) T1 proves it in a new file
  (recommended); (b) Alloc generalises hr1; (c) bound n in refine_t1c (Adam).
- `TopG.from4680G`, `refine_coreG` (with `SpecRun.output_eqG`): `from4680`/`refine_core` for 1 ≤ n ≤ 2²¹, from pc 0
  to the halt with ℰ(`BootstrapWorkOutput { outI is, I }`).
- Next: part B; then refine_t1c (T1's match form) once the bound question is settled.

**Progress on C (2026-11-16, third instance, branch `claude/bootstrap-t1-m1c`):** the handler and the wrapper are
proved up to the composition with `PInv`. All files build, axioms clean.
- `LookupHost.FreeStepsH.lookupRef`: one Ω_H step under `refineContractK cap` (cap ≥ 1125 + ⌈264·ω₁₁/1024⌉; the gas cap
  stays internal, coordinator 2026-11-16), `lookupVal` / `lookupR7` / `lookupMem`.
- `Lookup`: `ld` (5095 → 5288, flag set), `la` (5288 → 5366, the frame G = M − 48), `lf` (5372 → `format!`), `ll` (→ log
  5428), `lfr` / `lfz` (free or not), `lp0` / `lpg` (room, or `grow_one`), `lps` (the `LookedUp` slot {2^63 + 17 from
  M + 8, the result's three words}, len + 1, → 4046), `ldrop` (4046 → 5042 for index 8, given the ro table entry
  `dropEntry8` at 65568).
- `LookupWrap`: `wn`, `wz`, `wbig`, `wl` / `wlh` (lock + `alloc_impl`, units < 2^31 / ≥ 2^31), `wu`, `wr`.
- `LookupRun.lookup_wrap`: 5366 → 5372 with `ResAt` (`None`, `Some []` with buf 1, or `Some d` in a fresh chunk), or
  `Bridge.AllocFails` (null at 49149, or `sizeTrap`). Internal hypotheses: preimages < 2^63 octets (`hlen`; Adam
  decides whether refine_t1c assumes it, recommended (a)), and the cap covering the second Ω_H (`hgas`).
- `LookupFmt.LookupFmtOk`: the named hypothesis for 5398's `format!` (with `OptVecAt` for the argument).
- Approved: `VendoredFactsC` = `VendoredFacts` ∧ the 96-octet 4046 drop table at ro offset 0 (for refine_t1c only).
  The table (ro[0 … 96)): index 8 → jump entry 122 → 4115 (return), 9 → 4129, 10 → 4302, 0 → 4463, 5 → 4169, 12 → 4160,
  13 → 4496, 17 → 4231, 18 → 4266, 19 → 4362, 22 → 4529; all others → 4115.
- Next for C: the step 5042 → 5042 for an eager `Lookup` on `PInv`. It needs `PInv` to carry the chunks owned by
  output slots (the preimage's buffer), with their data, as part B does for the heap kinds: do it together with B.
- Notes from the previous instance (part B): a new append-only code-fact tier "T1B" (approved; `Tests/GenWitnessSteps.lean`,
  `bootstrapSvc` after `fnRangesR`: `tiers := [{ name := "T1B", ranges := [(29176, 29675)], excludes := ["X", "R"], doc
  := "refine's output drop (drop_in_place::<[Instruction]>): the heap variants' drop arms" }]`). Drop arms: jump entries
  679 → 29270 (DeleteItems, 5), 685 → 29476 (Imported, 19); the drop table at 67760 maps index t to entry
  (67760 + offset_t)/2 − 1. The encoder with growth needs H arms for every fixed kind (`ArmsHFixed` etc.). `LayLMH`
  needs cap = 232n + 6 ≤ capBound (2^28), i.e. n ≲ 1.157M internally until ReallocBig.

Decided by the coordinator on 2026-11-15:
- the new theorem `refine_t1c` is added in T1's match form, and `refine_milestone` stays unchanged;
- the wider `DRm` and the new `LookupFmtOk` go on `refine_t1c` only;
- E (the ☇ obligation) takes route (b), the table, after A and B. The sizing is in `scripts/allocfail/`.

Earlier open questions (now decided as above): the Debug line for the new kinds (a wider `DRm`), a `LookupFmtOk` hypothesis,
the successor theorem's shape (T1's match form, for Import's panic), and the route for E.
The executor PRs #192/#194 (loops, forking) are not needed. The loop-heavy pieces (decode batches, the drop of
`Vec<Vec<u8>>`, Import's loops) come last, and use #194 if it has landed by then.

## Dependencies on other sessions

- **Fmt.** The Fmt sites are named hypotheses (below) until the fmt summaries discharge them.
- **Decode (Vec) session.** The element decoders (`Decode/*Elem*.lean`, `ElemsBig.lean`) and `ElemOkAFC`
  (`VecVecOwn.lean`) are theirs. T1 only lifts them.
- **Executor.** `PVM/SymExec` core is on main. Use it for straight-line stretches longer than about 25
  instructions with stores.

## Layout of the transform loop (refine frame `M = ω[1]`)

- Loop head **5042**: cursor at `M+144`, end at `M+120`, constants `M+128 = 2^63+24`,
  `M+136 = 2^63+1`; staging area at `M+304`; output `Vec<Instruction>` at `M+248` = {cap, ptr, len};
  elements are 232 octets; input elements start at `E`, the discriminant word at offset 0 is
  `2^63−1 + t` for dispatch index `t`.
- Dispatch: **8 → Lookup 5278**, **9 → Import 5125**, **10 → Export 5587**, **21 → RSR 5217**,
  every other index → pass-through **5561**. `grow_one` is 32785.
- Exit: 5042 → 6120 → 33214 (IntoIter drop, frees input chunk) → Debug line **6159** (format 59375),
  log 6187, free 6202 → output encoder (prologue 6248–6291 inlined, `encode_to` 30145, encoder fn
  30073, length prefix 30977, writer 58508), returns at 204 → 6295 → frees → trap/return at 29087.

## Plan

### Export handler (5587–5960): pieces done, composition next
On the wip branch (with #167 merged in): `HostSteps.lean` has `FreeStepsH.logRef` (100) and
`FreeStepsH.exportRef` (8: `exportCtx`, `exportR7`). `Export.lean` has every straight-line piece:
`xd` (5095 → 5587), `xa` (setup → 5653), `xs1` (→ the `export` call at 5664), `xs2` (5667 → `format!`, the
`Result` at M + 560), `xl` (5751 → `log` at 5784), `xf`/`xf0`/`xf1` (the `String` freed → 5641), `xn` (next
segment or 5810), `xp0`/`xpg` (room, or `grow_one` → 5832), `xps` (`Exported(n)` pushed), `xr0`/`xr1`/`xr1z`/
`xr1r`/`xr2` (the segments freed), `xt0`/`xt0z` (their `Vec` freed), `xt1` (→ 5042, no drop: bit 10 of the
mask at M + 40). Next: the segment loop (invariant at 5653: segment j, the context with j exports appended,
`FmtCall` at 5744 as a hypothesis), the free loop, and the step 5042 → 5042 for `PInv` (`O k` = the
`Exported(n)` slot). `PInv` gained `c40`, `c16`, `c24`, `c32` (Lookup's log constants) for the handlers.

**Done (`ExportSeg.lean`)**: `ExportFmtOk` (the hypothesis for 5744's `format!`, `FmtCall`-shaped with the
context kept: the Fmt session was asked to provide x' = x), `seg` (one segment: export, format, log, `String`
freed, next), `expUpTo` (the context after j segments, read from μ0), `segs` (the whole segment loop
5653 → 5810, all n ≥ 1 segments exported in order).
**Done (`ExportStep.lean`, `ExportElem.lean`)**: `xhead`, `push_room` / `push_grow`, `tail`, and the whole
instruction: `ExportElem.export_step`, `PInv k` → `PInv (k + 1)` (5042 … 5042) for an `ExportSegs` element whose
`Vec<Vec<u8>>` buffer and segment buffers are chunks to keep (`Kp`), distinct; the chunks to keep afterwards
(`Kp'`) exclude the freed ones; slot k holds `Exported(ns)`; the context becomes `ExportSeg.expUpTo env μ0 ptrv x ns`.
Or an allocation fails (`ExhaustsX`, with an unbounded step count: the loop needs `LoopG`'s bound B replaced by
an existential).
**Old plan**: the full step 5042 → 5042 for index 10: stage (`Pass.pa` + `memcpy_any`, as in `pass_elem`) → `xd` →
`xa` (or the n = 0 case straight to 5810: needs a `xa0` variant) → `segs` → `xp0`+`xps` or `xpg` +
`Decode.GrowOne.grow_one_call` + `xps` (as in `PassGrow`) → the free loop (`xr0`, then per segment `xr1` +
`dealloc_call` + `xr1r` or `xr1z`, then `xr2`; a small induction like `segs`) → `xt0` + `dealloc_call` or
`xt0z` → `xt1`. The result: `PInv (k + 1)` with slot k `Exported(n)` (first word 2^63 + 19, count n), the
context `expUpTo … n`; the segments' chunks and their `Vec`'s chunk freed (they must not be in `Kp`).

Plan for the segment step (5653 … 5653 / 5810), one segment g = ptr + 24 j of the n:
`xs1` → `HostSteps.FreeStepsH.exportRef` (needs `μ.rangeReadable sp (min sl 4104)`: the segment's data lies in an
allocated chunk) → `xs2` (v = `exportR7 env x` ≠ 2^64 − 1, true while ς + 3072 < 2^64 − 9: take it as a
hypothesis on ς) → the `format!` at 59375 as a hypothesis in Fmt's `FmtCall` shape (`Fmt/Format.lean`: from
`HeapCtx`, `Keeps pb M (String at M + 584 … M + 608)`, `StrOut`, or `Fmt.Exhausts`, which `ExhaustsX.ofFmt`
absorbs) → `xl` → `FreeStepsH.logRef` → `xf` + `Decode.DeallocCall.dealloc_call` + `xf1`, or `xf0` → `xn`.
The context after segment j is `exportCtx` applied j times (`RSem.reply (.exportSeg d)` with
`padSeg d = d.take 4104 ++ zeros`, matching `exportCtx`'s `min (reg ω 8) 4104`).
`ExhaustsX` is now `Bridge.AllocFails` (any allocator's null return, or the size trap), so Fmt's exhaustion
(40611 / 40821) folds in (`ExhaustsX.ofFmt`).

#### (old notes)
Per segment of the element's `Vec<Vec<u8>>` (24-octet {cap, ptr, len} entries, loop 5641–5807):
setup 5587–5664; **ecalli 8 at 5664**; result check 5667–5695 (≥ 2^64−9 is an error; 2^64−1 →
trap 6377); per-segment `format!` at **5744** (→ 59375), log (host 100) at 5784, free at 5800
(→ 40613); back to 5641 via 5807. After the segments it pushes an `Exported` element (5810; grow
32785 at 5826). Spec side: `exportSeg` in `JAM/Refine.lean` — the context x's export list grows by
each segment.

### Lookup handler (5278–5558), part C (host 7 is gas-free on main)
Disassembly read 2026-11-16 (`python3 -I scripts/allocfail/dis.py services/bootstrap/jam-bootstrap-service.jam`):
- 5279: the eager flag at M + 348; 0 → pass-through 5561 (lazy Lookup is passed through unchanged).
- 5288–5364: the hash (4 words from the element at ω₅ + 12 … 36) to M + 168 … 192, service id (i32 at M + 312) as
  u64, out = M + 560; frame M − 48 (ret 170 at M − 8, ω₅/ω₆/out saved); ecalli 7 (ω₉ = buf 0, ω₁₀ = 0, ω₁₁ = 0:
  the length query), then the wrapper 49015.
- Wrapper 49015 on r = ω₇: r = 2^64 − 1 (NONE) → `None` (−1 stored at out), return; other r ≥ 2^64 − 9, or
  r ≥ 2^63 → trap. r = 0 → buf 1 (dangling). Otherwise r > 2^37 − 32 → trap 49074 (counts as heap exhaustion,
  standing decision), else the allocator's spin lock (196608 / 196792 + 10056), `alloc_impl` 41177 for (r + 31)/32
  units, align 1 (cf. `Decode/AllocHuge.alloc_impl_huge_callG`), lock cleared (store_u8 at 196792 + 8192 + 1864),
  null → trap 49074. Then ecalli 7 again (buf, offset 0, len r; result unchecked) and out = {r, buf, r}
  (`Some(Vec)`), return to 5372.
- 5372–5428: `format!` at **5398** (template args at M + 536: (M + 560, saved fmt fn)), string at M + 584, log
  (host 100) at 5428; free 5441 if cap ≠ 0.
- 5448–5545: the result {M + 560 … 576} copied to M + 584; push into the output `Vec` at M + 248 (grow_one 32785
  when len = cap); slot = {element word at M + 8 (the LookedUp discriminant), the three words}; len + 1; drop of
  the input element via 4046 (frame M + 304), → 5042.
- Output kind `LookedUp(Option<Vec<u8>>)`: a heap variant, so its encoding is an `EncOkMH` arm (growth) and its
  slot owns the preimage's chunk (Kp), like part B.

### Import handler (5125–5210), part D
Its fetch wrapper 44677 takes the allocator's lock, calls `alloc_impl` (41177, flag 0) for 129 units,
`memzero`s 4104 octets (70133), calls `fetch` (host 2, kind 6, index at sp + 16), keeps the whole 4104-octet
buffer on success; NONE → the locked free path (42327) and `None`; any other error → trap 44915. The collect
loop 30766 traps at 30976 on `None` (quirk Q10) and frees the input items (40613).

Disassembly: loads `M+328` (count) and `M+48`; `branchLtU 7 6 → 6375` (trap when out of range);
count 0 → 5963; otherwise allocates `count << 4` / `count << 3`-sized buffers via `loadImmJump 0 164
40494` (alloc), null → 6376; then 5194 → 5967 (fill loop). Can be done now with `CodeR`.

### Generalized loop invariant carrying x
`PInv` currently fixes the context `x` (only pass-through). Generalize to `PInv … k ω μ s x` where
the output prefix `μ.readN ptr (232k)` equals the encoding of the first k elements of
`Spec.refine`'s fold result (not just the input copy), and `x` equals the fold's context after k
elements (exports/imports). Each handler then supplies one step lemma of the shape
`step_room`/`step_full` (`FreeStepsH … 5042 … x 5042 … x'`), and `loop` is reproved over a
per-index step. The per-step bound is currently `512n + 6100`; handler bounds will need to be
added (Export scales with its segment count and lengths).

### Exit and encoder composition
Done: `ExitRun.exit_run`, from `PInv n` at 5042 to refine's return (6373 → the caller), for 1 ≤ n < 128 output
slots each satisfying `O`, from which the encoder's `rep`, the Debug line's `DR` and `NoDrop` follow.
`PInv` now also carries `Kp` (chunks to keep, e.g. the payload's copy at M + 88 / M + 112) and `fr` (the frame
words M + 80 … M + 120 and M + 600 … M + 632 as in μ0). The only hypothesis left is `DebugLineOk` (Fmt).

5042 → 6120 → IntoIter drop (33214) → Debug line 6159 / log 6187 / free 6202 → encoder:
`Encode.Loop.encode_ok` (n ≥ 1) and `encode_zero` (n = 0) with `Encode.Prefix.prefix_small` /
`prefix_zero` → 29087 frees. Compose into a top-level T1 against `Spec.refine`.

### The loop over every milestone kind (`LoopAll.lean`)
`LoopAll.loop_all`: from `PInv 0` to `PInv n` at 5042, each instruction passed through (`PassOk`: an index of
`Pass.PassK`, which includes a `Lookup` with flag 0, sent by its handler 5278 to 5561) or exported (`ExportOk`),
with the chunks to keep `Kp k` and the host context `ctx k` per instruction. `PInv` takes the entry pc: 5042
(the cursor at M + 144) or 5054, where refine's prologue enters the loop past the end test with ω₅ = E (the
cursor word not yet set). `Pass.pa`, `pass_elem`, `pass_elem_grow`, `ExportStep.xhead`, the steps and
`export_step` run from either. Eager `Lookup` and `Import` give `lookedUp` / `imported`, which are not fixed-width,
so the milestone excludes them.

### Refine's body, composed (`Entry.lean`, `Body.lean`)
- `Entry.entry` (4842 … 5054): from the decode's `Vec<Instruction>` `{cap, E, n}` at M + 168, the output
  `Vec::new()`, the `IntoIter`, the constants; `PInv` at 5054 for k = 0 with μ0 the memory there.
- `Body.body` (4842 … refine's return): `entry`, `LoopAll.loop_all`, `ExitRun.exit_run`. The instructions'
  facts (`PassOk` / `ExportOk`) are stated on the memory at 4842 and carried over (`PassOk.congr`,
  `ExportOk.congr`); the result is ℰ(`BootstrapWorkOutput`) at buf with the host context `ctx n`.
- `ExitRun.DebugLineOk` and `exit_run` now keep the host context (Fmt's `refineKeep` gives x' = x).

Left for T1's milestone:
1. Refine before 4842: the arguments, the payload's copy, the first log line (4742, a Fmt site) and
   `Instructions::decode` (31894) with the heap: the decoded `Vec<Instruction>` in an allocated chunk, each
   element's `Rep`, and for `ExportSegs` the `Vec<Vec<u8>>` and segment buffers as allocated chunks (`ExportOk`).
2. From the decoded `Rep`s and `Spec.refineInstr` to `PassOk` / `ExportOk`, the output slots' `O`, the encodings
   `enc` and `EncOk`; `ctx k` as the exports of the first k instructions.
3. The caller's halt and the lift to Ψ_R against `Bridge.RSem.run (Spec.refine …)`.

### `Instructions::decode` in refine (`DecodeTail.lean`, `DecodeVec.lean`, `Decode.lean`), interim n ≤ 70
- `DecodeTail.head` (4792 … 482): refine's reader `{q + 1, Ly − 1}` at M + 272 after `decodeU32_len1` of the
  one-octet length 1 ≤ n < 128, the inlined frame G = M − 136 (158, ω₅, ω₆ saved), the call of
  `Vec<Instruction>::decode` (return 922 → 20420).
- `DecodeVec.vec_one` (482 … 20420), one reserve batch (n ≤ 70): `vec_pre` (frame S = G − 552, `finish_grow`
  `g1x` for 232-octet elements, `alloc_call`, `InvAF` at k = 0 with F = S − 56, `OkF` from the payload's chunk
  being the heap's first), the Vec session's `loopAF_low` (#174), `v3a` / `v3b` (the `Vec` to the output, return).
- `DecodeTail.tail` (20420 … 4842): the salt (`read_big`), `Instructions` at M + 168, return.
- `Decode.decode_one` (4792 … 4842): the three, with each instruction's `ElemOkAF` (frame M − 744, reader M + 272)
  as hypotheses.
Left here: the second batch (70 < n < 128: `finish_grow` with the old buffer, an `InvAF` with an offset).

### Obligations T1's top level must discharge (never assumed by the final theorem)
- The payload's chunk is the heap's first chunk (`Decode.decode_one`'s `hcp`): from the prologue, the payload's
  copy being the first allocation.
- `hlast`, `hbig` (each append's 2·cap, len + n < 2³⁰ − 64) and the writer's capacity, carried by the Vec encoder arms: see `Services/Bootstrap/Encode/README.md`,
  "Obligations left to the top level". Route for `hlast`: refine's heap use is bounded by the payload's length,
  so no used chunk reaches the allocator's 1 GiB top.
- The Fmt sites (`ExportSeg.ExportFmtOk`, `ExitRun.DebugLineOk`, the first log line at 4742), discharged by
  the fmt summaries.

### Fixed-width instructions end to end (`Kinds.lean`, `RunFixed.lean`)
`Kinds.kind_of`: one slot property per milestone fixed-width instruction, shared by its decode (`ElemOkF`) and
encode (`EncOk`). `RunFixed.run_fixed`: refine from 4792 to its return for 1 ≤ n ≤ 70 such instructions
(`decode_one` + `Body.body`), returning n :: ℰ(is) ⌢ ℰ₂(w mod 2^16) with the context unchanged.

### The milestone (`Milestone.lean`, `Top.lean`, `SpecRun.lean`, `MixedKinds.lean`)
`Milestone.refine_milestone`, T1c's first milestone (`docs/bootstrap-target.md` M1): Ψ_R on a work item whose code
is bootstrap (`IsBootstrap`) and whose payload is ℰ(`Instructions { is, salt }`) ⌢ rest, with 1 ≤ |is| < 128
well-formed instructions each passed through (`Kinds.MFixed`) or `ExportSegs`, and |y| + 48 ≤ 2^24: `Spec.refine`
under `RSem` returns (out, ex), and Ψ_R's result and exports are (out, ex), or ∞ with no exports, or the run reaches
a failed allocation (`ExhaustsHeap`). Named hypotheses: `VendoredFacts` (layoutOk and the three read-only tables of
the vendored blob; step 10) and `FmtHyps` (`ArgsLineOk`, `ExportFmtOk`, `DebugLineOk` for `Top.DRm`).
- `Top.refine_core`: pc 0 … 6373 (`ArgsAll.refine_args`, the Vec session's, then `Top.from4680`).
- `Top.from4680`: 4680 … 6373 (`Prologue.tail4680`, `RunMixed.run_mixed` with `MixedKinds.mixed_kinds`).
- `SpecRun`: `run_refine` (`Spec.refine` under `RSem` for these payloads), `expTo_eq`, `output_eq`.
- `Kinds.kindRep`: the slot predicate of each milestone instruction (decoder, encoder and `Debug` share it).
- Not covered: eager `Lookup`, `Import`, `RandomStorageRefine`, the variable-width instructions, n ≥ 128, and
  that an allocation failure ends in ☇ with no exports.

### The second batch (`DecodeVec2.lean`, `DecodeVec2C.lean`)
For 70 < n < 128 `Vec<Instruction>::decode` reserves 70 slots, decodes them, grows the buffer to n with
`finish_grow` on the old buffer (`realloc`, 232-octet slots), and decodes the rest. `w1` (562 … 32989), `g3x`
(`finish_grow` → `realloc`), `v2g` (607 … 680), `v1bG` / `vec_preG` (the first batch of min(n, 70) for any n),
and `DecodeVec2C.vec_twoC` composing them with #182's `loopAFCd_lowF` (the slots' chunks fresh against the
heap at the loop's start, so disjoint across batches) and `loopAFCd_lowFD` (the payload only disjoint from the
batch's slots). `vec_anyC` is `vec_oneC` or `vec_twoC`; `DecodeC.decode_oneC` and `RunMixed.run_mixed` now take
1 ≤ n < 128.

### Refine's return (`Fin.RetTo`)
`RetTo P ret t`: a jump-table return (→ t), or the halt address 2³² − 2¹⁶ with the run stopping at the
`jump_ind` 6373 (`f4h`). `fin_run`, `exit_run`, `body`, `run_fixed`, `run_mixed` take it.

### The prologue (`Prologue.lean`)
`pro1` (4680 … 59375) and `tail4680` (4680 … 4792: `pro1`, then the service id's log line `ArgsLineOk`). The
arguments' parse (pc 0 … 4680, general in the payload, the payload's chunk at the heap's base) is the Vec
session's.

### Export at the top level (`DecodeVecC.lean`, `DecodeC.lean`, `ExportOkOf.lean`, `RunMixed.lean`)
`DecodeC.decode_oneC`: the decode with each instruction an `ElemOkAFC` (#178/#182), returning one `csOf`
(the slots' chunks, pairwise disjoint, none the payload's or the instructions' buffer). `ExportOkOf`:
`ExportOk` from the decoded slot (`export_ok_big` from `VecVecRepC`, `export_ok_empty` for `Export []`), the
context afterwards `expDs` (Ω_E on the segments' octets). `RunMixed.run_mixed`: refine from 4792 to its
return for 1 ≤ n < 128 instructions, each a `FixedKind` passed through or `ExportSegs ds`, the chunks to keep
before k being the payload's and those of instructions k…n−1; output ℰ of `outI` (`Exported |ds|`), the
context `expTo` (segments exported in order). Hypotheses beyond `run_fixed`: ≤ 2²⁶ segments of < 2³⁰ octets per `Export` (`export_elem_bigC`'s bounds). No bound on ς is needed: when Ω_E doesn't return FULL, ω₇ = ς + |e| < 𝖶_X.

### Next
See "Current state" at the top: parts A–E.

### Fmt hypotheses (temporary, "discharged by the fmt summaries")
Parent approved stating these against a `refine_debug_line`-shaped hypothesis, the same pattern as
`FmtOk`. Each must be listed here until discharged:

- **6159**: Debug line of the output instruction list (format 59375), with log 6187 and free 6202: stated as
  `ExitRun.DebugLineOk` (59375 → 6209).
- **5744**: Export's per-segment `format!` (then log 5784, free 5800).
- **5398**: Lookup's `format!` (then log 5428, free 5441).
- **4742**: the service id's log line in refine's prologue (template 66657, the u32 at M + 244 with `Display`
  2616; then log 4770, free 40613 → 4792): stated as `Prologue.ArgsLineOk` (59375 → 4792, keeps x, ω₁, ω₆, Glob,
  the heap's base).

All three take the real frame bound M + 632 ≤ S1. `DebugLineOk` is assumed for `Top.DRm C` (the slot of some
`MFixed`, well-formed instruction, `Kinds.kindRep`) and is given the output slots' chunk.

Fmt's planned `refine_debug_line` covers 6159 → 6209 (format, log, free), from `HeapCtx` with the output
`Vec` words and `DebugRep` slots. Export 5744's layout (from Fmt): template 66196, args at M + 168:
(M + 552, 1250 → `<&Vec<u8> as Debug>`), (M + 560, 692 → `<Result<u64, HostCallError> as Debug>`);
string at M + 584, log target 66793, free via 40613 (ret 186).

The Fmt session was asked to make its Debug proofs parametric with its own per-element
`DebugRep` predicate so these hypotheses can be discharged.

### RSR exclusion (`hrsr`)
Adam decided: T1 is stated for payloads **without** `RandomStorageRefine` (dispatch index 21,
handler 5217). The top-level theorem takes an explicit hypothesis `hrsr` that no input instruction
is `RandomStorageRefine`, and `docs/whats-proven.md` must say so (`docs/bootstrap-target.md` already
does, #149). SmallRng / Xoshiro256++ / 50409 are later, separate work.

## Lessons
- `decide`, not `unfold …; omega`, for membership in concrete multi-way disjunctions (OOM otherwise).
- Prefer targeted rewrites over `post_simp` when `rfl` times out; byte equalities via
  `encodeLE_mod` / `rw [← encodeLE_rdN μ _ 1]`.
- Keep per-case segment lemmas in separate files (`Segs.lean`) to bound elaboration memory.
