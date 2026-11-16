# Bootstrap T1 (refine): handoff

State of the work on bootstrap's `refine` (T1), written for the next session to pick up.
Everything cites Gray Paper v0.8.0 via the docstrings of the files named here; the spec side is
`Spec.refine` and `exportSeg` in `JAM/Refine.lean`.

## Current state (2026-11-16, read this first)

**Eighth instance (2026-11-16, branch `claude/bootstrap-t1c`, on top of m1d).** refine_t1c, in progress.
- Scope (Adam, 2026-11-16): Import excluded by a named hypothesis `hnoimport` (like `hrsr`), recorded as deferred;
  1 ≤ n kept (n = 0 is the existing NoInstr theorem). Both go in the docstring and `docs/whats-proven.md`.
- Done (build, axioms clean): `LoopT.loop_t` (the loop over pass / Export / eager Lookup steps; μ0, `Kp` and the written
  slots' octets `B` carried existentially with a caller's invariant `Inv k μ0 Kp B`; obligations `PassOkT`, `ExportOkT`,
  `LookupOk`; `PInv.mono_O`, `PInv.exact`, `LUSlotB`), `SpecRunT` (`NoImpRsr`, `outT lk`, `rsemLk`, `run_refineT`).
- `LookupStep2.lookup_step` now also exports `ptr' < 2^31` and that the adopted chunk is not `ce` (strengthening only).
- Done too (build, axioms clean): `SlotT` (`slotRep`, `DRt C` ⊇ `Top.DRm C`, `SlotW` = what `exit_runW` needs of one slot,
  `SlotOK` = `SlotW` for every memory keeping the owned chunks as in μr), `SlotFixed` (`kind_okH`, `slotOK_fixed`),
  `SlotLU` (`slotW_lu`, for pass-through `LookedUp` and the eager Lookup's slot).
- **Gas cap.** `lookup_step`'s internal `hgas` (1125 + ⌈264 |d| / 1024⌉ ≤ cap) cannot hold at cap 2^27 for preimages up
  to 2^63 octets; refine_t1c runs under `refineContractK K` with K = 2^62 (any cap works for Ψ_M's lift), so its Fmt
  hypotheses are stated at that cap (report to the parent with the statement).
- **Plan for the rest** (in order):
  1. Per kind (input x, `WF`, `NoImpRsr`), a decode package: `∃ N Rd, (∀ F RD, Lay F RD → ElemOkAFC … N x.encode Rd) ∧
     ∀ cs bs μr, (∀ μ'' agreeing with μr on cs, Rd cs bs μ'') → Step x cs bs μr`, where `Step` is: pass kinds — tag t,
     `PassK t flag`, `SlotOK (x.encode) bs (· ∈ cs) μr`, |x.encode| bound; eager Lookup — the `LookupOk` field facts
     from bs, cs = []; Export — `VecVecRepC` (as `RunMixedG`, via `ExportOkOf.export_ok_big` / `export_ok_empty`).
     Small and big sizes combine `ElemsSmallC` / `ElemsBigC` (and the Decode `*_elem*` lemmas); gaps: an `ElemOkF`
     wrapper for `RandomStorageAccumulate(None)` ([22, 1], `Decode.RandomStorage.random_storage_err`) may be missing.
     The `SlotOK` of each heap kind mirrors `slotW_lu`: rep = the encoder's `…RepAt q` (q the slot's buffer word),
     src = `SrcAtP q m` / `VecVecSrcH`, DR = rep (⊆ `DRt` by the `…Rep_iff` lemmas), drop by `HeapElW`
     (`VVAt` for DeleteItems / Imported, `BufEl` + `ArmOk` for 0, 11, 12, 13, 17, 22, 24).
  2. `Inv k μ0 Kp B` for `loop_t`: μ0 = μ1 (after decode) on ce's data and on the frame words; `Kp cp`; for j ≥ k the
     chunks `csOf j` kept with data as μ1; ∃ ownF, for j < k `SlotOK (outT lk x_j).encode (B j) (ownF j) μ0`, ownF j ⊆
     Kp, ≠ ce, ≠ cp, disjoint from `csOf j'` (j' ≥ k) and between slots, |enc| < 2^33. Steps: pass — Kp' = Kp, ownF k
     = (· ∈ csOf k); Export — Kp' = Kp minus `csOf k`; Lookup — `LUOwn` (ownF k = (· = ch) or none), old `SlotOK`s by
     `SlotOK.congr` (ch apart from kept chunks).
  3. `RunT` (as `RunMixedG`: decode_allC with the packages, `loop_t`, then `exit_runW` with rep/src/own/DR chosen from
     `SlotW` per slot; `hcapB`, `hbig` from n ≤ 2^24 and |enc| < 2^33), `TopT` (as `TopG`), `T1c.refine_t1c` (as
     `Milestone.refine_milestone`, match form, with `SpecRunT.run_refineT` and `rsemLk` = `LookupStep.lookupOf`).

**Seventh instance (2026-11-16, branch `claude/bootstrap-t1-m1d`).** Step 2 (the big `realloc`), approved by the parent
as option (A), in-place edits of Decode/Encode files used only by T1's chain:
- `Decode/ReallocBig.lean` (moved from `Refine/`): `OtherUsed s ptr` (another allocated chunk), `BigReq` (units ≥ 2^25,
  or = 2^25 − 1 with `OtherUsed`: **the gap is closed**, model `growInplace_none_big` / `alloc_none_big` via
  `bin_chunk` and `HeapFrame.Tiles.disjoint`, binary `fallback_entryB`), `realloc_call_big` for `BigReq`, and
  `realloc_call_any` (units < 2^25 − 1 ∨ `BigReq`, in `realloc_call`'s form).
- Changed statements (all weakenings, except the two new `oth` fields):
  - `Decode/GrowOne.grow_one_call`: `hoc : oc ≤ 2^21` → `oc ≤ 2^26`; `g3i`'s `hN : N ≤ 2^22` → `N ≤ 2^27`.
  - `Encode/WriterGrow.extend_grow`, `extend_any`: `hbig : 2·cap < 2^30 − 64 ∧ len + n < 2^30 − 64` → that `∨ OtherUsed s ptr`.
  - `Encode/GrowH.capBound`: 2^28 → 2^60 (every `hlen ≤ capBound` stays, now dischargeable from crude bounds).
  - New fields `BufH.oth` and `LayDH.oth : OtherUsed s ptr` (`BufH.init` takes it; `EncMHLoop` gets it from `LayLMH.arr`).
  - `Refine/DecodeVecNC` (`batch_step`, `batches`, `vec_allC`), `DecodeCG.decode_allC`: `hbig : 232 n < 2^30 − 64` → `< 2^32`.
- Omega pitfall: omega builds an ill-typed proof when it case-splits a hypothesis `… ∨ ∃ …` (e.g. `StackSrc ∨ HeapSrc`
  unfolded). Keep such hypotheses folded (a `def`), or wrap them in `Nonempty`.
  - `Refine/DecodeVec2.g3x`: `hN : 232 N < 2^30 − 64` → `< 2^32`.
  - Refine's n ≤ 2²¹ → n ≤ 2²⁴ everywhere (`PassLoop.LayP.hn`, `Entry`, `Body`, `ExportElem.push`, `ExportStep`,
    `PassGrow`, `LookupStep2.lpush`, `ExitEnc(H)`, `RunMixedG.run_mixedG`, `TopG`): |y| ≤ 2²⁴ gives n < 2²⁴.
  - A full `lake build` passed after the threading; axioms clean (`realloc_call_any`, `grow_one_call`,
    `refine_milestone`, `refine_coreG`).
- Scope (parent, 2026-11-16): refine_t1c keeps 1 ≤ n (n = 0 is not a small lemma: `psiR_noinstr` fixes |y| = 33 and says
  nothing of exports). Import: Adam decides; meanwhile state refine_t1c with an `hnoimport`-style hypothesis (as `hrsr`)
  and do not start Import's handler.

**Handoff (end of the seventh instance).**
- #217 (parts B/C): attempt-1 still running at handoff. Merge it (squash) on green. Then restart
  `claude/bootstrap-t1-m1c` from main, merge `claude/bootstrap-t1-m1d` into it, full `lake build`, and open the m1d PR.
  PR body: the drop arms, encoder arms (22, 17-inline), ElemsSmallC, the big `realloc` (every changed statement listed
  above), the new append-only tier T1C (jump entry 676 and 29153 … 29181; T1B untouched); no new findings. Check first
  that build-items' post_simp PR (≈21 Decode files) doesn't conflict.
- Then refine_t1c (the only remaining step):
  1. `hcapB` / `hbig` in `ExitEncH.enc_runH` / `ExitRunW.exit_runW` are now dischargeable (capBound = 2^60; each output
     element's data lies in a chunk below 2^30 and n ≤ 2²⁴); discharge them where refine_t1c calls `exit_runW`.
  2. `slotRep : Spec.Instr → List UInt8 → Memory → Prop`: `kindRep` for the fixed kinds, `VecEmptyRep` / `VecVecRep` for
     the vector ones, and the decode side's `CreateService{None,Some,Empty}Rep`, `BlessRep`, `AssignRep`,
     `AssignGasRep`, `DesignateRep`, `ProvideInlineRep`, `LookedUpSomeRep`, `RandomStorageOkRep` (Decode/*.lean), with
     the arguments as the decode lemmas instantiate them. `DRt C j bs μ := ∃ x, x.WF C ∧ … ∧ slotRep (outI x) bs μ`;
     the named hypothesis is `DebugLineOk … DRt` (in place of `DRm`, on refine_t1c only).
  3. The loop over pass (fixed and heap kinds) / Export / eager Lookup steps (`loop_all` with a third alternative from
     `LookupStep2.lookup_step`; μ0 / Kp carried existentially), the decode of the heap kinds (`ElemsBigC` / `ElemsSmallC`
     per kind into `decode_allC`), `exit_runW`, and the top as `TopG.refine_coreG` / `Milestone.refine_milestone`.

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

**Handoff (2026-11-16, end of the sixth instance).** Read this first.
- **PR #217** (parts B/C, `claude/bootstrap-t1-m1c` at 69626f5): `model` green, `attempt-1` still running at handoff
  (started 07:14). Subscribe to it, merge (squash) on green. Then restart `claude/bootstrap-t1-m1c` from main and merge
  **`claude/bootstrap-t1-m1d`** into it (pushed, no PR), then open the PR for it.
- m1d = #217 + ReallocBig, ElemsSmallC (fifth instance) + this instance's work below. **A full `lake build` of m1d passed**
  (then `Refine.EncProvide` added and rebuilt, exit 0); axioms clean.
- For the PR body: the new append-only tier **T1C** (jump entry 676 and the arm 29153 … 29181; T1B is untouched, per
  `docs/code-fact-tiers.md`, which forbids adding a range to an existing tier); no new findings (the encoder traps for vector
  lengths ≥ 2^32 at 20397 / 3779 are unreachable from |y| ≤ 2^24).
- Next steps: step 3 (thread `realloc_call_big`), then refine_t1c with `DRm` widened (see "Next" below).

**Progress (2026-11-16, sixth instance; branch `claude/bootstrap-t1-m1d`).** Every file below builds; axioms clean.
- **Drop arms done** (`DropArms`): `ArmOk` (what the drop of an element reads and whether it frees a buffer), the dispatch
  `dd0`/`dd11`/`dd12`/`dd13`/`dd17`/`dd22`/`dd24` and the arms (`aC*` CreateService, `aB*` Bless, `aA*` Assign and
  AssignForGasCost, `aD*` Designate, `aP*` Provide, `aR*` RandomStorageAccumulate), `run_buf`, `drop_buf` (one element
  dropped, as `drop_lu`). **AssignForGasCost (tag 24)** has index 24, past the table's 24 entries: the dispatch's
  `branchLtU 23 < idx` at 29221 goes straight to 29153, the arm it shares with `Assign` (`dd24`).
- **New append-only tier `T1C`** (`Tests/GenWitnessSteps.lean`, range 29153 … 29181, excludes X, R, T1B): jump entry 676
  (index 12 → 29153) and the arm 29153 … 29181, which no tier had. Say so in the PR.
- `DropVecW`: `BufEl` (an `ArmOk` element owning its buffer's chunk), `HeapElW = HeapEl ∨ BufEl` (+ `congr`), `drop_vecW`;
  `FinW.fin_runW`, `ExitRunW.exit_runW`: `fin_runH` / `exit_runH` over `HeapElW` (copies; the H files are unchanged).
- **Encoder arms** (`EncOkMH`) existing in `Encode/`: 0 (`ArmsHVecCS`, None / Some / empty), 5, 11, 12, 13, 18, 19, 24.
  Missing were 22 and 17-inline. **22 done** (`EncRSA`): `rsa_okH(_232)` (`RSAOkRepAt q n hs` → 22 :: 0 :: ℰ(n) ++ hs,
  n < 2^32) and `rsa_errH(_232)` (`RSAErrRep` → [22, 1]); `rsaOkRep_iff` links the decode side's `RandomStorageOkRep`. It
  needed ω₅ = 2^64 − 1 from the dispatch (19894 compares the word at S + 8 with ω₅): `dispatch22` / `startV22` /
  `startVH22` are `dispatchV` / `startV` / `startVH` for index 22. The binary traps at 20397 for n ≥ 2^32 (unreachable:
  |y| ≤ 2^24).
- **17-inline done** (`EncProvide`): `provide_inlineH` (`ProvideInlineRepAt s n q bytes` → 17 :: s ++ 1 :: ℰ(n) ++ bytes,
  n < 2^32, `EncOkMH 232`; `provideInlineRep_iff` links the decode side). The `[u8]` encoder 3716 runs in its own frame at
  F − 96: the `BufH` is carried across it by `BufH.frame`, with `prefix_anyH` / `extendH` at sp' = F − 96, and the arm's
  tail 19074 is `seg_3765` (the helper's return and `encode_to`'s epilogue). The binary traps at 3779 for n ≥ 2^32
  (unreachable). **Every output kind now has its `EncOkMH` arm.**
- **Next**, in order: step 3 (thread `realloc_call_big` into decode's `finish_grow`, `grow_one` and the writer's growth;
  close units = 2^25 − 1), then refine_t1c, with `DRm` widened there (define it from the slot predicates, the `rep j` of
  each output kind, as a named Fmt hypothesis `DebugLineOk … DRt`).

**Handoff (2026-11-16, end of the fifth instance).** Read this first.
- **PR #217** (parts B/C, branch `claude/bootstrap-t1-m1c` at 69626f5): `model` green, `attempt-1` still running at
  handoff. Merge it (squash) on green (the parent approved). Then restart `claude/bootstrap-t1-m1c` from main and bring
  in the work on **`claude/bootstrap-t1-m1d`** (pushed, no PR; it is 69626f5 plus the commits below), e.g. merge it.
- On m1d, beyond #217 (every file builds with `lake env lean`; axioms clean; a full `lake build` not yet run on it):
  `Refine/ReallocBig.lean` (`realloc_call_big`, see "ReallocBig done" below) and `Refine/ElemsSmallC.lean` (the 8 small
  `C` adapters), both imported in `Services.lean`; README updates.
- Order approved by the parent (2026-11-16): ReallocBig (done but for units = 2^25 − 1 and threading it into T1's
  callers, below), the small `C` forms (done), then the drop / `EncOkMH` arms for kinds 0, 11, 12, 13, 17, 22, 24 (tier
  T1B range; if an arm needs code facts outside it, add them to T1B append-only and say so in the PR) with `DRm`
  widened, all as new Refine files, then refine_t1c.
- Next steps, in order:
  1. Drop arms (see "Drop arms still to do" below; template `DropOutL`: `dd*` dispatch, the zero / nonzero pieces,
     `drop_*` with `dealloc_call`), then extend `DropVecH.HeapEl` with them (a new predicate per buffer layout) and
     re-run `drop_vecH` / `fin_runH` / `exit_runH` over the wider `HeapEl` (new files, as the parent asked).
  2. `EncOkMH` arms for those kinds (`Encode/`'s heap arms, as `delete_itemsH_232` / `looked_up_someH`) and the
     wider `DRm` (`ExitRun.DebugLineOk`'s slot predicate) with the formatters listed below.
  3. Thread `realloc_call_big` beside `realloc_call` into decode's `finish_grow`, `grow_one` and the writer's growth,
     and close units = 2^25 − 1; then n ≤ 2²¹, `hbig`, `hcapB` and `capBound` can go.
  4. refine_t1c: the loop's induction carries μ0 / `Kp` existentially (`lookup_step` rebases them, `LUOwn`).

**Progress (2026-11-16, fifth instance; branch `claude/bootstrap-t1-m1c`).** Main (#214) merged in. Every file below builds
with `lake env lean`; axioms clean.
- `LookupStep2.lookup_step`: the whole eager `Lookup` step, `PInv k` at i → `PInv (k + 1)` at 5042: `lmid`, then `lfmt`
  (5372 → 5448: `LookupFmtOk`, log, `String` freed), `lpush` (5448 → 4046: `LookedUp(result)` pushed, with room or
  `grow_one`), `Lookup.ldrop` (→ 5042). Slot k satisfies `LUSlot` (so `O k` via `hO`); `LUOwn` says what happens to μ0 and
  `Kp`: unchanged for `None` and `Some []` (buffer 1), else the preimage's chunk is adopted (`PInv.adopt`, μ0 rebased by
  `snapWith`). Named hypotheses: `LookupFmtOk` and `htab` (`(ro.drop 32).take 4 = dropEntry8`, part of `VendoredFactsC`);
  the step also takes `rtab` (65568 … 65572 readable at its start). Internal: `hlen`, `hgas`.
- `ElemsBigC`: the 8 `*_elem_bigC` (`import`, `bless`, `random_storage_ok`, `designate`, `looked_up_some`,
  `provide_inline`, `create_service_some`, `assign_gas`): `ElemsBig.*_elem_big` as `ElemOkAFC`, the slot's buffer word
  naming a returned chunk that holds the buffer (`OwnsBuf cs bs off m`: off 16, except `provide_inline` 24 and
  `create_service_some` 8). These cover only the large sizes (> 1024 pairs / > 512 hashes / > 48 keys / > 16384 octets);
  the small adapters are in `ElemsSmallC` (`bless_elemC`, `random_storage_ok_elemC`, `designate_elemC`,
  `looked_up_some_elemC`, `provide_inline_elemC`, `create_service_some_elemC`, `assign_gas_elemFC`, `assign_elemFC`;
  same `OwnsBuf` offsets). `import_elem` (part D's input, not an output) has no `C` form yet.
- **Drop arms still to do** (from the disassembly and the table at 67760; each mirrors `DropOutL`: the element at the
  frame word sp + 48, a capacity test, `dealloc(ptr, cap·size, align)` returning via jump entry 1356 → 29181, else
  straight to 29181). Index → jump entry → arm:
  0 (CreateService) → 687 → 29581: cap = ω₈ (the discriminant word; 2^64 − 1 = `None`, 0 = empty → 29181), ptr at +8,
  align 1. 11 (Bless; also 9, Import) → 678 → 29241: cap at +8 (0 → 29181), ptr at +16, size 16·cap, align 8.
  12 (Assign) → 676 → 29153 (below T1B's range, in `Code`). 13 (Designate) → 688 → 29609: cap at +8, ptr at +16,
  336·cap, align 1. 17 (Provide) → 681 → 29338: the octet at +8 (0 = by hash → 29181), cap at +16, ptr at +24,
  align 1. 22 (RandomStorageAccumulate) → 689 → 29640: cap at +8 (2^64 − 1 = `Err`, 0 → 29181), else → 29162 (12's
  arm's tail, in `Code`). AssignForGasCost (tag 24) is not among the table's 24 indices: check its dispatch index.
- Still open for part B: the output drop arms of the other heap kinds (indices 0, 11, 12, 13, 17, 22, 24; `DropOut.NoDrop`
  excludes them and `HeapEl` covers only 5, 18, 19), the encoder arms `EncOkMH` and `DRm` for them.
- **Debug field formatters the new kinds reach** (for the field-formatter session; from `Fmt/README.md`'s arm table): the
  output kinds refine_t1c adds are tags 0, 5, 11, 12, 13, 17, 18, 19, 22, 24. Beyond the milestone's formatters (28822,
  28843, 37549, 56340) they reach **315, 26397, 26605, 26905, 28739, 28801, 29877, 36534, 36594, 36654, 36732, 37611,
  57485**, through the builders/tails 63820 (tag 0), 28576 (5, 13, 18), 63570 (11), 27665 (12), 28280 (17), 62816 (19),
  62471 (22) and 28458 (24). Not needed: 26706 (tag 9, `Import`, never an output) and 36972 (tag 21, RSR, excluded).

**ReallocBig plan (fifth instance, from the disassembly).** Goal: `realloc_call`'s null outcome for
2^25 − 1 ≤ units, so n ≤ 2²¹, `hbig` and `capBound` can go. The wrapper 40701: size > 2^37 − 32 → ω₇ = 0 and return at
40724 (no lock). Otherwise lock (as `alloc_call`), units = (size + 31) >> 5 passed through `add_imm_32` (sign-extended:
units ≥ 2^31 arrive as 2^64 − 2^32 + units), `realloc_impl` 42980, unlock, 40821. In 42980 for units req ≥ 2^25 − 1:
- 42996 cur = header(ptr − 32).size >> 1; req ≠ cur − 1, req ≠ 0; 43023 req ≥ cur − 1 (unsigned) → grow path 43169.
- 43169: req = 2^64 − 1 (units 2^32 − 1) → fallback 43259. Otherwise ω₅ = req + 1 (32-bit, sign-extended), cur < ω₅;
  next = chunk + 32·cur (32-bit add): next ≥ heap top + 2^30 → 43259; next used → 43259; next free and
  cur + next.size < req + 1 (always: the heap has < 2^25 units) → 43259. The merge path 43375 (with `ecalli 1`) is
  never reached.
- 43259: `alloc_impl` 41177 (ω₈ = align, ω₉ = req, ω₁₀ = 0) returns null for these sizes (`Decode/AllocHuge`'s
  `alloc_impl_huge_callG`, both units < 2^31 and ≥ 2^31, as `LookupWrap.wl` / `wlh` use) → 43326: ω₇ = 0, return to
  40805 → unlock → 40821.
- Model side: check `realloc (growTo pb)` is `none` for these units (heap 2^30 octets).
New file `Refine/ReallocBig.lean`; the Alloc files are not changed (their `hr1` stays).

**ReallocBig done for 2^25 ≤ units < 2^31 − 1** (sizes < 2^36 − 32; every T1 request stays below 2^31 units, since
232·(2n + 4) octets for n ≤ 2^24 is about 2.4·10^8 units). `ReallocBig.realloc_call_big` (and `…G`): the model's
`realloc` is `none` (`growInplace_none_big`, `alloc_none_big`) and the binary returns null at 40821 with `HeapCtx` for
the same state, stack and globals kept. Proof: copies of `Alloc.fallback_pre` / `fallback_entryG` /
`fallback_refines_failG` with req < 2^31 − 1 (all their 32-bit arithmetic needs; the grow-heap branch is impossible for
req ≥ 2^25) and the fallback's general alloc tail (`fallback_tail_failG`, no size bound), inside `rw_lock` / `rw_unlock`.
- Tried and reverted: weakening `hr1` in the Alloc files in place to req < 2^31 − 1 fails in `ReallocGrowImpl` (the
  in-place merge's success path) at req = 2^25 − 1.
- **Gap: units = 2^25 − 1 exactly** (sizes 2^30 − 63 … 2^30 − 32) is covered by neither `realloc_call` (units < 2^25 − 1)
  nor `realloc_call_big`. There the merge with the next free chunk can only succeed when the chunk and its neighbour
  span the whole heap. To close it: either a case lemma for that value, or keep requests off it internally (232-octet
  multiples never land on it; the encoder's writer growth needs a check).
- Next: thread `realloc_call` ∨ `realloc_call_big` through `ReallocCall.realloc_call`'s users in T1 (decode's
  `finish_grow`, `grow_one`, the encoder's writer growth) so n ≤ 2²¹, `hbig` and `capBound` can go.

**Handoff (2026-11-16, end of the fourth instance; branch `claude/bootstrap-t1-m1c`, pushed, no PR yet).** Every file
below builds; axioms clean. #214 (part A) was still in attempt-1 at handoff (`model` green): merge it on green, then merge
main into this branch before opening its PR. A full `lake build` of this branch was started but not finished (the cache
from main@dd373c2 predates #201, so everything rebuilds cold); run it before the PR.
- Changed existing files (all T1's): `DropOut.dh` also exports n at the frame base; `DropOutH.items_loop` also keeps pages
  and read-only bytes; **`PInv` has a new field `c8`** (M + 8 = 2^63 + 17, `LookedUp`'s discriminant, which `Lookup.lps`
  reads), exported by `Entry.e2` and kept by `PassLoop` / `ExportElem` / `LoopAll` / `PInvAdopt`.
- `DropOutH.drop_vv`: one `DeleteItems` / `Imported` element dropped (29188 → 29181).
- `DropOutL`: `LookedUp`'s arm (index 18, jump entry 682 → 29376, tier T1B; `None` = cap 2^64 − 1): `ddL`, `lo0`, `lo1`,
  `drop_lu`.
- `DropVecH`: `VVAt`, `LUAt`, `HeapEl` (+ `congr`); `drop_vecH` (29087 → ret, elements `NoDrop` or `HeapEl`).
- `FinH.fin_runH`: the epilogue with `drop_vecH`.
- `ExitEncH.enc_runH`: the encoder via `encode_okMH_big`. Internal hypotheses, never in refine_t1c's statement: `hcapB`
  (232 n + 6 ≤ 2^28) and `hbig` (twice the output ≤ 2^28) until ReallocBig; the growth encoder's `FrH` also needs
  `2147484384 ≤ M` (LayP has 2147484104) and `S1 + 16 < 2^32`: both true of refine's real stack, to discharge where
  `LayP` is.
- `ExitRunH.exit_runH`: refine's exit (5042 → ret) with heap elements (slots at the end state, output buffer Eo; `rep` /
  `DR` depend on memory only through `src` in kept chunks; owned chunks kept, `Kp`, not `ce`).
- `PInvAdopt.PInv.adopt`: a fresh allocated chunk joins the kept chunks, rebasing μ0 on its data (`snapWith`).
- `LookupStep.lhead` (i → 5288: stage, `ld`), `lookupOf` (Ω_H's 𝐯 for service svc and hash h), `lmid` (i → 5372: `la`,
  `lookup_wrap`; result `ResAt μ' (M + 560) (lookupOf env svc h) s s'`; internal `hlen` (Adam's pending decision) and
  `hgas`).
- **Next, the second half of the Lookup step** (5372 → 5042, a new file `LookupStep2.lean` or appended): `Lookup.lf`
  (5372 → 59375) → `LookupFmt.LookupFmtOk` (needs `OptVecAt μ (M + 560)` from `ResAt`: `None` is the first disjunct;
  `Some d` gives cap = len = |d| < 2^63 and the buffer readable: chunk data, or buf = 1 with len 0) → `Lookup.ll` →
  `lfr` + `Decode.DeallocCall.dealloc_call` (return 174 → 5448) or `lfz` → `lp0` (room) or `lpg` +
  `Decode.GrowOne.grow_one_call` (return 176 → 5493; see `PassGrow` / `ExportElem.push` for the pattern) → `lps` (slot k
  = {2^63 + 17 from `st.c8`, the result's three words}) → `ldrop` (needs `dropEntry8` at 65568, from `VendoredFactsC`)
  → `PInv (k + 1)` at 5042 with O k for the `LookedUp` slot; for `Some d` with d ≠ [] apply `PInv.adopt` to its chunk
  (fresh: `ResAt`'s `∀ e ∈ chunks s, e ≠ c` gives ≠ ce, ∉ Kp, ≠ the output buffer). Then the 8 `*_elem_bigC` lemmas,
  ReallocBig, refine_t1c (the loop's induction must carry μ0 / Kp existentially, since Lookup steps rebase them).
- The pass-through heap kinds need no `PInv` change: their chunks come from the decoder, so they are `Kp` chunks with
  data as in μ0, and `HeapEl` at the loop's end follows by `VVAt.congr`.
- Debug field formatters the new kinds reach: not yet determined (the widened `DRm` is still to be written; candidates
  as listed in the third instance's handoff).

**Handoff (2026-11-16, end of the third instance; branch `claude/bootstrap-t1-m1c`, pushed, no PR yet):**
- The branch is `claude/bootstrap-t1-m1-wip` (#214) plus main merged plus parts C/B below. #214 (part A) was still in
  CI (attempt-1) at handoff: merge it on green (brief), then rebase or merge main into this branch before opening its PR.
- Open decision with Adam (via the coordinator): whether refine_t1c assumes looked-up preimages < 2^63 octets
  (recommended (a)). Approved: `VendoredFactsC` (the 4046 table), tier T1B, the gas cap as an internal choice (it must
  not surface in refine_t1c's statement).
- All new files build locally (`lake build Services.Bootstrap.Refine.LookupRun Services.Bootstrap.Refine.LookupFmt
  Services.Bootstrap.Refine.DropOutH`, `CodeT1BAll`, `CodeT1BOk`); axioms checked for `lookup_wrap`. A full `lake build`
  has not been run on this branch yet.
- When a PR goes up: add the binary-vs-spec note for preimages ≥ 2^63 octets (the wrapper traps; `Spec.refine` returns
  `lookedUp (some d)`) to `docs/upstream-candidates.md` and the PR body.
- Order still to do: `drop_vv`, `drop_vecH`, `exit_runH`, `PInv` with slot-owned chunks and the Lookup step, the 8
  `*_elem_bigC` lemmas (new files, mirroring `vecvec_elem_bigC`), ReallocBig, refine_t1c. When `DRm` is widened, list
  here which Debug field formatters the new kinds reach (candidates 315, 26397, 26605, 26706, 26905, 28739, 28801, 29877,
  36534, 36594, 36654, 36732, 36972, 37611).

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
  `bootstrapSvc` after `fnRangesR`: `tiers := [{ name := "T1B", ranges := [(29181, 29675)], excludes := ["X", "R"], doc
  := "refine's output drop (drop_in_place::<[Instruction]>): the heap variants' drop arms" }]`). Drop arms: jump entries
  679 → 29270 (DeleteItems, 5), 685 → 29476 (Imported, 19); the drop table at 67760 maps index t to entry
  (67760 + offset_t)/2 − 1. The encoder with growth needs H arms for every fixed kind (`ArmsHFixed` etc.). `LayLMH`
  needs cap = 232n + 6 ≤ capBound (2^28), i.e. n ≲ 1.157M internally until ReallocBig.

**Progress on B (2026-11-16, third instance):**
- Tier T1B generated and kernel-checked (`CodeT1B*`, range (29181, 29675); the previous note's 29176 starts inside the
  instruction at 29175 and gave a false fact).
- `DropOutH`: the drop arms of `DeleteItems` (5, arm 29270) and `Imported` (19, arm 29476), straight-line: `ddV`
  (dispatch 29188 → arm; table entries 1360 / 1372), `va` / `va0` (items or none), `vz` + `vn` = `vi0` (an item of
  capacity 0, on to the next), `vi1` (an item's `dealloc(q, c, 1)`, return 1362 → 29336 / 1374 → 29540), `vb` (after
  it), `vo0` / `vo1` (the outer buffer, `dealloc(ptr, 24·cap, 8)`, return 1356 → 29181). All build.
- `DropOutH.items_loop`: the item loop (head → 29542) by induction, each nonzero item freed by
  `Decode.DeallocCall.dealloc_call` (any host relation); proved.
- Next for B: `drop_vv` (one heap element, 29188 → 29181: `ddV`, then `va` + `items_loop` or `va0`, then `vo0` or
  `vo1` + `dealloc_call` of the outer buffer (return 1356 → 29181: `jte_677`, `bs_29181` are in `Code`)), then `drop_vecH` (the whole output drop with the
  heap context, `NoDrop` elements by `DropOut.dd`), then `exit_runH` (encoder with growth via
  `Encode.EncMHLoop.encode_okMH_big` and the arms `delete_itemsH_232` / `importedH_232` / `looked_up_someH`, the wider
  `DRm`, `drop_vecH`), then `PInv` carrying chunks owned by output slots (for Lookup), then refine_t1c.
- pvm_go pitfall: a piece whose start pc equals its target (a loop head reached again) can stop at once; split it
  (`vi0` = `vz` + `vn`). Negative offsets: read as `w + 2^64 − 8` and convert as in `Export.xr1`.

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
