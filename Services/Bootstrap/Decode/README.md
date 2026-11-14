# Decode: handoff note (paused 2026-11-14 for the account move)

This note is the handoff for the Decode/Encode child session (refine args, vector decoders, encoder).

## Done (on main)

| PR | What it adds |
|---|---|
| #172 | EncM, PrefixBig |
| #173 | Fmt/ReallocCopy* |
| #174 | Decode/LoopAPassLow |
| #175 | EncMD, VecCore, VecSegs*, VariantsVec*, HeapPad, VecSrcHeap, Encode/README.md |
| #177 | VariantsVec2*, VariantsVec3* |
| #183 | Writer growth (WriterGrow*, GrowH, PrefixH, EncMH*, ArmsH*); Encode/README.md obligations 1–4 |
| #167 | GasFreeId for ids 7 and 8 |
| #185 | The refine argument parse, pc 0 → 4680 (Alloc/AfterStart, StartMemZ, BParamsHdr, AllocStart, Decode/VecU8Args*, Refine/Args*) |
| #178 | Decode/VecVecOwn: VecVecRepC, ElemOkAFC, vecvec_elem_bigC, export_elem_bigC |
| #169 | Decode/AllocHuge: alloc_impl_huge_callG |

## In flight

- **PR #182** (branch `claude/loopafc`, head b78653d, main merged in): Decode/LoopAPassC (InvAFC, InvAFCd, loopAFCd_lowF/FD, OkFD) and Decode/ExportEmpty.
  - Its CI has been running since 10:27 and was still running at the pause.
  - When it's green, merge it. If it times out, re-run it once; the cache resumes.
- **Branch `claude/decode-heaphost`** (no PR): the HeapHost generalisation of Decode, core layer.
  - **Not verified to build.** The background build was stopped at the pause.
  - Edited files: LoopA, LoopAPass, LoopAPassLow, LoopAPassC, VecVecOwn.
  - Convention: a `G` suffix taking `{X} (env : HeapHost X)`, e.g. `ExhaustsG`, `ElemOkAFG`, `heap_writable_dataG`. Every refine name is kept, as an abbrev or instance, with its statement unchanged, plus `_iff` bridges (`Exhausts_iff`, `ElemOkAF_iff`).
  - Next: build `Services.Bootstrap.Decode.LoopAPassC` and `.VecVecOwn`, fix any errors, then check that every dependent of these modules builds unchanged.
  - **Merge rule (from the parent):** don't merge this branch until #182 and T1's milestone PR are on main. The PR body must say that no statement changed, and list every name whose elaborated type changed, even if it's definitionally equal.

## Next steps, in order

1. Finish the core layer above.
2. **Element-file layer**, the same pattern: ElemsBig, VariantsBig*, VecU8Heap*, VecPairs*, VecHash*, VecKey336*, CreateServiceHeap, BlessHeap, DesignateHeap, AssignGas, LookupProvideElem, and so on.
3. **Encode primitives to HeapHost** (decided by the parent, option (a)), in this order. These are the names promised to T2 Handlers A (session_017ptjPAYQLcfsxukAeywyqn):
   1. `ExhaustsWG`, `ExhaustsWG.pre` / `.mono`, `ExhaustsG.toW`; `BufHG` and its lemmas; `extend_growG`, `extend_anyG`, `extendHG`; `StHG`, `StDHG`, `ext_stepHG`, `ext_stepDHG`, `scratchDHG`, `heapDHG`.
   2. `prefixHG`, `prefixDHG`.
   3. `EncOkMHG`, `LayDHG`, `encode_okMH_bigG`.
4. **Accumulate's output decode at 7073** (BootstrapWorkOutput::decode, via 22145):
   - Entry: ω1 = sp − 72, ω5 = out = sp + 1568, ω6 = ω7 = rd = sp + 1144, ret 238 → 7080.
   - Success exits at 7091 with {cap, ptr, len} at sp + 1568 and k (u16) at sp + 1592.
   - Error: −1 at sp + 1568, then 7080 → 7088 → 15361 (panic).
   - Pieces: 22145 → 482 (ret 1028, out S + 576); 22168 → read_exact 58434 for 2 octets (ret 1030); 22213 → 22282 success.
   - Needs:
     - a generic 482 wrapper, with ret and out as parameters, using OkFD in place of vec_anyC's `hcp : cp.addr = s.base`;
     - an n = 0 lemma for 482 → 825;
     - CodeA glue segments.
   - Interface T2 wants: HeapHost-generic (env.rel cap, cap ≥ 2^27); HeapCtxC in and out, with used chunks kept with their data; the caller frame from sp up kept except the out slots; o a slice in a used chunk. Outcomes: success with refine's Reps plus k (the Vec's chunk fresh), or Exhausts.

## Open obligations (deliberately not proved; list them in the PR and here)

- **The decode-error outcome.** Wanted shape (T2), one-sided: spec `decode … = none` ⇒ the binary reaches 15361 or Exhausts. T2 keeps a local premise on its operand-arm lemma, marked as a TODO ("output decode failure contract"). It must not go into T2's stated theorem.
- **Inherited limits:** n < 128, and the Spec.Instr → ElemOkAFC map.

## Facts settled for others

- **36299** (accumulate's result encoder) jumps through a relative i32 table in RO data at 68264. Mapped through djump, tags 0–6 go to jump-table entries 711, 719, 714, 715, 712, 722 and 725, i.e. targets 30374, 30512, 30433, 30438, 30392, 30567 and 30640.
  - This was checked by parsing `services/bootstrap/jam-bootstrap-service.jam` against the `jte_*` facts.
  - Entries 843 and 844 belong to CreateService's Option<u32> decoder.
  - T2 needs RO-data code facts for 68264 … 68291 from T1.

## Waiting on

- T1's milestone PR (merge gate).
- Arm 17 Inline: after T1's #179 (code facts for 3716–3790).
