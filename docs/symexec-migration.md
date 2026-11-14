# Generated chains on the symbolic executor

The generated cut chains of `Services/Bootstrap` (`lake exe genwitnesssteps … cut … frame`) are
proved in part by the symbolic executor (`PVM/SymExec`, `docs/symexec-spike.md`) instead of one
`pvm_simp` proof per step. `scripts/gen_exec_chain.py` does the conversion, right after
`genwitnesssteps` has written a chain:

```
lake exe genwitnesssteps --service bootstrap cut0 35202 BTail1 0 1003 every=16 frame
scripts/gen_exec_chain.py Services/Bootstrap/BTail1
```

## What the converter does

For a chain `<C>` (the directory `<C>/` with `St.lean`, `S0.lean` … and the composition `<C>.lean`):

* Every maximal run of segments `S_b … S_{e-1}` that the executor follows becomes files
  `<C>/E<b>.lean`, each with one `run` theorem whose statement is exactly that of the composed
  `S_b.run … S_{e-1}.run`: `St_b → ∃ ω' μ', FreeStepsH … ∧ St_e`. Inside, the cut states (the
  generated `St_k`) become `Cut` data every 16 segments, and each piece is one `seg_sound` line
  checked by `decide +kernel`. Bridges convert `St_b` into the first cut (with the chain's start
  memory as the cut's base) and the last cut back into `St_e`, using `St_b`'s frame and page facts.
  A file holds at most 4 checks (`maxchecks=`), so files build in parallel.
* Segments the executor cannot follow stay as generated: host calls, segments stepping a pc
  listed in `nopc=` (default: 60553, the hex-digit table read), and those listed in `keep=`.
  Cuts are placed only at states it can encode (named naturals and literals); a state with, say,
  `ω[9] = UInt64.ofNat (S / 256)` is skipped as a cut point.
* `<C>.lean` composes the `E` and kept `S` runs. Only its imports and the body of `chain` change;
  `chain`, `run` and every other statement are unchanged. `prefix=n` also states the composition up
  to cut `n` (`prefix<n>`), for files that extend the chain.
* `<C>/St.lean` keeps only the states the composition names, and those named by files importing the
  chain. All frame conditions `C_i` stay.
* The page facts of the states (`rdq`, `wrq`, and the heap fields `hhp`, `rdA`, `rdm`, `wrm`) carry
  over from `St_b` to `St_e`: the executor keeps μ's pages.
* The replaced `S<i>.lean` are deleted.

Refine chains use the code table `Services.Bootstrap.SymExec.prog`; accumulate chains
(`accContract`) use `progAll`, which also holds the facts of `CodeX` and `CodeA`.

## Migrated chains

Lean time per module summed over the family (4 cores, `lake build`; before: the generated
`St`/`S*` files, after: `St`, `E*`, kept `S*` and the composition):

| Family | Segments | Kept as generated | Before (s) | After (s) |
|---|---|---|---|---|
| BTail1 … BTail8 | 63 … 71 | host call; hex-digit loop (2–6 segments) | ≈ 4430 | ≈ 670 |
| BParams | 177 | S174–S176 (extended by `BParamsConsts`) | ≈ 1330 | ≈ 90 |
| AccBParams | 177 | — (S176 until `progAll`) | ≈ 1440 | ≈ 100 |
| OTail | 100 | host call; S87–S99 (states not encodable) | ≈ 800 | ≈ 180 |
| GlueY | 20 | — | ≈ 170 | ≈ 12 |
| VTail1 … VTail8 | 70 … 83 | host calls; hex-digit loop (1–6 segments) | ≈ 5740 | ≈ 865 |
| PrefixC | 38 | 4 host calls | ≈ 500 | ≈ 180 |
| Witness ErrTail | — | host call | 687 | ≈ 40 |
| Witness EmptyTail | — | host call | 615 | ≈ 38 |
| Witness PrefixC | — | 4 host calls | 578 | ≈ 130 |

The code tables are built once: `Prog` ≈ 140 s, `ProgAll` more, the witness `Prog` ≈ 38 s.
Witness chains use `prog=Services.Witness.SymExec.Prog,Services.Witness.SymExec.hyp`; they were
generated without `frame`, so the converter takes all of ℕ_{2^32} as each cut's frame. AccPrefixC
is converted too (on `progAll`).

## Not migrated yet (handoff, 2026-11-14)

The parent session paused these: the remaining gains are small. In order of value:

1. **Phase 2 features (#156, on main).** The executor now follows the hex-digit table read at a
   symbolic index and `log` host calls; #164 (stacked on #156) adds `fetch` kind 0.
   * Drop the default `nopc=60553` so BTail/VTail S35–S40 convert.
   * Convert the kept host-call segments: build the table as
     `{ prog with hosts := .node (.node .leaf 2 [fetch0Eff …] .leaf) 100 [logEff] .leaf }` (or
     `logHosts`), a search tree keyed by host-call id, and pass `hH : HostOk R G.hosts` to
     `seg_sound` (its last argument, default `trivial`). Example: `prefixC2_ok` in
     `Services/Bootstrap/SymExec/Hosts.lean`. `fetch0Eff` takes the literal ω₇/ω₈/ω₉ at the call
     (`traceRun` / `traceCheck` print them).
   * `HeapPages` is not part of `Cut.Holds`: derive it in the bridge from `μ'.pages = μ.pages`.
   * `grow_heap` is not supported by the executor.
2. **OTail S87–S99**: states with byte-split cells (`I % 256`, `I / 256`). Converter work only:
   emit `.mod (.var k) 256` and `mkMod (.alu2i .shloRImm64 (.const 0) (.var k) 8) 256` for them.
3. **Witness Front3, Front4, EFront3**: states with derived values (Y + 32, Y − 1, a sign extension
   of S) and the extra field `uk`. Converter work only: `.addr ⟨some k, off⟩` and `.sx 4 (.var k)`.
4. **GlueY2** (3 segments): not worth it.

Each converter change must keep CI's generated-files check: the `python3 scripts/gen_exec_chain.py`
line after each chain's `genwitnesssteps` line in `.github/workflows/ci.yml` must reproduce the
committed files exactly.
