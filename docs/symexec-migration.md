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

The code tables are built once: `Prog` ≈ 140 s, `ProgAll` more.

## Not migrated yet

* `AccPrefixC`: it runs accumulate code, so it needs `progAll`.
* `GlueY2` (3 segments).
* The `Services/Witness` chains: they need a code table of the witness binary.
* Phase 2 of the executor: the hex-digit table read at a symbolic index (pc 60553, BTail and VTail
  S35–S40).
