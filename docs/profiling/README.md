# Build profiling data

These are the raw data for the build-profiling proposal (task 3 in `docs/BUILD-INFRA.md`).

- `build-times.tsv` holds the per-module build time from a cold local `lake build`, with the sources
  at #193's head (14a2f1d). The machine had 4 cores and 15 GB, and Lake ran up to 4 modules at once.
  Each time is therefore that module's wall time while sharing the machine; the times are not
  independent CPU costs.
  - It covers all 1305 library modules, 18.1 h of serial time. The 35 test executables and scripts
    (`Tests.*`, `scripts.CheckAxioms`) are not in the default target and are missing.
  - The machine ran out of memory once: `Services.Bootstrap.Refine.ArgsCtx` was killed while sharing
    the machine, so its time (417 s) and its two dependents' come from a second `lake build` run
    afterwards.
  - Modules that the first command built (the four largest Witness proofs) carry job numbers from
    that command's own counter.
- `scripts/import-graph.py docs/profiling/build-times.tsv` prints, for each module:
  - how many modules depend on it, directly or transitively;
  - their total build time, which is what a change to the module costs in rebuilding;
  - the slowest modules.
