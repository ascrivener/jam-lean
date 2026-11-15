# P3: module-system spike (Lean v4.36.0-rc1)

The throwaway branch is `claude/p3-module-spike`. Nothing from it is meant for `main`.

## Question

When a file uses the module system, can an edit that only changes a proof skip rebuilding the modules
downstream of it? And what breaks for `decide`, `simp` unfolding and reflection?

## What was done

1. **A toy Lake project** (modules A → B, plus a non-module C), used to establish the rules.
2. **A real closure.** `Services/Bootstrap/Alloc/Arith` and its whole import closure were converted:
   37 files, mostly PVM core, the Picoalloc model and `Alloc/Rep`.
   - Each file got `module`, `public import` and `@[expose] public section`, applied by a script.
   - One manual fix: the simprocs in `PVM/Logic/Steps.lean` need `public meta import` (of
     `PVM.Basic`, `PVM.Exec`, `PVM.Logic.Bits` and Lean's Nat simprocs), and their helpers
     `evalNatFn2`/`evalNatFn3` must be `meta def`.
3. **Reflection.** 20 more files (JAM core, `PVM.SymExec.*`, `Services.Bootstrap.Code`) were converted so
   that `Services/Bootstrap/SymExec/FixedZ` could build. It uses SymExec's `check_sound` by kernel
   reflection. No manual fixes were needed.

## Results

| Edit upstream | Rebuilt downstream |
|---|---|
| A tactic proof's body, axioms unchanged (`Alloc/Rep`, `PVM/Memory`, `PVM/SymExec/Sound`) | **nothing**: only the edited module (0 of about 30–50 dependents; a new public lemma in `PVM/Memory` rebuilt 31) |
| A new `private theorem` | nothing |
| A proof edit that changes the axioms the theorem uses (e.g. `simp` ↔ `omega`, gaining or losing `Quot.sound`) | everything downstream: the axiom set is part of the public `.olean` |
| A new public lemma, or a changed statement or definition body | everything downstream (expected) |
| Any edit, where the importer is **not** a `module` | the importer always rebuilds |
| Any edit, where the importer uses `import all` | the importer always rebuilds |

## Risks and constraints

- **Bottom-up only.** A `module` file cannot import a non-module file ("cannot import non-`module` …
  from `module`"). Converting a file means converting its whole import closure first. A rebuild is skipped
  only across an edge where both ends are modules. So the gain comes from converting large parts of the
  tree, starting at the bottom (PVM, JAM) and moving up.
- **Opaque definitions by default.** Without `@[expose]`, a definition's body is invisible downstream.
  In the toy project `decide`, `rfl`, `unfold` and `simp [d]` all fail on such definitions. The spike
  used `@[expose] public section` everywhere, which keeps every definition transparent, as today, and
  hides only proofs. With that:
  - `decide`, `simp` unfolding, the existing `by decide` proofs, the `check_sound` reflection in
    `FixedZ` and the code facts in `Code` all built unchanged;
  - the price is that editing a definition's body still rebuilds dependents, which is unavoidable for
    reflection anyway.
  - Narrowing `@[expose]` later is possible module by module, but every kernel computation
    (`checkCode`, `check`, generated `facts_k`) needs the definitions it unfolds to be exposed.
- **Meta code.** Simprocs, elaborators and macros need `meta import` and `meta def` helpers. Steps
  was the only such case in 57 files. More will turn up in tactic-heavy files: `PVM/Logic/Attr`,
  `Services/*/Tac`, the SymExec tactics and the Fmt tactic.
- **Generators.** The generated files (code facts, cut chains, `gen_exec_chain.py` output) would
  need their headers changed in the generators, and CI's generated-file diffs would change with them.
- **Not measured.** The cost of the module system itself, since `.olean` files are split three
  ways. In the spike, build times per module looked the same.
- **The toolchain is an rc.** `v4.36.0-rc1` may change module-system details before the release.

## Recommendation

It works, and the gain is real for the common iteration loop: fixing a proof in a hub no longer rebuilds
its dependents. The trade-off is that it only pays once the conversion reaches up to the files being
edited. A staged plan:

1. Convert PVM and JAM bottom-up, with `@[expose] public section`, in a few PRs. This is mechanical,
   plus meta fixes. Statements don't change.
2. Then Services, bottom-up, with each owning session converting its own area when it is quiet
   (Acc, Refine, Fmt and SymExec on request).
3. Update the generators to emit module headers.

Each conversion PR causes one cold rebuild of everything downstream of it, so batch them, and
sequence them like code-fact regenerations.
