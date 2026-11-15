# The module system: why and how to convert

> **Rule for new files.** Every new file under `PVM/` or `JAM/` must be a module. Start it with
> `module`, then `public import …`, then `@[expose] public section` (or run `scripts/to-module.py` on
> it). A converted file cannot import a file that is not a module, so a new file without the header
> breaks every converted importer.

Lean's module system splits each `.olean` into a public part and private parts. The public part holds
the statements and the definitions marked `@[expose]`; the private parts hold the proofs. Lake rebuilds
an importer only when the public part of what it imports changes. So, when **both ends of an import are
modules**, an edit that only changes a proof does not rebuild anything downstream.

The spike measured this on v4.36.0-rc1 (`docs/profiling/p3-module-spike.md` on branch
`claude/p3-module-spike`). A proof edit in `PVM/Memory`, `Services/Bootstrap/Alloc/Rep` or
`PVM/SymExec/Sound` rebuilt only that module, against about 30 dependents each.

Adam approved the conversion for PVM and JAM on 2026-11-15. The Services areas and the generators come
later, done by their owning sessions with this recipe.

## What still rebuilds the importers

- a changed statement, a new or removed public declaration, or a changed definition body;
- a proof edit that changes which axioms the theorem uses (e.g. a proof that gains or loses
  `Quot.sound`), because the axiom set is part of the public `.olean`;
- any edit at all, if the importer is not a module or uses `import all`.

A new `private` declaration rebuilds nothing downstream.

## The recipe

1. **Bottom-up.** A module cannot import a non-module ("cannot import non-`module` … from `module`").
   Convert a file only once everything it imports from the repository is a module, or convert those in
   the same change. A non-module can import a module, so files that aren't converted yet keep working.
2. **Run the script** from the repository root:

   ```sh
   scripts/to-module.py --check Services/Bootstrap/Foo.lean …   # what it would do
   scripts/to-module.py Services/Bootstrap/Foo.lean …
   ```

   For each file it:
   - adds `module` as the first line;
   - turns `import X` into `public import X`;
   - opens `@[expose] public section` after the imports.

   It refuses a file that imports a repository file that is not a module.
3. **Keep `@[expose] public section`.** It keeps every definition transparent downstream, as before.
   Without `@[expose]`, a definition's body is hidden: downstream `decide`, `rfl`, `unfold`, `simp [d]`
   and kernel reflection (`checkCode`, SymExec's `check`, the generated `facts_k`) fail on it.
   Narrowing it is possible later, file by file, but anything a kernel computation unfolds must stay
   exposed.
4. **Meta code.** Simprocs, elaborators, and macros that run code from imported modules need that code
   imported with `public meta import`, and their own helper functions declared `meta def`. The build
   names the missing pieces ("… is not accessible here; consider adding `public meta import …`",
   "… not marked `meta`"). Example: `PVM/Logic/Steps.lean`, whose simprocs need
   `public meta import PVM.Basic`, `PVM.Exec`, `PVM.Logic.Bits` and
   `Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat`, and whose helpers `evalNatFn2`/`evalNatFn3` are
   `meta def`.
   A `meta import` is not a regular import. If the file also uses those declarations ordinarily, keep
   both lines (`public import X` and `meta import X`).
   - **`#guard` and `#eval`** run the interpreter, which needs what they evaluate to be meta-imported.
     Example: `JAM/Disputes.lean` and `JAM/Safrole.lean` have `meta import JAM.Crypto` next to
     `public import JAM.Crypto`, for their `#guard`s on `contextString`. The error to look for is
     "Could not find native implementation of external declaration".
   - **A `match` written out in a proof** (e.g. as the pattern of a `generalize`) elaborates to a fresh
     matcher inside a module, not to the imported definition's matcher, so it no longer matches the
     unfolded term. Write holes instead: `generalize hl : min z (_ - min f _) = l` (see
     `JAM/Theorems/KeepRO.lean`, `writeValue_keep`). The symptom is a later "`simp` made no progress".
5. **New files.** Once a directory is converted, a new file that converted files import must be a
   module too: start it with `module`, `public import …` and `@[expose] public section`.
6. **Generated files.** A generator must emit the module header itself (change the generator, not its
   output), and CI's generated-file diffs follow.
7. **Build and check axioms** as usual. A conversion PR rebuilds everything downstream of the converted
   files once, so batch conversions and sequence them like code-fact regenerations.
