# Append-only code-fact tiers

Code facts are the per-instruction facts about a vendored blob (`.instr`, `.blockStart`, `.block`,
`.jumpEntry`, …) that the step proofs use, checked against the blob by the kernel. They live in
generated modules: `Code` (class `HasCode`) and the built-in tiers `CodeX`, `CodeA`, `CodeF` and `CodeR`
(`HasCodeX`, …). Adding a range to one of those regenerates it, and every module that imports it
rebuilds, which can mean hours of CI.

An **append-only tier** avoids that. The new facts go in a new module `Code<Name>` with its own class
`HasCode<Name>` and its own kernel check, so only the modules that import the new tier rebuild.

## Adding facts

1. In `Tests/GenWitnessSteps.lean`, append an entry to the service's `tiers` (for Bootstrap, in
   `bootstrapSvc`). Put it at the end and give it a new name:

   ```lean
   tiers := [
     { name := "Acc1", ranges := [(52000, 52100)], excludes := ["X", "A"],
       doc := "an example handler" }]
   ```

   - `ranges`: the instruction ranges `[lo, hi)` whose facts you need.
   - `excludes`: the tiers whose facts this one leaves out. These are the built-ins `X`, `A`, `F` and
     `R`, or tiers listed earlier. `Code` is always left out. List only tiers your proofs already
     assume, because the users of the new tier must also assume and import every tier it excludes.
     Leave it empty for a self-contained tier, which then repeats any facts the other tiers have.
   - `doc`: a few words on what the ranges are, for the module docstring.

2. Generate the tier. `7463` is the step count of `Code`, as in CI:

   ```sh
   lake exe genwitnesssteps --service bootstrap tier 7463 Acc1 > Services/Bootstrap/CodeAcc1.lean
   lake exe genwitnesssteps --service bootstrap tiercheck 7463 Acc1
   ```

   The first command writes `CodeAcc1.lean` (the facts and `HasCodeAcc1`), the lemma slices
   `CodeAcc1/L*.lean` and the umbrella `CodeAcc1All.lean`. The second writes the kernel-check groups
   `CodeAcc1Check/G*.lean` and `CodeAcc1Ok.lean`.

3. Add `import Services.Bootstrap.CodeAcc1All` and `import Services.Bootstrap.CodeAcc1Ok` to
   `Services.lean`, so that the default build checks the tier.

CI's generated-files step regenerates every tier that `lake exe genwitnesssteps --service bootstrap tiers`
lists and fails if a file differs, so commit everything the two commands wrote.

**Never** add a range to an existing tier, built-in or append-only, and never regenerate an existing tier
just to add facts. To cover more code, add another tier.

## Using a tier

- Import `Services.Bootstrap.CodeAcc1All` for the `@[pvm_code]` lemmas (`d_<pc>`, `nx_<pc>`,
  `bs_<t>`, `jte_<k>`), along with the umbrella module of each tier it excludes. A lemma whose
  fact an excluded tier already has is emitted only there.
- Assume `[HasCodeAcc1 p P]` next to the classes you already assume.
- A headline theorem discharges it without a new hypothesis, from the base facts:
  `haveI := CodeAcc1Check.hasCodeAcc1 hok`, where `hok : CodeOk p Code.facts P` (import
  `Services.Bootstrap.CodeAcc1Ok`). This is how `CodeA` is discharged (`Acc/CkLift.lean`), so a tier adds
  no assumption to the theorems that use it.

## Folding tiers together

Every tier adds a module, a class and a kernel check. Merge tiers back into a built-in tier (or merge
several append-only tiers into one) only as part of a planned cold rebuild, for example together with a
regeneration of `Code`. Coordinate that through the parent session. A fold changes every importer, and a
tier's contents depend on `Code` and on the tiers it excludes, so regenerating any of those regenerates
the tier too.
