# Contributing to jam-lean

Pull requests are welcome from anyone. jam-lean is a Lean 4 model of JAM written from the
Gray Paper. Outside review against the paper is among the most useful contributions it can get:
equations that don't match, readings you would choose differently, and gaps in the proofs.

## Disclosure

If you are on a team building a JAM implementation (for the JAM prize or otherwise), say so in your
PR description. It is the "Disclosure" section of the PR template. Being on a team does not stop
you contributing; the disclosure keeps the record clear.

## Rules

- **The paper is the only source.** Model only from the Gray Paper **v0.8.1** (tag `v0.8.1` of
  gavofyork/graypaper). Don't copy or consult other JAM or PVM implementations. Don't follow
  paper changes made after the tag.
- **Cite the paper.** Docstrings cite the section and equation they model.
- **Disclose readings.** Where the paper is ambiguous, or the code departs from its literal text,
  add a row to `docs/upstream-candidates.md` and a "Readings chosen" bullet in the chapter.
  Disagreements between the paper and the test vectors go there too.
- **Toolchain.** Lean `v4.36.0-rc1`, core and Std only. Mathlib is allowed only in the proofs-only
  library `proofs/`, which nothing else imports.
- **Forbidden:** `sorry`, `partial def`, `implemented_by`, `native_decide` and `bv_decide`. Axioms
  may be only `propext`, `Classical.choice` and `Quot.sound` (`scripts/CheckAxioms.lean`).
- **Keep the book in step.** A PR that changes the behaviour of a modelled function updates its
  companion chapter (`docs/site/Companion/`) and its model-map entries
  (`docs/site/model-map/*.json`) in the same PR.
- **Test vectors.** Don't change an expected output, except where a v0.8.1 paper change dictates
  it. List each such edit in the PR body, with the paper change and the equation.

## Workflow

1. Fork, and branch from `main`.
2. Build: `lake build` builds the model (`PVM` and `JAM`). The test executables are in
   `lakefile.lean`. A cold build of everything, Services proofs included, takes hours. The model
   alone takes minutes.
3. Sign off each commit (`git commit -s`), certifying the
   [Developer Certificate of Origin](https://developercertificate.org/).
4. Open a PR using the template. CI (the `model` and `chapters` jobs) must be green. PRs are
   squash-merged.

## Licence

jam-lean is licensed under the [Apache License 2.0](LICENSE). By contributing, you agree that your
contribution is licensed under it.
