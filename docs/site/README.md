# The documentation site

A separate Lake package (Adam, 2026-11-27) that builds the jam-lean site for GitHub Pages. It
requires the root package by path (`require «jam-lean» from "../.."`), plus doc-gen4 and Verso at
the tags matching the toolchain (`v4.36.0-rc1`, `v4.36.0-rc1-patch1`). The root lakefile never
resolves either tool, and nothing outside `docs/site/` imports anything here.

| Path on the site | What | Source |
| --- | --- | --- |
| `/api/` | doc-gen4 pages for `PVM`, `JAM` and `JamCrypto` | the model's docstrings |
| `/book/` | *A Companion to the Gray Paper* (Verso) | `Companion.lean`, `Companion/`, `CompanionMain.lean` |
| `/` | landing page | `landing/index.html` |

```
cd docs/site
./build-site.sh          # everything, into _site/ (first run: doc-gen4 + Verso + core docs, ~30 min)
lake build companion && lake exe companion --output _book   # the book alone
```

`.github/workflows/docs.yml` runs `build-site.sh` on every push to `main` and deploys `_site/` with
`actions/deploy-pages`. Actions → Docs → Run workflow builds any branch, and only a run on `main`
deploys. It is not part of CI's merge gate.

## Writing the companion

Each chapter is one Verso file in `Companion/`, in the order of GP v0.8.1's sections, and is included
from `Companion.lean`. A chapter imports the model modules it discusses. It can then use:

* `$$`…`` for the paper's equations, in KaTeX. Transcribe them from the pinned paper
  (`scripts/fetch-paper.sh`).
* `{leanSource N}` for the source of declaration `N`, semantically highlighted (hovers, links)
  by SubVerso, with links to its lines on GitHub and its API page (`Companion/Source.lean`).
  Nothing is copied: a renamed declaration fails the build, and an edited one shows its new text.
  A chapter that quotes a new model module must add it to `modelHighlights` in `lakefile.lean`
  (SubVerso's `highlighted` facet re-elaborates exactly those modules, about 0.5 s each); the build
  says so if one is missing.
* `{docstring N}` for a definition or theorem's signature and docstring.
* `{name}`N`` for an inline reference to `N`.

One rule for code: wherever the book names the definition that implements an equation or a step,
it *quotes* it with `{leanSource N}` (the header "N — file · GitHub · API" comes with it; blocks over
30 lines start collapsed). A bare GitHub or API link never stands in for the code. A theorem in the
`proofs/` package, which `{leanSource}` cannot reach, is quoted as its statement in a code block.
`{api}` and `{name}` references in running prose to something quoted elsewhere are fine.
Named in passing, and only linked: constants and context strings (`JAM.Xvalidif`, `JAM.nullEdKey`,
`Constants.*`), abbreviations, configuration, error, input, output and trace types, and theorems
mentioned without being discussed. `PVM.costRow?` (the generated 140-row cost table) is the one
definition the book cannot quote (its quotation exceeds Lean's code-generator recursion depth); it
stays a link.

Every page with Lean code has a "Show all Lean / Hide all Lean" switch under its title
(`collapseJs` in `CompanionMain.lean`). "Show all" opens every collapsed definition; "Hide all"
hides each quoted definition (header, docstring and code, the `lean-source` box `{leanSource}`
emits) and every other Lean code block, leaving the prose and the paper's equations; pressing the
active button again returns to the default. The choice is kept in `localStorage`
(`jam-lean-book.lean`) for every page; if the browser blocks storage the switch still works on the
page. So write the prose to read on its own when the code is hidden: don't let a sentence depend
on the reader seeing the quoted block.

The book has a dark mode. It follows the reader's system setting (`prefers-color-scheme`), and a
"Theme: Auto / Light / Dark" switch under each page's title overrides it (kept in `localStorage`
as `jam-lean-book.theme`, applied in the page head so the page never flashes in the wrong theme).
The palette is `darkRules` in `CompanionMain.lean`: Verso's colour variables, the few colours
Verso's styles hard-code, and this book's own `--jl-*` variables. New CSS takes its colours from
those variables (or `currentColor`), not from literal colours, so it works in both themes.
The API pages (doc-gen4) keep doc-gen4's own styling.

The readings the model chose should link to `docs/upstream-candidates.md` by note number.

## Notation: the paper's macros

Math in the book (KaTeX) and in the API docstrings (MathJax) can use the Gray Paper's own macros,
as `preamble.tex` and the section files define them (tag v0.8.1): `$\workcontext$` (ℂ),
`$\registers$` (φ), `$\workreport$` (ℝ), `$\sequence[:\Cepochlen]{\safroleticket}$`,
`$\bssignature{k}{c}{m}$`, `$\zerohash$` (ℍ₀), `$\H_\¬timeslot$` (H_T). Write the paper's names,
`¬` included (`$\wp¬authcode$`, `$\g¬workreport$`). Prefer a macro over a hand-picked glyph: it is
the paper's symbol by construction, and a later paper version changes it in one place.

* The table is `gp-macros.json` (with `gp-macros.js` for the site), generated by
  `scripts/gen_macros.py` from the pinned paper. CI checks that it matches the paper
  (`scripts/check-tables.sh`). Never edit it by hand. `build-site.sh` loads it in both renderers
  (`landing/math-macros.js`).
* `¬` cannot appear in a TeX control-sequence name in KaTeX or MathJax. Both renderers rewrite
  `\a¬b` to an internal ASCII name before parsing, so this works only on the site. Elsewhere (an
  editor hover, GitHub's view of a `.lean` file) the macro shows as written.
* Where the paper's body uses LaTeX packages that neither renderer has, the table uses supported
  equivalents. A few print a close glyph rather than the same one, listed under `approximate`:
  `\tricolon` and `\is` (the "is" of tuples, drawn as two stacked small ▸, the form the chapters
  use) and `\concatall` (an over-arc). `\anglebar` and `\dictionary` print ⟨|…|⟩. The macros listed under `unmapped` are not available:
  `\seqminusl`, `\seqminusr` and `\disjoint` (MnSymbol spoons), `\orderby` and `\sqorderby`
  (mathabx wavy delimiters), and layout macros. For those, write a standard symbol and say which
  macro the paper uses.
* A macro with an optional argument (`\sequence`, `\hash`, `\blob`, `\encode`, …) takes it in both
  renderers: `$\hash[0]$`, `$\encode[4]{x}$`.
* `node check-macros.js` renders every macro in both renderers (see its header). Run it after
  changing `gen_macros.py`.

`scripts/check-notation.py` (in CI) rejects known-wrong forms in docstrings and the book, for
example 𝕏 for the refinement context, ρ^‡‡, ω for registers or lowercase header fields. A genuine
use goes in a doc comment preceded by `-- notation-ok: <id> <reason>`.

## Model maps: every displayed equation has a model-map entry

**Rule: every equation the book displays has a model-map entry.** Each `{gpeq}` display and each
`{transcribed}` hand display is followed by a generated line, "*In the model:* …", saying how the
model handles the equation. The lines come from one file per chapter,
`model-map/<Chapter>.json` (`<Chapter>` is the chapter's file name in `Companion/`), so chapters
can be mapped in parallel without conflicts. Each file maps the paper's equation numbers to one
entry:

```json
{
  "equations": {
    "6.24": { "kind": "inline", "name": "JAM.safrole", "at": "-- Entropy (§6.4)", "note": "…" },
    "6.27": { "kind": "def", "name": "JAM.outsideIn" },
    "A.40": { "kind": "type", "name": "PVM.HostFn" },
    "X.YY": { "kind": "theorem", "name": "JAM.some_theorem" },
    "X.ZZ": { "kind": "notModelled", "reason": "…" },
    "A.12": { "kind": "notation", "reason": "…" }
  }
}
```

| Kind | Fields | Meaning | The line shows |
| --- | --- | --- | --- |
| `def` | `name` | the declaration that computes the equation | "computed by N", its API page and lines on GitHub, and either "quoted in this chapter" (a link to the chapter's `{leanSource N}`) or a "code" toggle that opens the declaration |
| `inline` | `name`, `at` | computed inside a larger declaration, at the line containing the text `at` | "inside N, at `at`", the located lines on GitHub, and a "code" toggle with those lines |
| `type` | `name` | a type, structure or constant | as `def`, "the type N" |
| `theorem` | `name` | only if the equation is a property the model *proves* rather than computes | as `def`, "proved as N" |
| `notModelled` | `reason` | the model has no counterpart | "not modelled: reason" |
| `notation` | `reason` | pure notation or convention, nothing to implement | "notation: reason" |

Every entry may add `note`, a short remark shown at the end of the line. Names are full names.
An `at` locator is a comment marker (`-- Entropy (§6.4)`) or a binding (`let acc' :=`), never a
line number: it must occur exactly once in the declaration's source, and the build finds the
lines from the live source (for a comment, the lines under it up to a blank line or the next
comment at its indentation; otherwise the line and the more-indented lines after it), so the
links stay current as the code moves. Equations of one display that share an entry get one line.

Checks:

* the book's build (`Companion/ModelMap.lean`, from `{gpeq}` and `{transcribed}`) fails when a
  displayed equation of a mapped chapter has no entry, a kind is unknown or lacks its fields, a
  `name` is not a declaration the chapter imports, or an `at` does not occur exactly once inside
  the declaration. Lake tracks `model-map/` (`input_dir modelMap` in `lakefile.lean`), so editing
  a map re-elaborates the chapters;
* `scripts/check-model-map.py` (CI's `model` job, no build needed) checks the same structure,
  rejects entries for equations the chapter does not display, and checks names and locators
  against the model's sources textually (`--counts` prints the entries per kind).

`model-map/unmapped.json` lists the chapters not mapped yet. A listed chapter may have a partial
map (its entries are shown); the list only shrinks: the check fails when a listed chapter's map is
complete, so remove the chapter from the list in the PR that completes it. When the list is
empty, every displayed equation is explained.

A PR that changes a modelled function updates its model-map entries (a renamed declaration or a
moved marker fails the book's build).

## Keeping the book in step with the model

* `chapter-map.json` maps each model module to the chapters that discuss it (seeded from the
  chapters' imports by `scripts/check-chapter-map.py --seed`; edit it by hand). A new chapter adds
  its modules. On a PR, CI's `chapters` job warns in its summary, without failing, when a mapped
  module changes but none of its chapters does.
* `scripts/check-citations.py` (CI) checks that every note the book and the model cite
  (`v0.8.1-A18`, "note 27") exists in `docs/upstream-candidates.md` and is not withdrawn.
* Equations come from the paper's TeX. `scripts/gen_equations.py` writes `gp-equations.json`
  (number, label, TeX body, fingerprint; run with `--aux` against a build of the tagged paper, it
  checks the numbers of the labelled equations against LaTeX's `.aux`).
  `{gpeq "6.24"}` displays the paper's equation (several numbers: one row each, aligned at their
  relation, each with its own number); ``{eq}`6.24` `` cites a number. Where a display
  must be the book's own (a part of an equation, a single case, a layout the renderers cannot
  draw), a `{transcribed "6.24" "<fingerprint>"}` paragraph goes just before it, and the build fails
  when that equation's TeX changes. `scripts/check-equations.py` (CI) rejects a numbered hand display
  without its marker, a hand-typed "(6.24)" or "(14.6–14.8)" in prose (write
  ``{eq}`14.6`–{eq}`14.8` ``), and a heading that cites an equation the paper does not have. After regenerating the table for a new
  paper version, `scripts/check-equations.py --changed OLD.json` lists the equations whose TeX
  changed or which moved, and the chapters that use them: re-read those passages. Lake tracks
  `gp-equations.json` and `gp-labels.json` (the `gpTables` target in `lakefile.lean`), so a change
  to either re-elaborates every chapter, even in a cached build.
