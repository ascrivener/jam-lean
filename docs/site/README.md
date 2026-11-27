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

The readings the model chose should link to `docs/upstream-candidates.md` by note number.
