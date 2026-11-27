import VersoManual
import Companion.Source

/-!
# Reader aids: the glossary and the plain-English chapter's figure

* `{glossarySection "state"}` renders one section of the glossary from `docs/site/glossary.json`:
  the section's introduction, then one entry per symbol: the symbol (the paper's macros, in
  KaTeX), its name and plain-English meaning, the model's declarations (each linked to its API page,
  with its hover, as `{api}` does) and the book section that defines it (a cross-reference). Every
  model name must be a declaration the glossary chapter imports, and every section tag must exist,
  or the build fails. `scripts/check-glossary.py` (CI) checks the file without building.
* `{figure "name"}` inserts one of the figures below as inline SVG. They draw in `currentColor`, so
  they follow the book's light and dark themes, and they scale to the column's width.
-/

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.Genre Manual

namespace Companion

/-- The glossary's styles. Colours come from `currentColor` (borders are a mix of it with
    transparency), so the entries work in both themes. -/
def glossaryCss : String := "
.glossary { margin: 0.5em 0 1.5em; }
.gl-entry { display: grid; grid-template-columns: minmax(3.5em, max-content) 1fr; column-gap: 1em;
  padding: 0.55em 0; border-top: 1px solid color-mix(in srgb, currentColor 18%, transparent);
  scroll-margin-top: 4.5em; }
.gl-entry:target { outline: 2px solid color-mix(in srgb, currentColor 45%, transparent); outline-offset: 2px; }
.gl-sym { font-size: 1.15em; padding-top: 0.05em; white-space: nowrap; }
.gl-body p { margin: 0 0 0.25em; }
.gl-body p:last-child { margin-bottom: 0; }
.gl-meta { font-family: system-ui, sans-serif; font-size: 0.85em; line-height: 1.45;
  color: var(--jl-muted); overflow-wrap: anywhere; }
.gl-meta code { font-size: 0.95em; }
@media (width <= 500px) { .gl-entry { grid-template-columns: 3em 1fr; column-gap: 0.6em; } }
.reader-figure { margin: 1em 0 1.5em; max-width: 40em; }
.reader-figure svg { display: block; width: 100%; height: auto; }
.reader-figure svg text { font-family: system-ui, sans-serif; fill: currentColor; }
"

-- The list of one section's entries.
block_extension Block.glossaryList where
  extraCss := [glossaryCss]
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ _ content => do
      pure html%{<div class="glossary">{← content.mapM go}</div>}

-- One entry: the first block (the symbol) on the left, the rest (name and meaning, the model line)
-- on the right; `id` is the entry's anchor, `gl-<id>`.
block_extension Block.glossaryEntry (id : String) where
  data := Json.str id
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ data content => do
      let .str i := data | pure .empty
      let (sym, body) := match content[0]? with
        | some b => (#[b], content.extract 1 content.size)
        | none => (#[], content)
      pure html%{<div class="gl-entry" id={s!"gl-{i}"}><div class="gl-sym">{← sym.mapM go}</div><div class="gl-body">{← body.mapM go}</div></div>}

-- The "Model: … · Defined in …" line of an entry.
block_extension Block.glossaryMeta where
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ _ content => do
      pure html%{<div class="gl-meta">{← content.mapM go}</div>}

/-- A text as inlines: `$…$` spans are inline maths, `…` spans (outside maths) code, the rest text. -/
def readerInlines (t : String) : DocElabM (Array Term) := do
  let mut out : Array Term := #[]
  let parts := (t.splitOn "$").toArray
  for h : i in [0:parts.size] do
    let part := parts[i]
    if part.isEmpty then continue
    if i % 2 == 1 then
      out := out.push (← ``(Verso.Doc.Inline.math Lean.Doc.MathMode.inline $(quote part)))
    else
      let pieces := (part.splitOn "`").toArray
      for h : j in [0:pieces.size] do
        let p := pieces[j]
        if p.isEmpty then continue
        out := out.push (← if j % 2 == 1 then ``(Verso.Doc.Inline.code $(quote p))
                            else ``(Verso.Doc.Inline.text $(quote p)))
  return out

/-- A model name as `{api}` renders it: its hover, linked to its API page. Fails when the glossary
    chapter does not import a declaration of that name. -/
def glossaryName (n : Name) : DocElabM Term := do
  let env ← getEnv
  unless env.contains n do
    throwError m!"glossary: no declaration {n} (docs/site/glossary.json); is it imported by the \
      glossary chapter?"
  let some idx := env.getModuleIdxFor? n
    | throwError m!"glossary: {n} is not defined in an imported module"
  let some mod := env.header.moduleNames[idx.toNat]?
    | throwError m!"glossary: no module for {n}"
  let url := s!"{apiRoot}/{modulePath mod}.html#{n}"
  let hl ← Verso.Genre.Manual.InlineLean.constTok n n.toString
  `(Verso.Doc.Inline.link
      #[Verso.Doc.Inline.other
        {Verso.Genre.Manual.InlineLean.Inline.name with data := Lean.ToJson.toJson $(quote hl)}
        #[Verso.Doc.Inline.code $(quote n.toString)]]
      $(quote url))

/-- `docs/site/glossary.json`. -/
def loadGlossary : IO Json := do
  let root ← findRepoRoot
  IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "docs" / "site" / "glossary.json"))

structure GlossaryArgs where
  sid : String

instance : FromArgs GlossaryArgs DocElabM :=
  ⟨GlossaryArgs.mk <$> .positional `sid (ValDesc.string.as "glossary section id (string literal)")⟩

/-- `{glossarySection "state"}`: one section of `docs/site/glossary.json`. -/
@[block_command]
def glossarySection : BlockCommandOf GlossaryArgs
  | ⟨sid⟩ => do
    let g ← loadGlossary
    let file := "docs/site/glossary.json"
    let places ← match g.getObjVal? "places" with
      | .ok p => pure p
      | .error e => throwError m!"glossary: {file}: {e}"
    let sections ← match g.getObjValAs? (Array Json) "sections" with
      | .ok s => pure s
      | .error e => throwError m!"glossary: {file}: {e}"
    let some sec := sections.find? (fun s => (s.getObjValAs? String "id").toOption == some sid)
      | throwError m!"glossary: {file} has no section {sid}"
    let str (j : Json) (k : String) (what : String) : DocElabM String :=
      match j.getObjValAs? String k with
      | .ok s => pure s
      | .error _ => throwError m!"glossary: {file}: {what} has no string field {k}"
    let intro ← str sec "intro" s!"section {sid}"
    let entries ← match sec.getObjValAs? (Array Json) "entries" with
      | .ok es => pure es
      | .error e => throwError m!"glossary: {file}: section {sid}: {e}"
    let mut blocks : Array Term := #[]
    for e in entries do
      let id ← str e "id" s!"an entry of section {sid}"
      let what := s!"entry {id}"
      let tex ← str e "tex" what
      let name ← str e "name" what
      let meaning ← str e "meaning" what
      let place ← str e "place" what
      let some label := (places.getObjValAs? String place).toOption
        | throwError m!"glossary: {file}: {what}: place {place} is not a key of places"
      let model := (e.getObjValAs? (Array String) "model").toOption.getD #[]
      let note := (e.getObjValAs? String "modelNote").toOption
      let sym ← ``(Verso.Doc.Block.para #[Verso.Doc.Inline.math Lean.Doc.MathMode.inline $(quote tex)])
      let headInls : Array Term := #[← ``(Verso.Doc.Inline.bold #[Verso.Doc.Inline.text $(quote name)]),
          ← ``(Verso.Doc.Inline.text ". ")] ++ (← readerInlines meaning)
      let head ← ``(Verso.Doc.Block.para #[$headInls,*])
      let mut metaInls : Array Term := #[← ``(Verso.Doc.Inline.emph #[Verso.Doc.Inline.text "In the model:"]),
        ← ``(Verso.Doc.Inline.text " ")]
      let mut first := true
      for n in model do
        unless first do metaInls := metaInls.push (← ``(Verso.Doc.Inline.text ", "))
        first := false
        metaInls := metaInls.push (← glossaryName n.toName)
      if let some t := note then
        unless model.isEmpty do metaInls := metaInls.push (← ``(Verso.Doc.Inline.text "; "))
        metaInls := metaInls ++ (← readerInlines t)
      metaInls := metaInls ++ #[← ``(Verso.Doc.Inline.text " · Defined in "),
        ← ``(Verso.Doc.Inline.other (Verso.Genre.Manual.Inline.ref $(quote place) none none)
              #[Verso.Doc.Inline.text $(quote label)])]
      let metaBlock ← ``(Verso.Doc.Block.other Companion.Block.glossaryMeta
        #[Verso.Doc.Block.para #[$metaInls,*]])
      blocks := blocks.push (← ``(Verso.Doc.Block.other (Companion.Block.glossaryEntry $(quote id))
        #[$sym, $head, $metaBlock]))
    let introInls ← readerInlines intro
    ``(Verso.Doc.Block.concat #[
        Verso.Doc.Block.para #[$introInls,*],
        Verso.Doc.Block.other Companion.Block.glossaryList #[$blocks,*]])

/-- The plain-English chapter's figure: the life of a work package, from submission (off-chain, on
    one core) to accumulation (on-chain). Drawn in `currentColor`; the dashed line separates the
    off-chain steps from the on-chain ones. -/
def lifeOfWorkSvg : String := "<svg viewBox=\"0 0 360 470\" role=\"img\" aria-labelledby=\"low-title low-desc\" xmlns=\"http://www.w3.org/2000/svg\">
<title id=\"low-title\">The life of a work package</title>
<desc id=\"low-desc\">Off-chain: a builder submits a work package to a core; the core's guarantors authorize and refine it, producing a work report, and spread the data to all validators. On-chain: a block includes the guaranteed report; later blocks carry availability assurances until the report is available; then accumulation runs the services' code and updates the state. Meanwhile auditors re-check the report, and a wrong report leads to a dispute.</desc>
<defs><marker id=\"low-arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\"><path d=\"M0,0 L10,5 L0,10 z\" fill=\"currentColor\"/></marker></defs>
<g fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\">
<rect x=\"20\" y=\"28\" width=\"230\" height=\"50\" rx=\"7\"/>
<rect x=\"20\" y=\"110\" width=\"230\" height=\"64\" rx=\"7\"/>
<rect x=\"20\" y=\"236\" width=\"230\" height=\"50\" rx=\"7\"/>
<rect x=\"20\" y=\"318\" width=\"230\" height=\"50\" rx=\"7\"/>
<rect x=\"20\" y=\"400\" width=\"230\" height=\"50\" rx=\"7\"/>
<rect x=\"268\" y=\"236\" width=\"82\" height=\"132\" rx=\"7\" stroke-dasharray=\"4 3\"/>
<path d=\"M135,78 V108\" marker-end=\"url(#low-arrow)\"/>
<path d=\"M135,174 V234\" marker-end=\"url(#low-arrow)\"/>
<path d=\"M135,286 V316\" marker-end=\"url(#low-arrow)\"/>
<path d=\"M135,368 V398\" marker-end=\"url(#low-arrow)\"/>
<path d=\"M250,261 H266\" marker-end=\"url(#low-arrow)\"/>
<path d=\"M6,205 H354\" stroke-dasharray=\"6 4\" stroke-width=\"1\"/>
</g>
<g font-size=\"11\" opacity=\"0.75\" text-anchor=\"end\"><text x=\"350\" y=\"196\">OFF-CHAIN · on one core ↑</text><text x=\"350\" y=\"222\">ON-CHAIN · in blocks ↓</text></g>
<g font-size=\"13\">
<text x=\"32\" y=\"49\" font-weight=\"600\">1. Work package</text><text x=\"32\" y=\"67\">a builder submits it to a core</text>
<text x=\"32\" y=\"131\" font-weight=\"600\">2. Guarantee</text><text x=\"32\" y=\"149\">guarantors authorize and refine it</text><text x=\"32\" y=\"166\">→ work report; data to all</text>
<text x=\"32\" y=\"257\" font-weight=\"600\">3. Reported</text><text x=\"32\" y=\"275\">a block carries the guarantee</text>
<text x=\"32\" y=\"339\" font-weight=\"600\">4. Available</text><text x=\"32\" y=\"357\">over 2/3 of validators assure</text>
<text x=\"32\" y=\"421\" font-weight=\"600\">5. Accumulated</text><text x=\"32\" y=\"439\">service code updates the state</text>
<text x=\"278\" y=\"257\" font-weight=\"600\">Audit</text><text x=\"278\" y=\"275\" font-size=\"11.5\">validators</text><text x=\"278\" y=\"290\" font-size=\"11.5\">re-check;</text><text x=\"278\" y=\"305\" font-size=\"11.5\">a wrong</text><text x=\"278\" y=\"320\" font-size=\"11.5\">report is</text><text x=\"278\" y=\"335\" font-size=\"11.5\">disputed</text>
</g>
</svg>"

-- A figure as inline SVG.
block_extension Block.readerFigure (svg : String) where
  data := Json.str svg
  extraCss := [glossaryCss]
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .str s := data | pure .empty
      pure html%{<figure class="reader-figure">{Html.raw s}</figure>}

structure FigureArgs where
  name : String

instance : FromArgs FigureArgs DocElabM :=
  ⟨FigureArgs.mk <$> .positional `name (ValDesc.string.as "figure name (string literal)")⟩

/-- `{figure "lifeOfWork"}`: one of the reader figures as inline SVG. -/
@[block_command]
def figure : BlockCommandOf FigureArgs
  | ⟨n⟩ => do
    let svg ← match n with
      | "lifeOfWork" => pure lifeOfWorkSvg
      | _ => throwError m!"figure: no figure {n} (Companion/Reader.lean)"
    ``(Verso.Doc.Block.other (Companion.Block.readerFigure $(quote svg)) #[])

end Companion
