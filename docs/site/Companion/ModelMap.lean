import VersoManual
import SubVerso.Module
import Companion.Source

/-!
# Where the model implements each displayed equation

Every equation the book displays (`{gpeq}` or a `{transcribed}` hand display) is followed by one
line, "In the model: …", generated from the chapter's model map,
`docs/site/model-map/<Chapter>.json` (`<Chapter>` is the chapter's file name in `Companion/`).
The file maps the paper's equation numbers to one entry each:

```
{ "equations": {
    "6.24": { "kind": "inline", "name": "JAM.safrole", "at": "-- Entropy (§6.4)" },
    "6.27": { "kind": "def", "name": "JAM.outsideIn" },
    "6.3":  { "kind": "type", "name": "JAM.SafroleState", "note": "…" },
    "A.12": { "kind": "notation", "reason": "…" } } }
```

* `def`: the declaration `name` computes it.
* `inline`: it is computed inside the larger declaration `name`, at the line holding the text
  `at` (a comment marker such as `-- Entropy (§6.4)`, or a binding such as `let acc' :=`). `at`
  must occur exactly once in the declaration's source; the line range shown is found from the
  live source at build time (the marker's block: for a comment, the lines under it up to a blank
  line or the next comment at its indentation; otherwise the more-indented lines after it).
* `type`: a type, structure or constant `name`.
* `theorem`: the equation is a property the model proves rather than computes: theorem `name`.
* `notModelled`: the model has no counterpart; `reason` says why.
* `notation`: pure notation or convention with nothing to implement; `reason` says what it is.

Every entry may carry `note` (a short remark shown after the line; `…` spans in it are code).

`def`, `type` and `theorem` lines link the declaration's API page and its lines on GitHub; when the
chapter quotes the declaration with `{leanSource}` the line points at that quotation, and otherwise
the line opens to show the declaration's code. `inline` lines open to show the located lines.

A chapter listed in `docs/site/model-map/unmapped.json` need not have a map yet (entries it does
have are shown); for every other chapter, a displayed equation without an entry, an unknown kind,
a missing declaration or an unresolved `at` fails the build. `scripts/check-model-map.py` (CI)
checks the same structure without building.
-/

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.Genre Manual
open SubVerso.Highlighting (Highlighted)

namespace Companion

/-- One model-map entry. -/
structure ModelEntry where
  kind : String
  name : Option Name := none
  at? : Option String := none
  reason : Option String := none
  note : Option String := none
  deriving BEq

def modelKinds : List String := ["def", "inline", "type", "theorem", "notModelled", "notation"]

/-- The chapter's map (equation number ↦ entry), and whether the chapter must be complete
    (it is not listed in `unmapped.json`). -/
def loadModelMap (chapter : String) : IO (Std.HashMap String ModelEntry × Bool) := do
  let root ← findRepoRoot
  let dir := root / "docs" / "site" / "model-map"
  let unmappedJson ← IO.ofExcept <| Json.parse (← IO.FS.readFile (dir / "unmapped.json"))
  let unmapped ← IO.ofExcept <| unmappedJson.getObjValAs? (Array String) "unmapped"
  let required := !unmapped.contains chapter
  let file := dir / s!"{chapter}.json"
  unless ← file.pathExists do
    if required then
      throw <| IO.userError s!"model map: {file} is missing; every chapter not listed in \
        model-map/unmapped.json needs one"
    return ({}, false)
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
  let eqs ← IO.ofExcept <| json.getObjVal? "equations"
  let some kvs := eqs.getObj?.toOption | throw <| IO.userError s!"{file}: equations is not an object"
  let m ← kvs.foldlM (init := ({} : Std.HashMap String ModelEntry)) fun m n v => do
    let str? (k : String) : Option String := (v.getObjValAs? String k).toOption
    let some kind := str? "kind" | throw <| IO.userError s!"{file}: ({n}) has no kind"
    unless modelKinds.contains kind do
      throw <| IO.userError s!"{file}: ({n}) has unknown kind {kind}; one of {modelKinds}"
    return m.insert n { kind, name := (str? "name").map String.toName, at? := str? "at",
                        reason := str? "reason", note := str? "note" }
  return (m, required)

/-- The chapter being elaborated: the base name of the current file (`Companion/Safrole.lean` ↦ `Safrole`). -/
def currentChapter : TermElabM String := do
  let f : System.FilePath := ← getFileName
  return f.fileStem.getD f.toString

/-- Indentation (leading spaces) of a line. -/
def indentOf (s : String) : Nat := (s.toList.takeWhile (· == ' ')).length

def isCommentLine (s : String) : Bool := (String.ofList (s.toList.dropWhile (· == ' '))).startsWith "--"

def isBlank (s : String) : Bool := s.toList.all (·.isWhitespace)

def containsStr (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- The lines (1-based, inclusive) that the locator `at` marks inside lines `first..last` of
    `lines`: `at` must occur on exactly one of them. -/
def resolveLocator (lines : Array String) (first last : Nat) (at_ : String) : Except String (Nat × Nat) := do
  let hits := (List.range (last + 1 - first)).map (· + first) |>.filter fun i =>
    containsStr (lines[i - 1]?.getD "") at_
  match hits with
  | [] => throw s!"`{at_}` does not occur in the declaration's source (lines {first}–{last})"
  | [l] =>
    let line := lines[l - 1]!
    let ind := indentOf line
    let comment := isCommentLine line
    let mut e := l
    while e < last do
      let nxt := lines[e]!  -- line e + 1
      if isBlank nxt then break
      if comment then
        if indentOf nxt < ind || (indentOf nxt == ind && isCommentLine nxt) then break
      else
        if indentOf nxt ≤ ind then break
      e := e + 1
    return (l, e)
  | ls => throw s!"`{at_}` occurs {ls.length} times in the declaration's source (lines {ls}); \
      make the locator unique"

/-- Where a declaration is: its module, file (relative to the repository root), lines, and the
    file's lines. -/
structure DeclSite where
  mod : Name
  rel : String
  first : Nat
  last : Nat
  lines : Array String

def declSite (name : Name) : TermElabM DeclSite := do
  let env ← getEnv
  unless env.contains name do
    throwError m!"model map: no declaration {name} (is it imported by this chapter?)"
  let some idx := env.getModuleIdxFor? name
    | throwError m!"model map: {name} is not defined in an imported module"
  let some mod := env.header.moduleNames[idx.toNat]?
    | throwError m!"model map: no module for {name}"
  let some ranges ← findDeclarationRanges? name
    | throwError m!"model map: no declaration range stored for {name}"
  let root ← findRepoRoot
  let rel := modulePath mod ++ ".lean"
  let file := root / rel
  unless ← file.pathExists do
    throwError m!"model map: {name} is defined in {mod}, but {file} does not exist"
  let lines := ((← IO.FS.readFile file).splitOn "\n").toArray
  return { mod, rel, first := ranges.range.pos.line, last := ranges.range.endPos.line, lines }

/-- Whether the chapter source `src` quotes `name` with `{leanSource …}` (written in full, or as a
    suffix of the full name after `open`). -/
def chapterQuotes (src : String) (name : Name) : Bool :=
  let full := name.toString
  (src.splitOn "{leanSource ").drop 1 |>.any fun rest =>
    let q := String.ofList (rest.toList.takeWhile (fun c => c != '}' && !c.isWhitespace))
    q == full || full.endsWith ("." ++ q)

/-- Like `loadHighlighted`, but `none` when the module has no highlighted JSON (it is not in
    `modelHighlights`): the quote is then shown as plain text. -/
def loadHighlighted? (root : System.FilePath) (mod name : Name) : IO (Option Highlighted) := do
  let file := (mod.components.foldl (init := root / "docs" / "site" / ".lake" / "build" / "highlighted")
    fun d c => d / c.toString (escape := false)).addExtension "json"
  unless ← file.pathExists do return none
  loadHighlighted root mod name

-- The "In the model:" line: `before` when it is emitted before its display (a `{transcribed}`
-- marker precedes the hand display), so the page script moves it after the display.
block_extension Block.modelLine (before : Bool) where
  data := Json.bool before
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ data content => do
      let cls := if data == Json.bool true then "model-line model-line-before" else "model-line"
      pure html%{<div class={cls}>{← content.mapM go}</div>}

-- A line that opens to show code: the first block (a paragraph) is the summary, the rest the body.
block_extension Block.modelDetails where
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI go _ _ content => do
      let (summary, body) ← match content[0]? with
        | some (Verso.Doc.Block.para inls) => pure (← inls.mapM goI, content.extract 1 content.size)
        | _ => pure (#[], content)
      pure html%{<details class="model-quote"><summary>{summary}<span class="model-show">{Html.text "code"}</span></summary>{← body.mapM go}</details>}

-- A pointer to the chapter's own quotation of a declaration (the page script makes it a link).
inline_extension Inline.modelQuoted (target : String) where
  data := Json.str target
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun go _ data content => do
      let .str t := data | pure .empty
      pure html%{<a class="model-quoted" data-target={t}>{← content.mapM go}</a>}

/-- A note's text as inlines: `…` spans are code, the rest text. -/
def noteInlines (t : String) : TermElabM (Array Term) :=
  ((t.splitOn "`").toArray.mapIdx fun i part => (i, part)).filterMapM fun (i, part) =>
    if part.isEmpty then pure none
    else if i % 2 == 1 then some <$> ``(Verso.Doc.Inline.code $(quote part))
    else some <$> ``(Verso.Doc.Inline.text $(quote part))

/-- The rendered line for the entry `e` of equations `ns` (their numbers prefix the line when the
    display shows other equations too: `label`). -/
def modelLineBlocks (chapterSrc : String) (ns : List String) (label : Bool) (e : ModelEntry) :
    TermElabM (Array Term) := do
  let n := ", ".intercalate ns
  let lead : Array Term := #[← ``(Verso.Doc.Inline.emph #[Verso.Doc.Inline.text "In the model"]),
    ← ``(Verso.Doc.Inline.text $(quote (if label then s!" ({n}): " else ": ")))]
  let tail : Array Term ← match e.note with
    | some t => pure (#[← ``(Verso.Doc.Inline.text " — ")] ++ (← noteInlines t))
    | none => pure #[]
  let need {α : Type} (what : String) (o : Option α) : TermElabM α := match o with
    | some x => pure x
    | none => throwError m!"model map: ({n}) of kind {e.kind} needs `{what}`"
  match e.kind with
  | "notModelled" | "notation" =>
    let r ← need "reason" e.reason
    let word := if e.kind == "notation" then "notation" else "not modelled"
    let para ← ``(Verso.Doc.Block.para #[$(lead ++ #[← ``(Verso.Doc.Inline.bold #[Verso.Doc.Inline.text $(quote word)]),
        ← ``(Verso.Doc.Inline.text $(quote s!": {r}"))] ++ tail),*])
    return #[para]
  | kind =>
    let name ← need "name" e.name
    let site ← declSite name
    let root ← findRepoRoot
    let commit ← repoCommit root
    let apiUrl := s!"{apiRoot}/{modulePath site.mod}.html#{name}"
    let (first, last, word) ← if kind == "inline" then
        let at_ ← need "at" e.at?
        match resolveLocator site.lines site.first site.last at_ with
        | .ok (a, b) => pure (a, b, "inside")
        | .error msg => throwError m!"model map: ({n}) inline in {name}: {msg}"
      else pure (site.first, site.last, match kind with
        | "def" => "computed by" | "type" => "the type" | _ => "proved as")
    let ghUrl := s!"{repoUrl}/blob/{commit}/{site.rel}#L{first}-L{last}"
    let nameLink ← ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.code $(quote name.toString)] $(quote apiUrl))
    let mut inls : Array Term := lead.push (← ``(Verso.Doc.Inline.text $(quote s!"{word} ")))
    inls := inls.push nameLink
    if kind == "inline" then
      inls := inls ++ #[← ``(Verso.Doc.Inline.text ", at "),
        ← ``(Verso.Doc.Inline.code $(quote (e.at?.getD "")))]
    let range := if first == last then s!"line {first}" else s!"lines {first}–{last}"
    inls := inls ++ #[← ``(Verso.Doc.Inline.text " · "),
      ← ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.text $(quote s!"{site.rel}, {range}")] $(quote ghUrl))]
    let quoted := kind != "inline" && chapterQuotes chapterSrc name
    if quoted then
      inls := inls ++ #[← ``(Verso.Doc.Inline.text " · "),
        ← ``(Verso.Doc.Inline.other (Companion.Inline.modelQuoted $(quote name.toString))
              #[Verso.Doc.Inline.text "quoted in this chapter"])]
    inls := inls ++ tail
    let para ← ``(Verso.Doc.Block.para #[$inls,*])
    if quoted then return #[para]
    -- Not quoted here: the line opens to show the code.
    let text := "\n".intercalate ((site.lines.toList.drop (first - 1)).take (last + 1 - first))
    let body ← if kind == "inline" then
        ``(Verso.Doc.Block.code $(quote text))
      else match ← loadHighlighted? root site.mod name with
        | some hl =>
          let (hl, _) := stripDocComment hl
          let cfg : Verso.Code.External.CodeConfig := { defSite := some false }
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.lean $(quote hl) $(quote cfg))
              #[Verso.Doc.Block.code $(quote text)])
        | none => ``(Verso.Doc.Block.code $(quote text))
    return #[← ``(Verso.Doc.Block.other Companion.Block.modelDetails #[$para, $body])]

/-- The "In the model:" block for the equations `ns` of one display (`before`: the display
    follows). Empty when the chapter is not mapped yet; an error when a mapped chapter lacks an
    entry. Equations of one display that share an entry get one line. -/
def modelLines (ns : List String) (before : Bool) : TermElabM Term := do
  let chapter ← currentChapter
  let (m, required) ← loadModelMap chapter
  let src ← IO.FS.readFile (← getFileName)
  -- Group the display's equations by entry, in order of first appearance.
  let mut groups : Array (ModelEntry × List String) := #[]
  for n in ns do
    match m.get? n with
    | none =>
      if required then
        throwError m!"model map: equation ({n}) is displayed but has no entry in \
          docs/site/model-map/{chapter}.json (every displayed equation needs one)"
    | some e =>
      match groups.findIdx? (·.1 == e) with
      | some i => groups := groups.modify i fun (e, l) => (e, l ++ [n])
      | none => groups := groups.push (e, [n])
  let mut blocks : Array Term := #[]
  for (e, g) in groups do
    blocks := blocks ++ (← modelLineBlocks src g (groups.size > 1) e)
  if blocks.isEmpty then return ← ``(Verso.Doc.Block.concat #[])
  ``(Verso.Doc.Block.other (Companion.Block.modelLine $(quote before)) #[$blocks,*])

end Companion
