import VersoManual
import Companion.Source
import Companion.ModelMap

/-!
# Worked examples: the model run on a test vector

`{example "safrole-epoch-change"}` renders `docs/site/examples/safrole-epoch-change.json` as a box.
The box says which vector and parameters were used, lists the inputs, shows a table of values
(usually before → after), and ends with the notes, the model functions that computed the values
(linked to their API pages), the paper's equations the box illustrates, and how the result was
checked against the vector.

The JSON files are not written by hand. `Tests/Examples.lean` (`lake build examples-exe &&
.lake/build/bin/examples`) runs the model on the vectors and writes them, and fails unless the
vector's expected output matches. CI regenerates them and fails on any difference
(`scripts/check-examples.sh`), so a box always shows what the current model computes.

Text fields may contain `$…$` (inline math, with the paper's macros) and `` `…` `` (code). A
`model` name must be a declaration the chapter imports, and an `equations` entry must be an
equation of the paper (`gp-equations.json`): either mistake fails the build. A box whose table has
more than ten rows starts collapsed.
-/

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.Genre Manual

namespace Companion

/-- The box. `data` holds the title, whether it starts open, and the number of blocks in each part
    of `content`: the blocks before the table, the column headings, the rows (each a label and
    `cols - 1` cells), then the blocks after the table. Each heading and cell is one paragraph. -/
block_extension Block.workedExample (cfg : Json) where
  data := cfg
  traverse := fun _ _ _ => pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ go _ data content => do
      let num (k : String) : Nat := (data.getObjValAs? Nat k).toOption.getD 0
      let title := (data.getObjValAs? String "title").toOption.getD ""
      let isOpen := (data.getObjValAs? Bool "open").toOption.getD true
      let before := num "before"
      let cols := num "cols"
      let rows := num "rows"
      let intro ← (content.extract 0 before).mapM go
      let heads ← (content.extract before (before + cols)).mapM go
      let start := before + cols
      let mut body : Array Verso.Output.Html := #[]
      for r in [0:rows] do
        let label ← go content[start + r * cols]!
        let cells ← ((content.extract (start + r * cols + 1) (start + (r + 1) * cols)).mapM go)
        body := body.push html%{<tr><th scope="row">{label}</th>{cells.map fun c => html%{<td>{c}</td>}}</tr>}
      let after ← (content.extract (start + rows * cols) content.size).mapM go
      let table := html%{<div class="we-table-wrap"><table class="we-table">
          <thead><tr>{heads.map fun h => html%{<th scope="col">{h}</th>}}</tr></thead>
          <tbody>{body}</tbody></table></div>}
      let summary := html%{<summary><span class="we-tag">{Html.text "Worked example"}</span>{Html.text title}</summary>}
      let inner := html%{<div class="we-body">{intro}{table}{after}</div>}
      if isOpen then
        pure html%{<details class="worked-example" open="open">{summary}{inner}</details>}
      else
        pure html%{<details class="worked-example">{summary}{inner}</details>}

/-- A text field as inlines: `$…$` is inline math, `` `…` `` code, the rest text. -/
def exampleInlines (s : String) : TermElabM (Array Term) := do
  let mut out : Array Term := #[]
  let mut cur : String := ""
  let mut mode : Char := ' '  -- ' ' text, '$' math, '`' code
  for c in s.toList do
    if (c == '$' && mode != '`') || (c == '`' && mode != '$') then
      if c == mode then
        out := out.push <| ← if mode == '$' then ``(Verso.Doc.Inline.math Lean.Doc.MathMode.inline $(quote cur))
          else ``(Verso.Doc.Inline.code $(quote cur))
        cur := ""
        mode := ' '
      else
        if !cur.isEmpty then out := out.push (← ``(Verso.Doc.Inline.text $(quote cur)))
        cur := ""
        mode := c
    else
      cur := cur.push c
  unless mode == ' ' do throwError m!"example: unclosed {mode} in {s}"
  if !cur.isEmpty then out := out.push (← ``(Verso.Doc.Inline.text $(quote cur)))
  return out

def examplePara (inls : Array Term) : TermElabM Term := ``(Verso.Doc.Block.para #[$inls,*])

/-- The equation numbers of the paper (`gp-equations.json`). -/
def paperEquations : IO (Std.HashSet String) := do
  let root ← findRepoRoot
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile (root / "docs" / "site" / "gp-equations.json"))
  let eqs ← IO.ofExcept <| json.getObjVal? "equations"
  let some kvs := eqs.getObj?.toOption | throw <| IO.userError "gp-equations.json: equations"
  return kvs.foldl (init := {}) fun s n _ => s.insert n

structure ExampleArgs where
  name : String

instance : FromArgs ExampleArgs DocElabM :=
  ⟨ExampleArgs.mk <$> .positional `name (ValDesc.string.as "the example's name (string literal)")⟩

/-- `{example "safrole-epoch-change"}`: the worked example `docs/site/examples/<name>.json` as a box. -/
@[block_command]
def «example» : BlockCommandOf ExampleArgs
  | ⟨name⟩ => do
    let root ← findRepoRoot
    let file := root / "docs" / "site" / "examples" / s!"{name}.json"
    unless ← file.pathExists do
      throwError m!"example: {file} does not exist; run `lake build examples-exe && .lake/build/bin/examples` \
        from the repository root (Tests/Examples.lean writes it)"
    let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
    let str (k : String) : TermElabM String := match j.getObjValAs? String k with
      | .ok s => pure s
      | .error _ => throwError m!"example {name}: no string field {k}"
    let strs (k : String) : TermElabM (List String) := match j.getObjValAs? (List String) k with
      | .ok s => pure s
      | .error _ => throwError m!"example {name}: no string list {k}"
    let title ← str "title"
    let src ← IO.ofExcept <| j.getObjVal? "source"
    let repo ← IO.ofExcept <| src.getObjValAs? String "repo"
    let path ← IO.ofExcept <| src.getObjValAs? String "path"
    let url ← IO.ofExcept <| src.getObjValAs? String "url"
    -- Before the table: the source sentence, the summary, the inputs.
    let lead ← examplePara (#[← ``(Verso.Doc.Inline.text "The model run on the vector "),
        ← ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.code $(quote path)] $(quote url)),
        ← ``(Verso.Doc.Inline.text $(quote s!" ({repo}), with "))] ++
      (← exampleInlines (← str "params")) ++ #[← ``(Verso.Doc.Inline.text ".")])
    let summary ← examplePara (← exampleInlines (← str "summary"))
    let inputs ← IO.ofExcept <| j.getObjValAs? (Array Json) "inputs"
    let mut inputInls : Array Term := #[← ``(Verso.Doc.Inline.emph #[Verso.Doc.Inline.text "Inputs:"]),
      ← ``(Verso.Doc.Inline.text " ")]
    for (i, it) in inputs.toList.zipIdx do
      let l ← IO.ofExcept <| it.getObjValAs? String "label"
      let v ← IO.ofExcept <| it.getObjValAs? String "value"
      if i > 0 then inputInls := inputInls.push (← ``(Verso.Doc.Inline.text "; "))
      inputInls := inputInls ++ (← exampleInlines l) ++ #[← ``(Verso.Doc.Inline.text " = ")] ++ (← exampleInlines v)
    let before := #[lead, summary, ← examplePara inputInls]
    -- The table.
    let cols ← strs "columns"
    let heads ← cols.toArray.mapM fun c => do examplePara (← exampleInlines c)
    let rows ← IO.ofExcept <| j.getObjValAs? (Array Json) "rows"
    let mut cells : Array Term := #[]
    for r in rows do
      let l ← IO.ofExcept <| r.getObjValAs? String "label"
      let cs ← IO.ofExcept <| r.getObjValAs? (List String) "cells"
      unless cs.length + 1 == cols.length do
        throwError m!"example {name}: row {l} has {cs.length} cells for {cols.length} columns"
      cells := cells.push (← examplePara (← exampleInlines l))
      for c in cs do cells := cells.push (← examplePara (← exampleInlines c))
    -- After the table: notes, then the model, the equations and the check.
    let notes ← (← strs "notes").toArray.mapM fun n => do examplePara (← exampleInlines n)
    let mut modelInls : Array Term := #[← ``(Verso.Doc.Inline.emph #[Verso.Doc.Inline.text "Computed by"]),
      ← ``(Verso.Doc.Inline.text " ")]
    for (i, n) in (← strs "model").zipIdx do
      let site ← declSite n.toName
      let apiUrl := s!"{apiRoot}/{modulePath site.mod}.html#{n}"
      if i > 0 then modelInls := modelInls.push (← ``(Verso.Doc.Inline.text ", "))
      modelInls := modelInls.push (← ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.code $(quote n)] $(quote apiUrl)))
    let known ← paperEquations
    let eqs ← strs "equations"
    for e in eqs do
      unless known.contains e do
        throwError m!"example {name}: no equation {e} in the paper (docs/site/gp-equations.json)"
    unless eqs.isEmpty do
      modelInls := modelInls ++ #[← ``(Verso.Doc.Inline.text "; it illustrates "),
        ← ``(Verso.Doc.Inline.text $(quote (", ".intercalate (eqs.map fun e => s!"({e})"))))]
    modelInls := modelInls.push (← ``(Verso.Doc.Inline.text "."))
    let check ← examplePara (#[← ``(Verso.Doc.Inline.bold #[Verso.Doc.Inline.text "Checked:"]),
      ← ``(Verso.Doc.Inline.text " ")] ++ (← exampleInlines (← str "check")))
    let after := notes ++ #[← examplePara modelInls, check]
    let cfg := Json.mkObj [("title", title), ("open", Json.bool (rows.size ≤ 10)),
      ("before", before.size), ("cols", cols.length), ("rows", rows.size)]
    ``(Verso.Doc.Block.other (Companion.Block.workedExample $(quote cfg)) #[$(before ++ heads ++ cells ++ after),*])

end Companion
