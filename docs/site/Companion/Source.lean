import VersoManual
import SubVerso.Module

/-!
# Quoting the model's source in the companion

`{leanSource N}` shows the declaration `N` exactly as it stands in the model's source, with
semantic highlighting (hovers with types and docstrings, links between names):

* SubVerso's `highlighted` facet (from the `subverso` package Verso already requires) re-elaborates
  the model module and writes its commands as highlighted JSON; this package's `modelHighlights`
  target builds it for the modules the chapters quote, from `docs/site` and without touching the
  root package;
* the command whose `defines` contains `N` is shown, and Lean's stored declaration range for `N`
  (kept in the `.olean`) gives the file and lines for the heading's links.

Nothing is copied into the book, so a renamed or removed declaration fails the book's build, and an
edited one shows its new text.

Each quotation is headed by its file and lines, a link to that range on GitHub at the commit the
book was built from, and a link to the declaration's doc-gen4 page.

This avoids Verso's external-example mechanism, which would need the model's package to require
`subverso` and its sources to carry `-- ANCHOR:` comments; the model stays core+Std and untouched.
-/

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.Genre Manual
open SubVerso.Highlighting (Highlighted)

namespace Companion

/-- The model's repository on GitHub. -/
def repoUrl : String := "https://github.com/ascrivener/jam-lean"

/-- Where the doc-gen4 pages are served: the `api/` directory of the same Pages site. -/
def apiRoot : String := "https://ascrivener.github.io/jam-lean/api"

/-- The repository root, seen from the directory the book is elaborated in (`docs/site`, or the
    root itself): the nearest candidate holding the model's `lakefile.lean` and `JAM.lean`. -/
def findRepoRoot : IO System.FilePath := do
  for d in ["../..", "..", "."] do
    let p : System.FilePath := d
    if (← (p / "JAM.lean").pathExists) && (← (p / "PVM.lean").pathExists) then
      return p
  throw <| IO.userError "leanSource: cannot find the jam-lean repository root (JAM.lean, PVM.lean)"

/-- The commit the book is built from, for GitHub links; `main` if git cannot say. -/
def repoCommit (root : System.FilePath) : IO String := do
  try
    let out ← IO.Process.output { cmd := "git", args := #["-C", root.toString, "rev-parse", "HEAD"] }
    if out.exitCode == 0 then return out.stdout.trimAscii.copy else return "main"
  catch _ => return "main"

/-- The semantically highlighted command defining `name`, from SubVerso's JSON for `mod`
    (`.lake/build/highlighted/…`, built by this package's `modelHighlights` target). -/
def loadHighlighted (root : System.FilePath) (mod name : Name) : IO (Option Highlighted) := do
  let file := (mod.components.foldl (init := root / "docs" / "site" / ".lake" / "build" / "highlighted")
    fun d c => d / c.toString (escape := false)).addExtension "json"
  unless ← file.pathExists do
    throw <| IO.userError s!"leanSource: {file} is missing; add {mod} to `modelHighlights` in \
      docs/site/lakefile.lean"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
  let m ← IO.ofExcept <| SubVerso.Module.Module.fromJson? json
  return m.items.find? (·.defines.contains name) |>.map (·.code)

/-- `JAM.Theorems.Safrole` ↦ `JAM/Theorems/Safrole` -/
def modulePath (mod : Name) : String :=
  "/".intercalate (mod.components.map (·.toString (escape := false)))

structure SourceConfig where
  name : Ident × Name

instance : FromArgs SourceConfig DocElabM :=
  ⟨SourceConfig.mk <$> .positional `name .documentableName⟩

/-- `{leanSource N}`: the source text of declaration `N`, read from the model's file. -/
@[block_command]
def leanSource : BlockCommandOf SourceConfig
  | ⟨(x, name)⟩ => do
    let env ← getEnv
    let some idx := env.getModuleIdxFor? name
      | throwErrorAt x m!"leanSource: {name} is not defined in an imported module"
    let some mod := env.header.moduleNames[idx.toNat]?
      | throwErrorAt x m!"leanSource: no module for {name}"
    let some ranges ← findDeclarationRanges? name
      | throwErrorAt x m!"leanSource: no declaration range stored for {name}"
    let root ← findRepoRoot
    let rel := modulePath mod ++ ".lean"
    let file := root / rel
    unless ← file.pathExists do
      throwErrorAt x m!"leanSource: {name} is defined in {mod}, but {file} does not exist"
    let lines := (← IO.FS.readFile file).splitOn "\n"
    let first := ranges.range.pos.line
    let last := ranges.range.endPos.line
    let text := "\n".intercalate ((lines.drop (first - 1)).take (last + 1 - first))
    let commit ← repoCommit root
    let ghUrl := s!"{repoUrl}/blob/{commit}/{rel}#L{first}-L{last}"
    let apiUrl := s!"{apiRoot}/{modulePath mod}.html#{name}"
    let label := s!"{rel}, lines {first}–{last}"
    let cfg : Verso.Code.External.CodeConfig := { defSite := some false }
    let some hl ← loadHighlighted root mod name
      | throwErrorAt x m!"leanSource: no command defining {name} in SubVerso's JSON for {mod}"
    ``(Verso.Doc.Block.concat #[
        Verso.Doc.Block.para #[
          Verso.Doc.Inline.code $(quote name.toString),
          Verso.Doc.Inline.text $(quote s!" — {label} · "),
          Verso.Doc.Inline.link #[Verso.Doc.Inline.text "GitHub"] $(quote ghUrl),
          Verso.Doc.Inline.text " · ",
          Verso.Doc.Inline.link #[Verso.Doc.Inline.text "API"] $(quote apiUrl)],
        Verso.Doc.Block.other (Verso.Genre.Manual.Block.lean $(quote hl) $(quote cfg))
          #[Verso.Doc.Block.code $(quote text)]])

end Companion
