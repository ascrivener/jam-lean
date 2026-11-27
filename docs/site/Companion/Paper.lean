import VersoManual
import Companion.Source

/-!
# Links to the Gray Paper

Every link from the book to the Gray Paper, and every section number it shows through these roles,
comes from one place: `docs/site/gp-labels.json`, generated from the pinned paper by
`scripts/gen_gp_labels.py` (the paper's version, its commit, and its section labels with their
numbers). The book holds no hand-written paper URL (`scripts/check-citations.py` rejects one).

* ``{gpsec}`sec:epochmarker` `` or ``{gpsec}`6.5` ``: the section's name ("§6.6", "§6.5", "Appendix A"),
  linked to the paper. An unknown label or number fails the build.
* ``{gpchapter}`sec:blockproduction` ``: "§6 Block Production and Chain Growth (GP v0.8.1)", linked.
* `{gp}[text]`: `text` linked to the paper (the pinned reader).
* `{gppdf}[text]`, `{gptag}[text]`: `text` linked to the release PDF, or to the release.

The links go to the Fluffy Labs reader pinned to the paper's commit (`#/<commit>`). The reader has
no section or equation anchors that can be formed from a number (its locations are opaque codes of
text selections), so a section link opens the pinned paper and its number says where to go.
-/

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.Genre Manual

namespace Companion

/-- The paper table (`gp-labels.json`): version, commit, section label ↦ number, number ↦ title. -/
structure GpTable where
  version : String
  commit : String
  sections : Std.HashMap String String
  titles : Std.HashMap String String

def loadGpTable : IO GpTable := do
  let root ← findRepoRoot
  let file := root / "docs" / "site" / "gp-labels.json"
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile file)
  let str (k : String) : IO String := IO.ofExcept <| json.getObjValAs? String k
  let obj (k : String) : IO (Std.HashMap String String) := do
    let o ← IO.ofExcept <| json.getObjVal? k
    let some kvs := (o.getObj?.toOption) | throw <| IO.userError s!"gp-labels.json: {k} is not an object"
    kvs.foldlM (init := {}) fun m key v => do
      let s ← IO.ofExcept v.getStr?
      return m.insert key s
  return { version := ← str "version", commit := ← str "commit",
           sections := ← obj "sections", titles := ← obj "titles" }

/-- The paper in the Fluffy Labs reader, pinned to the paper's commit. -/
def GpTable.readerUrl (t : GpTable) : String := s!"https://graypaper.fluffylabs.dev/#/{t.commit}"
/-- The release PDF of the pinned version. -/
def GpTable.pdfUrl (t : GpTable) : String :=
  s!"https://github.com/gavofyork/graypaper/releases/download/v{t.version}/graypaper-{t.version}.pdf"
/-- The release of the pinned version. -/
def GpTable.tagUrl (t : GpTable) : String :=
  s!"https://github.com/gavofyork/graypaper/releases/tag/v{t.version}"

/-- How the paper names a section: "§6.5", "§A.7", and "Appendix A" for a whole appendix. -/
def sectionName (n : String) : String :=
  if n.length == 1 && n.all Char.isUpper then s!"Appendix {n}" else s!"§{n}"

/-- The number of section `key`: a label in the table, or a number that names a section. -/
def GpTable.sectionNumber? (t : GpTable) (key : String) : Option String :=
  match t.sections.get? key with
  | some n => some n
  | none => if t.titles.contains key then some key else none

/-- `{gpsec}`label-or-number``: the paper's section ("§6.5", "Appendix A"), linked to the paper. -/
@[role]
def gpsec : RoleExpanderOf Unit
  | (), #[arg] => do
    let some { content := c, .. } := Lean.Doc.CodeView.of arg
      | throwErrorAt arg "gpsec: expected a code literal with a section label or number"
    let key := c.getVersoCode
    let t ← loadGpTable
    let some n := t.sectionNumber? key
      | throwErrorAt arg m!"gpsec: no section {key} in GP v{t.version} (docs/site/gp-labels.json)"
    ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.text $(quote (sectionName n))] $(quote t.readerUrl))
  | _, _ => throwError "gpsec: expected exactly one code literal"

/-- `{gpchapter}`label``: a chapter's pointer to its part of the paper, "§6 Block Production and
    Chain Growth (GP v0.8.1)", linked to the paper. -/
@[role]
def gpchapter : RoleExpanderOf Unit
  | (), #[arg] => do
    let some { content := c, .. } := Lean.Doc.CodeView.of arg
      | throwErrorAt arg "gpchapter: expected a code literal with a section label or number"
    let key := c.getVersoCode
    let t ← loadGpTable
    let some n := t.sectionNumber? key
      | throwErrorAt arg m!"gpchapter: no section {key} in GP v{t.version} (docs/site/gp-labels.json)"
    let title := (t.titles.get? n).getD ""
    let url := t.readerUrl
    ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.text $(quote s!"{sectionName n}{if n.length == 1 && n.all Char.isUpper then ":" else ""} {title} (GP v{t.version})")] $(quote url))
  | _, _ => throwError "gpchapter: expected exactly one code literal"

/-- `{gp}[text]`: `text` linked to the pinned paper (reader). -/
@[role]
def gp : RoleExpanderOf Unit
  | (), content => do
    let url := (← loadGpTable).readerUrl
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.link #[$content,*] $(quote url))

/-- `{gppdf}[text]`: `text` linked to the pinned version's release PDF. -/
@[role]
def gppdf : RoleExpanderOf Unit
  | (), content => do
    let url := (← loadGpTable).pdfUrl
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.link #[$content,*] $(quote url))

/-- `{gptag}[text]`: `text` linked to the pinned version's release. -/
@[role]
def gptag : RoleExpanderOf Unit
  | (), content => do
    let url := (← loadGpTable).tagUrl
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.link #[$content,*] $(quote url))

end Companion
