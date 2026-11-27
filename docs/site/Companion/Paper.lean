import VersoManual
import Companion.Source

/-!
# The Gray Paper's version and section numbers

Every reference the book makes to a part of the Gray Paper through these roles comes from one place:
`docs/site/gp-labels.json`, generated from the pinned paper by `scripts/gen_gp_labels.py` (the
paper's version, its commit, and its section labels with their numbers and titles). The book holds
no hand-written paper URL (`scripts/check-citations.py` rejects one).

* ``{gpchapter}`sec:blockproduction` ``: "§6 Block Production and Chain Growth (GP v0.8.1)".
* ``{gpsec}`sec:epochmarker` `` or ``{gpsec}`6.5` ``: the section's name ("§6.6", "§6.5", "Appendix A").
* `{gptag}[text]`: `text` linked to the pinned version's release.

An unknown label or number fails the build. The references are text for now: they link nowhere,
by decision (a reader of our own may come later). `GpTable.sectionUrl?` is the one place a link
target would be added.
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

/-- Where a reference to section `n` links: nowhere for now, by decision. The one place to add a
    link target (e.g. a reader of our own) later. -/
def GpTable.sectionUrl? (_t : GpTable) (_n : String) : Option String := none
/-- The release of the pinned version. -/
def GpTable.tagUrl (t : GpTable) : String :=
  s!"https://github.com/gavofyork/graypaper/releases/tag/v{t.version}"

/-- How the paper names a section: "§6.5", "§A.7", and "Appendix A" for a whole appendix. -/
def sectionName (n : String) : String :=
  if n.length == 1 && n.all Char.isUpper then s!"Appendix {n}" else s!"§{n}"

/-- The inline for a reference: `text`, linked when `GpTable.sectionUrl?` gives a target. -/
def sectionRef (t : GpTable) (n text : String) : TermElabM Term :=
  match t.sectionUrl? n with
  | some url => ``(Verso.Doc.Inline.link #[Verso.Doc.Inline.text $(quote text)] $(quote url))
  | none => ``(Verso.Doc.Inline.text $(quote text))

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
    sectionRef t n (sectionName n)
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
    sectionRef t n s!"{sectionName n}{if n.length == 1 && n.all Char.isUpper then ":" else ""} {title} (GP v{t.version})"
  | _, _ => throwError "gpchapter: expected exactly one code literal"

/-- `{gptag}[text]`: `text` linked to the pinned version's release. -/
@[role]
def gptag : RoleExpanderOf Unit
  | (), content => do
    let url := (← loadGpTable).tagUrl
    let content ← content.mapM elabInline
    ``(Verso.Doc.Inline.link #[$content,*] $(quote url))

end Companion
