import VersoManual

/-!
# `{mathdoc N}`: Verso's `{docstring N}` with math in docstrings

A copy of Verso's `docstring` block command (Verso `v4.36.0-rc1-patch1`,
`VersoManual/Docstring.lean`) that parses docstrings with MD4Lean's `MD_FLAG_LATEXMATHSPANS`, as
doc-gen4 does. `$…$` and `$$…$$` then become Verso math (rendered by KaTeX) instead of text in which
Markdown has already read `_` and `*` as emphasis. Everything else is Verso's code, unchanged.
-/

open Lean Elab
open Verso ArgParse Doc Elab
open Verso.Genre Manual
open Verso.Genre.Manual.Docstring
open Verso.Genre.Manual.Block.Docstring

namespace Companion

/-- GitHub-flavoured Markdown with LaTeX math spans, as doc-gen4 parses docstrings. -/
def mathFlags : UInt32 := MD4Lean.MD_DIALECT_GITHUB ||| MD4Lean.MD_FLAG_LATEXMATHSPANS

@[block_command]
def mathdoc : BlockCommandOf DocstringConfig
  | ⟨(x, name), allowMissing, hideFields, hideCtor, customLabel⟩ => do
    let opts : Options → Options := (verso.docstring.allowMissing.set · allowMissing)

    withOptions opts do
      Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
      let blockStx ←
        match ← getDocString? (← getEnv) name with
        | none => pure #[]
        | some docs =>
          let some ast := MD4Lean.parse docs mathFlags
            | throwErrorAt x "Failed to parse docstring as Markdown"

          ast.blocks.mapM (blockFromMarkdownWithLean [name])

      if !(← Docstring.getAllowDeprecated) && Lean.Linter.isDeprecated (← getEnv) name then
        Lean.logError m!"'{name}' is deprecated.\n\nSet option 'verso.docstring.allowDeprecated' to 'true' to allow documentation for deprecated names."

      let declType ← Block.Docstring.DeclType.ofName name (hideFields := hideFields) (hideStructureConstructor := hideCtor)

      let signature ← Signature.forName name

      let extras ← getExtras name declType

      let altNames ← getStoredSuggestions name

      ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature) $(quote customLabel) $(quote altNames.toArray)) #[$(blockStx ++ extras),*])
where
  getExtras (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match declType with
    | .structure isClass constructor? _ fieldInfo parents _ => do
      let ctorRow : Option Term ← constructor?.mapM fun constructor => do
        let header := if isClass then "Instance Constructor" else "Constructor"
        let sigDesc : Array Term ←
          if let some docs := constructor.docstring? then
            let some mdAst := MD4Lean.parse docs mathFlags
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
          else pure (#[] : Array Term)
        let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])

      let parentsRow : Option Term ← do
        if parents.isEmpty then pure none
        else
          let header := "Extends"
          let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
          some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])

      let fieldsRow : Option Term ← do
        let header := if isClass then "Methods" else "Fields"
        let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
        let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
          let inheritedFrom : Option Nat :=
            i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
          let sigDesc : Array Term ←
            if let some docs := i.docString? then
              let some mdAst := MD4Lean.parse docs mathFlags
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean <| name :: (constructor?.map ([·.name])).getD [])
            else
              pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.visibility) $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent))) #[$sigDesc,*])
        if fieldSigs.isEmpty then pure none
        else some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])

      pure <| ctorRow.toArray ++ parentsRow.toArray ++ fieldsRow.toArray
    | .inductive ctors .. => do
      let ctorSigs : Array Term ←
        -- Elaborate constructor docs in the type's NS
        ctors.mapM fun c => withTheReader Core.Context ({· with currNamespace := name}) do
          let sigDesc ←
            if let some docs := c.docstring? then
              let some mdAst := MD4Lean.parse docs mathFlags
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
            else pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
    | _ => pure #[]

end Companion
