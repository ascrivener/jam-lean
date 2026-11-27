import Tests.StfRunner

/-!
# Worked examples: the shared types and formatting

The `Example` record that `Tests/Examples.lean` writes as `docs/site/examples/<name>.json`, and the
helpers the topic modules (`Tests/Examples/*.lean`) use to fill it in.
-/

namespace JAM.Tests.Examples

open Lean (Json ToJson toJson)


/-- One labelled value of a box's inputs line. -/
structure Item where
  label : String
  value : String
  deriving ToJson

/-- One table row: a label and one cell per column after the first. -/
structure Row where
  label : String
  cells : List String
  deriving ToJson

/-- Where a vector comes from. -/
structure Source where
  /-- The repository and its tag, as the box names it. -/
  repo : String
  /-- The vector's path inside the repository. -/
  path : String
  url : String
  deriving ToJson

/-- A worked example. Text fields may hold `$…$` (inline math, the paper's macros allowed) and
    `` `…` `` (code). -/
structure Example where
  name : String
  title : String
  source : Source
  /-- The chain parameters, in a phrase ("the tiny chain: …"). -/
  params : String
  /-- What the box shows, in a sentence or two. -/
  summary : String
  inputs : List Item
  /-- The column headings, the first over the row labels. -/
  columns : List String
  rows : List Row
  notes : List String := []
  /-- The model functions that computed the values (full names; the book links them). -/
  model : List String
  /-- The paper's equations the box illustrates (the book checks they exist). -/
  equations : List String
  /-- How the result was checked against the vector, in a sentence. -/
  check : String
  deriving ToJson

/-! ## Formatting -/

def hexd (b : List UInt8) : String := JAM.Tests.Stf.hexS b

/-- A hash or key, abbreviated to its first four octets: `0x1a2b3c4d…`. -/
def abbr (b : List UInt8) : String :=
  if b.length ≤ 4 then s!"`0x{hexd b}`" else s!"`0x{hexd (b.take 4)}…`"

def abbrB (b : ByteArray) : String := abbr b.toList

/-- `n` things, with the right plural. -/
def count (n : Nat) (one many : String) : String := if n == 1 then s!"1 {one}" else s!"{n} {many}"

/-- The label of the first candidate equal to `x`, as " (= label)". -/
def sameAs {α} [BEq α] (x : α) (cands : List (String × α)) : String :=
  match cands.find? (·.2 == x) with
  | some (l, _) => s!" (= {l} before)"
  | none => ""

def vectorUrl (repo tag path : String) : String := s!"https://github.com/{repo}/blob/{tag}/{path}"

def jamSource (path : String) : Source :=
  { repo := "davxy/jam-test-vectors v0.8.0", path,
    url := vectorUrl "davxy/jam-test-vectors" "v0.8.0" path }

def tinyParams (p : Params) : String :=
  s!"the tiny chain the v0.8.0 vectors were made with ($\\mathsf\{E}$ = {p.epochLen} slots per epoch, " ++
  s!"$\\mathsf\{Y}$ = {p.epochTailStart}, $\\mathsf\{C}$ = {p.coreCount} cores, 6 validators)"

end JAM.Tests.Examples
