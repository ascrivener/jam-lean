import Tests.Examples.Basic
import Tests.BlockJson
import JAM.Trie
import JAM.Shuffle
import JAM.Erasure

/-!
# Worked examples for Appendices C, D, F and H

The codec (ℰ, Appendix C), the state trie (M, Appendix D), the shuffle (ℱ, Appendix F) and the
erasure code (Appendix H), each run on vectors of davxy/jam-test-vectors `v0.8.0`. Each example first
checks the vector with the comparison its suite makes (`codectest`, `trietest`, `shuffletest`,
`erasuretest`) and stops if the model disagrees. Every value it shows is computed by the model.
-/

namespace JAM.Tests.Examples

open Lean (Json)
open PVM.Tests (field natField readJson)
open JAM.Tests.Json (hex hexField)

/-- Octets as `04 03 02 01`; longer runs as their first four and last `tail` octets. -/
def octets (b : List UInt8) (tail : Nat := 2) : String :=
  let h (x : UInt8) : String := JAM.Tests.Stf.hexS [x]
  let sp (xs : List UInt8) := " ".intercalate (xs.map h)
  if b.length ≤ 8 then s!"`{sp b}`"
  else s!"`{sp (b.take 4)} … {sp (b.drop (b.length - tail))}`"

/-- The octet offsets a piece of `n` octets occupies when it starts at `o`. -/
def span (o n : Nat) : String := if n == 1 then toString o else s!"{o}–{o + n - 1}"

/-! ## Appendix C: the codec -/

def codecDir : System.FilePath := "vendor/jam-test-vectors/codec/tiny"

/-- One piece of an encoding: what it encodes, the value, its octets (computed by the model), and
    the rule that produced them. -/
structure Piece where
  label : String
  value : String
  enc : List UInt8
  rule : String
  /-- How many final octets a long encoding shows. -/
  tail : Nat := 2

def ruleNat : String := "$\\mathcal{E}$ (C.6)"
def ruleFixed (l : Nat) : String := s!"$\\mathcal\{E}_{l}$ (C.13)"
def ruleBlob : String := "itself (C.1)"

/-- The rows for a list of pieces, with each piece's offsets in the whole encoding. -/
def pieceRows (ps : List Piece) : List Row := Id.run do
  let mut o := 0
  let mut rows := #[]
  for p in ps do
    rows := rows.push { label := p.label, cells := [p.value, span o p.enc.length, octets p.enc p.tail, p.rule] }
    o := o + p.enc.length
  return rows.toList

/-- Run one codec vector as `codectest` does: encode the term read from the JSON and decode the
    `.bin` and encode again; both must give the `.bin` exactly. Returns the term and the octets. -/
def codecVector {α : Type} (name : String) (j : Json → Except String α) (d : Decoder α)
    (e : α → List UInt8) : IO (α × List UInt8) := do
  let bin ← IO.FS.readBinFile (codecDir / s!"{name}.bin")
  let js ← readJson (codecDir / s!"{name}.json")
  let some x := (j js).toOption | throw <| IO.userError s!"examples: codec {name}: cannot read the JSON"
  unless e x == bin.toList do throw <| IO.userError s!"examples: codec {name}: ℰ differs from the .bin"
  let some y := (Decoder.run d bin).toOption | throw <| IO.userError s!"examples: codec {name}: ℰ⁻¹ rejects the .bin"
  unless e y == bin.toList do throw <| IO.userError s!"examples: codec {name}: the round trip differs"
  return (x, bin.toList)

def codecCheck (name : String) : String :=
  s!"The pieces above, joined in order, are the model's encoding, and it equals the vector's `{name}.bin` \
    octet for octet. The model's decoder also reads the `.bin` back to a term that encodes to the same \
    octets. `lake build codectest` makes both comparisons on every codec vector."

/-- The pieces must join up to the model's whole encoding. -/
def checkPieces (name : String) (ps : List Piece) (whole : List UInt8) : IO Unit :=
  unless (ps.flatMap (·.enc)) == whole do
    throw <| IO.userError s!"examples: codec {name}: the pieces do not join up to the encoding"

def codecPreimages : IO Example := do
  let name := "preimages_extrinsic"
  let (xs, bin) ← codecVector name (JAM.Tests.Json.items · JAM.Tests.Json.preimage) decodePreimages encodePreimages
  let ps : List Piece :=
    { label := "Number of preimages", value := toString xs.length, enc := Codec.nat xs.length, rule := ruleNat } ::
    (xs.zipIdx.flatMap fun (p, i) => [
      { label := s!"Preimage {i + 1}: requester $s$", value := toString p.requester,
        enc := Codec.fixed 4 p.requester, rule := ruleFixed 4 },
      { label := s!"Preimage {i + 1}: length of $\\mathbf\{p}$", value := toString p.blob.size,
        enc := Codec.nat p.blob.size, rule := ruleNat },
      { label := s!"Preimage {i + 1}: data $\\mathbf\{p}$", value := count p.blob.size "octet" "octets",
        enc := Codec.blob p.blob, rule := ruleBlob }])
  checkPieces name ps (encodePreimages xs)
  return {
    name := "codec-preimages", title := "Encoding a short sequence: the preimages extrinsic",
    source := jamSource s!"codec/tiny/{name}.json", params := "no chain parameters: the codec alone",
    summary := s!"The preimages extrinsic $\\mathbf\{E}_P$ is a sequence of pairs (service, data). \
      Its encoding $\\mathcal\{E}(\\updownarrow[(\\mathcal\{E}_4(s), \\updownarrow\\mathbf\{p})])$ starts with the \
      number of pairs; each pair is the service as four octets, then the data's length, then the data. \
      This vector's {xs.length} preimages encode to {bin.length} octets.",
    inputs := [
      { label := "Preimages $\\mathbf{E}_P$", value := toString xs.length },
      { label := "Encoded size", value := count bin.length "octet" "octets" }],
    columns := ["", "Value", "Octets at", "Encoding", "Rule"],
    nowrapColumns := [2, 3],
    rows := pieceRows ps,
    notes := ["Every number below 128 is a single octet under $\\mathcal{E}$ (the case $x < 2^7$ of eq. C.6), so the \
      count 3 and the length 16 are the octets `03` and `10`. Larger numbers take two to nine octets, the \
      first of which says how many follow.",
      "$\\mathcal{E}_4$ writes the least significant octet first: 16909060 is `0x01020304`, written `04 03 02 01`.",
      "A long run shows its first four and last two octets; \"Octets at\" gives its place in the encoding."],
    model := ["JAM.encodePreimages", "JAM.Codec.varSeq", "JAM.Codec.var", "JAM.Codec.nat", "JAM.Codec.fixed", "JAM.Codec.blob"],
    equations := ["C.1", "C.6", "C.7", "C.8", "C.13", "C.19"],
    check := codecCheck name }

def importDesc : SegmentRoot × Nat → String
  | (.root h, i) => s!"root {abbrB h}, index {i}"
  | (.package h, i) => s!"package {abbrB h}, index {i}"

def codecWorkItem : IO Example := do
  let name := "work_item"
  let (w, bin) ← codecVector name JAM.Tests.Json.workItem WorkItem.decode WorkItem.encode
  let ps : List Piece := [
    { label := "Service $s$", value := toString w.service, enc := Codec.fixed 4 w.service, rule := ruleFixed 4 },
    { label := "Code hash $c$", value := abbrB w.codeHash, enc := Codec.blob w.codeHash, rule := ruleBlob },
    { label := "Refine gas limit $g$", value := toString w.refineGasLimit, enc := Codec.fixed 8 w.refineGasLimit, rule := ruleFixed 8 },
    { label := "Accumulate gas limit $a$", value := toString w.accumulateGasLimit, enc := Codec.fixed 8 w.accumulateGasLimit, rule := ruleFixed 8 },
    { label := "Exported segments $e$", value := toString w.exportCount, enc := Codec.fixed 2 w.exportCount, rule := ruleFixed 2 },
    { label := "Payload $\\mathbf{y}$, with its length", value := count w.payload.size "octet" "octets",
      enc := Codec.var w.payload, rule := "$\\updownarrow$ (C.8)" },
    { label := "Number of imports $|\\mathbf{i}|$", value := toString w.importSegments.length,
      enc := Codec.nat w.importSegments.length, rule := ruleNat }] ++
    (w.importSegments.zipIdx.map fun (x, k) =>
      { label := s!"Import {k + 1}", value := importDesc x, enc := encodeImport x,
        rule := "$I$ (C.39)" }) ++
    [{ label := "Number of extrinsics $|\\mathbf{x}|$", value := toString w.extrinsics.length,
       enc := Codec.nat w.extrinsics.length, rule := ruleNat }] ++
    (w.extrinsics.zipIdx.map fun ((h, l), k) =>
      { label := s!"Extrinsic {k + 1}", value := s!"hash {abbrB h}, length {l}",
        enc := Codec.blob h ++ Codec.fixed 4 l, tail := 4, rule := "itself, $\\mathcal{E}_4$" })
  checkPieces name ps (WorkItem.encode w)
  return {
    name := "codec-work-item", title := "Encoding a structure: a work item",
    source := jamSource s!"codec/tiny/{name}.json", params := "no chain parameters: the codec alone",
    summary := s!"A work item encodes as its fields in a fixed order: fixed-width numbers in $\\mathcal\{E}_4$, \
      $\\mathcal\{E}_8$ and $\\mathcal\{E}_2$, hashes as themselves, and the variable-length parts (the payload, \
      the imports, the extrinsics) each preceded by their length. This vector's item encodes to {bin.length} octets.",
    inputs := [
      { label := "Service $s$", value := toString w.service },
      { label := "Payload $\\mathbf{y}$", value := octets w.payload.toList },
      { label := "Imports, extrinsics", value := s!"{w.importSegments.length}, {w.extrinsics.length}" }],
    columns := ["", "Value", "Octets at", "Encoding", "Rule"],
    nowrapColumns := [2, 3],
    rows := pieceRows ps,
    notes := ["$\\updownarrow$ puts $\\mathcal{E}$ of the length before the payload. $I$ writes an import's root as itself, then its index in $\\mathcal{E}_2$; \
      an extrinsic is its hash, then its length in $\\mathcal{E}_4$.",
      "Long runs show their first four octets and their last few.",
      "Every count and length here is below 128, so $\\mathcal{E}$ writes each as one octet (eq. C.6)."],
    model := ["JAM.WorkItem.encode", "JAM.encodeImport", "JAM.Codec.var", "JAM.Codec.varSeq", "JAM.Codec.nat", "JAM.Codec.fixed", "JAM.Codec.blob"],
    equations := ["C.6", "C.8", "C.13", "C.34", "C.39"],
    check := codecCheck name }

/-! ## Appendix D: the state trie -/

def trieFile : System.FilePath := "vendor/jam-test-vectors/trie/trie.json"

/-- The entries of a trie vector's case, with each key cut to 31 octets, as `trietest` does. -/
def trieCase (j : Json) : Except String (List (List UInt8 × List UInt8) × List UInt8) := do
  let .obj kvs := ← field j "input" | throw "input is not an object"
  let entries ← kvs.toArray.toList.mapM fun (k, v) => do
    let key ← hex (Json.str k)
    if key.size ≠ 32 then throw s!"key of {key.size} octets"
    return ((key.toList.take 31), (← hex v).toList)
  let keys := entries.map (·.1)
  if keys.eraseDups.length ≠ keys.length then throw "two keys share their first 31 octets"
  let expected ← hex (← (← field j "output").getStr?)
  return (entries, expected.toList)

def bitsOf (k : List UInt8) (n : Nat) : String :=
  String.ofList ((List.range n).map fun i => if Trie.bit k i then '1' else '0')

def trieExample (case : Nat) : IO Example := do
  let j ← readJson trieFile
  let some c := (j.getArr?.toOption.bind (·[case]?)) | throw <| IO.userError "examples: no trie case"
  let some (entries, expected) := (trieCase c).toOption | throw <| IO.userError "examples: cannot read the trie case"
  let got := Trie.root (Std.ExtTreeMap.ofList entries)
  unless got == expected do throw <| IO.userError s!"examples: trie case {case}: the root differs"
  -- The levels of the recursion of M, from the root down, while both halves are not single leaves.
  let zero := Trie.zeroHash
  let name (h : List UInt8) := if h == zero then "$\\mathbb{H}_0$ (empty)" else abbr h
  let leafRow (k v : List UInt8) : Row :=
    let n := Trie.leaf k v
    let kind := if v.length ≤ 32 then s!"embedded: the {v.length}-octet value, padded to 32"
      else s!"regular: $\\mathcal\{H}(v)$ of the {v.length}-octet value"
    { label := s!"Leaf $L(k, v)$ for $k$ = {abbr k}",
      cells := [kind, octets (n.take 1), abbr (Trie.hashNode n)] }
  let mut levels : Array Row := #[]
  let mut d := entries
  let mut depth := 0
  for _ in [0:248] do
    if d.length ≤ 1 then break
    let l := d.filter fun (k, _) => !Trie.bit k depth
    let r := d.filter fun (k, _) => Trie.bit k depth
    let ml := Trie.merkle (248 - depth - 1) (depth + 1) l
    let mr := Trie.merkle (248 - depth - 1) (depth + 1) r
    let node := Trie.branch ml mr
    let h := Trie.merkle (248 - depth) depth d
    unless h == Trie.hashNode node do throw <| IO.userError "examples: the branch does not hash to M"
    let row : Row := ⟨s!"Branch $B(l, r)$ on bit {depth}", [s!"$l$ = {name ml}, $r$ = {name mr}", octets (node.take 1), abbr h]⟩
    levels := levels.push row
    d := if l.length ≥ r.length then l else r
    depth := depth + 1
  let leaves := entries.map fun (k, v) => leafRow k v
  let keyItems := entries.map fun (k, v) =>
    ({ label := s!"Key {abbr k}", value := s!"first bits `{bitsOf k (depth + 1)}`, value of {v.length} octets" } : Item)
  return {
    name := "trie-two-keys", title := "The root of a small state trie",
    source := jamSource "trie/trie.json", params := s!"no chain parameters: case {case} of the trie vectors",
    summary := s!"{count entries.length "key" "keys"} that agree on their first {depth - 1} bits. $M$ splits the \
      entries on one bit at each level. While both keys fall on the same side, the other side is empty \
      ($\\mathbb\{H}_0$). At bit {depth - 1} they part, and each becomes a leaf. The root is the hash of the top branch.",
    inputs := keyItems,
    columns := ["Node", "Contents", "First octet", "Hash $\\mathcal{H}$ of the node"],
    nowrapColumns := [2, 3],
    rows := leaves ++ levels.toList.reverse ++ [{ label := "Root $M(d)$", cells := ["the top branch's hash", "", abbr got] }],
    notes := ["Every node is 64 octets. The first bit says what it is: a branch has 0, a leaf 1. An embedded-value leaf's first octet is \
      $2^7$ plus the value's length; a regular leaf's is $2^7 + 2^6$ = `c0`. A branch is its two children's hashes, with \
      the left one's first bit cleared, so its first octet is the left child's first octet without its high bit. \
      $l$ is the root of the entries whose bit is 0, $r$ of those whose bit is 1.",
      "The vectors' keys are 32 octets; as in `trietest`, the model is given their first 31, the paper's state-key length."],
    model := ["JAM.Trie.root", "JAM.Trie.merkle", "JAM.Trie.branch", "JAM.Trie.leaf", "JAM.Trie.hashNode", "JAM.Trie.bit"],
    equations := ["D.3", "D.4", "D.5", "D.6"],
    check := "The model's root equals the vector's expected root (the comparison `lake build trietest` makes on every \
      trie vector). Each branch row's hash is $M$ of the entries below it, computed by the model's `merkle`." }

/-! ## Appendix F: the shuffle -/

def shuffleFile : System.FilePath := "vendor/jam-test-vectors/shuffle/shuffle_tests.json"

def showList (xs : List Nat) : String := "[" ++ ", ".intercalate (xs.map toString) ++ "]"

def shuffleExample (case : Nat) : IO Example := do
  let j ← readJson shuffleFile
  let some c := (j.getArr?.toOption.bind (·[case]?)) | throw <| IO.userError "examples: no shuffle case"
  let some (n, h, expected) := (do
      let n ← natField c "input"
      let h ← hexField c "entropy"
      let e ← (← JAM.Tests.Json.arr c "output").mapM (fun (x : Json) => x.getNat?)
      return (n, h, e.toList) : Except String (Nat × ByteArray × List Nat)).toOption
    | throw <| IO.userError "examples: cannot read the shuffle case"
  let s0 := List.range n
  let got := Shuffle.shuffleHash s0 h
  unless h.size == 32 && got == expected do throw <| IO.userError s!"examples: shuffle case {case}: the order differs"
  let r0 := Shuffle.seqFromHash n h
  -- ℱ (eq. F.1), one step at a time; each step must agree with the model's `shuffle`.
  let mut rows : Array Row := #[]
  let mut s := s0
  let mut r := r0
  for k in [0:n] do
    let l := s.length
    let x := r.headD 0
    let i := x % l
    let picked := s.getD i 0
    let s' := (s.set i (s.getLastD 0)).take (l - 1)
    unless Shuffle.shuffle s r == picked :: Shuffle.shuffle s' r.tail do
      throw <| IO.userError "examples: a shuffle step disagrees with the model"
    let row : Row := ⟨toString (k + 1), [showList s, toString x, s!"{i}", toString picked,
        if i + 1 == l then "it was last: dropped" else s!"last ({s.getLastD 0}) → position {i}"]⟩
    rows := rows.push row
    s := s'
    r := r.tail
  return {
    name := "shuffle-eight", title := "Shuffling eight indices",
    source := jamSource "shuffle/shuffle_tests.json", params := s!"no chain parameters: case {case} of the shuffle vectors",
    summary := s!"$\\mathcal\{F}([0, \\dots, {n - 1}], h)$: the entropy $h$ is stretched into {n} numbers $\\mathcal\{Q}_{n}(h)$, \
      and each step uses the next one to pick an element of what is left.",
    inputs := [
      { label := "Sequence $\\mathbf{s}$", value := showList s0 },
      { label := "Entropy $h$", value := abbrB h },
      { label := s!"$\\mathcal\{Q}_{n}(h)$", value := showList r0 }],
    columns := ["Step", "Left $\\mathbf{s}$", "$\\mathbf{r}_0$", "$\\mathbf{r}_0 \\bmod l$", "Picked", "Then"],
    nowrapColumns := [1, 2, 3],
    rows := rows.toList ++ [{ label := "Result", cells := [showList got, "", "", "", ""] }],
    notes := ["$l$ is the length of what is left. The picked element is replaced by the last one, the last position is \
      dropped, and $\\mathbf{r}$ moves on by one, as in eq. F.1.",
      s!"The {n} numbers of $\\mathcal\{Q}_{n}(h)$ are the eight four-octet words of $\\mathcal\{H}(h \\frown \\mathcal\{E}_4(0))$ (eq. F.2)."],
    model := ["JAM.Shuffle.shuffleHash", "JAM.Shuffle.shuffle", "JAM.Shuffle.seqFromHash"],
    equations := ["F.1", "F.2", "F.3"],
    check := "The model's result equals the vector's expected order (the comparison `lake build shuffletest` makes on \
      every shuffle vector), and each step above agrees with the model's `shuffle` on what is left." }

/-! ## Appendix H: erasure coding -/

def erasureDir : System.FilePath := "vendor/jam-test-vectors/erasure/tiny"

def erasureExample (file : String) (subsets : List (List Nat)) : IO Example := do
  let v := 6
  let j ← readJson (erasureDir / file)
  let some (data, shards) := (do
      let data ← hexField j "data"
      let shards := (← (← JAM.Tests.Json.arr j "shards").mapM JAM.Tests.Json.hex).toList.map (·.toList)
      return (data, shards) : Except String (ByteArray × List (List UInt8))).toOption
    | throw <| IO.userError s!"examples: {file}: cannot read the vector"
  let d := Erasure.originalShards v
  let padded := data ++ ⟨Array.replicate ((2 * d - data.size % (2 * d)) % (2 * d)) 0⟩
  let some got := Erasure.encode v padded | throw <| IO.userError s!"examples: {file}: encode rejected the data"
  unless got.map (·.toList) == shards do throw <| IO.userError s!"examples: {file}: the chunks differ"
  let chunkRow (c : ByteArray) (i : Nat) : Row :=
    { label := s!"Chunk {i} (validator {i})",
      cells := [octets c.toList, if i < d then s!"data: octets {2 * i}–{2 * i + 1} of the padded data" else "parity"] }
  let mut recRows : Array Row := #[]
  for sub in subsets do
    let chunks := sub.map fun i => (got.getD i ⟨#[]⟩, i)
    let some r := Erasure.recover v chunks | throw <| IO.userError s!"examples: {file}: recover rejected {sub}"
    unless r == padded do throw <| IO.userError s!"examples: {file}: recovery from {sub} differs"
    let row : Row := ⟨s!"$\\mathcal\{R}^{v}_1$ from chunks {", ".intercalate (sub.map toString)}", [octets r.toList, "the padded data"]⟩
    recRows := recRows.push row
  return {
    name := "erasure-tiny", title := "Erasure coding for six validators: three octets into six chunks, and back",
    source := jamSource s!"erasure/tiny/{file}",
    params := s!"$v$ = {v} validators, so $\\mathcal\{D}(v)$ = {d}: any {d} of the {v} chunks recover the data",
    summary := s!"The data $\\mathbf\{d}$, {count data.size "octet" "octets"}, is padded with zeroes to a multiple of $2\\mathcal\{D}(v)$ = {2 * d} octets, \
      so it is one word (two octets) for each of {d} runs. The code $\\mathcal\{C}^{v}_1$ is systematic: the first {d} chunks are the data itself, \
      and the other {v - d} are parity. Any {d} chunks give the data back.",
    inputs := [
      { label := "Data $\\mathbf{d}$", value := octets data.toList },
      { label := "Padded data", value := octets padded.toList }],
    columns := ["", "Octets", "What it is"],
    nowrapColumns := [1],
    rows := (got.zipIdx.map fun (c, i) => chunkRow c i) ++ recRows.toList,
    notes := ["Each chunk is one word because the padded data is one word per run ($k$ = 1). Longer data gives each chunk one \
      word per piece, with the same code applied to every piece.",
      "The first recovery uses only parity chunks, so the model interpolates through the field of §H.2; the second mixes data and parity."],
    model := ["JAM.Erasure.encode", "JAM.Erasure.recover", "JAM.Erasure.originalShards"],
    equations := ["H.1", "H.5", "H.6", "H.13"],
    check := "The model's six chunks equal the vector's shards (the comparison `lake build erasuretest` makes on every \
      erasure vector), and recovering from each subset above gives the padded data back." }

/-- The examples of this module, listed in `Tests/Examples.lean`'s `examples`. -/
def appendixExamples : List (IO Example) :=
  [codecPreimages, codecWorkItem, trieExample 8, shuffleExample 1, erasureExample "ec-3.json" [[3, 4, 5], [1, 3, 5]]]

end JAM.Tests.Examples
