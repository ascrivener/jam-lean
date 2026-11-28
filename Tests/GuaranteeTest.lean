import JAM.Guarantee
import Tests.RefineTest

/-!
# Work-package refinement (GP v0.8.1 §14): tests

No published vector covers bundles, availability specifiers or Ξ (davxy/jam-test-vectors master
has codec vectors for work packages and reports, which `codectest` runs, and erasure vectors, which
`erasuretest` runs, but nothing that ties a package to its report). So these are hand-built:

* the sized transpose ᵀ_m, including the empty case of GP #583;
* C on a small item;
* I's branch order (GP #568): an error result wins over oversize and a bad export count, oversize
  over a bad export count; zero segments on every error; z counts only the results I keeps; ℓ is
  the sum of the earlier items' w_e;
* B on a small package, written out by hand, and its decoding split per item;
* the bundle checks on genuine data and on tampered data;
* A: |**s**♣| = v, the 𝟬 columns with no exports, the erasure root recomputed from the erasure
  code directly;
* Ξ end to end with the services of `Tests.RefineTest`: success, a bad export count, a panic, and
  each ∇ case.
-/

namespace JAM.Tests.Guarantee

open JAM JAM.Guarantee
open JAM.Tests.Refine (acct echo exportThenHalt exportThenTrap item pkg codeHash)

def str (s : String) : List UInt8 := s.toUTF8.toList

/-- A "hash" that brackets its input: H(b) = "(" ⌢ b ⌢ ")". -/
def br (b : ByteArray) : ByteArray := ⟨(str "(" ++ b.toList ++ str ")").toArray⟩

def blake : ByteArray → ByteArray := Blake2b.hash256

/-! ## ᵀ_m -/

#guard sizedTranspose 3 0 [[1, 2, 3], [4, 5, 6]] == [[1, 4], [2, 5], [3, 6]]
#guard sizedTranspose 2 0 ([] : List (List Nat)) == [[], []]
#guard sizedTranspose 0 0 [[1, 2]] == []
-- Short rows are filled (never used by A, whose rows have v items).
#guard sizedTranspose 2 9 [[1], [2, 3]] == [[1, 2], [9, 3]]

/-! ## C -/

def w0 : WorkItem :=
  { service := 7, codeHash := ⟨#[1]⟩, payload := ⟨#[9, 9]⟩, refineGasLimit := 5,
    accumulateGasLimit := 6, exportCount := 2,
    importSegments := [(.root ⟨#[0]⟩, 0), (.package ⟨#[1]⟩, 3), (.root ⟨#[2]⟩, 1)],
    extrinsics := [(⟨#[3]⟩, 10), (⟨#[4]⟩, 32)] }

def d0 : WorkDigest := itemToDigest br w0 (.err .panic) 11

#guard d0.service == 7 && d0.codeHash.toList == [1] && d0.payloadHash.toList == str "(" ++ [9, 9] ++ str ")"
#guard d0.gasLimit == 6 && d0.gasUsed == 11 && d0.importCount == 3 && d0.exportCount == 2
#guard d0.extrinsicCount == 2 && d0.extrinsicSize == 42
#guard (match d0.result with | .err .panic => true | _ => false)

/-! ## p_a -/

#guard (WorkPackage.authorizer br { pkg with authConfig := ⟨#[5, 6]⟩ }).toList ==
  str "(" ++ codeHash ++ [5, 6] ++ str ")"

/-! ## I: the branch order of GP #568 -/

def seg (k : UInt8) : List UInt8 := List.replicate Constants.Csegmentsize k
def zeroSeg : List UInt8 := seg 0

def tag (o : ItemOut) : String :=
  match o.result with
  | .ok _ => "ok"
  | .err .oversize => "oversize"
  | .err .badExports => "badExports"
  | .err .panic => "panic"
  | .err _ => "other"

def big : ByteArray := ⟨(List.replicate 100 1).toArray⟩

-- An error result wins over everything else: kept, with m_e zero segments and Ψ_R's gas.
#guard let o := itemResult 50 w0 1000 ⟨.err .panic, [seg 1], 17⟩
  tag o == "panic" && o.exports == [zeroSeg, zeroSeg] && o.gasUsed == 17
-- Oversize (|r| + z > 𝖶_R) wins over a bad export count.
#guard let o := itemResult 50 w0 0 ⟨.ok big, [seg 1], 17⟩
  tag o == "oversize" && o.exports == [zeroSeg, zeroSeg] && o.gasUsed == 17
-- z counts: 100 + 0 ≤ 100 but 100 + 1 > 100.
#guard tag (itemResult 100 w0 0 ⟨.ok big, [seg 1, seg 2], 0⟩) == "ok"
#guard tag (itemResult 100 w0 1 ⟨.ok big, [seg 1, seg 2], 0⟩) == "oversize"
-- A bad export count: ⊚ with zero segments.
#guard let o := itemResult 1000 w0 0 ⟨.ok big, [seg 1], 17⟩
  tag o == "badExports" && o.exports == [zeroSeg, zeroSeg]
#guard tag (itemResult 1000 w0 0 ⟨.ok big, [seg 1, seg 2, seg 3], 0⟩) == "badExports"
-- Otherwise the result and the exports as given.
#guard let o := itemResult 1000 w0 0 ⟨.ok big, [seg 1, seg 2], 17⟩
  tag o == "ok" && o.exports == [seg 1, seg 2]

/-! ## I over a package: ℓ and z -/

def item1 (e : Nat) : WorkItem := { w0 with exportCount := e }

/-- A fake Ψ_R: item j outputs `outs[j]` octets and exports w_e segments tagged with ℓ. -/
def fake (items : List WorkItem) (outs : List Nat) (j ℓ : Nat) : RefineOut :=
  ⟨.ok ⟨(List.replicate (outs.getD j 0) 1).toArray⟩,
   List.replicate ((items.getD j w0).exportCount) (seg (UInt8.ofNat ℓ)), j⟩

def items3 : List WorkItem := [item1 1, item1 2, item1 1]

-- ℓ = 0, 1, 3: each item's exports carry the number of earlier exports.
#guard (refineItems 1000 (fake items3 [1, 1, 1]) items3 0).map (·.exports) ==
  [[seg 0], [seg 1, seg 1], [seg 3]]
-- z: with |t| = 10 and outputs 40, 60, 50 under 𝖶_R = 100, item 1 is oversize (10 + 40 + 60 > 100)
-- and adds nothing, so item 2 fits (10 + 40 + 50 ≤ 100).
#guard (refineItems 100 (fake items3 [40, 60, 50]) items3 10).map tag == ["ok", "oversize", "ok"]
#guard (refineItems 100 (fake items3 [40, 60, 50]) items3 10).map (·.exports.length) == [1, 2, 1]
#guard ((refineItems 100 (fake items3 [40, 60, 50]) items3 10).map (·.exports)).getD 1 [] ==
  [zeroSeg, zeroSeg]
-- The error result of an earlier item adds nothing to z either.
#guard (refineItems 100 (fun j ℓ => if j = 0 then ⟨.err .outOfGas, [], 0⟩ else fake items3 [0, 60, 30] j ℓ)
  items3 10).map tag == ["other", "ok", "ok"]

/-! ## B and its decoding -/

def h32 (k : UInt8) : ByteArray := ⟨(List.replicate 32 k).toArray⟩

/-- `pkg` of `Tests.RefineTest` with 32-octet context hashes, so that it decodes. -/
def pkg32 : WorkPackage :=
  { pkg with context := { anchorHash := h32 1, anchorSlot := 0, anchorStateRoot := h32 2,
                          anchorAccOutLog := h32 3, lookupAnchorHash := h32 4, lookupAnchorSlot := 10,
                          lookupAnchorStateRoot := h32 5 } }

def segA : List UInt8 := seg 0xa1
def segB : List UInt8 := seg 0xb2

def wb : WorkItem :=
  { service := 3, codeHash := ⟨codeHash.toArray⟩, payload := ⟨#[1]⟩, refineGasLimit := 1,
    accumulateGasLimit := 2, exportCount := 0,
    importSegments := [(.root ⟨(List.replicate 32 7).toArray⟩, 1), (.package ⟨(List.replicate 32 8).toArray⟩, 0)],
    extrinsics := [(⟨(Segments.hashL blake [1, 2, 3]).toArray⟩, 3)] }

def wc : WorkItem := { wb with importSegments := [], extrinsics := [(⟨(Segments.hashL blake [4]).toArray⟩, 1)] }

def pb : WorkPackage := { pkg32 with items := [wb, wc] }

def path1 : List (List UInt8) := [List.replicate 32 0x11, List.replicate 32 0x22]

def datab : List ItemData :=
  [⟨[[1, 2, 3]], [segA, segB], [path1, []]⟩, ⟨[[4]], [], []⟩]

-- The package, then the extrinsics (no prefixes), then the segments, then ↕ each path.
#guard bundle pb datab ==
  pb.encode ++ [1, 2, 3, 4] ++ segA ++ segB ++ ([2] ++ path1.flatten) ++ [0]

def roundTrip (p : WorkPackage) (data : List ItemData) : Bool :=
  match Decoder.run Bundle.decode ⟨(bundle p data).toArray⟩ with
  | .ok b => b.package.encode == p.encode && b.items == data
  | .error _ => false

#guard roundTrip pb datab
#guard roundTrip pkg32 [⟨[], [], []⟩]
-- Truncated or with trailing octets: no bundle.
#guard (match Decoder.run Bundle.decode ⟨((bundle pb datab).dropLast).toArray⟩ with
  | .ok _ => false | .error _ => true)
#guard (match Decoder.run Bundle.decode ⟨((bundle pb datab) ++ [0]).toArray⟩ with
  | .ok _ => false | .error _ => true)

/-! ## The bundle checks -/

/-- Three exported segments under one root, and two under another. -/
def exA : List (List UInt8) := [seg 1, seg 2, seg 3]
def exB : List (List UInt8) := [seg 4, seg 5]
def rootA : List UInt8 := Segments.cdRoot blake exA
def rootB : List UInt8 := Segments.cdRoot blake exB
def pkgHashB : List UInt8 := List.replicate 32 0x5b

def src : DataSource :=
  { preimage := fun h =>
      if h == Segments.hashL blake [1, 2, 3] then some [1, 2, 3]
      else if h == Segments.hashL blake [4] then some [4] else none,
    exports := fun r => if r == rootA then some exA else if r == rootB then some exB else none }

def wi : WorkItem :=
  { wb with importSegments := [(.root ⟨rootA.toArray⟩, 2), (.package ⟨pkgHashB.toArray⟩, 1),
                               (.root ⟨rootA.toArray⟩, 0)] }
def pi : WorkPackage := { pkg32 with items := [wi, wc] }
def li : OctetDict := Std.ExtTreeMap.ofList [(pkgHashB, rootB)]

def datai : List ItemData := (packageData blake src li pi).getD []

#guard datai.length == 2
#guard (datai.map (·.imports)) == [[seg 3, seg 5, seg 1], []]
#guard (datai.map (·.extrinsics)) == [[[1, 2, 3]], [[4]]]
#guard (datai.getD 0 ⟨[], [], []⟩).justifications ==
  [Segments.justify blake 0 exA 2, Segments.justify blake 0 exB 1, Segments.justify blake 0 exA 0]
#guard lookupMatches pi li
#guard checkBundle blake li ⟨pi, datai⟩
#guard (verifyBundle blake li (bundle pi datai)).isSome
#guard bundleOf blake src li pi == some (bundle pi datai)

def setImports (k : Nat) (ss : List (List UInt8)) : List ItemData :=
  datai.set k { datai.getD k ⟨[], [], []⟩ with imports := ss }

-- A wrong segment, a segment swapped with another, a short segment: rejected.
#guard !checkBundle blake li ⟨pi, setImports 0 [seg 9, seg 5, seg 1]⟩
#guard !checkBundle blake li ⟨pi, setImports 0 [seg 1, seg 5, seg 3]⟩
#guard !checkBundle blake li ⟨pi, setImports 0 [seg 3, seg 5, [1]]⟩
-- A missing segment: rejected.
#guard !checkBundle blake li ⟨pi, setImports 0 [seg 3, seg 5]⟩
-- A wrong justification: rejected.
#guard !checkBundle blake li ⟨pi, datai.set 0 { datai.getD 0 ⟨[], [], []⟩ with
  justifications := [Segments.justify blake 0 exA 1, Segments.justify blake 0 exB 1,
                     Segments.justify blake 0 exA 0] }⟩
-- A wrong extrinsic, or one too many: rejected.
#guard !checkBundle blake li ⟨pi, datai.set 1 { datai.getD 1 ⟨[], [], []⟩ with extrinsics := [[5]] }⟩
#guard !checkBundle blake li ⟨pi, datai.set 1 { datai.getD 1 ⟨[], [], []⟩ with extrinsics := [[4], [4]] }⟩
-- A dictionary with a missing, an extra, or a wrong entry: rejected.
#guard !checkBundle blake ∅ ⟨pi, datai⟩
#guard !lookupMatches pi (li.insert (List.replicate 32 1) rootA)
#guard !checkBundle blake (Std.ExtTreeMap.ofList [(pkgHashB, rootA)]) ⟨pi, datai⟩
-- Data for one item only: rejected.
#guard !checkBundle blake li ⟨pi, datai.take 1⟩
-- A data source whose segments do not match the root, or a dictionary without the package: no data.
#guard (packageData blake { src with exports := fun _ => some exB } li pi).isNone
#guard (packageData blake src ∅ pi).isNone
-- An index past the end of the exports: no data.
#guard (packageData blake src li { pi with items := [{ wi with importSegments := [(.root ⟨rootA.toArray⟩, 3)] }] }).isNone

/-! ## A -/

def v6 : Nat := 6

#guard pieceSize v6 == 6 && pieceSize 1023 == 684
#guard (segmentsClub blake [] v6) == List.replicate 6 JAM.zeroHash
#guard (segmentsClub blake exA v6).length == 6
#guard (segmentsClub blake exA 9).length == 9
#guard (bundleClub blake [1, 2, 3] v6).length == 6

/-- The erasure root recomputed from `Erasure.encode` directly: the bundle padded to 6 octets is
    coded into 6 chunks of 2 octets; the 3 segments and 1 paged-proof segment are each coded into
    6 chunks; chunk i of the bundle is hashed and followed by ℳ_B of chunk i of the 4 segments. -/
def erasureRootByHand (b : List UInt8) (s : List (List UInt8)) : List UInt8 :=
  let bc := ((Erasure.encode 6 ⟨(b ++ List.replicate (6 - b.length % 6) 0).toArray⟩).getD []).map
    (fun c => (blake c).toList)
  let all := s ++ Segments.pagedProofs blake s
  let sc := all.map fun x => ((Erasure.encode 6 ⟨x.toArray⟩).getD []).map (·.toList)
  let cols := (List.range 6).map fun i => Merkle.root blake (sc.map fun row => row.getD i [])
  Merkle.root blake ((bc.zip cols).map fun (x, y) => x ++ y)

#guard erasureRoot blake [1, 2, 3, 4] exA v6 == erasureRootByHand [1, 2, 3, 4] exA
#guard erasureRoot blake [1, 2, 3, 4] [] v6 ==
  Merkle.root blake ((((Erasure.encode 6 ⟨#[1, 2, 3, 4, 0, 0]⟩).getD []).map
    (fun c => (blake c).toList)).map (· ++ JAM.zeroHash))

def specA : AvailabilitySpec := availabilitySpec blake ⟨#[7]⟩ [1, 2, 3, 4] exA v6
#guard specA.packageHash.toList == [7] && specA.bundleLength == 4 && specA.erasureShards == 6
#guard specA.segmentRoot.toList == rootA && specA.segmentCount == 3

/-! ## Ξ end to end -/

/-- A service account with code `code` under hash `ch` (metadata "m"), requested and available
    from slot 0. -/
def svcAcct (ch code : List UInt8) : ServiceAccount :=
  let pre := Codec.nat 1 ++ [0x6d] ++ code
  ServiceAccount.requestSet
    { acct with codeHash := ch, preimages := Std.ExtTreeMap.ofList [(ch, pre)], entries := ∅,
                items := 0, octets := 0 } ch pre.length [0]

def authHash : List UInt8 := List.replicate 32 0xaa

/-- Service 3 runs `code`; service 4 hosts the authorizer `echo`. -/
def accts (code : List UInt8) : Accounts :=
  Std.ExtTreeMap.ofList [(3, svcAcct codeHash code), (4, svcAcct authHash echo)]

/-- `item` of `Tests.RefineTest` with export count e, authorized by `echo` on service 4. -/
def pkgE (e : Nat) : WorkPackage :=
  { pkg with authCodeHost := 4, authCodeHash := ⟨authHash.toArray⟩,
             items := [{ item with exportCount := e }] }

def xi (code : List UInt8) (e : Nat) (l : OctetDict := ∅) (v : Nat := 6) : Option WorkReport :=
  computeReport .tiny (accts code) (pkgE e) 1 l v [⟨[], [], []⟩]

def resultTag (r : WorkReport) : List String :=
  r.digests.map fun d => match d.result with
    | .ok _ => "ok" | .err .badExports => "badExports" | .err .panic => "panic"
    | .err .oversize => "oversize" | .err _ => "other"

-- `echo` as authorizer and refine, exporting nothing as declared: a report with the 𝟬 columns.
#guard match xi echo 0 with
  | some r => resultTag r == ["ok"] && r.spec.segmentCount == 0 &&
      r.spec.segmentRoot.toList == Segments.cdRoot blake [] &&
      r.spec.erasureRoot.toList == erasureRoot blake (bundle (pkgE 0) [⟨[], [], []⟩]) [] 6 &&
      r.spec.bundleLength == (bundle (pkgE 0) [⟨[], [], []⟩]).length &&
      r.spec.packageHash.toList == (blake ⟨(pkgE 0).encode.toArray⟩).toList &&
      r.authTrace.toList == [1, 0] && r.core == 1 && r.authGasUsed > 0 &&
      r.authorizerHash.toList == (WorkPackage.authorizer blake (pkgE 0)).toList &&
      (r.digests.map (·.exportCount)) == [0]
  | none => false
-- `echo` declared to export one segment but exporting none: ⊚, one zero segment.
#guard match xi echo 1 with
  | some r => resultTag r == ["badExports"] && r.spec.segmentCount == 1 &&
      r.spec.segmentRoot.toList == Segments.cdRoot blake [zeroSeg]
  | none => false
/-- Ψ_R's arguments **a** = ℰ(c, i, w_s, ↕w_y, ℋ(p)) for `pkgE e` on core 1. -/
def argsE (e : Nat) : List UInt8 :=
  Codec.nat 1 ++ Codec.nat 0 ++ Codec.nat 3 ++ Codec.var ⟨#[7, 8, 9]⟩ ++
    (blake ⟨(pkgE e).encode.toArray⟩).toList

-- `exportThenHalt` exports its arguments: kept.
#guard match xi exportThenHalt 1 with
  | some r => resultTag r == ["ok"] && r.spec.segmentCount == 1 &&
      r.spec.segmentRoot.toList ==
        Segments.cdRoot blake [argsE 1 ++ List.replicate (Constants.Csegmentsize - (argsE 1).length) 0]
  | none => false
-- `exportThenTrap` panics: ☇, one zero segment.
#guard match xi exportThenTrap 1 with
  | some r => resultTag r == ["panic"] && r.spec.segmentCount == 1 &&
      r.spec.segmentRoot.toList == Segments.cdRoot blake [zeroSeg]
  | none => false
-- ∇: no authorizer code, a trace over 𝖶_R, or a dictionary with keys nothing imports through.
#guard (computeReport .tiny ∅ (pkgE 0) 1 ∅ 6 [⟨[], [], []⟩]).isNone
#guard (computeReport { Params.tiny with maxReportVarSize := 1 } (accts echo) (pkgE 0) 1 ∅ 6
  [⟨[], [], []⟩]).isNone
#guard (xi echo 0 (Std.ExtTreeMap.ofList [(List.replicate 32 (1 : UInt8), List.replicate 32 (2 : UInt8))])).isNone

/-! ## The ancestor set -/

def hdr (k : Nat) : Header :=
  { parent := ⟨#[]⟩, priorStateRoot := ⟨#[]⟩, extrinsicHash := ⟨#[]⟩, slot := k, epochMark := none,
    winnersMark := none, offendersMark := [], authorIndex := 0, vrfSig := ⟨#[]⟩, sealSig := ⟨#[]⟩ }

def chainN (n : Nat) : Chain := (List.range n).foldl (fun c k => c.extend .tiny (hdr k)) ⟨[]⟩

#guard (chainN 5).ancestors.map (·.slot) == [0, 1, 2, 3, 4]
#guard (chainN 30).ancestors.length == Params.tiny.maxLookupAnchorAge
#guard (chainN 30).ancestors.map (·.slot) == (List.range 24).map (· + 6)

end JAM.Tests.Guarantee
