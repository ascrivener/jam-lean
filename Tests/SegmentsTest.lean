import JAM.Segments
import JAM.Blake2b

/-!
# Constant-depth Merkle trees and segment justifications: tests

No published vector carries segments together with their segment root or justifications
(davxy/jam-test-vectors v0.8.0 and master have none), so these are:

* small cases computed by hand with an unhashing "hash" that brackets its input, so the expected
  trees can be read off;
* the same small cases with Blake2b, written out with explicit hash calls;
* Blake2b values from an independent Python reading of GP v0.8.1 Appendix E and eq. `pagedproofs`
  (with `hashlib.blake2b`), for ℳ on 0–8 segments of 𝖶_G octets, a J_0 justification, and P on 130
  short segments;
* exhaustive checks of the verification functions and of the theorems' statements on small sizes,
  including tampered inputs.
-/

namespace JAM.Tests.Segments
open JAM.Segments

def str (s : String) : List UInt8 := s.toUTF8.toList

/-- A "hash" that brackets its input: H(b) = "(" ⌢ b ⌢ ")". -/
def br (b : ByteArray) : ByteArray := ⟨(str "(" ++ b.toList ++ str ")").toArray⟩

def z : List UInt8 := zeroHash
def lf (s : String) : List UInt8 := str "(leaf" ++ str s ++ str ")"
def nd (l r : List UInt8) : List UInt8 := str "(node" ++ l ++ r ++ str ")"

/-! ## C, ℳ, T, J_x, L_x by hand -/

#guard ceilLog2 0 == 0 && ceilLog2 1 == 0 && ceilLog2 2 == 1 && ceilLog2 3 == 2 &&
  ceilLog2 4 == 2 && ceilLog2 5 == 3 && ceilLog2 64 == 6 && ceilLog2 65 == 7 && ceilLog2 3072 == 12

#guard constancy br [] == [z]
#guard constancy br [str "a"] == [lf "a"]
#guard constancy br [str "a", str "b", str "c"] == [lf "a", lf "b", lf "c", z]

#guard cdRoot br [] == z
#guard cdRoot br [str "a"] == lf "a"
#guard cdRoot br [str "a", str "b"] == nd (lf "a") (lf "b")
#guard cdRoot br [str "a", str "b", str "c"] == nd (nd (lf "a") (lf "b")) (nd (lf "c") z)
#guard cdRoot br ((List.range 5).map (fun k => str (toString k))) ==
  nd (nd (nd (lf "0") (lf "1")) (nd (lf "2") (lf "3"))) (nd (nd (lf "4") z) (nd z z))

def abc : List (List UInt8) := [str "a", str "b", str "c"]
#guard justify br 0 abc 0 == [nd (lf "c") z, lf "b"]
#guard justify br 0 abc 1 == [nd (lf "c") z, lf "a"]
#guard justify br 0 abc 2 == [nd (lf "a") (lf "b"), z]
#guard justify br 1 abc 0 == [nd (lf "c") z]
#guard justify br 1 abc 1 == [nd (lf "a") (lf "b")]
#guard justify br 2 abc 0 == []
#guard justify br 0 [str "a"] 0 == []
#guard page br 1 abc 0 == [lf "a", lf "b"]
#guard page br 1 abc 1 == [lf "c"]
#guard page br 2 abc 0 == [lf "a", lf "b", lf "c"]
#guard pageRoot br 1 [lf "c"] [nd (lf "a") (lf "b")] == nd (lf "c") z
#guard pageRoot br 2 [lf "a", lf "b", lf "c"] [] == cdRoot br abc

#guard foldPath br (lf "c") 2 (justify br 0 abc 2) == cdRoot br abc
#guard verifySegment br (cdRoot br abc) 2 (str "c") (justify br 0 abc 2)
#guard !verifySegment br (cdRoot br abc) 2 (str "x") (justify br 0 abc 2)
#guard !verifySegment br (cdRoot br abc) 1 (str "c") (justify br 0 abc 2)
-- an index beyond the depth of the path is rejected
#guard !verifySegment br (cdRoot br abc) 6 (str "c") (justify br 0 abc 2)

#guard zeroPad 4 [] == [] && zeroPad 4 [1] == [1, 0, 0, 0] && zeroPad 4 [1, 2, 3, 4] == [1, 2, 3, 4] &&
  zeroPad 4 [1, 2, 3, 4, 5] == [1, 2, 3, 4, 5, 0, 0, 0]

/-! ## Blake2b, written out -/

def b2 : ByteArray → ByteArray := Blake2b.hash256
def h (b : List UInt8) : List UInt8 := (Blake2b.hash256 ⟨b.toArray⟩).toList
def bl (s : String) : List UInt8 := h (str "leaf" ++ str s)
def bn (l r : List UInt8) : List UInt8 := h (str "node" ++ l ++ r)

#guard cdRoot b2 [] == List.replicate 32 0
#guard cdRoot b2 [str "a"] == bl "a"
#guard cdRoot b2 abc == bn (bn (bl "a") (bl "b")) (bn (bl "c") (List.replicate 32 0))
#guard justify b2 0 abc 2 == [bn (bl "a") (bl "b"), List.replicate 32 0]
#guard verifySegment b2 (cdRoot b2 abc) 0 (str "a") (justify b2 0 abc 0)

/-! ## Blake2b against an independent reading (Python `hashlib.blake2b`) -/

def hex (b : List UInt8) : String :=
  String.join (b.map fun x => let d := "0123456789abcdef".toList;
    String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

/-- Segment k of `size` octets: octet i is (7i + 3k + 1) mod 256. -/
def seg (k size : Nat) : List UInt8 := (List.range size).map fun i => UInt8.ofNat ((7 * i + 3 * k + 1) % 256)
def segs (n size : Nat) : List (List UInt8) := (List.range n).map fun k => seg k size

#guard hex (cdRoot b2 (segs 0 4104)) == "0000000000000000000000000000000000000000000000000000000000000000"
#guard hex (cdRoot b2 (segs 1 4104)) == "df26eb15ea75e4e3a6fe50966b7b32aed7d0c3ab4b04245ca9ae4d274f4cde8c"
#guard hex (cdRoot b2 (segs 2 4104)) == "1aa5b5a74af37560f2fcdab820725262b5c117d5e536a4191a84cd7573fbbe6b"
#guard hex (cdRoot b2 (segs 3 4104)) == "c6fd00933b1196c8a581578a74798741856c151e1b11b1925b25fd261db7be31"
#guard hex (cdRoot b2 (segs 5 4104)) == "e2bc3b6e91a4a09b7e018cefcd73081338fb1058d10df52fb2225874ddeb688e"
#guard hex (cdRoot b2 (segs 8 4104)) == "e8d534d1ae120ce35c3205383e984b4b78cc1d3c6e907dedf0c00f6f1cdf45f6"
#guard (justify b2 0 (segs 5 4104) 3).map hex ==
  ["b45b823049cf7dc59c8ae707164e134c10d265dc075aa8ce49fa05b09fd9f316",
   "1aa5b5a74af37560f2fcdab820725262b5c117d5e536a4191a84cd7573fbbe6b",
   "b464cc7aa1123ede1d24a3d48fec97686462b6e786bb8622abc8c6f2abd36cd8"]

def s130 : List (List UInt8) := segs 130 12
#guard hex (cdRoot b2 s130) == "5722d96d5e6e1b7c057a55a8fc49ed94cea5b76d3c6e055de7f04b32be3b0cfa"
#guard (justify b2 6 s130 1).map hex ==
  ["6676d1bed0df0e3ea3e6611eff9fa3b66e389f11095a2a7b607efa0a60235605",
   "3097d3f332d03f0099a19a2f72b0e913843451af5f59f2d5a905690ff1f5534f"]
#guard (pagedProofs b2 s130).length == 3
#guard (pagedProofs b2 s130).all (·.length == Constants.Csegmentsize)
#guard hex (h (pagedProofs b2 s130).flatten) ==
  "3bc2894889d50046d175028aa7da7704c35a372532e07737982a0a6a9bd3022c"
-- the last page of P holds the two remaining leaf hashes after its two-node path
#guard (pagedProofs b2 s130)[2]!.take (1 + 64 + 1) ==
  [2] ++ (justify b2 6 s130 2).flatten ++ [2]

/-! ## The theorems' statements, checked on small sizes (with tampering) -/

def vs (n : Nat) : List (List UInt8) := (List.range n).map fun k => str (toString k)

-- verifySegment_justify, and rejection of a wrong segment or index
#guard (List.range 18).all fun n => (List.range n).all fun i =>
  verifySegment br (cdRoot br (vs n)) i (str (toString i)) (justify br 0 (vs n) i) &&
  !verifySegment br (cdRoot br (vs n)) i (str "x") (justify br 0 (vs n) i) &&
  (n == 1 || !verifySegment br (cdRoot br (vs n)) ((i + 1) % n) (str (toString i))
    (justify br 0 (vs n) i))

-- verifyPage_page_justify for x ≤ 3, and rejection of a tampered page
#guard (List.range 18).all fun n => (List.range 4).all fun x =>
  (List.range ((n + 2 ^ x - 1) / 2 ^ x)).all fun i =>
    verifyPage br (cdRoot br (vs n)) x i (page br x (vs n) i) (justify br x (vs n) i) &&
    !verifyPage br (cdRoot br (vs n)) x i (page br x (vs n) i ++ [lf "x"]) (justify br x (vs n) i)

-- justify_zero_eq_page
#guard (List.range 18).all fun n => (List.range 4).all fun x => (List.range n).all fun i =>
  justify br 0 (vs n) i ==
    justify br x (vs n) (i / 2 ^ x) ++
      trace br (2 ^ x) (pageLeaves x (page br x (vs n) (i / 2 ^ x)) (justify br x (vs n) (i / 2 ^ x)))
        (i % 2 ^ x)

/-! ## Axioms -/

/-- info: 'JAM.Segments.verifySegment_justify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verifySegment_justify

/-- info: 'JAM.Segments.verifyPage_page_justify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms verifyPage_page_justify

/-- info: 'JAM.Segments.pagedProofs_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pagedProofs_verify

/-- info: 'JAM.Segments.justify_zero_eq_page' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms justify_zero_eq_page

/-- info: 'JAM.Segments.length_pagedProofs' depends on axioms: [propext] -/
#guard_msgs in #print axioms length_pagedProofs

end JAM.Tests.Segments
