import JAM.Sha512
import JAM.Blake2b

/-!
# SHA-512 tests

* The FIPS 180-2 Appendix C examples: "abc" (one block) and the 896-bit message (two blocks), and
  the empty message.
* Against Python's `hashlib.sha512` for messages whose octet `i` is `(7i + 3) mod 256`, at the
  lengths around the 128-octet block and its 112-octet padding boundary.
* The VRF output Y of one trace block's entropy source, checked against η'_0 = ℋ(η_0 ⌢ Y(H_V)) in
  that block's post-state (`fallback/00000001`).
-/

namespace JAM.Tests.Sha512
open JAM.Sha512

def msg (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat ((7 * i + 3) % 256)
def hex (b : List UInt8) : String :=
  String.join (b.map fun x => let d := "0123456789abcdef".toList; String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

#guard hex (hash []) == "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"
#guard hex (hash "abc".toUTF8.toList) == "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
#guard hex (hash "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu".toUTF8.toList) == "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
#guard hex (hash (msg 111)) == "68cffa6d0d76f309c9ce0d35280939f8e25990c43b7b086ccdf709be35b07d4ddba599541ff2b1c19d34ea49aeafb9659adb7ac3c0b078bb30a22d57fc6687ef"
#guard hex (hash (msg 112)) == "d0865c524d1dddf7c23b799c413f5adcd7caefd3f66a9b49750ec81066012c25a8bcf94ddea6dc525691673097ca40e0101e897fc97218cfdb0704084e2bef4b"
#guard hex (hash (msg 127)) == "e0b6a20f1c0c88970a9340152cd5a1c1ecf3d3b8de55102741879438079473540133b812706e5dbec322c8c9523b6fc8c6d16ee626e87ad5fe3d2916afedc369"
#guard hex (hash (msg 128)) == "99b16f17aa0b969a5b8f08f367719d516e330ccd2660b6f0688ec031dbc783de50a1cd185a2568dba75070a2403d17d4741d163578515dfd2ff756ddfe4d47b1"
#guard hex (hash (msg 129)) == "a1556e29185778aa5991e34b8884c840d589f0fbb4b8ed590e51e9ac4eb03a008125000db2671f8fe7f485b59a77b518670078ecb41a54b4cd02a7f1d2ca4c6d"
#guard hex (hash (msg 1000)) == "00e36fccf193e59697a92b5ab24666ce6326d7fa16bf10832d0991ddc591112e9dfa6a636950ed9c4d67344a760654c2ff7785e1d60094d651038735b5dccabd"

def unhex (s : String) : List UInt8 :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toNat - 87
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => UInt8.ofNat (16 * d cs[2 * i]! + d cs[2 * i + 1]!)

/-- `fallback/00000001`: H_V, η_0 and η'_0. -/
def hv := unhex "62bc9d2311da8db52da45c5785333b39da3f1464b0d0341d12e2ee2987da6595463487a2d903c169560a90521ce06ecc99e466afeaa04f766e4e6fd3bf3677170282a54709e0e92a1a37c853f8c83053c9746e53581366bf1aaedd621bd4a713"
def eta0 := unhex "15791ce2f9ad023b718ff82e41541cbdb452b39e8eb79204f81989e25717c70f"
def eta0' := unhex "5b8e9d7c5c737a1d41f8dc4ad0cd7962e4718ee3761146c2ba992f6fbdf172ce"

#guard (Blake2b.hash256 ⟨(eta0 ++ vrfOutput hv).toArray⟩).toList == eta0'

end JAM.Tests.Sha512
