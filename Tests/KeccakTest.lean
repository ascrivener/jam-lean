import JAM.Keccak

/-!
# Keccak tests

* SHA3-256 against Python's `hashlib.sha3_256` for messages whose octet `i` is `(7i + 3) mod 256`, covering
  the 136-octet rate boundaries; this tests the permutation and sponge shared with Keccak-256.
* Keccak-256 against its standard published values for "" and "abc".
-/

namespace JAM.Tests.Keccak
open JAM.Keccak

def msg (n : Nat) : ByteArray := ⟨((List.range n).map fun i => UInt8.ofNat ((7 * i + 3) % 256)).toArray⟩
def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x => let d := "0123456789abcdef".toList; String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

#guard hex (sha3_256 (msg 0)) == "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
#guard hex (sha3_256 (msg 1)) == "e3ed56bd086d8958483a12734fa0ae7f5c8bb160ef9092c67e82ed9b19e4c7b2"
#guard hex (sha3_256 (msg 3)) == "fffadd0ae913c0947143ac7c6bf1d512c1b265db8ac52100614bd022ae2412d4"
#guard hex (sha3_256 (msg 100)) == "ad0c0e561bdd605f010b02816765cceb72c9101e9904a2f517b1a2b9b56863be"
#guard hex (sha3_256 (msg 134)) == "c8883239d2ce058b11d87de7cd74805cb7e073b1b4884636fb2b5d1982c7bb9d"
#guard hex (sha3_256 (msg 135)) == "d9dcf1f98e49a79b0643a9e68fef48079ff8777c5e7e7f93469ded65f192ac71"
#guard hex (sha3_256 (msg 136)) == "743bd32e775ac7387a57d4d574c89ddef5ebcb08bb5cc6b88c55a27b5035cc45"
#guard hex (sha3_256 (msg 137)) == "01d47e8d6dce6e3dcbf1baa6f845b6ace4ef74bd17da8176ecc49bc35dbe5d21"
#guard hex (sha3_256 (msg 200)) == "9da37ea2fb33acd563a014f50d6f7cc225f25577a81d900452b72b5de98f239d"
#guard hex (sha3_256 (msg 271)) == "20bf2d2a8b462cf032927768963867773b04bcfdbf1419d1ac06aa23637e5b19"
#guard hex (sha3_256 (msg 272)) == "ddeb5151c079739970e780e6257d0c4d52d83bf82c6aa8d47d5195530b5d5f4b"
#guard hex (sha3_256 (msg 273)) == "ca74f68cfcda3bbd9068ae31dd3156e6df046aeb68e3176e4e17bf1557174553"
#guard hex (sha3_256 (msg 1000)) == "bd8b4d76041e0135e53fab1aaf425c7b1c129d8878ffb64cc31230ccafd7dc7c"
#guard hex (keccak256 ByteArray.empty) == "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard hex (keccak256 "abc".toUTF8) == "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

end JAM.Tests.Keccak
