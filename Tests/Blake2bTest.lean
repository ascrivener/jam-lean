import JAM.Blake2b

/-!
# Blake2b test vectors

Reference digests from Python's `hashlib.blake2b` for messages whose octet `i` is `(7i + 3) mod 256`,
covering the empty message and the 128-octet block boundaries, plus RFC 7693 Appendix A ("abc",
64-octet digest).

* `#guard` checks every case by ordinary evaluation.
* `decide +kernel` re-checks the small cases in the kernel itself. Kernel evaluation is far slower:
  about 5 s per block here, and longer messages (eight blocks) exhaust memory, apparently in the
  `ByteArray` operations rather than in the hash.
-/

namespace JAM.Tests.Blake2b
open JAM.Blake2b

def msg (n : Nat) : ByteArray := ⟨((List.range n).map fun i => UInt8.ofNat ((7 * i + 3) % 256)).toArray⟩
def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x => let d := "0123456789abcdef".toList; String.ofList [d[x.toNat / 16]!, d[x.toNat % 16]!])

#guard hex (hash256 (msg 0)) == "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"
#guard hex (hash256 (msg 1)) == "e88bd757ad5b9bedf372d8d3f0cf6c962a469db61a265f6418e1ffed86da29ec"
#guard hex (hash256 (msg 3)) == "9facd640130c81e7f318a8d5c660bc1b0f5d03861ffbd4cc1358e0e904593c28"
#guard hex (hash256 (msg 63)) == "a69e023685fa5f19fca13acc02142a9cf8450ce5b77966586e0d000c4a4ea942"
#guard hex (hash256 (msg 64)) == "586c0dd87616ec042093edc5f87f880d37ca73618e99b03d5850ce9be478721f"
#guard hex (hash256 (msg 127)) == "c9ae3859964b35f04c54b36d33cf299d7290ee621005d28e51598a943560aaaa"
#guard hex (hash256 (msg 128)) == "f0501d06597880592bc49234eef100ec1ff349058d0e9d9b753504e24af86dd6"
#guard hex (hash256 (msg 129)) == "a34a4e1e03c541dfbf3099c4b6c143c022ced65c28bd7e8a10e0a098461aecf0"
#guard hex (hash256 (msg 255)) == "f2d64a40e9412a3414161ff6250075225418fd7c271c1123e162e1bca0de9f93"
#guard hex (hash256 (msg 256)) == "d93ebb9c802f5630ab22516fd82b6c21bc8bd551d531349b715f046ed11ed871"
#guard hex (hash256 (msg 257)) == "4ce481b24d387422d2bc2baa03d1afd55a1327939ff537c71eb9b38709268649"
#guard hex (hash256 (msg 1000)) == "d62b6c768ce1afc8367e0498ab2f8e3f7c178c35b1429f14c4604b545d200f52"
#guard hex (hash 64 "abc".toUTF8) == "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"

example : hex (hash256 (msg 0)) = "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8" := by decide +kernel
example : hex (hash256 (msg 3)) = "9facd640130c81e7f318a8d5c660bc1b0f5d03861ffbd4cc1358e0e904593c28" := by decide +kernel
example : hex (hash256 (msg 129)) = "a34a4e1e03c541dfbf3099c4b6c143c022ced65c28bd7e8a10e0a098461aecf0" := by decide +kernel

end JAM.Tests.Blake2b
