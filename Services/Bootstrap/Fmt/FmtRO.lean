/-!
# The read-only data the Fmt summaries read (`FmtRO`)

`FmtRO ro`: the slices of the service's read-only segment (loaded at 65536; `ro` its octets) whose
values the formatting proofs depend on: the `format!` templates of refine's log sites, the `String`
sink's vtable, `<&Instruction as Debug>`'s jump table and the `Debug` vtables' `fmt` words, and
`HostCallError`'s name tables. Names and other octets that are only written out need just to be
readable, which `HeapCtx` gives. Each slice is `(ro.drop k).take m = […]` with k the address − 65536.
Refine's milestone proves `FmtRO` of the vendored blob's RO data (`VendoredFacts`); later sites extend
it only by adding conjuncts. It imports nothing.
-/

namespace Services.Bootstrap.Fmt

/-- **The read-only octets the Fmt summaries read.** -/
def FmtRO (ro : List UInt8) : Prop :=
  -- template 66099: refine's level-3 line (6159), "Returning {:?} into accumulate"
  (ro.drop 563).take 30 = [10, 82, 101, 116, 117, 114, 110, 105, 110, 103, 32, 192, 16, 32, 105, 110, 116, 111, 32, 97, 99, 99, 117, 109, 117, 108, 97, 116, 101, 0] ∧
  -- template 66196: refine's Export line (5744)
  (ro.drop 660).take 25 = [16, 69, 120, 112, 111, 114, 116, 101, 100, 32, 115, 108, 105, 99, 101, 58, 32, 192, 4, 32, 45, 62, 32, 192, 0] ∧
  -- template 66506: refine's Lookup line (5398)
  (ro.drop 970).take 21 = [18, 69, 97, 103, 101, 114, 32, 108, 111, 111, 107, 117, 112, 44, 32, 103, 111, 116, 32, 192, 0] ∧
  -- template 66657: refine's service line (4742)
  (ro.drop 1121).take 31 = [26, 66, 111, 111, 116, 115, 116, 114, 97, 112, 32, 83, 101, 114, 118, 105, 99, 101, 32, 82, 101, 102, 105, 110, 101, 44, 32, 192, 1, 104, 0] ∧
  -- `<&Instruction as Debug>`'s jump table (25 relative offsets, 4 octets each)
  (ro.drop 2040).take 100 = [250, 252, 254, 255, 24, 253, 254, 255, 14, 253, 254, 255, 20, 253, 254, 255, 6, 253, 254, 255, 32, 253, 254, 255, 38, 253, 254, 255, 22, 253, 254, 255, 46, 253, 254, 255, 10, 253, 254, 255, 44, 253, 254, 255, 2, 253, 254, 255, 8, 253, 254, 255, 36, 253, 254, 255, 0, 253, 254, 255, 18, 253, 254, 255, 254, 252, 254, 255, 28, 253, 254, 255, 42, 253, 254, 255, 54, 253, 254, 255, 30, 253, 254, 255, 34, 253, 254, 255, 50, 253, 254, 255, 58, 253, 254, 255, 12, 253, 254, 255] ∧
  -- `HostCallError`'s `Debug` name lengths (8 words)
  (ro.drop 3408).take 64 = [15, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 13, 0, 0, 0, 0, 0, 0, 0] ∧
  -- `HostCallError`'s `Debug` name offsets (8 × 4 octets)
  (ro.drop 3472).take 32 = [79, 255, 255, 255, 94, 255, 255, 255, 105, 255, 255, 255, 117, 255, 255, 255, 128, 255, 255, 255, 135, 255, 255, 255, 141, 255, 255, 255, 155, 255, 255, 255] ∧
  -- the `Debug` vtable at 74040 (&u64 (37589)): its `fmt` word
  (ro.drop 8528).take 8 = [2, 7, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 74648 (&Vec<u8> (26807)): its `fmt` word
  (ro.drop 9136).take 8 = [226, 4, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 74776 (&HostCallError (37312)): its `fmt` word
  (ro.drop 9264).take 8 = [228, 6, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 74808 ([u8; 32] / hash (56340)): its `fmt` word
  (ro.drop 9296).take 8 = [198, 9, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 74840 (u64 (28843)): its `fmt` word
  (ro.drop 9328).take 8 = [68, 5, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75112 (&u64 (37589)): its `fmt` word
  (ro.drop 9600).take 8 = [2, 7, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75144 (u32 (28822)): its `fmt` word
  (ro.drop 9632).take 8 = [66, 5, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75176 (tag 2's last field (33162)): its `fmt` word
  (ro.drop 9664).take 8 = [252, 5, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75208 (&u32 (37549)): its `fmt` word
  (ro.drop 9696).take 8 = [254, 6, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75240 (tag 4's last field (33167)): its `fmt` word
  (ro.drop 9728).take 8 = [254, 5, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75304 (hash (56340)): its `fmt` word
  (ro.drop 9792).take 8 = [198, 9, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75336 (&bool (37522)): its `fmt` word
  (ro.drop 9824).take 8 = [250, 6, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75528 (&[u8; 32] (36529)): its `fmt` word
  (ro.drop 10016).take 8 = [176, 6, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75784 (&Instruction): its `fmt` word
  (ro.drop 10272).take 8 = [240, 4, 0, 0, 0, 0, 0, 0] ∧
  -- the `Debug` vtable at 75976 (&u8 (37527)): its `fmt` word
  (ro.drop 10464).take 8 = [252, 6, 0, 0, 0, 0, 0, 0] ∧
  -- the `String` sink's `fmt::Write` vtable (`write_str` at 77040, `write_char` at 77048)
  (ro.drop 11480).take 48 = [22, 10, 0, 0, 0, 0, 0, 0, 24, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 36, 10, 0, 0, 0, 0, 0, 0, 32, 10, 0, 0, 0, 0, 0, 0, 16, 10, 0, 0, 0, 0, 0, 0]

end Services.Bootstrap.Fmt
