import Services.Bootstrap.Vendored.Facts

/-!
# The vendored blob's octets behind the field formatters' read-only hypotheses

`Fmt.RO70824` and `Fmt.RO70833` (`Fmt/FieldN56Hex.lean`, `Fmt/FieldSliceHex.lean`) are named hypotheses on a
memory μ: that it holds the templates `0x{}...` (70824) and `{:02x}` (70833) of the read-only data. Here the
kernel checks the vendored blob's side: its read-only data holds those octets at offsets 5288 and 5297 from
65536 (GP eq. `conditions`: Y loads the read-only data at 65536). Turning these into the memory-level
hypotheses, for the memory of a run from Y's start, is left to the field formatters' line. The UTF-8 width
table [71078, 71334) that `from_utf8` reads lies inside the 11608-octet read-only data `layout_ok` fixes.
-/

namespace Services.Bootstrap.Vendored

open PVM PVM.NatBlob Services.Bootstrap.CodeCheck

/-- The template 70824 (`0x{}...`, 9 octets): literal 2 (`0x`), argument 0xC0, literal 3 (`...`), end 0. -/
theorem ro_70824 : (jamBlob.ro.toList.drop 5288).take 9 = [2, 48, 120, 192, 3, 46, 46, 46, 0] := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The template 70833 (`{:02x}`, 8 octets): 0xC3, the options word 0x69000020, the width 2, end 0. -/
theorem ro_70833 : (jamBlob.ro.toList.drop 5297).take 8 = [195, 32, 0, 0, 105, 2, 0, 0] := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The UTF-8 width table [71078, 71334) lies inside the read-only data (65536 … 77143). -/
theorem utf8Table_in_ro : 65536 ≤ 71078 ∧ 71334 ≤ 65536 + jamBlob.ro.size := by
  simp only [jamBlob, size_ba]; omega

end Services.Bootstrap.Vendored
