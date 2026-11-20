import Services.Bootstrap.Refine.T1c
import Services.Bootstrap.Acc.Final.Hyps
import Services.Bootstrap.CodeOk
import Services.Bootstrap.CodeXOk
import Services.Bootstrap.CodeAOk
import Services.Bootstrap.CodeFOk
import Services.Bootstrap.CodeROk
import Services.Bootstrap.CodeT1BOk
import Services.Bootstrap.CodeT1COk

/-!
# The vendored bootstrap blob's facts, by the kernel alone (step 10 of `docs/bootstrap-target.md`)

T1 (`Refine.T1c.refine_t1c`) and T2 (`Acc.Final.accumulate_spec`) take closed hypotheses about the
constant vendored blob `Bridge.vendored` (`VendoredFactsC`, `AccVendoredFacts`) and about the looked-up
code (`IsBootstrapC`, `IsBootstrapCode`). Here the kernel checks them for the deployed binary
`Blob.preimage` (the octets of `services/bootstrap/jam-bootstrap-service.jam`), in the style of
`Services.Witness.Rejects`:

* `vendored_eq`: the blob splits from its metadata (`CodeCheck.split`) and parses to `CodeCheck.jamBlob`
  (`CodeCheck.jam`), GP §A.7 and eq. `conditions`;
* `layout_ok`: its section sizes and the data octets Y's path reads (`Prefix.layoutOk`), by
  `decide +kernel` on the blob's octets;
* `heap_ok`: its heap bounds, pages 48 … 1044430 (GP eq. `conditions`);
* each read-only slice the hypotheses name, `(ro.drop k).take m = […]`, by one `decide +kernel` on the
  first 12 of the blob's 1024-octet chunks (which hold the read-only data, octets 92 … 11699);
* the code facts, from the existing kernel checks (`Code*Check.checkCode_ok`).

So `vendoredFactsC`, `accVendoredFacts`, `isBootstrapC_preimage` and `isBootstrapCode_deployed` depend on
no compiled evaluation: only on the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace Services.Bootstrap.Vendored

open PVM PVM.NatBlob JAM Services.Bootstrap Services.Bootstrap.Blob Services.Bootstrap.CodeCheck
  Services.Bootstrap.Bridge

/-! ## The blob's sections -/

/-- The vendored blob is `CodeCheck.jamBlob`: the preimage splits from its metadata (GP §A.7) and its code
    parses as a standard program blob (GP eq. `conditions`). -/
theorem vendored_eq : vendored = some jamBlob := by
  show (splitMetadata preimage).bind (fun code => JamBlob.parse? code) = _
  rw [split, Option.bind_some]
  exact jam

/-- The read-only data, read from the chunks that hold it (octets 92 … 11699 lie in chunks 0 … 11). -/
theorem ro_toList : jamBlob.ro.toList = bytes (ofChunks (chunks.take 12)) 92 11608 := by
  show (ba N 92 11608).toList = _
  rw [toList_ba, show N = ofChunks chunks from rfl,
    bytes_ofChunks_window chunks chunks_lt 0 12 92 11608 (by omega) (by omega)]
  rfl

/-- A slice of the read-only data: m octets from offset k. -/
theorem ro_slice (k m : Nat) (h : k + m ≤ 11608) :
    (jamBlob.ro.toList.drop k).take m = bytes (ofChunks (chunks.take 12)) (92 + k) m := by
  rw [ro_toList]
  unfold bytes
  rw [drop_map_range, take_map_range _ _ _ (by omega)]
  simp only [Nat.add_assoc]

/-- The deployed blob's section sizes and the data octets Y's path reads (GP eq. `conditions`). -/
theorem layout_ok : Prefix.layoutOk jamBlob = true := by
  simp only [Prefix.layoutOk, jamBlob, size_ba, toList_ba, getElem!_bytes]
  decide +kernel

/-- The heap bounds of a standard program blob, from its sections (GP eq. `conditions`). -/
theorem heapBounds_of {code : ByteArray} {jb : JamBlob} (h : JamBlob.parse? code = some jb) :
    heapBounds code = ((2 * zoneSize + roundZone jb.ro.size) / pageSize,
      (2 ^ 32 - 3 * zoneSize - inputSize - roundPage jb.stackSize) / pageSize) := by
  unfold heapBounds; rw [h]

/-- The deployed blob's heap bounds: pages 48 … 1044430. -/
theorem heap_ok : heapBounds (ba N 81 95042) = (48, 1044430) := by
  rw [heapBounds_of jam]
  simp only [jamBlob, size_ba]
  decide

/-! ## The read-only slices -/

/-- The decoder's variant table (67476, 100 octets). -/
theorem ro_tag : (jamBlob.ro.toList.drop 1940).take 100 = Decode.Tag.table := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The encoder's dispatch table (67376, 100 octets). -/
theorem ro_enc : (jamBlob.ro.toList.drop 1840).take 100 = Encode.Enc.table := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The drop dispatch table (67760, 96 octets). -/
theorem ro_drop : (jamBlob.ro.toList.drop 2224).take 96 = Refine.DropOut.dtable := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The drop dispatch table's entry for index 8 (65568, 4 octets). -/
theorem ro_dropEntry8 : (jamBlob.ro.toList.drop 32).take 4 = Refine.Lookup.dropEntry8 := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The slices the Fmt summaries read (`Fmt.FmtRO`), one kernel check each. -/
theorem fmtRO : Fmt.FmtRO jamBlob.ro.toList := by
  unfold Fmt.FmtRO
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [ro_slice _ _ (by omega)]; decide +kernel)

/-- Accumulate's first log line's template (66464, 42 octets). -/
theorem ro_accTmpl : (jamBlob.ro.toList.drop 928).take 42 = Fmt.accTmplBytes := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The `String` vtable's words (77040, 16 octets). -/
theorem ro_strVt : (jamBlob.ro.toList.drop 11504).take 16 =
    [36, 10, 0, 0, 0, 0, 0, 0, 32, 10, 0, 0, 0, 0, 0, 0] := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The key "transfer-count" (65956, 14 octets). -/
theorem ro_key : (jamBlob.ro.toList.drop 420).take 14 =
    [116, 114, 97, 110, 115, 102, 101, 114, 45, 99, 111, 117, 110, 116] := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- `set`'s error table (69056, 20 octets). -/
theorem ro_setErr : (jamBlob.ro.toList.drop 3520).take 20 =
    [178, 250, 254, 255, 180, 250, 254, 255, 176, 250, 254, 255, 182, 250, 254, 255, 184, 250, 254, 255] := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The key-size words (68680, 24 octets). -/
theorem ro_keySz : (jamBlob.ro.toList.drop 3144).take 24 =
    [1, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 0] := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-- The instruction jump table (65736, 100 octets). -/
theorem ro_jumpTab : (jamBlob.ro.toList.drop 200).take 100 = Acc.Handlers.jumpTab := by
  rw [ro_slice _ _ (by omega)]; decide +kernel

/-! ## The named hypotheses, discharged -/

/-- **`Milestone.VendoredFacts` holds**, by the kernel. -/
theorem vendoredFacts : Refine.Milestone.VendoredFacts :=
  ⟨jamBlob, vendored_eq, layout_ok, ro_tag, ro_enc, ro_drop, fmtRO⟩

/-- **`T1c.VendoredFactsC` holds**, by the kernel. -/
theorem vendoredFactsC : Refine.T1c.VendoredFactsC :=
  ⟨vendoredFacts, jamBlob, vendored_eq, ro_dropEntry8⟩

/-- **`Acc.Final.AccVendoredFacts` holds**, by the kernel. -/
theorem accVendoredFacts : Acc.Final.AccVendoredFacts :=
  ⟨jamBlob, vendored_eq, layout_ok, ro_accTmpl, ro_strVt, ro_key, ro_setErr, ro_keySz, ro_jumpTab⟩

/-- The deployed code (after the metadata) is within 𝖶_C. -/
theorem code_size : (ba N 81 95042).size ≤ Constants.Cmaxservicecodesize := by
  rw [size_ba]; decide

/-- **The deployed binary is bootstrap** (`Bridge.IsBootstrap`), by the kernel. -/
theorem isBootstrap_preimage : IsBootstrap preimage :=
  ⟨by rw [preimage, length_bytes]; decide, ba N 81 95042, jamBlob, jamBlob, split, jam, vendored_eq,
    rfl, rfl, rfl, rfl, heap_ok, CodeCheck.checkCode_ok, CodeXCheck.checkCode_ok, CodeACheck.checkCode_ok,
    CodeFCheck.checkCode_ok, CodeRCheck.checkCode_ok⟩

/-- **The deployed binary is bootstrap with T1c's code facts** (`T1c.IsBootstrapC`), by the kernel. -/
theorem isBootstrapC_preimage : Refine.T1c.IsBootstrapC preimage :=
  ⟨isBootstrap_preimage, ba N 81 95042, jamBlob, split, jam, CodeT1BCheck.checkCode_ok,
    CodeT1CCheck.checkCode_ok⟩

/-- **The deployed code is bootstrap's** (`Acc.Final.IsBootstrapCode`), by the kernel: the code after the
    deployed binary's metadata. -/
theorem isBootstrapCode_deployed : Acc.Final.IsBootstrapCode (ba N 81 95042) :=
  ⟨code_size, jamBlob, jamBlob, jam, vendored_eq, rfl, rfl, rfl, rfl, heap_ok, CodeCheck.checkCode_ok,
    CodeXCheck.checkCode_ok, CodeACheck.checkCode_ok, CodeFCheck.checkCode_ok⟩

/-- For any code the deployed binary's metadata split gives, it is bootstrap's. -/
theorem isBootstrapCode_of_split {code : ByteArray} (h : splitMetadata preimage = some code) :
    Acc.Final.IsBootstrapCode code := by
  have hc : ba N 81 95042 = code := Option.some.inj (split.symm.trans h)
  exact hc ▸ isBootstrapCode_deployed

end Services.Bootstrap.Vendored
