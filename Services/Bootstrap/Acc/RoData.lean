import Services.Bootstrap.Prefix

/-!
# Read-only data accumulate's SDK wrappers read

The SDK's `set` (48104) maps Ω_W's error codes through a table of i32 offsets in read-only data at
69040 (GP v0.8.0 Appendix A: the blob's **o**, at 2¹⁶ onward). Bootstrap's writes reply NONE or FULL,
so two entries are read: entry 8 (NONE) at 69072 and entry 4 (FULL) at 69056 (`accRoBytes`).
`on_transfer` also copies the key "transfer-count" from 65956.

`accRoOk jb` checks them against a blob's read-only section (by evaluation, as `Prefix.layoutOk` does
for refine's `roBytes`); `initialMemory_accRo` gives them in Y's starting memory. The blob's values were read from
`services/bootstrap/jam-bootstrap-service.jam`; `accRoOk` is to be added to the blob checks.
-/

namespace Services.Bootstrap.Acc

open PVM JAM

/-- The read-only octets accumulate's wrappers read: `set`'s error-table entries 4 (FULL, −66894)
    and 8 (NONE, −66888), little-endian i32; and the key "transfer-count" (14 octets at 65956) that
    `on_transfer` copies. -/
def accRoBytes : List (Nat × UInt8) :=
  [(65956, 116), (65957, 114), (65958, 97), (65959, 110), (65960, 115),
   (65961, 102), (65962, 101), (65963, 114), (65964, 45), (65965, 99),
   (65966, 111), (65967, 117), (65968, 110), (65969, 116),
   (69056, 178), (69057, 250), (69058, 254), (69059, 255),
   (69072, 184), (69073, 250), (69074, 254), (69075, 255)]

/-- The blob's read-only section holds `accRoBytes` (with the deployed size). -/
def accRoOk (jb : JamBlob) : Bool :=
  jb.ro.size == 11608 && accRoBytes.all (fun q => jb.ro.toList[q.1 - 65536]! == q.2)

/-- **Y's starting memory holds `accRoBytes`.** -/
theorem initialMemory_accRo (jb : JamBlob) (a : ByteArray) (hl : Prefix.layoutOk jb = true)
    (hr : accRoOk jb = true) (ha : a.size ≤ inputSize) :
    ∀ q ∈ accRoBytes, (initialMemory jb a).read q.1 = q.2 := by
  simp only [Prefix.layoutOk, Bool.and_eq_true, beq_iff_eq] at hl
  obtain ⟨⟨⟨⟨⟨hro, hrw⟩, -⟩, -⟩, -⟩, -⟩ := hl
  simp only [accRoOk, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨-, hrob⟩ := hr
  have hrs : rwStart jb = 196608 := by simp [rwStart, hro, roundZone, zoneSize]
  intro q hq
  have hv := beq_iff_eq.1 (List.all_eq_true.1 hrob _ hq)
  have hx : 65536 ≤ q.1 ∧ q.1 < 77144 := by
    have := List.all_eq_true.1
      (show accRoBytes.all (fun q => decide (65536 ≤ q.1 ∧ q.1 < 77144)) = true by decide) q hq
    simpa using this
  rw [initialMemory_read jb a q.1 (by simp [two32]; omega) (by simp [hro, roStart, zoneSize, two32])
    (by simp [hrs, hrw, two32]) (by simp [argStart, zoneSize, inputSize, two32] at ha ⊢; omega)]
  rw [ite_eq_right (by simp only [argStart, zoneSize, inputSize]; omega),
    ite_eq_right (by rw [hrs]; omega), ite_eq_left (by simp only [roStart, zoneSize, hro]; omega)]
  simpa [roStart, zoneSize] using hv

end Services.Bootstrap.Acc
