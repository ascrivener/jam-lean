import JamCrypto.Fast.Fr
import JamCrypto.Fast.RingCurveF

/-!
# The ring's Bandersnatch curve on `Fast.Fr`, swapped in for the reference by `@[csimp]`

`decode` and `smulW` compute `JamCrypto.Ring.Curve.decode` and `JamCrypto.Ring.Curve.smulW` with
`Fast.RingCurveF` on the fixed-limb field `Fast.Fr`, and are proved equal to them. A reference
extended point is converted when its coordinates are reduced (as every point the reference
decodes or computes is); otherwise the reference runs.
-/

namespace JamCrypto.Fast.RingCurveFr

open JamCrypto.Fast JamCrypto.Fast.RingCurveF
open JamCrypto.Fr (R)

abbrev E := JamCrypto.Fast.Fr.Elem

instance : IsFr E := ⟨rfl⟩

/-- Back to a reference affine point. -/
def toAff (a : AF E) : JamCrypto.Ring.Curve.Aff := ⟨Field.toNat a.x, Field.toNat a.y⟩

theorem toAff_eq {a : AF E} {b : JamCrypto.Ring.Curve.Aff} (h : ARel a b) : toAff a = b := by
  unfold toAff; rw [h.1.toNat, h.2.toNat]

/-- A reference extended point, converted. -/
def ofExt (q : JamCrypto.Ring.Curve.Ext) : EF E :=
  ⟨Field.ofNat q.x, Field.ofNat q.y, Field.ofNat q.t, Field.ofNat q.z⟩

/-- Back to a reference extended point. -/
def toExt (a : EF E) : JamCrypto.Ring.Curve.Ext :=
  ⟨Field.toNat a.x, Field.toNat a.y, Field.toNat a.t, Field.toNat a.z⟩

/-- The coordinates are reduced. -/
def redE (q : JamCrypto.Ring.Curve.Ext) : Bool :=
  decide (q.x < R) && decide (q.y < R) && decide (q.t < R) && decide (q.z < R)

theorem ofExt_rel {q : JamCrypto.Ring.Curve.Ext} (h : redE q = true) : ERel (ofExt q) q := by
  simp only [redE, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨W.ofNat h.1.1.1, W.ofNat h.1.1.2, W.ofNat h.1.2, W.ofNat h.2⟩

theorem toExt_eq {a : EF E} {q : JamCrypto.Ring.Curve.Ext} (h : ERel a q) : toExt a = q := by
  unfold toExt; rw [h.1.toNat, h.2.1.toNat, h.2.2.1.toNat, h.2.2.2.toNat]

/-- `Curve.smulW`. -/
def smulW (q : JamCrypto.Ring.Curve.Ext) (k : Nat) : JamCrypto.Ring.Curve.Ext :=
  if redE q then toExt (RingCurveF.smulW (ofExt q) k) else JamCrypto.Ring.Curve.smulW q k

theorem smulW_eq (q : JamCrypto.Ring.Curve.Ext) (k : Nat) : smulW q k = JamCrypto.Ring.Curve.smulW q k := by
  unfold smulW
  split
  · exact toExt_eq (RingCurveF.smulW_rel (ofExt_rel ‹_›) k)
  · rfl

/-- `Curve.decode`. -/
def decode (bs : List UInt8) : Option JamCrypto.Ring.Curve.Aff := (RingCurveF.decode (F := E) bs).map toAff

theorem decode_eq (bs : List UInt8) : decode bs = JamCrypto.Ring.Curve.decode bs := by
  unfold decode
  have h := RingCurveF.decode_rel (F := E) bs
  revert h
  cases RingCurveF.decode (F := E) bs <;> cases JamCrypto.Ring.Curve.decode bs <;> simp [OR]
  exact fun h => toAff_eq h

@[csimp] theorem smulW_csimp : @JamCrypto.Ring.Curve.smulW = @smulW :=
  funext fun q => funext fun k => (smulW_eq q k).symm

@[csimp] theorem decode_csimp : @JamCrypto.Ring.Curve.decode = @decode :=
  funext fun bs => (decode_eq bs).symm

end JamCrypto.Fast.RingCurveFr
