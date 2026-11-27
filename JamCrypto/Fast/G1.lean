import JamCrypto.Fast.Fq
import JamCrypto.Fast.G1F

/-!
# G1 of BLS12-381 on `Fast.Fq`, swapped in for the reference by `@[csimp]`

`smul`, `msm` and `decompress` below compute `JamCrypto.G1.smul`, `JamCrypto.G1.msm` and
`JamCrypto.G1.decompress` with the operations of `Fast.G1F` on the fixed-limb field `Fast.Fq`,
and are proved equal to them. A reference Jacobian or affine point is converted when its
coordinates are reduced (as every point the reference computes or decodes is); otherwise the
reference itself runs.
-/

namespace JamCrypto.Fast.G1Fq

open JamCrypto.Fast JamCrypto.Fast.G1F
open JamCrypto.Fq (P)

abbrev E := JamCrypto.Fast.Fq.Elem

instance : IsFq E := ⟨rfl⟩

/-- A reference Jacobian point, converted. -/
def ofJac (q : JamCrypto.G1.Jac) : JF E := ⟨Field.ofNat q.x, Field.ofNat q.y, Field.ofNat q.z⟩

/-- Back to a reference Jacobian point. -/
def toJac (a : JF E) : JamCrypto.G1.Jac := ⟨Field.toNat a.x, Field.toNat a.y, Field.toNat a.z⟩

/-- The coordinates are reduced. -/
def redJ (q : JamCrypto.G1.Jac) : Bool := decide (q.x < P) && decide (q.y < P) && decide (q.z < P)

/-- The coordinates are reduced. -/
def redA (q : JamCrypto.G1.Aff) : Bool := decide (q.x < P) && decide (q.y < P)

theorem ofJac_rel {q : JamCrypto.G1.Jac} (h : redJ q = true) : JRel (ofJac q) q := by
  simp only [redJ, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨V.ofNat h.1.1, V.ofNat h.1.2, V.ofNat h.2⟩

theorem toJac_eq {a : JF E} {q : JamCrypto.G1.Jac} (h : JRel a q) : toJac a = q := by
  unfold toJac; rw [h.1.toNat, h.2.1.toNat, h.2.2.toNat]

/-- `G1.smul`. -/
def smul (q : JamCrypto.G1.Jac) (k : Nat) : JamCrypto.G1.Jac :=
  if redJ q then toJac (G1F.smul (ofJac q) k) else JamCrypto.G1.smul q k

theorem smul_eq (q : JamCrypto.G1.Jac) (k : Nat) : smul q k = JamCrypto.G1.smul q k := by
  unfold smul
  split
  · exact toJac_eq (G1F.smul_rel (ofJac_rel ‹_›) k)
  · rfl

/-- `G1.msm`. -/
def msm (points : Array JamCrypto.G1.Aff) (scalars : Array Nat) : JamCrypto.G1.Jac :=
  if points.all redA then toJac (G1F.msm (points.map ofAff) scalars)
  else JamCrypto.G1.msm points scalars

theorem msm_eq (points : Array JamCrypto.G1.Aff) (scalars : Array Nat) :
    msm points scalars = JamCrypto.G1.msm points scalars := by
  unfold msm
  split
  · rename_i h
    rw [Array.all_eq_true] at h
    refine toJac_eq (G1F.msm_rel ⟨by simp, fun i h1 h2 => ?_⟩ scalars)
    have := h i h2
    simp only [redA, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [Array.getElem_map]
    exact ofAff_rel this
  · rfl

/-- `G1.decompress`. -/
def decompress (bs : List UInt8) : Option JamCrypto.G1.Aff :=
  (G1F.decompress (F := E) bs).map toAffNat

theorem decompress_eq (bs : List UInt8) : decompress bs = JamCrypto.G1.decompress bs := by
  unfold decompress
  have h := decompress_rel (F := E) bs
  revert h
  cases G1F.decompress (F := E) bs <;> cases JamCrypto.G1.decompress bs <;> simp [OR]
  exact fun h => toAffNat_eq h

@[csimp] theorem smul_csimp : @JamCrypto.G1.smul = @smul :=
  funext fun q => funext fun k => (smul_eq q k).symm

@[csimp] theorem msm_csimp : @JamCrypto.G1.msm = @msm :=
  funext fun p => funext fun s => (msm_eq p s).symm

@[csimp] theorem decompress_csimp : @JamCrypto.G1.decompress = @decompress :=
  funext fun bs => (decompress_eq bs).symm

end JamCrypto.Fast.G1Fq
