import JamCrypto.Fast.G1
import JamCrypto.Fast.PairingF

/-!
# The BLS12-381 pairing check on `Fast.Fq`, swapped in for the reference by `@[csimp]`

`pairingCheck` computes `JamCrypto.Pairing.pairingCheck` with `Fast.PairingF` on the fixed-limb
field `Fast.Fq`, and is proved equal to it. The points are converted when their coordinates are
reduced (as every point the reference decodes or computes is); otherwise the reference runs.
-/

namespace JamCrypto.Fast.PairingFq

open JamCrypto.Fast JamCrypto.Fast.G1F JamCrypto.Fast.PairingF JamCrypto.Fast.G1Fq
open JamCrypto.Fq (P)

/-- A reference 𝔽_q2 element, converted. -/
def ofFq2 (x : JamCrypto.Pairing.Fq2) : E2 E := ⟨Field.ofNat x.a, Field.ofNat x.b⟩

/-- A reference G2 point, converted. -/
def ofG2 (q : JamCrypto.Pairing.G2) : G2F E := ⟨ofFq2 q.x, ofFq2 q.y, q.inf⟩

def red2 (x : JamCrypto.Pairing.Fq2) : Bool := decide (x.a < P) && decide (x.b < P)

def redG2 (q : JamCrypto.Pairing.G2) : Bool := red2 q.x && red2 q.y

theorem ofFq2_rel {x : JamCrypto.Pairing.Fq2} (h : red2 x = true) : V2 (ofFq2 x) x := by
  simp only [red2, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨V.ofNat h.1, V.ofNat h.2⟩

theorem ofG2_rel {q : JamCrypto.Pairing.G2} (h : redG2 q = true) : GRel (ofG2 q) q := by
  simp only [redG2, Bool.and_eq_true] at h
  exact ⟨ofFq2_rel h.1, ofFq2_rel h.2, rfl⟩

/-- Back to a reference 𝔽_q12 element. -/
def toFq12 (f : E12 E) : JamCrypto.Pairing.Fq12 :=
  let c (x : E2 E) : JamCrypto.Pairing.Fq2 := ⟨Field.toNat x.a, Field.toNat x.b⟩
  ⟨⟨c f.d0.c0, c f.d0.c1, c f.d0.c2⟩, ⟨c f.d1.c0, c f.d1.c1, c f.d1.c2⟩⟩

theorem toFq12_eq {f : E12 E} {f' : JamCrypto.Pairing.Fq12} (h : V12 f f') : toFq12 f = f' := by
  obtain ⟨⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := h
  unfold toFq12
  dsimp only
  rw [a0.1.toNat, a0.2.toNat, a1.1.toNat, a1.2.toNat, a2.1.toNat, a2.2.toNat,
    b0.1.toNat, b0.2.toNat, b1.1.toNat, b1.2.toNat, b2.1.toNat, b2.2.toNat]

/-- The pair's coordinates are reduced. -/
def redPair (pq : JamCrypto.G1.Aff × JamCrypto.Pairing.G2) : Bool := redA pq.1 && redG2 pq.2

/-- `Pairing.pairingCheck`. -/
def pairingCheck (pairs : List (JamCrypto.G1.Aff × JamCrypto.Pairing.G2)) : Bool :=
  if pairs.all redPair then
    toFq12 (PairingF.finalExp (millerProd (pairs.map fun pq => (ofAff pq.1, ofG2 pq.2)))) ==
      JamCrypto.Pairing.Fq12.one
  else JamCrypto.Pairing.pairingCheck pairs

theorem pairingCheck_eq (pairs : List (JamCrypto.G1.Aff × JamCrypto.Pairing.G2)) :
    pairingCheck pairs = JamCrypto.Pairing.pairingCheck pairs := by
  unfold pairingCheck
  split
  · rename_i h
    have hl : PairingF.ListRel PairingF.PRel (pairs.map fun pq => ((ofAff pq.1 : AF E), ofG2 pq.2)) pairs := by
      induction pairs with
      | nil => trivial
      | cons x xs ih =>
        simp only [List.all_cons, Bool.and_eq_true] at h
        have hx := h.1
        simp only [redPair, redA, Bool.and_eq_true, decide_eq_true_eq] at hx
        exact ⟨⟨ofAff_rel hx.1, ofG2_rel hx.2⟩, ih h.2⟩
    rw [toFq12_eq (millerProd_rel hl)]
    rfl
  · rfl

@[csimp] theorem pairingCheck_csimp : @JamCrypto.Pairing.pairingCheck = @pairingCheck :=
  funext fun ps => (pairingCheck_eq ps).symm

end JamCrypto.Fast.PairingFq
