import JamCrypto.Fast.G1
import JamCrypto.Fast.PairingF

/-!
# The BLS12-381 pairing check on `Fast.Fq`, swapped in for the reference by `@[csimp]`

`pairingCheck` computes `JamCrypto.Pairing.pairingCheck` with `Fast.PairingF` on the fixed-limb
field `Fast.Fq`, and is proved equal to it. The line coefficients of the ring SRS's two G2 points
are computed once (`srsLines`) and used whenever a pair's G2 point is one of them. The points are converted when their coordinates are
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

/-- Equality of reference G2 points, coordinate by coordinate. -/
def eqG2 (a b : JamCrypto.Pairing.G2) : Bool :=
  a.x.a == b.x.a && a.x.b == b.x.b && a.y.a == b.y.a && a.y.b == b.y.b && a.inf == b.inf

theorem eq_of_eqG2 {a b : JamCrypto.Pairing.G2} (h : eqG2 a b = true) : a = b := by
  obtain ⟨⟨xa, xb⟩, ⟨ya, yb⟩, i⟩ := a
  obtain ⟨⟨xa', xb'⟩, ⟨ya', yb'⟩, i'⟩ := b
  simp only [eqG2, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

/-- The two G2 points of the ring SRS ([1]G2 and [τ]G2, `JamCryptoTest/data/…-zcash.bin`), whose
    line coefficients every ring proof verification needs. -/
def srsG2 : List JamCrypto.Pairing.G2 := [
  ⟨⟨352701069587466618187139116011060144890029952792775240219908644239793785735715026873347600343865175952761926303160,
      3059144344244213709971259814753781636986470325476647558659373206291635324768958432433509563104347017837885763365758⟩,
    ⟨1985150602287291935568054521177171638300868978215655730859378665066344726373823718423869104263333984641494340347905,
      927553665492332455747201965776037880757740193453592970025027978793976877002675564980949289727957565575433344219582⟩, false⟩,
  ⟨⟨186544079744757791750913777923182116923406997981176124505869835669370349308168084101869919858020293159217147453183,
      2680951345815209329447762511030627858997446358927866220189443219836425021933771668894483091748402109907600527683136⟩,
    ⟨2902268288386460594512721059125470579172313681349425350948444194000638363935297586336373516015117406788334505343385,
      1813420068648567014729235095042931383392721750833188405957278380281750025472382039431377469634297470981522036543739⟩, false⟩]

/-- Their line coefficients, computed once. -/
def srsLines : List (JamCrypto.Pairing.G2 × Array (E12 E × E12 E)) :=
  srsG2.map fun q => (q, PairingF.lines (ofG2 q))

/-- The line coefficients of `q`: the precomputed ones for an SRS point, else computed. -/
def linesOf (q : JamCrypto.Pairing.G2) : Array (E12 E × E12 E) :=
  match srsLines.find? (fun e => eqG2 e.1 q) with
  | some e => e.2
  | none => PairingF.lines (ofG2 q)

theorem linesOf_rel {q : JamCrypto.Pairing.G2} (h : redG2 q = true) :
    ArrRel LRel (linesOf q) (JamCrypto.Pairing.lines q) := by
  unfold linesOf
  split
  · rename_i e he
    have hq : e.1 = q := eq_of_eqG2 (List.find?_some (p := fun e : JamCrypto.Pairing.G2 × Array (E12 E × E12 E) => eqG2 e.1 q) he)
    have hm : e ∈ srsLines := List.mem_of_find?_eq_some he
    unfold srsLines at hm
    obtain ⟨q', -, rfl⟩ := List.mem_map.mp hm
    simp only at hq ⊢
    subst hq
    exact lines_rel (ofG2_rel h)
  · exact lines_rel (ofG2_rel h)

/-- `Pairing.pairingCheck`. -/
def pairingCheck (pairs : List (JamCrypto.G1.Aff × JamCrypto.Pairing.G2)) : Bool :=
  if pairs.all redPair then
    toFq12 (PairingF.finalExp (millerProd (pairs.map fun pq => (ofAff pq.1, ofG2 pq.2, linesOf pq.2)))) ==
      JamCrypto.Pairing.Fq12.one
  else JamCrypto.Pairing.pairingCheck pairs

theorem pairingCheck_eq (pairs : List (JamCrypto.G1.Aff × JamCrypto.Pairing.G2)) :
    pairingCheck pairs = JamCrypto.Pairing.pairingCheck pairs := by
  unfold pairingCheck
  split
  · rename_i h
    have hl : PairingF.ListRel PairingF.PRel
        (pairs.map fun pq => ((ofAff pq.1 : AF E), ofG2 pq.2, linesOf pq.2)) pairs := by
      induction pairs with
      | nil => trivial
      | cons x xs ih =>
        simp only [List.all_cons, Bool.and_eq_true] at h
        have hx := h.1
        simp only [redPair, Bool.and_eq_true] at hx
        have ha := hx.1
        simp only [redA, Bool.and_eq_true, decide_eq_true_eq] at ha
        exact ⟨⟨ofAff_rel ha, ofG2_rel hx.2, linesOf_rel hx.2⟩, ih h.2⟩
    rw [toFq12_eq (millerProd_rel hl)]
    rfl
  · rfl

@[csimp] theorem pairingCheck_csimp : @JamCrypto.Pairing.pairingCheck = @pairingCheck :=
  funext fun ps => (pairingCheck_eq ps).symm

end JamCrypto.Fast.PairingFq
