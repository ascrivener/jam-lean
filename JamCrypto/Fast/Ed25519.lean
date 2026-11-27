import JamCrypto.Fast.Fp25519
import JamCrypto.Fast.EdwardsF
import JamCrypto.Ed25519

/-!
# Ed25519 verification on fixed-limb field arithmetic, proved equal to the reference

`verifyWith` performs the same sequence of operations as `JamCrypto.Ed25519.verifyWith` (the
reference implementation, unchanged), on `Fast.Fp25519` instead of `Nat` mod $p$, and is proved
equal to it (`verifyWith_eq`) from the field laws of `Fast.Fp25519` and the curve lemmas of
`Fast.EdwardsF`.
-/

namespace JamCrypto.Fast.Ed25519

open JamCrypto.Fast
open JamCrypto.Modular (leToNat subMod invMod powMod)

attribute [local irreducible] JamCrypto.Modular.powMod JamCrypto.Modular.invMod
attribute [local irreducible] Fp25519.mul Fp25519.sq Fp25519.add Fp25519.sub Fp25519.ofNat Fp25519.toNat
  Fp25519.isZero Fp25519.beq JamCrypto.Fast.powF

abbrev F := Fp25519.Elem

local notation "p" => Field.p F

theorem curve_p : JamCrypto.Ed25519.curve.p = p := rfl
theorem p_eq : JamCrypto.Ed25519.p = p := rfl

/-- The curve constants $a = -1$ and $d$. -/
@[irreducible] def C : CurveF F := ⟨Field.ofNat JamCrypto.Ed25519.curve.a, Field.ofNat JamCrypto.Ed25519.curve.d⟩

theorem hC : C.Rel JamCrypto.Ed25519.curve := by
  unfold C; exact ⟨VRel.ofNat _, VRel.ofNat _, curve_p⟩

theorem vofNat (x : Nat) : VRel (Field.ofNat x : F) x := VRel.ofNat x
theorem vone : VRel (Field.one : F) 1 := VRel.one
theorem vzero : VRel (Field.zero : F) 0 := VRel.zero
theorem vmod {a : F} {n : Nat} (h : VRel a n) : VRel a (n % p) := VRel.mod.mpr h
theorem ltp (n : Nat) : n % p < p := lt_of_mod (F := F)

abbrev OP : Option (Pt F) → Option JamCrypto.Point → Prop := OR PRel

/-- As `Ed25519.decode`. -/
def decode (rules : JamCrypto.Ed25519.Rules) (bs : List UInt8) : Option (Pt F) := do
  guard (bs.length == 32)
  let n := leToNat bs
  let sign := n / 2 ^ 255
  let yy := n % 2 ^ 255
  if rules.canonicalPoints && yy ≥ JamCrypto.Ed25519.p then none
  let y : F := Field.ofNat yy
  let y2 := Field.mul y y
  let u := Field.sub y2 Field.one
  let v := Field.add (Field.mul (Field.ofNat JamCrypto.Ed25519.d) y2) Field.one
  let w := Field.mul u (invF v)
  let x0 := powF w ((JamCrypto.Ed25519.p + 3) / 8)
  let x ← if Field.beq (Field.mul x0 x0) w then some x0
    else if Field.beq (Field.mul x0 x0) (Field.sub Field.zero w) then
      some (Field.mul x0 (Field.ofNat JamCrypto.Ed25519.sqrtM1))
    else none
  if Field.toNat x == 0 && sign == 1 && rules.canonicalPoints then none
  let x := if Field.toNat x % 2 != sign then Field.sub Field.zero x else x
  return ofAffineF x y

theorem decode_rel (rules : JamCrypto.Ed25519.Rules) (bs : List UInt8) :
    OP (decode rules bs) (JamCrypto.Ed25519.decode rules bs) := by
  unfold decode JamCrypto.Ed25519.decode
  rw [p_eq]
  refine OR.guard Iff.rfl fun _ => ?_
  extract_lets n sign yy y y2 u v w x0 k kU y' y2' u' v' w' x0' k' kU'
  refine OR.ite (fun _ => trivial) fun _ => ?_
  have vy : VRel y y' := vmod (vofNat yy)
  have vy2 : VRel y2 y2' := vmod (vy.mul vy)
  have vu : VRel u u' := vy2.sub vone
  have vv : VRel v v' := vmod (((vofNat _).mul vy2).add vone)
  have vw : VRel w w' := vmod (vu.mul (invF_rel vv))
  have hw : w' < p := ltp _
  have vx0 : VRel x0 x0' := (powF_rel' vw _).1
  have hx0 : x0' < p := powMod_lt (F := F) _ _
  -- the continuation after x
  have hk : ∀ a b, VRel a b ∧ b < p → OP (k a) (k' b) := by
    rintro a b ⟨va, hb⟩
    simp only [k, k']
    rw [va.toNat, Nat.mod_eq_of_lt hb]
    refine OR.ite (fun _ => trivial) fun _ => ?_
    refine ofAffine_rel curve_p ?_ vy
    split
    · exact vzero.sub va
    · exact va
  simp only [kU, kU']
  rw [(vmod (vx0.mul vx0)).beq_lt vw (ltp _) hw,
    (vmod (vx0.mul vx0)).beq_lt (vzero.sub vw) (ltp _) (by unfold subMod; exact ltp _)]
  refine OR.ite (fun _ => OR.bind (R := fun a x => VRel a x ∧ x < p) ⟨vx0, hx0⟩ hk) fun _ => ?_
  refine OR.ite (fun _ => OR.bind (R := fun a x => VRel a x ∧ x < p) ⟨vmod (vx0.mul (vofNat _)), ltp _⟩ hk)
    fun _ => trivial

/-- The base point. -/
@[irreducible] def B : Pt F :=
  ofAffineF (Field.ofNat 15112221349535400772501151409588531511454012693041857206046113283949847762202)
    (Field.ofNat 46316835694926478169428394003475163141307993866256225615783033603165251855960)

theorem B_rel : PRel B JamCrypto.Ed25519.B := by
  unfold B; exact ofAffine_rel curve_p (vofNat _) (vofNat _)

/-- As `Ed25519.verifyWith`. -/
def verifyWith (rules : JamCrypto.Ed25519.Rules) (key msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 64 then return false
  let Rb := sig.take 32
  let S := leToNat (sig.drop 32)
  if S ≥ JamCrypto.Ed25519.L then return false
  let some A := decode rules key | return false
  let some R := decode rules Rb | return false
  let k := leToNat (JAM.Sha512.hash (Rb ++ key ++ msg)) % JamCrypto.Ed25519.L
  if rules.cofactored then
    return CurveF.isZero (C.smul 8 (C.sub (C.sub (C.smul S B) R) (C.smul k A)))
  else
    return CurveF.eq (C.smul S B) (C.add R (C.smul k A))

theorem verifyWith_eq (rules : JamCrypto.Ed25519.Rules) (key msg sig : List UInt8) :
    verifyWith rules key msg sig = JamCrypto.Ed25519.verifyWith rules key msg sig := by
  unfold verifyWith JamCrypto.Ed25519.verifyWith
  rw [Id.run, Id.run]
  by_cases h1 : (key.length != 32 || sig.length != 64) = true
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  have hA := decode_rel rules key
  have hR := decode_rel rules (sig.take 32)
  generalize decode rules key = a at hA ⊢
  generalize JamCrypto.Ed25519.decode rules key = a' at hA ⊢
  extract_lets Rb S k E
  generalize decode rules Rb = b at hR ⊢
  generalize JamCrypto.Ed25519.decode rules Rb = b' at hR ⊢
  by_cases h2 : S ≥ JamCrypto.Ed25519.L
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  cases a <;> cases a' <;> simp only [OR] at hA
  all_goals cases b <;> cases b' <;> simp only [OR] at hR
  all_goals dsimp (config := {zeta := false}) only
  rename_i A A' R R'
  have hp : E.p = p := curve_p
  by_cases h3 : rules.cofactored = true
  · rw [if_pos h3, if_pos h3]
    exact congrArg _ (isZero_eq hp (smul_rel hC 8 (sub_rel hC (sub_rel hC (smul_rel hC S B_rel) hR)
      (smul_rel hC k hA))))
  · rw [if_neg h3, if_neg h3]
    exact congrArg _ (eq_eq hp (smul_rel hC S B_rel) (add_rel hC hR (smul_rel hC k hA)))

/-- As `Ed25519.verify` (ZIP 215). -/
def verify (key msg sig : List UInt8) : Bool := verifyWith JamCrypto.Ed25519.zip215 key msg sig

theorem verify_eq (key msg sig : List UInt8) : verify key msg sig = JamCrypto.Ed25519.verify key msg sig :=
  verifyWith_eq _ key msg sig

end JamCrypto.Fast.Ed25519
