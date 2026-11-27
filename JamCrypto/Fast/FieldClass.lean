/-!
# The interface of a fast prime field, and what its operations are proved to compute

`Fast.Field F` gives the operations of a field 𝔽_p on a representation `F`; `Fast.LawfulField F`
states that each computes the corresponding `Nat` operation mod p on values (`value`), for reduced
elements (`Ok`). The generated fields (`Fast/Fr`, `Fast/Fq`, `Fast/Fp25519`) are instances; the
curve code is written once against this interface and its proofs use only these laws.
-/

namespace JamCrypto.Fast

class Field (F : Type) where
  p : Nat
  zero : F
  one : F
  add : F → F → F
  sub : F → F → F
  mul : F → F → F
  sq : F → F
  ofNat : Nat → F
  toNat : F → Nat
  beq : F → F → Bool
  isZero : F → Bool
  Ok : F → Prop
  value : F → Nat

class LawfulField (F : Type) [Field F] : Prop where
  one_lt_p : 1 < Field.p F
  ok_zero : Field.Ok (Field.zero : F)
  ok_one : Field.Ok (Field.one : F)
  value_zero : Field.value (Field.zero : F) = 0
  value_one : Field.value (Field.one : F) = 1
  value_lt : ∀ a : F, Field.value a < Field.p F
  ok_add : ∀ {a b : F}, Field.Ok a → Field.Ok b → Field.Ok (Field.add a b)
  ok_sub : ∀ {a b : F}, Field.Ok a → Field.Ok b → Field.Ok (Field.sub a b)
  ok_mul : ∀ {a b : F}, Field.Ok a → Field.Ok b → Field.Ok (Field.mul a b)
  ok_sq : ∀ {a : F}, Field.Ok a → Field.Ok (Field.sq a)
  ok_ofNat : ∀ x, Field.Ok (Field.ofNat x : F)
  value_add : ∀ {a b : F}, Field.Ok a → Field.Ok b →
    Field.value (Field.add a b) = (Field.value a + Field.value b) % Field.p F
  value_sub : ∀ {a b : F}, Field.Ok a → Field.Ok b →
    Field.value (Field.sub a b) = (Field.value a + Field.p F - Field.value b) % Field.p F
  value_mul : ∀ {a b : F}, Field.Ok a → Field.Ok b →
    Field.value (Field.mul a b) = Field.value a * Field.value b % Field.p F
  value_sq : ∀ {a : F}, Field.Ok a → Field.value (Field.sq a) = Field.value a * Field.value a % Field.p F
  value_ofNat : ∀ x, Field.value (Field.ofNat x : F) = x % Field.p F
  toNat_eq : ∀ {a : F}, Field.Ok a → Field.toNat a = Field.value a
  beq_eq : ∀ {a b : F}, Field.Ok a → Field.Ok b → Field.beq a b = (Field.value a == Field.value b)
  isZero_eq : ∀ {a : F}, Field.Ok a → Field.isZero a = (Field.value a == 0)

end JamCrypto.Fast
