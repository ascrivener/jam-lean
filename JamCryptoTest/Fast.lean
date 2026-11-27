import JamCrypto
import JamCrypto.Fast.Fp25519

/-!
# Differential tests of `JamCrypto.Fast` against the reference implementations

The fast implementations are proved equal to the reference ones (`Fast.withSignatures_eq` and the
theorems it rests on); these tests are an extra check of the same equalities. `runFast` compares them on randomized inputs (a fixed-seed generator, so runs are
reproducible): field arithmetic against `Nat` arithmetic mod p, and each verifier and output
function against its reference on valid signatures, mutated signatures and random octets.
Published vectors are compared by the callers (`cryptotest`, `ringtest`) as they read them.
-/

namespace JamCryptoTest.Fast

open JamCrypto JamCrypto.Modular

/-- A 64-bit linear congruential generator (Knuth's MMIX constants). -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s * 6364136223846793005 + 1442695040888963407
  (s ^^^ (s >>> 29), ⟨s⟩)

def Rng.nat (g : Rng) (words : Nat) : Nat × Rng := Id.run do
  let mut g := g
  let mut x := 0
  for _ in [0:words] do
    let (w, g') := g.next
    g := g'
    x := x * 2 ^ 64 + w.toNat
  return (x, g)

def Rng.bytes (g : Rng) (n : Nat) : List UInt8 × Rng := Id.run do
  let mut g := g
  let mut out : Array UInt8 := #[]
  for _ in [0:n] do
    let (w, g') := g.next
    g := g'
    out := out.push (w >>> 24).toUInt8
  return (out.toList, g)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.nat 1
  (x % n, g)

/-- Values that exercise limb boundaries: 0, 1, p − 1, p − 2, 2^32k ± 1, and so on. -/
def edgeValues (p : Nat) : List Nat :=
  [0, 1, 2, p - 1, p - 2, (p - 1) / 2, (p + 1) / 2] ++
    ((List.range 13).flatMap fun k => [2 ^ (32 * k), 2 ^ (32 * k) - 1, 2 ^ (32 * k) + 1]).filter (· < p)

structure FieldOps where
  name : String
  p : Nat
  /-- (a, b) ↦ the values of a·b, a + b, a − b, −a, a⁻¹, a² computed by the fast field. -/
  ops : Nat → Nat → Nat × Nat × Nat × Nat × Nat × Nat
  /-- The value round trip. -/
  roundTrip : Nat → Nat
  eq : Nat → Nat → Bool
  isSquare : Nat → Bool

def fieldOps : List FieldOps :=
  [ { name := "Fr", p := Fast.Fr.p,
      ops := fun a b => let (x, y) := (Fast.Fr.ofNat a, Fast.Fr.ofNat b)
        ((x * y).toNat, (x + y).toNat, (x - y).toNat, (-x).toNat, x.inv.toNat, x.sq.toNat)
      roundTrip := fun a => (Fast.Fr.ofNat a).toNat
      eq := fun a b => Fast.Fr.ofNat a == Fast.Fr.ofNat b
      isSquare := fun a => Fast.Fr.isSquare (Fast.Fr.ofNat a) },
    { name := "Fp25519", p := Fast.Fp25519.p,
      ops := fun a b => let (x, y) := (Fast.Fp25519.ofNat a, Fast.Fp25519.ofNat b)
        ((x * y).toNat, (x + y).toNat, (x - y).toNat, (-x).toNat, x.inv.toNat, x.sq.toNat)
      roundTrip := fun a => (Fast.Fp25519.ofNat a).toNat
      eq := fun a b => Fast.Fp25519.ofNat a == Fast.Fp25519.ofNat b
      isSquare := fun a => Fast.Fp25519.isSquare (Fast.Fp25519.ofNat a) } ]

/-- Field arithmetic against `Nat` mod p: every pair of edge values, and `n` random pairs (inverse
    and Euler's criterion on a tenth of them). Returns the number of mismatches. -/
def fieldTests (n : Nat) (log : String → IO Unit) : IO Nat := do
  let mut bad := 0
  let mut g : Rng := ⟨1⟩
  for f in fieldOps do
    let p := f.p
    let edges := edgeValues p
    let mut pairs : Array (Nat × Nat) := #[]
    for a in edges do
      for b in edges do
        pairs := pairs.push (a, b)
    for i in [0:n] do
      let (a, g1) := g.nat 7
      let (b, g2) := g1.nat 7
      g := g2
      -- also unreduced inputs (ofNat reduces): a may exceed p
      pairs := pairs.push (if i % 3 == 0 then a % (4 * p) else a % p, b % p)
    let mut i := 0
    for (a, b) in pairs do
      let (a', b') := (a % p, b % p)
      let (m, s, d, ng, iv, sq) := f.ops a b
      let ok := m == a' * b' % p && s == (a' + b') % p && d == (a' + p - b') % p
        && ng == (p - a') % p && sq == a' * a' % p && f.roundTrip a == a'
        && f.eq a b == (a' == b')
      let ok2 := i % 10 != 0 ||
        (iv == Modular.powMod a' (p - 2) p && f.isSquare a == Modular.isSquare a' p)
      unless ok && ok2 do
        log s!"field {f.name} mismatch at a = {a}, b = {b}"
        bad := bad + 1
      i := i + 1
  return bad


/-- A signature with octet i flipped in bit `bit`. -/
def flip (sig : List UInt8) (i bit : Nat) : List UInt8 :=
  sig.set i (sig[i]! ^^^ (1 <<< (bit % 8)).toUInt8)

/-- Mutations of a 96-octet signature: one flipped bit in each part, a random part, s + r. -/
def mutations (g : Rng) (sig : List UInt8) : List (List UInt8) × Rng := Id.run do
  let mut g := g
  let mut out : Array (List UInt8) := #[]
  for part in [0:3] do
    let (i, g1) := g.below 32
    let (b, g2) := g1.below 8
    let (rnd, g3) := g2.bytes 32
    g := g3
    out := out.push (flip sig (32 * part + i) b)
    out := out.push (sig.take (32 * part) ++ rnd ++ sig.drop (32 * part + 32))
  out := out.push (sig.take 64 ++ natToLE 32 (leToNat (sig.drop 64) + Bandersnatch.r))
  out := out.push (sig.take 95)
  return (out.toList, g)

/-- Encodings to decode: random octets (about half on the curve, an eighth in the subgroup), keys,
    and the encodings with the sign bit set on y = ±1 (x = 0). -/
def bsDecodeTests (n : Nat) (log : String → IO Unit) : IO Nat := do
  let mut bad := 0
  let mut g : Rng := ⟨7⟩
  let mut inputs : Array (List UInt8) := #[]
  for _ in [0:n] do
    let (bs, g') := g.bytes 32
    g := g'
    inputs := inputs.push bs
  inputs := inputs.push (natToLE 32 (1 + 2 ^ 255))
  inputs := inputs.push (natToLE 32 1)
  inputs := inputs.push (natToLE 32 (Bandersnatch.q - 1 + 2 ^ 255))
  inputs := inputs.push (natToLE 32 (Bandersnatch.q - 1))
  inputs := inputs.push (natToLE 32 0)
  inputs := inputs.push (natToLE 32 Bandersnatch.q)
  for bs in inputs do
    let r1 := (Bandersnatch.decodeOnCurve bs).map Bandersnatch.encode
    let f1 := (Fast.Bandersnatch.decodeOnCurve bs).map Fast.Bandersnatch.encode
    let r2 := (Bandersnatch.decode bs).map Bandersnatch.encode
    let f2 := (Fast.Bandersnatch.decode bs).map Fast.Bandersnatch.encode
    let ok := r1 == f1 && r2 == f2 && Bandersnatch.vrfOutput (bs ++ bs ++ bs) == Fast.Bandersnatch.vrfOutput (bs ++ bs ++ bs)
      && Bandersnatch.Thin.vrfOutput (bs ++ bs ++ bs) == Fast.Bandersnatch.Thin.vrfOutput (bs ++ bs ++ bs)
      && (Bandersnatch.hashToCurve bs).map Bandersnatch.encode
        == (Fast.Bandersnatch.hashToCurve bs).map Fast.Bandersnatch.encode
    unless ok do
      log s!"bandersnatch decode/output mismatch on {bs}"
      bad := bad + 1
  return bad

/-- Valid IETF and Thin VRF signatures of random secrets over random inputs, their mutations, other
    keys and other inputs: each fast verifier and output function against its reference. -/
def bsVerifyTests (n : Nat) (log : String → IO Unit) : IO Nat := do
  let mut bad := 0
  let mut g : Rng := ⟨42⟩
  for i in [0:n] do
    let (x, g1) := g.nat 4
    let (cl, g2) := g1.below 40
    let (ctx, g3) := g2.bytes cl
    let (ml, g4) := g3.below 40
    let (msg, g5) := g4.bytes ml
    g := g5
    let x := x % Bandersnatch.r
    let key := Bandersnatch.publicKey x
    let other := Bandersnatch.publicKey (x + 1)
    let rd : Reading := if i % 2 == 0 then .prose else .vectors
    let sigI := (Bandersnatch.ietfSign x ctx msg).getD []
    let sigT := (Bandersnatch.Thin.sign x ctx msg rd).getD []
    let (mI, g6) := mutations g sigI
    let (mT, g7) := mutations g6 sigT
    g := g7
    let cases := [(key, ctx, msg)] ++ [(other, ctx, msg), (key, ctx ++ [1], msg), (key, ctx, msg ++ [1])]
    for (k, c, m) in cases do
      for s in sigI :: sigT :: mI do
        unless Bandersnatch.ietfVerify k c m s == Fast.Bandersnatch.ietfVerify k c m s do
          log s!"ietf verify mismatch: x = {x}, ctx = {c}, msg = {m}, sig = {s}"
          bad := bad + 1
      for s in sigT :: sigI :: mT do
        unless Bandersnatch.Thin.verify k c m s rd == Fast.Bandersnatch.Thin.verify k c m s rd do
          log s!"thin verify mismatch: x = {x}, ctx = {c}, msg = {m}, sig = {s}"
          bad := bad + 1
    for s in [sigI, sigT] ++ mI ++ mT do
      unless Bandersnatch.vrfOutput s == Fast.Bandersnatch.vrfOutput s
          && Bandersnatch.Thin.vrfOutput s == Fast.Bandersnatch.Thin.vrfOutput s do
        log s!"output mismatch on {s}"
        bad := bad + 1
    -- the valid ones must verify (guards against both being wrong in the same way)
    unless Fast.Bandersnatch.ietfVerify key ctx msg sigI && Fast.Bandersnatch.Thin.verify key ctx msg sigT rd do
      log s!"valid signature rejected: x = {x}"
      bad := bad + 1
  return bad


/-- Ed25519 under all three rules: valid signatures of random seeds over random messages, their
    mutations, other keys and messages, random octets as keys, and non-canonical encodings. -/
def edTests (n : Nat) (log : String → IO Unit) : IO Nat := do
  let mut bad := 0
  let mut g : Rng := ⟨99⟩
  let rules := [Ed25519.zip215, Ed25519.rfc8032Strict, Ed25519.rfc8032Cofactorless]
  -- non-canonical and small-order encodings: y ≥ p, x = 0 with the sign bit, y = ±1, 0
  let p := Ed25519.p
  let specials := [natToLE 32 1, natToLE 32 (1 + 2 ^ 255), natToLE 32 (p - 1), natToLE 32 (p - 1 + 2 ^ 255),
    natToLE 32 0, natToLE 32 (2 ^ 255), natToLE 32 p, natToLE 32 (p + 1), natToLE 32 (p + 1 + 2 ^ 255),
    natToLE 32 (2 ^ 255 - 1), natToLE 32 (2 ^ 256 - 1)]
  for i in [0:n] do
    let (seed, g1) := g.bytes 32
    let (ml, g2) := g1.below 50
    let (msg, g3) := g2.bytes ml
    let (rk, g4) := g3.bytes 32
    let (rs, g5) := g4.bytes 64
    let (bi, g6) := g5.below 64
    let (bb, g7) := g6.below 8
    g := g7
    let key := Ed25519.publicKey seed
    let sig := Ed25519.sign seed msg
    let sp := specials[i % specials.length]!
    let sigs := [sig, flip sig bi bb, rs, sp ++ sig.drop 32, sig.take 32 ++ natToLE 32 (leToNat (sig.drop 32) + Ed25519.L),
      sig.take 63]
    let keys := [key, rk, sp, Ed25519.publicKey (seed.set 0 (seed[0]! + 1))]
    for r in rules do
      for k in keys do
        for s in sigs do
          for m in [msg, msg ++ [0]] do
            unless Ed25519.verifyWith r k m s == Fast.Ed25519.verifyWith r k m s do
              log s!"ed25519 mismatch: rules = {repr r}, key = {k}, msg = {m}, sig = {s}"
              bad := bad + 1
    unless Fast.Ed25519.verify key msg sig do
      log s!"ed25519 valid signature rejected: seed = {seed}"
      bad := bad + 1
  -- decoding alone, on random octets and the special encodings
  for i in [0:4 * n] do
    let (bs, g') := g.bytes 32
    g := g'
    for r in rules do
      for e in [bs, specials[i % specials.length]!] do
        let a := (Ed25519.decode r e).map fun P => Ed25519.curve.toAffine P
        let b := (Fast.Ed25519.decode r e).map fun P =>
          let zi := P.Z.inv
          ((P.X * zi).toNat, (P.Y * zi).toNat)
        unless a == b do
          log s!"ed25519 decode mismatch: rules = {repr r}, enc = {e}"
          bad := bad + 1
  return bad

end JamCryptoTest.Fast
