import JamCrypto.Edwards
import JAM.Sha512

/-!
# Bandersnatch IETF VRF (GP v0.8.0 Appendix G)

𝔹̄_k⟨c⟩⟨m⟩ is the IETF VRF of the Bandersnatch VRF-AD specification (Hosseini–Galassi, the draft GP
cites), suite `Bandersnatch_SHA-512_ELL2`, with VRF input data c and additional data m; Y is its
output. The 96-octet signature is the output point O, then the proof (c, s), 32 octets each.

Choices the spec's prose leaves open or states differently from its own test vectors follow those
vectors and ark-vrf 0.1.0, which produce them:

* the challenge is the first 32 octets of the SHA-512 transcript hash read **big-endian**, reduced
  mod r, and stored little-endian (the prose says cLen = 16 and little-endian, which would not fit
  GP's 96-octet signatures);
* hash-to-curve is RFC 9380 `expand_message_xmd` (SHA-512) with a zero prefix Z_pad of 48 octets
  (arkworks 0.5; RFC 9380 uses the hash block size, 128), field elements read big-endian mod q,
  and the arkworks Elligator 2 map, whose sign choice is "y odd for the first candidate";
* points: y little-endian (must be < q), the top bit of the last octet set iff x > (q−1)/2 (the
  top bit is ignored when x = 0); decoded points must lie in the prime-order subgroup;
* c is reduced mod r; s must be below r.
-/

namespace JamCrypto.Bandersnatch

open JamCrypto.Modular

/-- The base field order q (the BLS12-381 scalar field). -/
def q : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The prime subgroup order r. -/
def r : Nat := 0x1cfb69d4ca675f520cce760202687600ff8f87007419047174fd06b52876e7e1

/-- Bandersnatch in twisted Edwards form: a = −5. -/
def curve : Curve :=
  { p := q, a := q - 5,
    d := 45022363124591815672509500913686876175488063829319466900776701791074614335719 }

/-- The prime subgroup generator. -/
def G : Point :=
  curve.ofAffine 18886178867200960497001835917649091219057080094937609519140440539760939937304
    19188667384257783945677642223292697773471335439753913231509108946878080696678

/-- √n in 𝔽_q: q − 1 = 2^32·t, and 7 is a non-residue. -/
def sqrt (n : Nat) : Option Nat :=
  sqrtTS q 32 12208678567578594777604504606729831043093128246378069236549469339647 7 n

/-- The 32-octet encoding of a valid point. -/
def encode (P : Point) : List UInt8 :=
  let (x, y) := curve.toAffine P
  natToLE 32 (y + (if x > (q - 1) / 2 then 2 ^ 255 else 0))

/-- The point a 32-octet encoding stands for, on the curve but not necessarily in the subgroup. -/
def decodeOnCurve (bs : List UInt8) : Option Point := do
  guard (bs.length == 32)
  let n := leToNat bs
  let negative := n / 2 ^ 255 == 1
  let y := n % 2 ^ 255
  guard (y < q)
  let y2 := y * y % q
  let den := subMod curve.a (curve.d * y2 % q) q
  guard (den != 0)
  let x ← sqrt (subMod 1 y2 q * invMod den q % q)
  let small := min x (subMod 0 x q)
  let large := max x (subMod 0 x q)
  return curve.ofAffine (if negative then large else small) y

/-- A point of the prime-order subgroup: [r]P = 0, checked as [r − 1]P = −P so that no step of the
    multiplication is exceptional. -/
def inSubgroup (P : Point) : Bool := curve.eq (curve.smul (r - 1) P) (curve.neg P)

/-- string_to_point: the subgroup point a 32-octet encoding stands for. -/
def decode (bs : List UInt8) : Option Point := do
  let P ← decodeOnCurve bs
  guard (inSubgroup P)
  return P

/-- The suite string. -/
def suiteString : List UInt8 := "Bandersnatch_SHA-512_ELL2".toUTF8.toList

/-- The hash-to-curve domain separation tag: "ECVRF_" ⌢ h2c suite id ⌢ suite string. -/
def dst : List UInt8 :=
  "ECVRF_".toUTF8.toList ++ "Bandersnatch_XMD:SHA-512_ELL2_RO_".toUTF8.toList ++ suiteString

/-- expand_message_xmd (RFC 9380 §5.3.1) with SHA-512, 96 output octets, and the arkworks 0.5
    zero prefix of 48 octets. -/
def expandMessage (msg : List UInt8) : List UInt8 :=
  let dstPrime := dst ++ [UInt8.ofNat dst.length]
  let b0 := JAM.Sha512.hash (List.replicate 48 0 ++ msg ++ [0, 96, 0] ++ dstPrime)
  let b1 := JAM.Sha512.hash (b0 ++ [1] ++ dstPrime)
  let b2 := JAM.Sha512.hash ((b0.zip b1).map (fun (u, v) => u ^^^ v) ++ [2] ++ dstPrime)
  (b1 ++ b2).take 96

/-- Montgomery-form constants of arkworks' Bandersnatch `Elligator2Config`. -/
def montB : Nat := 25465760566081946422412445027709227188579564747101592991722834452325077642517
def montAoverB : Nat := 22511181562295907836254750456843438087744031914659733450388350895537307167857
def oneOverB2 : Nat := 35484827650731063748396669747216844996598387089274032563585525486049249153249

/-- The arkworks 0.5 Elligator 2 map 𝔽_q → curve (Z = 5). -/
def elligator2 (u : Nat) : Option Point := do
  let k := montB
  let j := montAoverB
  let den1 := (1 + 5 * (u * u % q)) % q
  let x1 := subMod 0 (j * invMod (if den1 == 0 then 1 else den1) q % q) q
  let g := fun (x : Nat) => (x * x % q * x + j * (x * x % q) + x * oneOverB2) % q
  let gx1 := g x1
  let x2 := subMod (subMod 0 x1 q) j q
  let (x, odd) := if isSquare gx1 q then (x1, true) else (x2, false)
  let y0 ← sqrt (g x)
  let y := if (y0 % 2 == 1) != odd then subMod 0 y0 q else y0
  let s := x * k % q
  let t := y * k % q
  let tv1 := (s + 1) % q
  let tv2 := tv1 * t % q
  if tv2 == 0 then return curve.ofAffine 0 1
  let inv := invMod tv2 q
  return curve.ofAffine (inv * tv1 % q * s % q) (inv * t % q * subMod s 1 q % q)

/-- hash_to_curve (RFC 9380 §3) with Elligator 2, as ark-vrf 0.1.0 instantiates it. -/
def hashToCurve (data : List UInt8) : Option Point := do
  let u := expandMessage data
  let P0 ← elligator2 (beToNat (u.take 48) % q)
  let P1 ← elligator2 (beToNat (u.drop 48) % q)
  let P := curve.smul 4 (curve.add P0 P1)
  guard (curve.valid P)
  return P

/-- The challenge for the points and additional data (spec §1.10, ark-vrf 0.1.0). -/
def challenge (pts : List Point) (ad : List UInt8) : Nat :=
  let h := JAM.Sha512.hash (suiteString ++ [2] ++ pts.flatMap encode ++ ad ++ [0])
  beToNat (h.take 32) % r

/-- x ∈ 𝔹̄_k⟨c⟩⟨m⟩: the IETF VRF signature `sig` = O ⌢ c ⌢ s is valid under the public key `key`
    for VRF input data `ctx` and additional data `msg` (spec §2.3). -/
def ietfVerify (key ctx msg sig : List UInt8) : Bool := Id.run do
  if key.length != 32 || sig.length != 96 then return false
  let s := leToNat (slice sig 64 32)
  if s ≥ r then return false
  let c := leToNat (slice sig 32 32) % r
  let some Y := decode key | return false
  let some O := decode (sig.take 32) | return false
  let some I := hashToCurve ctx | return false
  let E := curve
  let U := E.sub (E.smul s G) (E.smul c Y)
  let V := E.sub (E.smul s I) (E.smul c O)
  if !(E.valid U && E.valid V) then return false
  return challenge [Y, I, O, U, V] msg == c

/-- The output hash of an output point: SHA-512(suite ⌢ 3 ⌢ point ⌢ 0) (RFC 9381 §5.2). -/
def pointToHash (O : Point) : List UInt8 :=
  JAM.Sha512.hash (suiteString ++ [3] ++ encode O ++ [0])

/-- Y(sig) (GP Appendix G): the first 32 octets of the output hash of the output point O, the
    first 32 octets of the signature. For an encoding that does not decode (no valid signature
    has one) it hashes the octets as given, like `JAM.Sha512.vrfOutput`. -/
def vrfOutput (sig : List UInt8) : List UInt8 :=
  match decodeOnCurve (sig.take 32) with
  | some O => (pointToHash O).take 32
  | none => JAM.Sha512.vrfOutput sig

end JamCrypto.Bandersnatch
