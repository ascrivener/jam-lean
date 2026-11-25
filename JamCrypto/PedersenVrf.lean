import JamCrypto.ThinVrf

/-!
# Bandersnatch Pedersen VRF (VRF-AD spec Draft 35 §4, GP v0.8.1)

The Pedersen VRF that GP v0.8.1's ring VRF builds on (Draft 35 §5: a ring VRF proof is a Pedersen
proof and a ring proof). It shares the suite, transcript, hash-to-curve and output of
`JamCrypto.Bandersnatch.Thin`. With one I/O pair (I, O) the delinearization of §1.6.4 returns the
pair unchanged (it still absorbs nothing into the caller's transcript, since it works on a fork).

Prove (§4.1): T = vrf_transcript(PedersenVrf, [(I, O)], ad); b = blinding(x, fork T) (App. A.4);
Ȳ = x·G + b·B; T absorbs enc_point(Ȳ); k = nonce(x, fork T), k_b = nonce(b, fork T);
R = k·G + k_b·B, O_k = k·I; c = challenge([R, O_k], T); s = k + c·x, s_b = k_b + c·b.

Verify (§4.2): Ȳ, I and O in 𝔾 and not the identity, R and O_k in 𝔾 (the identity allowed);
O_k + c·O = s·I and R + c·Ȳ = s·G + s_b·B.

The 160-octet proof is enc_point(Ȳ) ⌢ enc_point(R) ⌢ enc_point(O_k) ⌢ enc_scalar(s) ⌢
enc_scalar(s_b), the field order of §4 (aggregate encoding, §1.5).
-/

namespace JamCrypto.Bandersnatch.Pedersen

open JamCrypto.Modular
open JamCrypto.Bandersnatch (curve G r encode decode)
open JamCrypto.Bandersnatch.Thin

def tagPedersenVrf : UInt8 := 0x02
def tagPedersenBlinding : UInt8 := 0x12

/-- The blinding base B (§4), hash_to_curve("pedersen-blinding"). -/
def blindingBase : Point :=
  curve.ofAffine 23335687741101763108036518445642207119627658113885888016488710494487028845889
    5552214580375038693022409684979828600325210968745774080859660443337357929963

/-- vrf_transcript(PedersenVrf, [(I, O)], ad) (§1.6.5). -/
def vrfTranscript (I O : Point) (ad : List UInt8) : Transcript :=
  Transcript.new.absorb
    ([tagPedersenVrf] ++ enc64 1 ++ encode I ++ encode O ++ enc64 ad.length ++ ad)

/-- blinding(x, T) (App. A.4). -/
def blinding (x : Nat) (t : Transcript) : Nat := nonce x (t.absorb [tagPedersenBlinding])

/-- A Pedersen proof (§4). -/
structure Proof where
  pkCom : Point
  R : Point
  Ok : Point
  s : Nat
  sb : Nat
  deriving Inhabited

/-- The 160-octet encoding. -/
def Proof.encode (p : Proof) : List UInt8 :=
  Bandersnatch.encode p.pkCom ++ Bandersnatch.encode p.R ++ Bandersnatch.encode p.Ok ++
    encScalar p.s ++ encScalar p.sb

/-- Decoding: points in the prime subgroup, scalars below r. -/
def Proof.decode (bs : List UInt8) : Option Proof := do
  guard (bs.length == 160)
  let pkCom ← Bandersnatch.decode (bs.take 32)
  let R ← Bandersnatch.decode (slice bs 32 32)
  let Ok ← Bandersnatch.decode (slice bs 64 32)
  let s := leToNat (slice bs 96 32)
  let sb := leToNat (slice bs 128 32)
  guard (s < r && sb < r)
  return { pkCom, R, Ok, s, sb }

/-- The challenge of a proof for (I, O, ad). -/
def proofChallenge (I O : Point) (ad : List UInt8) (pkCom R Ok : Point) : Nat :=
  let t := (vrfTranscript I O ad).absorb (Bandersnatch.encode pkCom)
  decScalarMod ((t.absorb ([tagChallenge] ++ Bandersnatch.encode R ++ Bandersnatch.encode Ok)).squeeze challengeLen)

/-- Pedersen prove (§4.1) for the input point I: the proof and the blinding factor b. -/
def prove (x : Nat) (I : Point) (ad : List UInt8) : Proof × Nat :=
  let O := curve.smul x I
  let t := vrfTranscript I O ad
  let b := blinding x t
  let pkCom := curve.add (curve.smul x G) (curve.smul b blindingBase)
  let t := t.absorb (Bandersnatch.encode pkCom)
  let k := nonce x t
  let kb := nonce b t
  let R := curve.add (curve.smul k G) (curve.smul kb blindingBase)
  let Ok := curve.smul k I
  let c := decScalarMod ((t.absorb ([tagChallenge] ++ Bandersnatch.encode R ++ Bandersnatch.encode Ok)).squeeze challengeLen)
  ({ pkCom, R, Ok, s := (k + c * x) % r, sb := (kb + c * b) % r }, b)

/-- Pedersen verify (§4.2) for the input point I and output point O. -/
def verify (I O : Point) (ad : List UInt8) (p : Proof) : Bool :=
  if curve.isZero p.pkCom || curve.isZero I || curve.isZero O then false else
  let c := proofChallenge I O ad p.pkCom p.R p.Ok
  let l0 := curve.add p.Ok (curve.smul c O)
  let r0 := curve.smul p.s I
  let l1 := curve.add p.R (curve.smul c p.pkCom)
  let r1 := curve.add (curve.smul p.s G) (curve.smul p.sb blindingBase)
  [l0, r0, l1, r1].all curve.valid && curve.eq l0 r0 && curve.eq l1 r1

end JamCrypto.Bandersnatch.Pedersen
