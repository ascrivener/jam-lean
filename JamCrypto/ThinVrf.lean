import JamCrypto.Bandersnatch
import JamCrypto.Reading

/-!
# Bandersnatch Thin VRF (GP v0.8.1 Appendix G)

GP v0.8.1 (GP #550) defines the singly-contextualized Bandersnatch signatures
$\overset{\backsim}{\mathbb{V}}{}_k^{m}\langle c\rangle$ under the **Thin VRF** of the Bandersnatch
VRF-AD specification (Galassi–Hosseini, **Draft 35**, 12 Aug 2026,
github.com/davxy/bandersnatch-vrf-spec commit 181aba2), suite `Bandersnatch-SHA512-ELL2-v1`. This
file follows that draft; section numbers below are its own. The v0.8.0 IETF VRF
(`JamCrypto.Bandersnatch.ietfVerify`) is left as it is.

* Transcript (§1.6.1, App. A.1): SHA-512 over `suite_id` and everything absorbed; a squeeze
  finalizes it to a 64-octet seed and reads the stream $\text{SHA-512}(\text{seed} \frown
  \text{enc}\_\text{64}(i))$, $i = 0, 1, \dots$. Every squeeze here is the first squeeze of its transcript,
  so a transcript is just the octets absorbed so far.
* hash_to_curve (§1.6.2, App. A.2): RFC 9380 `_RO_` with expand_message_xmd(SHA-512) and Elligator
  2, $\text{DST} = \text{suite}\_\text{id} \frown \texttt{0x60}$. The zero prefix $Z_{\text{pad}}$ depends
  on the `Reading` (default `.prose`): 128 octets under `.prose`, as RFC 9380 §5.3.1 step 4 has it
  for SHA-512 ($\text{s}\_\text{in}\_\text{bytes} = 128$) and App. A.2 cites; 48 octets under `.vectors`, which
  the draft's vectors and printed constants need (Draft 36 later states this deviation from RFC 9380
  explicitly). The rest of A.2 is RFC 9380 as written: $Z = 5$ (App. H.3), the Elligator 2 sign rule
  of §6.7.1, the rational map of App. D.1, a cofactor of 4, and 48 octets per field element.
* output (§1.6.3): $o = \text{squeeze}\_\text{32}(\text{suite}\_\text{id} \frown \texttt{0x20} \frown
  \text{enc}\_\text{point}(O))$; GP takes the first 32 octets.
* Thin VRF (§3) with one I/O pair $(I, O)$, $I = \text{hash}\_\text{to}\_\text{curve}(c)$, additional data $m$:
  the pairs are $[(G, Y), (I, O)]$, merged by delinearization (§1.6.4) into $(I_m, O_m) = (G + z
  \cdot I, Y + z \cdot O)$; the proof $(R, s)$ satisfies $s \cdot I_m = R + c \cdot O_m$ with $c =
  \text{challenge}([R], T)$ (§1.6.7).

**Signature encoding (our reading of GP v0.8.1 and Draft 35; Adam, 2026-11-25).** GP gives
$\overset{\backsim}{\mathbb{V}}$ as 96-octet strings and reads $\mathcal{Y}$ from the signature alone, but the
draft encodes only the proof $(R, s)$, 64 octets. We take the 96-octet signature to be
$\text{enc}\_\text{point}(O) \frown \text{enc}\_\text{point}(R) \frown \text{enc}\_\text{scalar}(s)$, the output point
first as in the v0.8.0 IETF signature ($O \frown c \frown s$) and the ring VRF proof ($O \frown
\text{proof}$). `thinEncode`/`thinDecode` are the only places that fix this order.
-/

namespace JamCrypto.Bandersnatch.Thin

open JamCrypto.Modular
open JamCrypto.Bandersnatch (curve G r encode decode elligator2 q)

/-- suite_id (§1.4). -/
def suiteId : List UInt8 := "Bandersnatch-SHA512-ELL2-v1".toUTF8.toList

/-! ## Domain separation tags (§1.4) -/

def tagThinVrf : UInt8 := 0x01
def tagNonceExpand : UInt8 := 0x10
def tagNonce : UInt8 := 0x11
def tagPointToHash : UInt8 := 0x20
def tagDelinearize : UInt8 := 0x30
def tagChallenge : UInt8 := 0x40
def tagHashToCurve : UInt8 := 0x60

/-- challenge_len (§1.4). -/
def challengeLen : Nat := 16
/-- expanded_scalar_len (§1.4). -/
def expandedScalarLen : Nat := 48

/-- enc_64 (§1.5): 8 octets little-endian. -/
def enc64 (n : Nat) : List UInt8 := natToLE 8 n

/-- enc_scalar (§1.5). -/
def encScalar (s : Nat) : List UInt8 := natToLE 32 s

/-- dec_scalar_mod (§1.5). -/
def decScalarMod (bs : List UInt8) : Nat := leToNat bs % r

/-! ## Transcript (§1.6.1, App. A.1) -/

/-- A transcript before its first squeeze: the octets absorbed after `suite_id`. -/
structure Transcript where
  absorbed : List UInt8

/-- new_transcript(). -/
def Transcript.new : Transcript := ⟨[]⟩

/-- absorb(data). -/
def Transcript.absorb (t : Transcript) (data : List UInt8) : Transcript := ⟨t.absorbed ++ data⟩

/-- The first $n$ octets squeezed from the transcript (counter-mode XOF over SHA-512). -/
def Transcript.squeeze (t : Transcript) (n : Nat) : List UInt8 :=
  let seed := JAM.Sha512.hash (suiteId ++ t.absorbed)
  ((List.range ((n + 63) / 64)).flatMap fun i => JAM.Sha512.hash (seed ++ enc64 i)).take n

/-! ## Hash to curve (§1.6.2, App. A.2) -/

/-- $\text{DST} = \text{suite}\_\text{id} \frown \text{HashToCurve}$. -/
def dst : List UInt8 := suiteId ++ [tagHashToCurve]

/-- The length of $Z_{\text{pad}}$: 128 octets (RFC 9380 §5.3.1, s_in_bytes of SHA-512) under the
    prose reading, 48 under the vectors' reading. -/
def zPadLen : Reading → Nat
  | .prose => 128
  | .vectors => 48

/-- expand_message_xmd (RFC 9380 §5.3.1) with $H = \text{SHA-512}$ and a zero prefix of `zPad`
    octets (RFC 9380: `zPad` = s_in_bytes = 128): `len` uniform octets for `msg` under `dst`. The
    RFC's step 2 aborts for $\text{ell} > 255$, `len` > 65535 or $|\text{DST}| > 255$; no caller
    here comes near those bounds, so they are not checked. -/
def expandMessageXmd (zPad : Nat) (dst msg : List UInt8) (len : Nat) : List UInt8 := Id.run do
  let dstPrime := dst ++ [UInt8.ofNat dst.length]
  let ell := (len + 63) / 64
  let b0 := JAM.Sha512.hash
    (List.replicate zPad 0 ++ msg ++ [UInt8.ofNat (len / 256), UInt8.ofNat len, 0] ++ dstPrime)
  let mut prev := JAM.Sha512.hash (b0 ++ [1] ++ dstPrime)
  let mut out := prev
  for i in [2:ell + 1] do
    prev := JAM.Sha512.hash ((b0.zip prev).map (fun (u, v) => u ^^^ v) ++ [UInt8.ofNat i] ++ dstPrime)
    out := out ++ prev
  return out.take len

/-- expand_message_xmd for hash_to_curve: 96 output octets under the suite's DST, with the
    $Z_{\text{pad}}$ of the reading `rd`. -/
def expandMessage (msg : List UInt8) (rd : Reading := .prose) : List UInt8 :=
  expandMessageXmd (zPadLen rd) dst msg 96

/-- hash_to_curve under the reading `rd`: hash_to_field (two elements, 48 octets each, big-endian
    mod $q$), Elligator 2 on each, add, clear the cofactor 4. -/
def hashToCurve (data : List UInt8) (rd : Reading := .prose) : Option Point := do
  let u := expandMessage data rd
  let P0 ← elligator2 (beToNat (u.take 48) % q)
  let P1 ← elligator2 (beToNat (u.drop 48) % q)
  let P := curve.smul 4 (curve.add P0 P1)
  guard (curve.valid P)
  return P

/-! ## Procedures -/

/-- The VRF output hash (§1.6.3), $N$ octets. -/
def output (O : Point) (n : Nat := 32) : List UInt8 :=
  (Transcript.new.absorb ([tagPointToHash] ++ encode O)).squeeze n

/-- $\text{vrf}\_\text{transcript}(\text{ThinVrf}, [(G, Y), (I, O)], \mathit{ad})$ (§1.6.5) and
    delinearization (§1.6.4): the transcript and the merged pair $(I_m, O_m)$. -/
def vrfTranscript (Y I O : Point) (ad : List UInt8) : Transcript × Point × Point :=
  let t := Transcript.new.absorb
    ([tagThinVrf] ++ enc64 2 ++ encode G ++ encode Y ++ encode I ++ encode O ++ enc64 ad.length ++ ad)
  let z := decScalarMod ((t.absorb [tagDelinearize]).squeeze challengeLen)
  (t, curve.add G (curve.smul z I), curve.add Y (curve.smul z O))

/-- $\text{nonce}(d, T)$ (§1.6.6). -/
def nonce (d : Nat) (t : Transcript) : Nat :=
  let h := (t.absorb ([tagNonceExpand] ++ encScalar d)).squeeze 64
  decScalarMod ((t.absorb ([tagNonce] ++ h)).squeeze expandedScalarLen)

/-- $\text{challenge}([R], T)$ (§1.6.7). -/
def challenge (R : Point) (t : Transcript) : Nat :=
  decScalarMod ((t.absorb ([tagChallenge] ++ encode R)).squeeze challengeLen)

/-! ## Thin VRF (§3) -/

/-- The 96-octet signature of the output point $O$ and the proof $(R, s)$ (assumed layout, see the
    module comment). -/
def thinEncode (O R : Point) (s : Nat) : List UInt8 := encode O ++ encode R ++ encScalar s

/-- The output point, $R$ and $s$ of a 96-octet signature; `none` if a point does not decode to the
    prime subgroup or $s \ge r$ (dec_point, dec_scalar of §1.5). -/
def thinDecode (sig : List UInt8) : Option (Point × Point × Nat) := do
  guard (sig.length == 96)
  let O ← decode (sig.take 32)
  let R ← decode (slice sig 32 32)
  let s := leToNat (slice sig 64 32)
  guard (s < r)
  return (O, R, s)

/-- Thin VRF prove (§3.1) for one I/O pair: $(O, R, s)$; `none` only if `ctx` does not hash to the
    curve. -/
def proveParts (x : Nat) (ctx ad : List UInt8) (rd : Reading := .prose) :
    Option (Point × Point × Nat) := do
  let I ← hashToCurve ctx rd
  let Y := curve.smul x G
  let O := curve.smul x I
  let (t, Im, _) := vrfTranscript Y I O ad
  let k := nonce x t
  let R := curve.smul k Im
  let c := challenge R t
  return (O, R, (k + c * x) % r)

/-- $x \in \overset{\backsim}{\mathbb{V}}{}_k^{m}\langle c\rangle$ (GP v0.8.1): the 96-octet `sig` is a
    valid Thin VRF signature under the key `key` for VRF input data `ctx` and additional data `msg`
    (§3.2), under the reading `rd`. -/
def verify (key ctx msg sig : List UInt8) (rd : Reading := .prose) : Bool := Id.run do
  if key.length != 32 then return false
  let some Y := decode key | return false
  let some (O, R, s) := thinDecode sig | return false
  let some I := hashToCurve ctx rd | return false
  -- step 1: Y, I and O must not be the identity (R may be)
  if curve.isZero Y || curve.isZero I || curve.isZero O then return false
  let (t, Im, Om) := vrfTranscript Y I O msg
  let c := challenge R t
  let lhs := curve.smul s Im
  let rhs := curve.add R (curve.smul c Om)
  return curve.valid lhs && curve.valid rhs && curve.eq lhs rhs

/-- $\mathcal{Y}(\text{sig})$ (GP v0.8.1 Appendix G): $\text{output}(O)$ of the signature's output
    point, 32 octets. For an encoding that does not decode to a point on the curve (no valid
    signature has one) it hashes the 32 octets as given in its place. -/
def vrfOutput (sig : List UInt8) : List UInt8 :=
  match Bandersnatch.decodeOnCurve (sig.take 32) with
  | some O => output O
  | none => (Transcript.new.absorb ([tagPointToHash] ++ sig.take 32)).squeeze 32

/-- The secret scalar of a seed (App. A.3). -/
def secretOfSeed (seed : List UInt8) : Nat := Id.run do
  let d := decScalarMod seed
  for i in [0:256] do
    let t := Transcript.new.absorb (seed ++ (if i == 0 then [] else [UInt8.ofNat i]))
    let x := nonce d t
    if x != 0 then return x
  return 1

/-- The public key $[x]G$. -/
def publicKey (x : Nat) : List UInt8 := encode (curve.smul x G)

/-- The 96-octet Thin VRF signature of the secret $x$ for VRF input data `ctx` and additional data
    `msg` under the reading `rd`; `none` only if `ctx` does not hash to the curve. -/
def sign (x : Nat) (ctx msg : List UInt8) (rd : Reading := .prose) : Option (List UInt8) := do
  let (O, R, s) ← proveParts x ctx msg rd
  return thinEncode O R s

/-- $\mathcal{Y}$ of the signature `sign x ctx _` would give, without signing. -/
def signOutput (x : Nat) (ctx : List UInt8) (rd : Reading := .prose) : Option (List UInt8) := do
  let I ← hashToCurve ctx rd
  return output (curve.smul x I)

end JamCrypto.Bandersnatch.Thin
