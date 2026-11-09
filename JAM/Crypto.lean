/-!
# Cryptographic primitives as parameters (GP v0.8.0 §3.8)

The model does not implement signature schemes. The state-transition functions that check
signatures take a `Crypto` whose fields stand for the paper's primitives; a caller supplies them (a
real implementation, or, in the vector tests, an oracle read from each vector's expected outcome).

Ed25519 verification is used by disputes, assurances and guarantees (§10–§11). Safrole (§6) uses
the Bandersnatch primitives of Appendix G (`sec:bandersnatch`): the IETF VRF signatures 𝔹̄_k⟨c⟩⟨m⟩
(header seal and entropy source) and the Ring VRF proofs 𝔹̄°_r⟨c⟩⟨m⟩ (tickets), their output Y, and
the ring root O.

The Bandersnatch fields default to rejecting every signature and proof and to empty outputs, so a
caller that needs only Ed25519 can write `{ edVerify := … }`. The defaults are placeholders, not
the primitives: a transition that uses a field must be given it.
-/

namespace JAM

/-- The cryptographic primitives the transitions use. -/
structure Crypto where
  /-- s ∈ 𝕍̄_k⟨m⟩ (GP §3.8.2): s is a valid Ed25519 signature on the message m under the public
      key k. -/
  edVerify : (key : List UInt8) → (msg : List UInt8) → (sig : List UInt8) → Bool
  /-- x ∈ 𝔹̄_k⟨c⟩⟨m⟩ (GP Appendix G): x is a valid Bandersnatch IETF VRF signature under the key k
      with context c and message m. -/
  bsVerify : (key : List UInt8) → (ctx : List UInt8) → (msg : List UInt8) → (sig : List UInt8) → Bool :=
    fun _ _ _ _ => false
  /-- Y(s) (GP Appendix G): the 32-octet VRF output of a Bandersnatch IETF VRF signature. -/
  bsOut : (sig : List UInt8) → List UInt8 := fun _ => []
  /-- O(**k**) (GP Appendix G): the ring root (commitment) of a sequence of Bandersnatch keys. A key
      with no corresponding curve point stands for the padding point; that is O's concern. -/
  bsRingRoot : (keys : List (List UInt8)) → List UInt8 := fun _ => []
  /-- x ∈ 𝔹̄°_r⟨c⟩⟨m⟩ (GP Appendix G): x is a valid Bandersnatch Ring VRF proof for the ring root r
      with context c and message m. -/
  bsRingVerify : (root : List UInt8) → (ctx : List UInt8) → (msg : List UInt8) → (proof : List UInt8) → Bool :=
    fun _ _ _ _ => false
  /-- Y(p) (GP Appendix G): the 32-octet VRF output of a Ring VRF proof. -/
  bsRingOut : (proof : List UInt8) → List UInt8 := fun _ => []

/-- The ASCII octets of a context string such as `$jam_valid` (GP §3.8.2, Appendix I.4.5). -/
def contextString (s : String) : List UInt8 := s.toUTF8.toList

end JAM
