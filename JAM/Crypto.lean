/-!
# Cryptographic primitives as parameters (GP v0.8.0 §3.8)

The model does not implement signature schemes. The state-transition functions that check
signatures take a `Crypto` whose fields stand for the paper's primitives; a caller supplies them (a
real implementation, or, in the vector tests, an oracle read from each vector's expected outcome).

Only Ed25519 verification is needed so far (disputes, assurances and guarantees, §10–§11).
-/

namespace JAM

/-- The cryptographic primitives the transitions use. -/
structure Crypto where
  /-- s ∈ 𝕍̄_k⟨m⟩ (GP §3.8.2): s is a valid Ed25519 signature on the message m under the public
      key k. -/
  edVerify : (key : List UInt8) → (msg : List UInt8) → (sig : List UInt8) → Bool

/-- The ASCII octets of a context string such as `$jam_valid` (GP §3.8.2, Appendix I.4.5). -/
def contextString (s : String) : List UInt8 := s.toUTF8.toList

end JAM
