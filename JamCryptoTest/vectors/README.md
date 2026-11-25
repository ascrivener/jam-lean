# JamCrypto test vectors

Read by `lake exe cryptotest` (`JamCryptoTest.lean`). One case per line, fields separated by one
space, octet strings in hex, `-` for the empty string.

## `ed25519.txt`

`tag zip215 rfc8032Strict rfc8032Cofactorless key msg sig`, where the three flags (1 = valid) are
the expected verdicts under the three `JamCrypto.Ed25519.Rules`.

* `rfc8032-*`: the five Ed25519 test vectors of RFC 8032 §7.1.
* `jam-zip215-*`: the 196 consensus-critical vectors of jam-conformance/jam-fuzzing (commit
  5bbd4266, `crypto/ed25519/vectors.json`, removed by #219): small-order A and R, s = 0, canonical
  and non-canonical encodings; ZIP 215 accepts all of them.
* `gen-*`: signatures from ed25519-dalek with deterministic random keys and messages, and their
  mutations: bit flips in R, S, key and message, S + L, torsion added to R, a 63-octet signature,
  and signatures whose R and/or A carry a torsion component but are otherwise consistent (valid
  under the cofactored equation only).

Expected verdicts: ZIP 215 from ed25519-zebra 4 (checked against a curve25519-dalek reference),
the strict variants from that reference (canonical encoding = re-encoding is identical).

## `bandersnatch_ietf.txt`

`tag valid key ctx msg sig Y`: `valid` is the verdict of x ∈ 𝔹̄_key⟨ctx⟩⟨msg⟩ and `Y` the VRF
output of a valid signature (`-` otherwise).

* `ark-vrf-*`: the 7 vectors of ark-vrf 0.1.0 (`data/vectors/bandersnatch_sha-512_ell2_ietf.json`,
  identical to those of the spec's Draft 29), with ctx = alpha, msg = ad, sig = gamma ⌢ c ⌢ s.
* `gen-*`: proofs from ark-vrf 0.1.0 with deterministic random keys, inputs and additional data,
  and mutations: bit flips in the output, c, s and key, another ctx or msg, c + r (accepted: c is
  reduced mod r), s + r (rejected), key or output plus the 2-torsion point (0, −1) (rejected), key
  with y + q (rejected), a 95-octet signature.

Expected verdicts: ark-vrf 0.1.0 verification after checked (`deserialize_compressed`) decoding of
the key, the output point and the proof.

## `bandersnatch_thin.txt`

The Thin VRF of GP v0.8.1 (`JamCrypto.Bandersnatch.Thin`, GP #550): the 7 vectors of the
Bandersnatch VRF-AD specification, Draft 35 (davxy/bandersnatch-vrf-spec commit 181aba2,
`assets/vectors/bandersnatch_sha-512_ell2_thin.json`, unchanged up to Draft 36),
`tag sk pk alpha ad h gamma beta proof_r proof_s`. `cryptotest` checks the public key, the input
point h, the output point gamma, the output hash beta, signing (byte for byte) and verification
of the 96-octet signature gamma ⌢ proof_r ⌢ proof_s (our assumed layout, see `ThinVrf.lean`).
It also checks that mutations are rejected (bit flips in O, R and s, s + r, another ad, input
or key, a 95-octet signature); those verdicts are ours, not from a reference.

## `bandersnatch_pedersen.txt`

The Pedersen VRF of GP v0.8.1's ring VRF (`JamCrypto.Bandersnatch.Pedersen`): the 7 vectors of
Draft 35 (same commit, `bandersnatch_sha-512_ell2_pedersen.json`),
`tag sk pk alpha ad h gamma beta blinding pk_com r ok s sb`. `cryptotest` checks the input point,
the blinding factor, proving (byte for byte), verification, the output hash, and that another ad
or s is rejected. It also checks that Draft 35's blinding base, ring accumulator and ring padding
points are hash_to_curve of "pedersen-blinding", "ring-accumulator" and "ring-padding". The ring
vectors of Draft 35 are in `JamCryptoTest/ring/ring-d35.txt` (`ringtest`).

All Draft 35 vectors (thin, pedersen, ring) are checked under `JamCrypto.Reading.vectors`; they
follow the vectors' reading of the draft (Z_pad of 48 octets, the suite id as the ring transcript
label). `cryptotest` and `ringtest` also check that they fail under `Reading.prose`, the default.
No published vectors follow `Reading.prose` (see `docs/jamcrypto.md`).

## `expand_message_xmd_sha512.txt`

`msg len uniform_bytes`: the ten expand_message_xmd(SHA-512) vectors of RFC 9380 Appendix K.3
(DST `QUUX-V01-CS02-with-expander-SHA512-256`, len 32 and 128), extracted from the RFC text and
checked against Python's hashlib. They check `Thin.expandMessageXmd` with the RFC's Z_pad of 128
octets, i.e. the hash to curve's expansion under `Reading.prose`: the only external oracle for any
part of that reading.

## `signing.txt`

Signing (`JamCrypto.Ed25519Sign`, `JamCrypto.BandersnatchSign`). Lean's signature must equal the
reference's byte for byte (both are deterministic), the public key must match, and our verifiers
must accept it.

* `ed TAG seed msg sig key`: `rfc8032-*` are the RFC 8032 §7.1 vectors with their secret keys
  (`generator/rfc8032_ed25519_secrets.txt`; the generator checks ed25519-dalek reproduces each
  signature); `gen-*` are ed25519-dalek signatures with deterministic random seeds and messages.
* `bssk TAG secret ctx msg sig key`: the 7 ark-vrf 0.1.0 IETF vectors (secret scalar
  little-endian, ctx = alpha, msg = ad).
* `bsseed TAG seed ctx msg sig key`: ark-vrf 0.1.0 `Secret::from_seed(seed)` and `prove`, seeds of
  32, 0, 1 and 64 octets.

`cryptotest` also checks the JIP-5 development keys (`JamCrypto.DevKeys`) against the six genesis
validators of the fuzzer's 0.8.0 sessions. `gen verify` (below) checks arbitrary signatures with
ed25519-dalek (`verify_strict`) and ark-vrf, e.g. those of a crafted block.

## Regenerating

```
git -C jam-fuzzing show c3c6fb23^:crypto/ed25519/vectors.json > jam_ed25519.json
cd JamCryptoTest/generator
cargo run --release -- rfc8032_ed25519.txt ../../jam_ed25519.json \
  ARK_VRF_0.1.0/data/vectors/bandersnatch_sha-512_ell2_ietf.json ../vectors
cargo run --release -- signing rfc8032_ed25519.txt rfc8032_ed25519_secrets.txt \
  ARK_VRF_0.1.0/data/vectors/bandersnatch_sha-512_ell2_ietf.json ../vectors
cargo run --release -- verify < LINES     # `ed KEY MSG SIG` / `bs KEY CTX MSG SIG`, hex
```

`rfc8032_ed25519.txt` holds the RFC 8032 §7.1 vectors (`name key msg sig`). The generator is not
part of the Lean build and CI does not run it.
