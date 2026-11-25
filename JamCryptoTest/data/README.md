# Data

* `bls12-381-srs-2-11-uncompressed-zcash.bin` (590320 octets, sha256
  `1d7d27e4f5f3c6190989bea58803180d3e19f725a57069392a405ac78b233c7d`): the KZG SRS of the
  Bandersnatch ring VRF, [τⁱ]G1 for i < 6145 and [τⁱ]G2 for i < 2 from the Zcash powers-of-τ
  ceremony, as shipped by ark-vrf 0.1.0 (`data/srs/`). Loaded by `JamCrypto.Ring.Srs.load`.
