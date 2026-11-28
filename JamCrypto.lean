import JamCrypto.Modular
import JamCrypto.Edwards
import JamCrypto.Ed25519
import JamCrypto.Bandersnatch
import JamCrypto.Reading
import JamCrypto.Crypto
import JamCrypto.Ring
import JamCrypto.Ed25519Sign
import JamCrypto.BandersnatchSign
import JamCrypto.ThinVrf
import JamCrypto.PedersenVrf
import JamCrypto.DevKeys
import JamCrypto.Fast
import JamCrypto.Model

/-!
# JamCrypto: the crypto parameter of the model, in plain Lean

The JAM model (`JAM`) takes its cryptography as a parameter, `JAM.Crypto`; this library implements
it with core and Std only, and the model never imports it
([`docs/jamcrypto.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/jamcrypto.md)):

* Ed25519 signatures (`JamCrypto.Ed25519`, `JamCrypto.Ed25519Sign`);
* the Bandersnatch IETF, Thin and Pedersen VRFs (`JamCrypto.Bandersnatch`, `JamCrypto.ThinVrf`,
  `JamCrypto.PedersenVrf`) and the ring root and ring VRF (`JamCrypto.Ring`), the latter over
  BLS12-381;
* the `JAM.Crypto` instance built from them (`JamCrypto.Crypto`), and development keys
  (`JamCrypto.DevKeys`);
* the closed state-transition function: Υ with the full GP v0.8.1 crypto fixed
  (`JamCrypto.Model.crypto`, `JamCrypto.Model.importBlock`), the target of a conformance proof;
* faster implementations proved equal to the reference ones (`JamCrypto.Fast`).
-/
