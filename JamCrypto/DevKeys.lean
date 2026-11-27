import JamCrypto.Ed25519Sign
import JamCrypto.BandersnatchSign
import JAM.Blake2b

/-!
# Development validator keys (JIP-5)

JIP-5 derives a validator's secrets from a 32-octet seed:
* Ed25519 secret seed = $\text{Blake2b-256}(\texttt{"jam}\_\texttt{val}\_\texttt{key}\_\texttt{ed25519"} \frown \text{seed})$;
* Bandersnatch secret =
  `Secret::from_seed`($\text{Blake2b-256}(\texttt{"jam}\_\texttt{val}\_\texttt{key}\_\texttt{bandersnatch"} \frown \text{seed})$).

The development validator $i$ (0 = Alice, …, 5 = Fern for the tiny chain) has seed
$\mathcal{E}_4(i)$ repeated 8 times. These are the genesis validators of the fuzzer's 0.8.0 sessions
(Alice's Bandersnatch key is ff71c6c0…, her Ed25519 key 4418fb8c…).
-/

namespace JamCrypto.DevKeys

/-- A validator's secrets and public keys. -/
structure DevKey where
  edSeed : List UInt8
  bsSecret : Nat
  ed : List UInt8
  bs : List UInt8

def blake256 (m : List UInt8) : List UInt8 := (JAM.Blake2b.hash256 ⟨m.toArray⟩).toList

/-- The JIP-5 keys of a seed. -/
def ofSeed (seed : List UInt8) : DevKey :=
  let edSeed := blake256 ("jam_val_key_ed25519".toUTF8.toList ++ seed)
  let bsSecret := Bandersnatch.secretOfSeed (blake256 ("jam_val_key_bandersnatch".toUTF8.toList ++ seed))
  { edSeed, bsSecret, ed := Ed25519.publicKey edSeed, bs := Bandersnatch.publicKey bsSecret }

/-- The seed of development validator $i$. -/
def devSeed (i : Nat) : List UInt8 := (List.replicate 8 (Modular.natToLE 4 i)).flatten

/-- Development validator $i$. -/
def dev (i : Nat) : DevKey := ofSeed (devSeed i)

end JamCrypto.DevKeys
