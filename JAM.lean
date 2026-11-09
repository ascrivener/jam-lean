import JAM.Codec
import JAM.Constants
import JAM.Account
import JAM.Blake2b
import JAM.Keccak
import JAM.Work
import JAM.Decode
import JAM.Block
import JAM.Trie
import JAM.Shuffle
import JAM.Erasure
import JAM.Params
import JAM.Host.General
import JAM.Merkle
import JAM.Accumulate
import JAM.Accumulation
import JAM.History
import JAM.Authorization
import JAM.Statistics
import JAM.Preimages
import JAM.Crypto
import JAM.Disputes
import JAM.Refine
import JAM.Theorems.HostGas
import JAM.Theorems.Confinement
import JAM.Theorems.RefineContract
import JAM.Theorems.KeepRO
import JAM.Theorems.GrowHeap

/-!
# Gray Paper v0.8.0, Appendix B and the protocol terms it needs

Built on `PVM` (Appendix A).

* `JAM.Codec` — the serialization codec ℰ (Appendix C)
* `JAM.Constants` — generated from `definitions.tex`: protocol and host-call gas constants
* `JAM.Account` — service accounts, footprint and threshold balance, historical lookup (§9)
* `JAM.Blake2b` — ℋ, Blake2b-256 (§3.8)
* `JAM.Params` — chain parameters (full and tiny)
* `JAM.Host.General` — the general host functions: gas, grow_heap, fetch, lookup, read, write, info
* `JAM.Work`  — work packages, items, digests and reports (§11, §14)
* `JAM.Decode` — ℰ⁻¹, the decoders of Appendix C, and those of the work-package family
* `JAM.Block` — blocks, headers and extrinsics with their encoders and decoders (Appendix C)
* `JAM.Trie` — state keys C and the state trie root M (Appendix D)
* `JAM.Shuffle` — the Fisher–Yates shuffle ℱ and 𝒬_l (Appendix F)
* `JAM.Erasure` — Reed–Solomon erasure coding ℰ_C and recovery ℛ over GF(2¹⁶) (Appendix H)
* `JAM.History` — recent history β and the accumulation-output belt (§7, Appendix E MMB)
* `JAM.Authorization` — the authorizer pool α (§8)
* `JAM.Statistics` — validator, core and service activity statistics (§13)
* `JAM.Preimages` — the preimages extrinsic and its integration (§12.4)
* `JAM.Crypto` — the cryptographic primitives (Ed25519 verification) as parameters (§3.8)
* `JAM.Disputes` — verdicts, culprits and faults, ψ' and the cleared assignments ρ^‡ (§10)
* `JAM.Refine` — the refine and is-authorized invocations Ψ_R and Ψ_I, with the refine host functions
* `JAM.Theorems.HostGas` — the dispatchers of Ψ_A, Ψ_R and Ψ_I never add gas
-/
