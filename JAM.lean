import JAM.Fast
import JAM.Codec
import JAM.Constants
import JAM.Account
import JAM.Blake2b
import JAM.Keccak
import JAM.Sha512
import JAM.Work
import JAM.Decode
import JAM.Block
import JAM.Trie
import JAM.Shuffle
import JAM.Erasure
import JAM.Params
import JAM.Host.General
import JAM.Merkle
import JAM.Segments
import JAM.Accumulate
import JAM.Accumulation
import JAM.History
import JAM.Authorization
import JAM.Statistics
import JAM.Preimages
import JAM.Crypto
import JAM.Disputes
import JAM.Assurances
import JAM.Reports
import JAM.Safrole
import JAM.State
import JAM.StateDecode
import JAM.BlockImport
import JAM.Model
import JAM.Refine
import JAM.Auditing
import JAM.Guarantee
import JAM.BestChain
import JAM.Theorems.HostGas
import JAM.Theorems.Confinement
import JAM.Theorems.RefineContract
import JAM.Theorems.KeepRO
import JAM.Theorems.KeepROAcc
import JAM.Theorems.GrowHeap
import JAM.Theorems.Safrole
import JAM.Theorems.Auditing
import JAM.Theorems.CheckedIndex
import JAM.Theorems.CheckedIndex.Blake2b
import JAM.Theorems.CheckedIndex.Keccak
import JAM.Theorems.CheckedIndex.Erasure
import JAM.Theorems.BestChain

/-!
# Gray Paper v0.8.1, Appendix B and the protocol terms it needs

Built on `PVM` (Appendix A).

* `JAM.Codec` — the serialization codec $\mathcal{E}$ (Appendix C)
* `JAM.Constants` — generated from `definitions.tex`: protocol and host-call gas constants
* `JAM.Account` — service accounts, footprint and threshold balance, historical lookup (§9)
* `JAM.Blake2b` — $\mathcal{H}$, Blake2b-256 (§3.8)
* `JAM.Params` — chain parameters (full and tiny)
* `JAM.Host.General` — the general host functions: gas, grow_heap, fetch, lookup, read, write, info
* `JAM.Work`  — work packages, items, digests and reports (§11, §14)
* `JAM.Decode` — $\mathcal{E}^{-1}$, the decoders of Appendix C, and those of the work-package family
* `JAM.Block` — blocks, headers and extrinsics with their encoders and decoders (Appendix C)
* `JAM.Trie` — state keys $C$ and the state trie root $\mathcal{M}$ (Appendix D)
* `JAM.Shuffle` — the Fisher–Yates shuffle $\mathcal{F}$ and $\mathcal{Q}_l$ (Appendix F)
* `JAM.Erasure` — Reed–Solomon erasure coding $\mathcal{E}_C$ and recovery $\mathcal{R}$ over $\mathrm{GF}(2^{16})$ (Appendix H)
* `JAM.History` — recent history $\beta$ and the accumulation-output belt (§7, Appendix E MMB)
* `JAM.Segments` — constant-depth Merkle trees $\mathcal{M}$, $\mathcal{J}_x$, $\mathcal{L}_x$ and the paged proofs $P$, with their verifiers (Appendix E, §14)
* `JAM.Authorization` — the authorizer pool $\alpha$ (§8)
* `JAM.Statistics` — validator, core and service activity statistics (§13)
* `JAM.Preimages` — the preimages extrinsic and its integration (§12.4)
* `JAM.Crypto` — the cryptographic primitives (Ed25519 verification; Bandersnatch VRF, Ring VRF and ring root) as parameters (§3.8, Appendix G)
* `JAM.Disputes` — verdicts, culprits and faults, $\psi'$ and the cleared assignments $\rho^\dagger$ (§10)
* `JAM.Assurances` — the assurances extrinsic, the newly available reports $\mathbf{R}$ and $\rho$ after assurances (§11.2)
* `JAM.Reports` — guarantor assignments $\mathbf{M}$ and $\mathbf{M}^{\ast}$, the guarantees extrinsic, $\rho'$ and the reporters $\mathbf{G}$ (§11.3–§11.5)
* `JAM.Safrole` — Safrole: timekeeping, key rotation, entropy, the slot-sealer sequence, the markers and the tickets (§6)
* `JAM.State` — the state $\sigma$, its serialization $T(\sigma)$ and the state root $\mathcal{M}_\sigma$ (§4.2, Appendix D)
* `JAM.StateDecode` — $\sigma$ from its key-values, the inverse of $T$ (Appendix D)
* `JAM.BlockImport` — the block-level transition $\Upsilon(\sigma, \mathbf{B})$ with the header's validity conditions (§4, §5)
* `JAM.Refine` — the refine and is-authorized invocations $\Psi_R$ and $\Psi_I$, with the refine host functions
* `JAM.Guarantee` — work-package refinement: the work-report $\Xi$, item results $I$, item-to-digest $C$, the bundle $B$ and its checks, the availability specifier $A$, and the ancestor-set helper `Chain.extend` (§14, §17.1, §11.4.1)
* `JAM.Auditing` — auditing and judging: the reports to audit, tranche-0 and later-tranche selection, announcements, judgments and the audited condition $\mathbf{U}$ (§17)
* `JAM.Theorems.HostGas` — the dispatchers of $\Psi_A$, $\Psi_R$ and $\Psi_I$ never add gas
* `JAM.Theorems.Safrole` — Safrole invariants: $\gamma'_A$ sorted, unique and bounded by $\mathsf{E}$; $Z$ a permutation; $|\gamma'_S| = \mathsf{E}$; $\eta'$ and key well-formedness
* `JAM.Theorems.Auditing` — auditing invariants: $\mathcal{F}$ a permutation, tranche 0 draws at most ten distinct cores, no no-shows no escalation, $\mathbf{U}$ monotone in $J_\top$ and the §10 verdict link
* `JAM.Theorems.CheckedIndex` — the spec definitions rewritten without unchecked indexing (`a[i]!`) equal their earlier forms (Sha512, state keys, `Decoder.byte`; Blake2b, Keccak and the erasure code in `JAM.Theorems.CheckedIndex.Blake2b`, `.Keccak` and `.Erasure`)
* `JAM.BestChain` — the best chain (§19): acceptable blocks (19.1)–(19.3) with the §17.3 disregard rule, the ticketed metric $m$ (19.4), the best heads and the §5 timeslot rule
* `JAM.Theorems.BestChain` — best-chain facts: best heads are acceptable, extend the finalized block and maximise $m$; independence from store order
-/
