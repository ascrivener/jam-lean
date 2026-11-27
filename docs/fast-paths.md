# Fast paths: spec definitions and their proved-equal compiled forms

The model's definitions follow the Gray Paper literally, which is often slow to run. For each slow
definition that the tests and tools execute, a *fast module* defines a faster implementation, proves
it equal to the spec definition, and registers the equality with `@[csimp]`. The compiler then uses
the fast form in compiled code. The kernel and every theorem see only the spec definitions: a
`@[csimp]` equality is a proved theorem, unlike `implemented_by` (which this repository forbids).

## Layout

- Spec modules hold no fast code.
- Fast modules are every module with a `Fast` path component: `PVM/Fast/*`, `JAM/Fast/*` and
  `JamCrypto/Fast/*`. The aggregators are `PVM.Fast`, which imports every PVM fast module, and
  `JAM.Fast`, which imports `PVM.Fast` and every JAM fast module.
- The library roots `PVM` and `JAM` import the aggregators. Executables (the tests, `witnessrun`,
  …) import `PVM` or `JAM`, so every replacement applies to their own code.

### Why some spec modules import fast modules

A `@[csimp]` replacement takes effect where a *caller* is compiled with the lemma imported. Code
already compiled inside an imported module is not changed by what an executable imports. So the
spec modules whose own compiled code calls a replaced definition import the specific fast module
that replaces it. These imports change nothing that the kernel or any proof sees; they only decide
which code the compiler emits. They are the only spec→fast imports allowed:

| spec module | imports | why |
|---|---|---|
| `PVM` (root) | `PVM.Fast` | the aggregator |
| `JAM` (root) | `JAM.Fast` | the aggregator |
| `JamCrypto` (root) | `JamCrypto.Fast` | the aggregator |
| `PVM.Invocation` | `PVM.Fast.Basic` | its Ψ_H/Ψ_M code calls Ψ |
| `JAM.Refine`, `JAM.Accumulate` | `PVM.Fast.Host`, `JAM.Fast.HostGeneral`, `JAM.Fast.Blake2b` | they call Ψ, Ψ_M, `hostGrowHeap` and ℋ |
| `JAM.Host.General` | `PVM.Fast.Parse` | `heapBounds` parses the blob at every `grow_heap` |
| `JAM.Account`, `JAM.Assurances`, `JAM.Auditing`, `JAM.BlockImport`, `JAM.Disputes`, `JAM.Preimages`, `JAM.Reports`, `JAM.Safrole`, `JAM.Shuffle`, `JAM.StateDecode` | `JAM.Fast.Blake2b` | they call ℋ |
| `JAM.Accumulation` | `JAM.Fast.Blake2b`, `JAM.Fast.Keccak` | it calls ℋ and ℋ_K |
| `JAM.History` | `JAM.Fast.Keccak` | it calls ℋ_K |
| `JAM.State` | `JAM.Fast.Trie` | `State.root` calls M |

Proof modules (`Theorems`, `Logic`, `SymExec`, `Services`) import no fast module directly.
`scripts/check-fast-imports.py` enforces this table and that rule; it runs in CI's `model` job. To
add a fast path: put it in a fast module, list it below, and, if a spec module's own compiled code
must use it, add that import to the table here and to `ALLOW` in the script.

A thin spec wrapper defined in the same spec file as the definition it wraps is compiled before the
replacement exists, for example `hash256 := hash 32`. Such a wrapper is restated word for word in
the fast module, and the restatement is registered with `@[csimp]` (the equality is `rfl`).

## The pairs

### PVM (`PVM/Fast/`)

| spec | fast | theorem | file |
|---|---|---|---|
| `psi` (Ψ) | `psiFast` | `psi_eq_psiFast` | `PVM/Fast/Basic.lean` |
| `psiFast` | `psiFaster` (page-chunked memory, per-index decode and block-cost tables) | `psiFast_eq_psiFaster` | `PVM/Fast/Step.lean` |
| `psiHStar` (Ψ_H*) | `psiHStarFast` | `psiHStar_eq_psiHStarFast` | `PVM/Fast/Host.lean` |
| `psiHStarFast` | `psiHStarFaster` | `psiHStarFast_eq_psiHStarFaster` | `PVM/Fast/Host.lean` |
| `psiH` (Ψ_H) | `psiHFast` | `psiH_eq_psiHFast` | `PVM/Fast/Host.lean` |
| `psiM` (Ψ_M) | `psiMFast` | `psiM_eq_psiMFast` | `PVM/Fast/Host.lean` |
| `Exec.bitwise` | `Exec.bitwiseFast` | `Exec.bitwise_eq_bitwiseFast` | `PVM/Fast/Alu.lean` |
| `Exec.twoRegImmAlu` | `Exec.twoRegImmAluFast` (restated) | `Exec.twoRegImmAlu_eq_twoRegImmAluFast` | `PVM/Fast/Alu.lean` |
| `Exec.threeRegAlu` | `Exec.threeRegAluFast` (restated) | `Exec.threeRegAlu_eq_threeRegAluFast` | `PVM/Fast/Alu.lean` |
| `Blob.parse?` (deblob's encoding) | `Blob.parseFast` | `Blob.parse?_eq_parseFast` | `PVM/Fast/Parse.lean` |
| `JamBlob.parse?` | `JamBlob.parseFast` | `JamBlob.parse?_eq_parseFast` | `PVM/Fast/Parse.lean` |
| `JamBlob.parseStd?` | `JamBlob.parseStdFast` (restated) | `JamBlob.parseStd?_eq_parseStdFast` | `PVM/Fast/Parse.lean` |
| `validJamBlob?` | `validJamBlobFast` (restated) | `validJamBlob?_eq_validJamBlobFast` | `PVM/Fast/Parse.lean` |
| `standardInit` (Y) | `standardInitFast` (restated) | `standardInit_eq_standardInitFast` | `PVM/Fast/Parse.lean` |
| `Sim.live` | `Sim.liveFast` | `Sim.live_eq_liveFast` | `PVM/Fast/Gas.lean` |
| `Sim.decodeStep` (𝔛') | `Sim.decodeStepFast` | `Sim.decodeStep_eq_decodeStepFast` | `PVM/Fast/Gas.lean` |
| `Sim.readyToStart` (𝔖) | `Sim.readyFast` | `Sim.readyToStart_eq_readyFast` | `PVM/Fast/Gas.lean` |
| `Sim.cycleStep` (𝔛''') | `Sim.cycleStepFast` | `Sim.cycleStep_eq_cycleStepFast` | `PVM/Fast/Gas.lean` |
| `Program.blockCost?` (ϱ^Δ) | `Program.blockCost?Fast` | `Program.blockCost?_eq_blockCost?Fast` | `PVM/Fast/Gas.lean` |
| `Program.blockCost` | `Program.blockCostFast` (restated) | `Program.blockCost_eq_blockCostFast` | `PVM/Fast/Gas.lean` |

Supporting equalities, not registered with `@[csimp]`:
- `FastMem.toMemory_ofMemory`, `FastMem.read_eq`, `FastMem.toMemory_write`, `FastMem.readLE_eq`,
  `FastMem.writeLE_eq` (`PVM/Fast/Mem.lean`).
- `Prepared.infoAt_prepare`, `startAt_prepare`, `chargeAt_prepare` (`PVM/Fast/Basic.lean`).
- `Prepared.fexec_eq`, `fstep_eq`, `frun_eq` (`PVM/Fast/Step.lean`).
- `Prepared.hostFuelF_eq` (`PVM/Fast/Host.lean`).
- `Blob.decodeBits?_eq_bitsFast` (`PVM/Fast/Parse.lean`).
- `Sim.run_eq_runFast`, `Sim.transition_eq_transitionFast` (`PVM/Fast/Gas.lean`).

### JAM (`JAM/Fast/`)

| spec | fast | theorem | file |
|---|---|---|---|
| `Blake2b.blocks` | `Blake2b.blocksFast` | `Blake2b.blocks_eq_blocksFast` | `JAM/Fast/Blake2b.lean` |
| `Blake2b.hash` | `Blake2b.hashFast` | `Blake2b.hash_eq_hashFast` | `JAM/Fast/Blake2b.lean` |
| `Blake2b.hash256` (ℋ) | `Blake2b.hash256Fast` (restated) | `Blake2b.hash256_eq_hash256Fast` | `JAM/Fast/Blake2b.lean` |
| `Keccak.sponge256` | `Keccak.sponge256Fast` | `Keccak.sponge256_eq_sponge256Fast` | `JAM/Fast/Keccak.lean` |
| `Keccak.keccak256` (ℋ_K) | `Keccak.keccak256Fast` (restated) | `Keccak.keccak256_eq_keccak256Fast` | `JAM/Fast/Keccak.lean` |
| `Keccak.sha3_256` | `Keccak.sha3_256Fast` (restated) | `Keccak.sha3_256_eq_sha3_256Fast` | `JAM/Fast/Keccak.lean` |
| `Trie.merkle` (M) | `Trie.merkleFast` | `Trie.merkle_eq_merkleFast` | `JAM/Fast/Trie.lean` |
| `Trie.root` | `Trie.rootFast` (restated) | `Trie.root_eq_rootFast` | `JAM/Fast/Trie.lean` |
| `growHeapCore` | `growHeapCoreFast` | `growHeapCore_eq_growHeapCoreFast` | `JAM/Fast/HostGeneral.lean` |
| `hostGrowHeap` (Ω_♊) | `hostGrowHeapFast` (restated) | `hostGrowHeap_eq_hostGrowHeapFast` | `JAM/Fast/HostGeneral.lean` |

### JamCrypto

`JamCrypto` (the crypto parameter in plain Lean, not imported by the model) keeps its fast code in
its own `JamCrypto/Fast/` directory; the aggregator `JamCrypto.Fast` is imported by the root
`JamCrypto`. The same script checks it. The fast functions perform the reference's own sequence of
field operations on fixed-limb fields (`JamCrypto/Fast/Fr.lean`, `Fp25519.lean`, `Fq.lean`, with
generated proofs); see docs/jamcrypto.md. The replacements are in `JamCrypto/Fast/Crypto.lean`,
`G1.lean`, `Pairing.lean` and `Ring.lean`.

| spec | fast | theorem | file |
|---|---|---|---|
| `Ed25519.verifyWith` | `Fast.Ed25519.verifyWith` | `Fast.Ed25519.verifyWith_eq` | `JamCrypto/Fast/Ed25519.lean` |
| `Bandersnatch.ietfVerify` | `Fast.Bandersnatch.ietfVerify` | `Fast.Bandersnatch.ietfVerify_eq` | `JamCrypto/Fast/Bandersnatch.lean` |
| `Bandersnatch.vrfOutput` | `Fast.Bandersnatch.vrfOutput` | `Fast.Bandersnatch.vrfOutput_eq` | `JamCrypto/Fast/Bandersnatch.lean` |
| `Bandersnatch.Thin.verify` | `Fast.Bandersnatch.Thin.verify` | `Fast.Bandersnatch.Thin.verify_eq` | `JamCrypto/Fast/Bandersnatch.lean` |
| `Bandersnatch.Thin.vrfOutput` | `Fast.Bandersnatch.Thin.vrfOutput` | `Fast.Bandersnatch.Thin.vrfOutput_eq` | `JamCrypto/Fast/Bandersnatch.lean` |
| `withSignatures` | `Fast.withSignatures` (restated) | `Fast.withSignatures_eq` | `JamCrypto/Fast/Crypto.lean` |
| `G1.smul` | `Fast.G1Fq.smul` | `Fast.G1Fq.smul_eq` | `JamCrypto/Fast/G1.lean` |
| `G1.msm` | `Fast.G1Fq.msm` | `Fast.G1Fq.msm_eq` | `JamCrypto/Fast/G1.lean` |
| `G1.decompress` | `Fast.G1Fq.decompress` | `Fast.G1Fq.decompress_eq` | `JamCrypto/Fast/G1.lean` |
| `Pairing.pairingCheck` | `Fast.PairingFq.pairingCheck` | `Fast.PairingFq.pairingCheck_eq` | `JamCrypto/Fast/Pairing.lean` |
| `Ring.root` | `Ring.Fast.root` (restated) | `Ring.Fast.root_eq` | `JamCrypto/Fast/Ring.lean` |
| `Ring.withSelectors` | `Ring.Fast.withSelectors` (restated) | `Ring.Fast.withSelectors_eq` | `JamCrypto/Fast/Ring.lean` |
| `Ring.verify` | `Ring.Fast.verify` (restated) | `Ring.Fast.verify_eq` | `JamCrypto/Fast/Ring.lean` |
| `Ring.verify081` | `Ring.Fast.verify081` (restated) | `Ring.Fast.verify081_eq` | `JamCrypto/Fast/Ring.lean` |
| `Ring.crypto` | `Ring.Fast.crypto` (restated) | `Ring.Fast.crypto_eq` | `JamCrypto/Fast/Ring.lean` |
