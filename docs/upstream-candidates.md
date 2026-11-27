# Upstream candidates

Findings from this model worth reporting to the Gray Paper or the test vectors. The full notes
are in the README, under "Notes on the paper and the vectors"; the numbers below are theirs.
Every place where the model fills a gap in GP v0.8.1 with a choice (error names, the order in
which conditions are checked, encodings, readings of ambiguous text, constants) is listed here,
with where the choice comes from (usually the test vectors) and where the model makes it.

Filed so far (marked **Filed** below): gavofyork/graypaper#592 (note v0.8.1-A1) and
gavofyork/graypaper#593 (the Thin VRF signature encoding).

Before filing, check each against the latest Gray Paper: some may be fixed after v0.8.1.

## Gray Paper issues

Inconsistencies, where the paper contradicts itself:

| Note | Section | Finding |
|---|---|---|
| 1 | §A.10 | 𝔓_S compares φ_A = φ_D (the paper writes the registers φ), which read literally compares register values. The gas model has no values, so it must mean the indices r_A = r_D. |
| 3 | §A.4 | The prose says RAM below 2^16 always panics, but the formula for ε^μ only considers inaccessible indices. |

Gaps, where the paper leaves behaviour undefined:

| Note | Section | Finding |
|---|---|---|
| 13 | Ψ_H | Ψ_H* need not terminate: a handler that returns more gas than it was given can recurse forever. Termination holds for handlers that do not add gas (`JAM/Theorems/HostGas.lean`). |
| 2 | 𝔟 | A branch target ı + 𝒵(…) can be negative, where ζ is undefined. |
| 17 | Y | **a** ∈ 𝔹_{:𝖹_I}; the paper does not say what happens to a longer argument. |
| 18 | Ψ_R | The refine dispatcher passes x̄ to `fetch`, but Ψ_R's arguments do not include that data. The account state **d** is also implicit. |
| 19 | Ψ_R, §14.3 | A looked-up preimage that is not of the form ℰ(↕**m**, **c**). *Resolved in v0.8.1 (#582): the code is the whole preimage and Y fails on it (Ψ_M panics).* |
| 20 | Ω_Z (`pages`) | The row defines only (ω'_7, **m**'), with no ε'. |
| 21 | §8, F(c) | α[c] ⊖ {(g_w)_a} names a g bound only in the case condition; it should say the guarantee on core c. The model reads it so (`JAM/Authorization.lean`, `poolUsed`). |
| 23 | §13.1 | The guarantee count tests κ'_v ∈ G, a validator key against a set of Ed25519 keys (*resolved in v0.8.1, #565: (κ'_v)_e ∈ G*). The fresh accumulator [(0, …), …] has no stated length (\|κ'\| is implied); the model uses \|κ'\| (`JAM/Statistics.lean`, `validatorStats`). |
| 24 | §13.2 | The provision sum ∑_{(s, **d**) ∈ E_P} reuses s, already bound by ∀ s ∈ **s**. It reads as a fresh binding unless the reader knows it is a filter. *Resolved in v0.8.1 (#567): the sum is over **p** ∈ E_P with **p**_s = s.* |
| 25 | §12.4 | No error is named for an invalid E_P, and no order is given between the ordering check and the providable check. The model uses the vectors' `preimages_not_sorted_unique` and `preimage_unneeded`, ordering first (`JAM/Preimages.lean`, `preimages`). |
| 31 | §6.7 | Tickets are ordered by their identifier y ∈ ℍ, but no order on ℍ is defined (lexicographic on octets is the evident reading and the vectors use it). `$jam_ticket_seal` ⌢ η_2' ⧺ e appends a natural number (as an element, ⧺) to an octet sequence without saying how it is encoded. No errors are named for an invalid E_T, and no order is given between its conditions. The model compares y lexicographically (`octetLt`), appends the attempt as one octet (`ticketContext`), and uses the vectors' error names (`SafroleError`) in the order given in the module docstring (`JAM/Safrole.lean`, `safrole`). |
| 26 | Appendix C | No encoding of Booleans {⊤, ⊥} is defined, though 𝔼_D's judgments and faults contain them; 0/1 is the evident reading and the vectors use it (`JAM/Decode.lean`, `Decoder.bool`). |
| 29 | §10.2 | The fault condition r ∈ ψ_B' ⇔ r ∉ ψ_G' ⇔ v can be read as a chain or as ((… ⇔ …) ⇔ v); the second accepts a ⊤ fault on a good report. No errors are named and no order is given between the conditions. The model reads a chain, uses the vectors' error names (`DisputesError`; a key outside **k** is `offender_already_reported` when in ψ_O and an unknown auditor or guarantor otherwise) and checks each part's order before its elements' conditions: verdict order (10.8); per verdict its epoch index, judgment order (10.11), count, judge indices and signatures (10.4), not already judged (10.10), V defined (10.12); culprit order (10.9), then each culprit's (10.6); fault order (10.9), then each fault's (10.7); last (10.13) (`JAM/Disputes.lean`, `checkVerdict`, `disputesTransition`). |
| 30 | §11.2 | No errors are named and no order is given between the assurance conditions. The model uses the vectors' names (`AssurancesError`) and checks each assurance in turn: index range, order, signature, bits (`JAM/Assurances.lean`, `assurances`, `checkAssurance`). |
| 33 | Appendix D, §13.2 | D.1 says every non-discriminator number in the state is serialized fixed-length by the size of its term, but π_C and π_S (C(13)) hold ℕ and ℕ_G terms with no stated encoding; the traces use the general encoding ℰ for all of them, gas included. The model follows the traces: ℰ for π_C and π_S (`JAM/State.lean`, `stats`). (Withdrawn 2026-11-25: whether 𝒜 includes the block being imported. Eq. `ancestors` (§5) puts H in 𝒜, which the model follows in `JAM/BlockImport.lean`, `lookupAnchorKnown`.) |
| 32 | §11.3–§11.4 | R and P divide by 3 (\|**c**\|/3, ⌊i/3⌋); the division is exact, as every validator key sequence has length in 𝕍 = {3c \| c ∈ ℕ_{2…𝖢+1}} (eqs. `validatorkeys`, `valcount`, (6.7)–(6.8)), but the model's types do not enforce \|κ'\| ∈ 𝕍 and its integer division floors otherwise (`rotate`, `checkGuarantee`). M* uses τ' − 𝖱, negative when τ' < 𝖱; the model's natural subtraction truncates it at 0, which is never reached, since M* is used only for t ≤ τ' in an earlier rotation than τ', so τ' ≥ 𝖱. No errors are named and no order is given between the guarantee conditions; a segment-root lookup key outside the extrinsic and β fails two conditions at once. The model uses the vectors' error names (`ReportsError`) and the order given at `guarantees`: the lookup is checked before the prerequisites, and an anchor found by hash with another field wrong names the first field that differs (`JAM/Reports.lean`, `guarantees`, `checkGuarantee`, `checkAnchor`). |
| v0.8.1-A1 | eq. `accpar`, N(**o**) | GP v0.8.1: the discard function N(**o**) gives every field a value except the post-state, written bare. The prose ("discard all results of the service's execution", except provided preimages) suggests the round's input state; reading it as **o**'s post-state would keep a discarded run's new services and privilege, staging and queue changes while M(s) drops its own account change. The model uses the input state (`JAM/Accumulation.lean`, `accPar`). A consequence of that reading: if E(s)'s own run is discarded too (because E(E(s)) also modified E(s)), s's run was already discarded (the raw **y** = Δ_1(E(s)) modified s), so M(s) = **e**[s] and both changes to s are lost. **Filed:** gavofyork/graypaper#592. |
| v0.8.1-A2 | eq. `reportrefineload` (#563) | GP v0.8.1 adds the work-package limits on each report (∑ u ≤ 𝖦_R, ∑ i ≤ 𝖶_M, (r_s)_n = ∑ e ≤ 𝖶_X, ∑ x ≤ 𝖳, ∑ (z + i·𝖶_F) ≤ 𝖶_I, (r_s)_l ≤ 𝖶_B, r_g ≤ 𝖦_I) but names no errors and gives no order between them or against the other guarantee conditions. The model uses the vectors' errors 28–31 (davxy/jam-test-vectors master after v0.8.0): `bad_exports_count` when (r_s)_n ≠ ∑ e, `refine_load_too_high` for any sum over its limit, `bundle_too_big` and `auth_gas_too_high`; the rows in the paper's order, after ∑ d_g ≤ 𝖦_A (`JAM/Reports.lean`, `checkReportLoad`). |
| v0.8.1-A3 | eqs. `xtpreimages`, `maxxtpreimagesdatasize` | GP v0.8.1 bounds \|E_P\| and its total data size, but names no errors and gives no order against the ordering and providable checks (note 25). No vector covers them; the names `tooMany` and `tooMuchData` are the model's own, and the bounds are checked first (`JAM/Preimages.lean`, `preimages`). |
| v0.8.1-A4 | §3.8.2, 𝕍̄_k⟨m⟩ | "Valid Ed25519 signatures, defined by RFC 8032": RFC 8032 allows the cofactored or the cofactorless equation, and implementations differ on non-canonical encodings. The model follows ZIP 215, which the jam-fuzzing conformance vectors (commit 5bbd4266, `crypto/ed25519`) target (Adam, 2026-11-15; `JamCrypto/Ed25519.lean`, `verify`, `Rules.zip215`). |
| v0.8.1-A5 | Appendix G, O(**k**) | The ring root's ring size (hence the ring proof's domain) is not fixed. The v0.8.0 path uses the chain's V whatever \|**k**\| is, as `stf/safrole/full/enact-epoch-change-with-set-resize-1` requires (`JamCrypto/RingRoot.lean`, `root`). The v0.8.1 path uses Draft 35 §5's fixed domain 2048 (its prose; its own ring vectors use 512, regenerated at 2048 in 0b7422f): `Ring.domain081`, Adam 2026-11-25. |
| v0.8.1-A6 | Appendix G, 𝔹̄_k⟨c⟩⟨m⟩ | GP gives Thin VRF signatures as 96 octets and reads Y from the signature, but Draft 35 encodes only the proof (R, s), 64 octets. The model reads O ⌢ R ⌢ s (Adam, 2026-11-25; `JamCrypto/ThinVrf.lean`, `thinEncode`, `thinDecode`). **Filed:** gavofyork/graypaper#593; the spec's author confirmed O ⌢ R ⌢ s and opened davxy/bandersnatch-vrf-spec#30. |
| v0.8.1-A7 | notation, context strings | `$jam_ticket_seal`, `$jam_valid`, …: the wording leaves open whether `$` is an octet of the string. Every v0.8.0 vector signature (58 ticket proofs, seals, entropy sources, Ed25519 judgments, guarantees, assurances) verifies only without it; the model drops a leading `$` (`JAM/Crypto.lean`, `contextString`). See also "Not for upstream" below. |
| v0.8.1-A8 | §17.3, U(w) | U(w) ⇔ (J_⊥(w) = ∅ ∧ ∃ n : A_n(w) ⊆ J_⊤(w)) ∨ … leaves n unbounded. Eq. `latertranches` makes A_n(w) = ∅ for every tranche after one with no no-shows (a_n needs a positive no-show count), and tranches not yet reached are perceived as ∅, so read literally the first clause is just J_⊥(w) = ∅: a report nobody judged is audited. The model bounds n by the current tranche (`JAM/Auditing.lean`, `audited`), and shows the collapse of the literal form (`auditedLiteral_degenerate`). Even bounded, a tranche ≤ current with nobody announced for w (A₀(w) = ∅ happens when no validator draws w's core) accepts w with no judgment at all (`audited_of_empty_tranche`); the intent is presumably a tranche whose announced auditors all judged, with at least one auditor. Adam confirmed the bounded reading (n ≤ current tranche), 2026-11-26. |
| v0.8.1-A9 | §17.3, eqs. `announcement`, `latertranches` | X_I ⧺ n and ℋ(w) ⧺ n append a natural to an octet sequence without its encoding (as note 31 for Safrole); **x**_n = ℰ({ℰ₂(w_c) ⌢ ℋ(w)}) relies on "proper order" of octet strings, and ℰ₂ being little-endian, that order is not core order; ℋ(w) and ℋ(H) are hashes of items, not octet strings. The model uses ℰ(n) (one octet below 128), lexicographic order with no length prefix, and ℋ(ℰ(·)) (`announcementMessage`, `announcementItems`, `laterContext`, `reportHash`). |
| v0.8.1-A10 | §17.3, eq. `latertranches` | The prose says later tranches contain a report either because a negative judgment was received ("the validator is always required to issue a judgment") or because of no-shows, but **a**_n has only the no-show VRF condition. The model gives both: `laterTranche` (the equation) and `laterTrancheWithNegatives` (with the prose rule). Also: the source's line placing v in A₀(w) for its own tranche-0 items is commented out (`TODO: #445`); A_n is an input in the model. |
| v0.8.1-A11 | §17.1 vs §17.3 | The overview ban-lists a block when *greater than* ⅓ of validators judge a report invalid; the best-block paragraph disregards chains with a report *at least* ⅓ judge invalid. The model's `disregarded` follows the latter (3·\|J_⊥\| ≥ \|κ\|). The audited condition's > ⅔\|κ\| matches the good-verdict count ⌊⅔\|κ\|⌋ + 1 of §10 exactly (`supermajority_iff_verdictGood`). |
| v0.8.1-A12 | §17.3, **q** and n | **q** has \|κ\|/3 entries ("active cores") while ρ has 𝖢; the two agree for both chains, and the model reads ρ below \|κ\|/3 (`auditReports`). n = ⌊(𝒯 − 𝖯·H_T)/𝖠⌋ is negative for a wall clock before the slot; the model's natural subtraction reads it as tranche 0 (`currentTranche`). The block author's choice among possible verdicts (good, bad, wonky) is not specified; `formVerdict` tries them in that order. |
| v0.8.1-A13 | §14.3, §17, segment justifications | The paper defines how justifications are made (J_𝐫 from J_0, P from J_6 and L_6) but not how they are checked: §14.3 and §17 only say a justification "allows verification that each segment's hash is included in the referencing Merkle root". The model's check (`JAM/Segments.lean`, `verifySegment`, `verifyPage`) is the inverse of T on the perfect tree C produces: the depth is read from the path's length, and the index must be below 2^\|path\|. A page's subtree root pads the page with 𝟬 to 2^x leaves when its path is non-empty, and to 2^⌈log₂ \|page\|⌉ when the page is the whole tree. Proved to accept everything J_0, J_x and L_x produce (`verifySegment_justify`, `verifyPage_page_justify`). |
| v0.8.1-A14 | Appendix E, eqs. `constantdepthsubtreemerklejust`, `constantdepthsubtreemerkleleafpage` | J_x and L_x type their index as i ∈ ℕ_{\|**v**\|}, but it is a page index: only i < ⌈\|**v**\|/2^x⌉ names a page (P uses only those). For larger i, J_x's T(C(**v**), 2^x·i) indexes past C(**v**). The model accepts any i and states its results for page indices. |
| v0.8.1-A15 | §14.4, after eq. `pagedproofs` | "each composed of a page of 64 hashes of segments": the page is L_6, the hashes H($leaf ⌢ s) of the segments (not ℋ(s)), and the last page holds only \|**s**\| mod 64 of them when 64 ∤ \|**s**\|. The model follows the equation. |
| v0.8.1-A16 | §14.3–§14.4, X, S_l, J_l, Ξ | X(w) and S_l / J_l are comprehensions over data Ξ is not given: the preimages of the extrinsic hashes ("we make an assumption that the preimage … is known by the guarantor") and, for each import, the whole exported-segment sequence ŝ with ℳ(ŝ) = L_l(r). L_l(h^⊞) is undefined when h ∉ K(l), and an index n ≥ \|ŝ\| names no segment. The model takes that data from a `DataSource` (each of X, S_l, J_l is `none` when data is missing, an index is out of range, or ŝ's root differs), and Ξ takes the resulting per-item data as an argument, as Ψ_R already takes x̄ (`JAM/Guarantee.lean`, `packageData`, `computeReport`). ℋ(p) is read as ℋ(ℰ(p)), as in Ψ_R's arguments. |
| v0.8.1-A17 | eq. `computereport`, z in I | z = \|t\| + Σ_{k<j, (r ∈ 𝔹, …) = I(p, k)} \|r\| is defined through I itself, so the outputs of earlier items count only as I returns them: an output replaced by ⊖ (oversize) or ⊚ (bad export count) adds nothing, and neither does an error result. The model computes I left to right carrying z that way (`refineItems`). The alternative reading (counting Ψ_R's raw outputs) would make one oversized item push every later item over 𝖶_R. |
| v0.8.1-A18 | §17.1, bundle checks | The checks an auditor or guarantor applies to a bundle are only prose ("validate the extrinsic data through ensuring their hashes are each equivalent…", "a justification … allows verification that each segment's hash is included in the referencing Merkle root"), and §17.3's e_n instead asks for some p with B(p, r_l) = C(r). The model decodes a bundle (the package, then extrinsics at their referenced lengths, 𝖶_G octets per imported segment, a ↕ path per imported segment; trailing octets rejected) and checks: one data entry per item; extrinsic count, hash and length; segment count, size 𝖶_G and `verifySegment` (v0.8.1-A13) against L_l(r) at index n; and K(l) = {h \| (h^⊞, n) ∈ w_i} (E's second disjunct). The package-hash check against the report is left to the caller (`Bundle.decode`, `checkBundle`, `verifyBundle`). |
| v0.8.1-A19 | Ω_N, eq. `newserviceindex` | check(i) tests i ∉ K(**e**_d) with **e** the base state passed to Ψ_A (`local¬basestate`), but Ω_N applies it to i* in the middle of an invocation. Read literally, an id ejected earlier in the same invocation is skipped (it is in the base state), and an id created earlier in the invocation can be returned again, so a later `new` would overwrite that account. The model checks against the current (x_e)_d (`JAM/Accumulate.lean`, `new`); the two differ only if the stride sequence meets such an id. |
| v0.8.1-A20 | Ω_N, registrar case | With x_s = χ_R, i < 𝖲 and i = s (the funding service's own id), **d'** sets **d'**[i'] = **a** and also changes **d'**[s]'s balance, which conflict, and the CASH condition (checked before FULL) reads **d'**[s]. The model tests CASH on s's own balances, then answers FULL (`JAM/Accumulate.lean`, `new`). |
| v0.8.1-A21 | §19, (19.2) | The formula asks 𝐔^♭ ≡ ⊤, the audited condition of the best block alone, while the list says the best block "is considered audited" and §17.3 asks a block to be audited before it is finalized; a chain whose head is audited can hold an unaudited unfinalized ancestor. The model offers both readings (`AuditReading.head`, the formula, and `.chain`, every unfinalized ancestor audited too; `JAM/BestChain.lean`, `acceptable`). |
| v0.8.1-A22 | §19 vs §17.3 and §4 | The disregard rule ("we pointedly disregard chains which include the accumulation of a report which we know at least ⅓ of validators judge as being invalid", §17.3) is not among §19's formal criteria, and §4 words it differently ("a block in which data is *reported* which any other block's state has tagged as invalid"). The model adds §17.3's rule to acceptability, per block as an input flag, over all ancestors, finalized ones included, so a disregarded finalized block leaves nothing acceptable (`JAM/BestChain.lean`, `acceptable`, `disregardedBlock`). |
| v0.8.1-A23 | §19, (19.3) | "Two valid blocks at the same timeslot": H^B is unconstrained (any block seen, on any fork, finalized or not; no same-author condition, though one slot has one sealer key under Safrole), and only H^A must be unfinalized. So any two seen blocks at one unfinalized slot rule out every chain through either. The model reads it literally, with H^B over the store (`JAM/BestChain.lean`, `equivocates`). |
| v0.8.1-A24 | §19, (19.4) | No tie-break is given among acceptable blocks of equal m, and every acceptable block is a candidate, not only leaves: a fallback-sealed child ties with its parent. The model returns every maximiser (`bestHeads`); `bestHead?` takes the first in store order (`JAM/BestChain.lean`). |
| v0.8.1-A25 | §19, (19.4) and §5 | m sums 𝐓 over all of 𝐀^♭ back to genesis, while §5 lets nodes keep only the last 𝖫 = 24 hours of headers. The model counts the ancestors in the given store; every acceptable block passes through H^♮, so the ancestors shared through H^♮ add the same amount to every candidate when the store holds H^♮'s ancestry consistently (`JAM/BestChain.lean`, `metric`). |
| v0.8.1-A26 | §7, (7.5) | β_H^† sets the state root of β_H[\|β_H\| − 1], which does not exist when β_H is empty (as at genesis). The model leaves an empty β_H unchanged (`JAM/History.lean`, `Recent.withParentRoot`). |
| v0.8.1-A27 | §7, (7.8) | **p** = {((g_r)_s)_p ↦ ((g_r)_s)_e \| g ∈ E_G} is a dictionary built from pairs; two guarantees with one package hash would give two values for one key. §11 rejects duplicate packages first (`duplicatePackage`), so a valid block never has them; the model would keep the later pair (`JAM/History.lean`, `recentHistory`, `Std.ExtTreeMap.ofList`). |
| v0.8.1-A28 | §8, (8.3) | F(c) removes one authorizer, assuming at most one guarantee on core c (which §11 enforces). If there were several, the model removes each one's authorizer in turn (`JAM/Authorization.lean`, `poolUsed`). |
| v0.8.1-A29 | §8, (8.1)–(8.2) | φ'[c][H_T]↺ is i mod \|φ'[c]\|, undefined for an empty queue; (8.1) gives every queue exactly 𝖰 entries, but the model's queues are lists of any length. For an empty queue the model appends nothing (`JAM/Authorization.lean`, `poolNext`). |
| v0.8.1-A30 | §5, (5.8) | H_T·𝖯 ≤ 𝒯 depends on the wall clock 𝒯, which Υ(σ, B) does not take. The model's Υ does not check it; a caller with a clock checks it separately (`JAM/BlockImport.lean`, `importBlock`). |
| v0.8.1-A31 | §5, (5.2)–(5.3) | 𝒜 and P(H) come from headers outside σ. The model takes the retained headers as an argument (`Chain`); with none retained, the H_P check is skipped (`JAM/BlockImport.lean`, `importBlock`). |
| v0.8.1-A32 | §4, (4.1) | No errors are named for an invalid block and no order is given between the sections' validity conditions. The model reports the first failing check in the order of `importBlock` (header checks, disputes, Safrole and the markers, seal, assurances, guarantees, preimages; `BlockError`). |
| v0.8.1-A33 | §3.8.1 | ℋ_K is "Keccak 256-bit … proposed by Bertoni et al. and utilized by" the Yellow Paper; the FIPS 202 SHA3-256 padding differs. The model uses the original Keccak padding (domain octet 0x01), as Ethereum does (`JAM/Keccak.lean`, `keccak256`). |
| v0.8.1-A34 | §10.2, eq. `verdicts` | When \|**k**\| < 3, ⌊⅓\|**k**\|⌋ = 0, so V(a, **j**)'s cases ⊥ (t = 0) and ∅ (t = ⌊⅓\|**k**\|⌋) both hold at t = 0. The model takes ⊥ (`JAM/Disputes.lean`, `verdictOutcome`). Validator counts are in 𝕍 (eq. `valcount`), so \|**k**\| ≥ 6 and the paper never reaches it. |
| v0.8.1-A35 | §11.2, eq. `availassignmentspostassurancesdef` | (p_**g**)_**r** ∈ **R** tests whether a work-report is in **R** without saying how reports are compared. The model compares their encodings ℰ(**r**) (`JAM/Assurances.lean`, `assurances`). |
| v0.8.1-A36 | Appendix F, eq. `suffle` | ℱ types its entropy as **r** ∈ ⟦ℕ⟧_{l:}, so **r**_0 always exists. The model's ℱ is total over any **r** and reads a missing entry as 0 (`JAM/Shuffle.lean`, `shuffle`); the paper's uses never reach this, as (F.3) passes 𝒬_l(h), which has exactly l entries. |
| v0.8.1-A37 | §11.4, eqs. (11.32), `reportcodesarecorrect` | δ[**d**_s] is undefined when **d**_s ∉ 𝒦(δ), and no condition requires a digest's service to exist. The model rejects such a report with the vectors' `bad_service_id`, before the minimum-gas condition (`JAM/Reports.lean`, `guarantees`). |

## Resolved in GP v0.8.1

| Note | Resolution |
|---|---|
| 4 | #554: r_D = min(12, ζ_{ı+2} mod 16). |
| 12 | #533: Ψ_H, 𝔉_X and the host functions all use gas in ℕ_G. |
| 19 | #582: the looked-up code is the whole preimage. |
| 23 (first part) | #565: the guarantee count tests (κ'_v)_e ∈ G. |
| 24 | #567: the provision sum filters E_P by service. |

## Paper and vectors

| Note | Finding | Where |
|---|---|---|
| 5 | Ψ returns ı = 0 on ∎ and ☇; the vectors report the exiting instruction. | Paper or vector docs: which one is meant? |
| 15 | The accumulate vectors follow later GP PRs rather than v0.8.0: `bless_from_non_manager-1` and `-2`. | Already in the vectors' CHANGELOG; no issue needed. |
| 33 | The `fuzzy` and `fuzzy_light` block-import traces follow GP #519 (`bless` from a non-manager accepted), like the accumulate vectors (note 15): `fuzzy_light` blocks 77, 86, 118, 148, 151, 163, 165, 179 and `fuzzy` block 17. | Already in the vectors' CHANGELOG; no issue needed. |
| 32 | The vectors' README tiny chainspec omits 𝖫; the tiny vectors (`stf/reports/tiny/lookup_anchor_not_recent-1`, master) use 24, the fuzzer protocol's value. | Vectors: list `max_lookup_anchor_age` in the README's tiny chainspec. |
| 27 | `trie/trie.json` gives 32-octet keys; GP §D.1 state keys are 31 octets. The roots match with the last octet dropped. | Vectors: say keys are cut to 31 octets, or give 31-octet keys. |
| 28 | **Resolved in GP v0.8.1 (#580):** §H.3 now defines the vectors' layout, and the model follows it (all erasure vectors match). Was: every erasure vector pads the message polynomial with zeroes to degree < n = 2^⌈log₂ R(v)⌉ and puts parity word i at point (n + i − R(v))~; §H.3 says degree < R(v) and point ĩ. No GP release (v0.1.1–v0.8.0) describes the vectors' layout; it is the "low rate" layout `reed-solomon-simd` documents (originals in one zero-padded power-of-two chunk, recovery shards in the chunks after). | Paper: if that code is intended (the cited Lin–Chung–Han transform works on power-of-two blocks), §H.3 should define p of degree < n with zeroes at d̃ … (n−1)~ and parity at (n + i − d)~; otherwise the vectors should follow §H.3. |

## Vector coverage

These cases have no test vector, so the readings above are untested:

| Note | Missing case |
|---|---|
| 11 | Any program using `cmov_nz_imm` (opcode 148). |
| 2 | A branch with a target outside [0, \|**c**\|). |
| 3 | A program that maps a page below 2^16. |
| 31 | A tickets extrinsic whose tickets are valid but not all kept in γ_A' (**n** ⊄ γ_A'). |
| 24 | Core statistics π_C, and the refinement and accumulation parts of π_S, in the statistics and preimages suites. They are covered by the reports and accumulate suites. |
| 29 | Ed25519 verification is a parameter of the model, so the disputes, assurances and reports vectors' signatures are not verified; the runner rejects all of them exactly when a vector expects `bad_signature`. |
| 32 | The lookup-anchor conditions of §11.4.1 (x_t ≥ H_T − 𝖫, and h, h' in the ancestor set A): the reports vectors carry no ancestor set. (Master after v0.8.0 adds `lookup_anchor_not_recent`; on its tiny vector see the table above.) |

## Bootstrap service binary

Behaviour of the bootstrap service's PVM binary that differs from the instruction set it implements.
These would go to the service's authors, not to the Gray Paper.

| Where | Finding |
|---|---|
| `Designate` decode, 35300 … 35315 | The bound check on `keys: BoundedVec<[u8; 336], 3·𝖢>` loads 𝖢 sign-extended (`loadI16`), computes 3·𝖢 and zero-extends it from 16 bits, so the decoder accepts n ≤ (3·𝖢) mod 2¹⁶ instead of n ≤ 3·𝖢. The two agree for 𝖢 < 21846 (the full parameters' 𝖢 = 341 gives 1023); for 𝖢 ≥ 21846 the bound wraps and valid key lists are rejected. Proven as stated in `Decode.Designate.designate_heap` (`hnC : n ≤ 3 * C % 65536`). |
| `remove`, 48481 … 48533 | A removal (`write` of an empty value) panics when the host replies FULL, i.e. when the account's threshold balance after the removal still exceeds its balance. A removal only lowers the threshold, so failing it rolls back the whole accumulate where going on would be harmless. Quirk Q18 in `docs/bootstrap-target.md`. |
| `add_recent_work_item`, 8293 … 8323 | The next ring slot is `(c + 1) % (2·𝖢·𝖨)` computed in 32 bits: `2·𝖢·𝖨` is `(𝖢·𝖨 << 1) mod 2³²` (`shloLImm32`, a panic if it is 0) and `c + 1` is reduced mod 2³² by `remU32`. So a stored counter 2³² − 1 wraps to slot 0 rather than to 2³² mod 2·𝖢·𝖨 (quirk Q19 in `docs/bootstrap-target.md`), and parameters with 2·𝖢·𝖨 ≥ 2³² would size the ring mod 2³² (or panic when that is 0). Harmless for the full parameters (2·341·16 = 10912) and for any counter the service itself wrote (always below 2·𝖢·𝖨). The proofs assume 0 < 2·𝖢·𝖨 < 2³² (`RingFits`). |
| SDK `get` (`read` wrapper), 47888 … 47907 | The length returned by Ω_R in ω₇ is compared against the host error codes (≥ 2⁶⁴ − 9) before it is used. A value of exactly 2⁶⁴ − 1 octets is therefore indistinguishable from NONE and `get` returns `None` for a key that is present; lengths in [2⁶⁴ − 9, 2⁶⁴ − 2] trap (47929), and lengths in [2⁶³, 2⁶⁴ − 9) trap as a negative `isize` (47901). The same ambiguity is in Ω_R's interface itself (GP Appendix B: a length and an error code share ω₇), so it may also be a note for the paper. Unreachable in practice; T2 assumes values shorter than 2⁶³ octets (`ValuesFit`). |
| SDK `foreign_historical_lookup` (refine's eager `Lookup`), 49015 … 49074 | The preimage length Ω_H returns in ω₇ is checked against the host error codes and then used as a signed size: lengths in [2⁶³, 2⁶⁴ − 9) trap, and so do lengths above 2³⁷ − 32 (the allocator's limit, counted as heap exhaustion). `Spec.refine` (GP Appendix B.6, Ω_H) returns `lookedUp (some d)` for any preimage d. Unreachable in practice; T1's eager `Lookup` step takes preimages shorter than 2⁶³ octets as an internal hypothesis (`hlen`, whether refine_t1c assumes it is pending with Adam). |

## Bandersnatch VRF-AD specification, Draft 35 (cited by GP v0.8.1)

The 96-octet signature encoding, which GP and the draft leave open together, is note v0.8.1-A6 above
(**Filed:** gavofyork/graypaper#593; davxy/bandersnatch-vrf-spec#30).

GP v0.8.1 cites Draft 35 (davxy/bandersnatch-vrf-spec commit 181aba2) for all of Appendix G. Where
its prose and its own vectors (Appendix C, ark-vrf 0.5.0) disagree, JamCrypto's v0.8.1 path
follows the prose by default (`Reading.prose`) and the vectors on request (`Reading.vectors`;
Adam, 2026-11-25). Details in `docs/jamcrypto.md`. For the draft's author, or for the GP if it
should cite a later draft.

| Where | Prose | What the vectors need |
|---|---|---|
| App. A.2, hash_to_curve | "`expand_message_xmd` with SHA-512 (section 5.3.1)" of RFC 9380, whose step 4 is Z_pad = I2OSP(0, s_in_bytes): 128 zero octets for SHA-512. | 48 zero octets. Draft 36 (fcf7012) states the 48 as a deliberate deviation and announces a suite `…-v2` with RFC 9380's 128; GP v0.8.1 cites Draft 35, which does not state it. |
| §4, §5, the fixed points B, S, □ | Each "is defined as" printed coordinates, and is "derived using the `hash_to_curve` function as described in Appendix A.2" from its name. With A.2 read as RFC 9380, the two disagree: the printed coordinates are the 48-octet derivation. | The printed coordinates. |
| §5, Fiat–Shamir of the ring proof | "Begin with empty transcript and "ring-proof" label." | The suite id `Bandersnatch-SHA512-ELL2-v1` as the label; no ring vector verifies with "ring-proof". |
| §5, Fiat–Shamir of the ring proof | "Push R to the transcript after instancing." R is not defined in §5 (Pedersen's nonce commitment is R in §4), and no framing is given. | Nothing is pushed after the instance (Ȳ) other than the proof's own columns. Not modelled under either reading (`.prose` omits the step, since the prose leaves it underdetermined). |

## Not for upstream

- **The picoalloc model's alignment rounding.** A bug in this repository's own model, not in the
  paper or the vectors. The model rounded the data unit from the heap base; the binary rounds it
  in the address space. Fixed in `Services/Picoalloc/Model.lean`.
- **The lookup anchor's state root in `lookupAnchorKnown`.** A bug in this repository's own
  model, found by the jam-lean-target fuzzing work. §11.4.1 (GP eq. 11.36) requires the lookup
  anchor's child to have h'_R = x_lookupanchorpoststate; the model compared it with the anchor's
  x_stateroot, rejecting valid blocks whose lookup anchor differs from their anchor. Fixed in
  `JAM/BlockImport.lean`, with a regression test in `Tests/TraceTest.lean`.
- **The `$` of the context strings.** A bug in this repository's own model, reported by the
  jam-lean-target crypto work. The model kept the GP's `$` as the first octet of `$jam_ticket_seal`
  and the other context strings. In the paper `$` only marks the set of ASCII strings
  (`notation.tex`), though its wording leaves this open; the v0.8.0 vectors settle it: their 58
  ticket proofs verify only with "jam_ticket_seal" ⌢ …. Fixed in `JAM.contextString` (it drops a
  leading `$`), with `#guard`s on X_T, X_E and X_G. The paper's side of it is note v0.8.1-A7.
- **Notes 6–10, 14, 16 and 22.** Points where the vectors confirm a subtle reading, or observations
  that need no change.
