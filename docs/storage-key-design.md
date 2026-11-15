# Storage keys: loading σ from serialized state (design note)

Status: **scoping only, nothing decided.** No Lean is changed by this note.

**The problem** (reported by jam-lean-target, which uses jam-lean as a conformance fuzzing target):
σ cannot be rebuilt from its key–value form T(σ) (GP v0.8.0 Appendix D) when an account has storage
entries, or request entries whose preimage is absent. As a result, 52 of the 89 published GP 0.8.0
fuzz traces (jam-fuzzing `fuzz-reports/0.8.0`) cannot be replayed. That figure is the reporter's;
it was not re-measured here. Fuzzing from genesis is unaffected.

`Tests/TraceState.lean:10-15` already documents the limitation. Its `decodeState` handles storage
only for keys the caller already knows (`knownKeys`, `Tests/TraceState.lean:166-176`). It
recognises preimages by hashing the value (`:177-184`) and requests through a known preimage
(`:185-198`), and throws on anything else (`:198`).

GP references are to `text/*.tex` at tag v0.8.0 of `gavofyork/graypaper`.

## 1. What GP v0.8.0 says

### σ (eq. `serviceaccount`, accounts.tex:12-27)

| Term | Type in GP | Type in the model |
|---|---|---|
| **s** (storage) | 𝔹 → 𝔹, keyed by the unhashed key **k** | `JAM/Account.lean:24` |
| **p** (preimages) | ℍ → 𝔹 | `:26` |
| **l** (requests) | (ℍ, ℕ_L) → ⟦ℕ_T⟧_{:3} | `:28` |

a_i and a_o are **dependent terms** (eq. `deposits`, accounts.tex:143-157):

- a_i = 2·|**l**| + |**s**|
- a_o = Σ_{(h,z)∈K(**l**)} (81 + z) + Σ_{(x,y)∈**s**} (34 + |y| + |x|)
- a_t = max(0, B_S + B_I·a_i + B_L·a_o − a_f)

The model computes them from the dictionaries: `JAM/Account.lean:53-62`.

### T(σ) (merklization.tex:9-17, 86-111)

The service rows are:

- C(255, s) ↦ ℰ(0, a_c, ℰ_8(a_b, a_g, a_m, **a_o**, a_f), ℰ_4(**a_i**, a_r, a_a, a_p)). So a_o and
  a_i *are* serialized, but in GP they are outputs of the formula, not stored state.
- storage: C(s, ℰ_4(2³²−1) ⌢ **k**) ↦ **v**
- preimages: C(s, ℰ_4(2³²−2) ⌢ h) ↦ **p**
- requests: C(s, ℰ_4(l) ⌢ h) ↦ ℰ(↕[ℰ_4(x) | x ← **t**])

C(s, h) = [n₀, a₀, n₁, a₁, n₂, a₂, n₃, a₃, a₄, …, a₂₆], where n = ℰ_4(s) and a = ℋ(h)
(merklization.tex:15). The key therefore keeps the service id and only the **first 27 octets of
ℋ(discriminator ⌢ key)**. The model implements this in `JAM/Trie.lean:32-38` (`keyOfServiceData`)
and `JAM/State.lean:164-177`.

What follows for loading σ from key–values:

1. **Storage.** Neither **k** nor |**k**| can be recovered.
2. **Preimages.** These can be recovered: h = ℋ(**p**), and the key can be checked.
3. **Requests.** (h, l) can be recovered only if the preimage is present. Without it, a request
   entry cannot even be told apart from a storage entry, because the discriminator is inside the
   hash.
4. **a_o and a_i.** These cannot be recomputed from the formula (|x| is lost) and must be read from
   C(255, s). Today the model recomputes them, so a loaded state's C(255, s) would not round-trip.

GP says this is intended (merklization.tex:116): *"JAM does not allow service storage keys to be
directly inspected or enumerated … Implementations are free to use this fact in order to avoid
storing the keys themselves."* It also assumes collision-freedom (merklization.tex:19): *"Cryptographic
hashing ensures that there will be no duplicate state-keys given that there are no duplicate inputs
to C."*

### What touches these fields

| GP | Model | Uses |
|---|---|---|
| Ω_L `lookup` (pvm_invocations.tex:416-440) | `JAM/Host/General.lean:190-198` | **p**[h] |
| Ω_R `read` (:442-470) | `General.lean:204-216` | **s**[k] of self or another service |
| Ω_W `write` (:472-497) | `General.lean:224-247` | **s**[k] insert/erase; old \|v\|; FULL test on a_t of the *new* account (needs \|k\|) |
| Ω_I `info` (:498-526) | `General.lean:253-256` | a_t, a_o, a_i |
| Ω_H `historical_lookup` (:546) and Λ (accounts.tex:114-118) | `JAM/Refine.lean:59-69`, `Account.lean:74-77` | **p**[h], then **l**[h, \|p\|] |
| Ω_N `new` (:807-845) | `JAM/Accumulate.lean:165-173` | new account with **l** = {(c,l) ↦ []}; a_t of the new account and of self |
| Ω_T `transfer` (:864-895) | `Accumulate.lean:206` | a_t of self |
| Ω_J `eject` (:896-920) | `Accumulate.lean:233-235` | l = max(81, d_o) − 81; d_i = 2; **l**[h, l] |
| Ω_Q `query` (:921-945) | `Accumulate.lean:254` | **l**[h, z] |
| Ω_S `solicit` (:946-970) | `Accumulate.lean:272-279` | **l** insert; FULL on a_t |
| Ω_F `forget` (:971-1000) | `Accumulate.lean:292-298` | **l**, **p** erase/update |
| Ω_♈ `provide` (:1017-1045) | `Accumulate.lean:324` | **l**[ℋ(i), z] = [] |
| Preimage integration (accumulation.tex:268-283) | `JAM/Accumulation.lean:89-91` | **l**, **p** insert |
| E_P validity | `JAM/Preimages.lean:34` | **l**[ℋ(i), \|i\|] = [] |
| Code c (accounts.tex:41-45) | `Accumulate.lean:372`, `Services/Witness/Confined.lean:19` | **p**[a_c] |
| Refine (Λ on the code hash) | `Refine.lean:302, 326` | via Λ |
| T(σ) | `JAM/State.lean:164-177` | everything |

Every access to **s** and **l** goes through a key that the caller supplies: k from memory, or
(h, z). No function enumerates **s**, and **l** is enumerated only by a_i and a_o. This is what
makes re-keying by hash GP-faithful *given collision-freedom*.

## 2. Options

### (A) Re-key by state key, carry a_o and a_i (suggested by the reporter)

Per account:

- Keep `preimages : ℍ → 𝔹`. It is recoverable from T(σ), and Λ and the code lookup are unchanged.
- Replace `storage` and `requests` with **one** dictionary `entries : 𝔹_27 → 𝔹`, keyed by the
  27-octet hash part of C(s, ·). Storage values are stored raw and request values as
  ℰ(↕[ℰ_4 x]), exactly as in T(σ).
  - Storage and requests have to share one dictionary: two separate hash-keyed dictionaries
    (call that A1) do not solve the problem. A loaded request entry without its preimage cannot be
    classified, so the loader would not know which dictionary to put it in.
  - Keying by the 27-octet part rather than the full 31-octet state key leaves out the service id,
    which is redundant inside an account. Otherwise Ω_W (`hostWrite`, which takes no service id)
    would need one.
- Carry `octets` (a_o) and `items` (a_i) as fields. Every mutation updates them:
  - write: ±1 item, ±(34 + |k| + |v|) octets. |k| and the old |v| are known at the call.
  - solicit (new request): +2, +(81 + z).
  - forget (drop): −2, −(81 + z).
  - new: (2, 81 + l).
  - Preimage provision changes neither.
- Accessors: `storageGet a k := a.entries.get? (key27 (ℰ_4(2³²−1) ⌢ k))` and
  `requestGet a h z := (a.entries.get? (key27 (ℰ_4 z ⌢ h))).bind decodeSlots`.

**GP-faithfulness.** This is faithful to T(σ) and to every transition *if* C has no collision on
the keys that occur. That is the paper's own assumption (merklization.tex:19), and its explicit
licence (:116). It is **not** faithful to σ as literally defined: on a collision, two distinct
**k** alias, while the k-keyed model would keep them apart. Blake2b is concrete plain Lean here
(`JAM/Blake2b.lean`), so collision-freedom cannot be proved; it would be an assumption.

Faithfulness can be made explicit with a **bridging theorem** that relates the old k-keyed account
to the new one:

- on states built from k-keyed dictionaries, carried a_o and a_i equal the formula;
- every host function commutes with the abstraction;
- it holds under a "no collision among the keys used" hypothesis.

That hypothesis would appear only on the bridging theorem, not on T1 or T2.

One open point the paper does not decide: a request access that hits an `entries` value that does
not decode as ⟦ℕ_T⟧_{:3}. The genuine T(σ) of any σ never contains such a value; a loaded,
invalid state can. The model must pick a behaviour, for example "absent". Any choice agrees with GP
on valid states.

**What changes.**

- **Definitions:**
  - `JAM/Account.lean` (structure, `items`, `octets`; `historicalLookup` changes in its request
    step only);
  - `JAM/Host/General.lean` (Ω_R, Ω_W, Ω_I);
  - `JAM/Accumulate.lean` (new, eject, query, solicit, forget, provide);
  - `JAM/Accumulation.lean:89-91`;
  - `JAM/Preimages.lean:34`;
  - `JAM/State.lean:164-177` (simpler: `entries` serialize directly; C(255) emits the carried
    fields).
- **Test loaders:**
  - `Tests/TraceState.lean` becomes total: preimages are classified by hash, everything else goes
    into `entries`, and a_o/a_i come from C(255);
  - `Tests/AccumulateTest.lean:29-38` (hash the vectors' raw keys, take a_o/a_i from the
    vectors);
  - `Tests/PreimagesTest.lean:33`, `Tests/RefineTest.lean:163, 209`;
  - `Tests/HostGeneralTest.lean:46-53` (`.storage.get?` becomes the accessor).
- **Effort: M.**
  - About 10 definitions.
  - The proofs listed in §3 need mechanical restatement.
  - A **cold CI rebuild** (about 4.5–5 h), because `JAM/Account.lean` is imported by nearly
    everything.
  - The optional bridging theorem is extra (S–M).

### (B) Keep the k-keyed dictionaries; add an "opaque entries" layer

Add `opaque : 𝔹_27 → 𝔹` per account. It is filled only by the loader, with the entries it cannot
classify, and a_o/a_i are still carried, because opaque storage has no |k|.

- Every storage or request access first checks the typed dictionary, then `opaque` under the hashed
  key.
- Every write or erase must also delete the opaque twin, or the two copies diverge.
- a_o/a_i maintenance then has to know which layer held the old value.

**GP-faithfulness.** On states without opaque entries it is the same as today. With them, it
depends on the same collision-freedom assumption as (A), plus an invariant that no key is live in
both layers. It is two representations of one GP dictionary, so it is less faithful in form.

**What changes.**

- **Definitions:** the same definitions as (A), each gaining a fallback branch.
- **Proofs:** every lemma that states a host result as `self.storage.get? key` (§3) becomes false as
  stated. It must either:
  - take a hypothesis `self.opaque = ∅`. Carried up to T2, this **narrows T2** to states that
    were not loaded from key–values, a change to what T2 assumes; or
  - be restated with a two-layer accessor, which is the same restatement work as (A) with a messier
    accessor.

**Effort: M+.** It is no cheaper than (A), and it leaves a permanent dual representation.

### (C) No model change; handle it in the target harness

jam-lean-target skips or rejects traces whose pre-state has unclassifiable entries. That is the
status quo, and the 52 traces stay unreplayable.

A variant, (C′), seeds `decodeState`'s `knownKeys` from the trace's earlier blocks. It does not help
with mid-chain pre-states, whose history is not given.

**GP-faithfulness:** unchanged. **Effort:** none in the model, and it fixes nothing.

### (D) Generalise the account to an abstract interface (considered, not recommended)

Make `ServiceAccount` a typeclass or record of operations (get, put, erase, footprint), with both
representations as instances. This is the most general option. It roughly doubles the work of (A),
and every proof would carry the instance.

## 3. Impact on statements

The grep covered `JAM/`, `PVM/` and `Services/` for `.storage`, `.preimages`, `.requests`,
`.octets`, `.items`, `minBalance` and `historicalLookup`. Matches on work-package `p.items` are not
counted, and `PVM/` has no matches.

### Unchanged under (A)

These mention only `historicalLookup` or Λ, whose signature is unchanged.

- **JAM theorems:**
  - `JAM/Theorems/Confinement.lean:271, 299`
  - `JAM/Theorems/HostGas.lean:235-249`
  - `JAM/Theorems/KeepRO.lean:167`
  - `JAM/Theorems/RefineContract.lean:229`
  - `Services/Bootstrap/Alloc/Pages.lean:115`

  The first, third and fourth files, and `Alloc/Pages.lean`, unfold the *Refine host* wrapper,
  which does not read the fields.
- **T1 chain:**
  - `Services/Bootstrap/Bridge.lean:80-88, 147-148`
  - `Services/Bootstrap/NoInstr.lean:108-109`
  - `Services/Bootstrap/PsiREmpty.lean:60-61`
- **Witness:**
  - `Services/Witness/PsiR.lean:32-33, 87-88`
  - `PsiREmpty.lean:25-107, 161-162`
  - `PsiRLift.lean:18-19, 73-74`
  - `Rejects.lean:47-48`
  - `Services/Witness.lean:53-54`
  - `Confined.lean:19-46`: `a.preimages.get? a.codeHash`, and `preimages` is kept.
- **Bootstrap specs:**
  - `Services/Bootstrap/ASem.lean`: no field access. Its `myInfo` decodes Ω_I's reply
    (`ASem.lean:84-99`), whose a_o/a_i are now carried rather than computed.
  - `Services/Bootstrap/Spec.lean:626`: uses `info.bytes` / `info.items` from that reply.

### Mechanical restatement under (A)

In each, `self.storage.get? key` becomes `storageGet self key`. Proofs case-split on the lookup and
carry the minBalance comparison through `by_cases`, so they should follow once the accessor has its
`get?`-style lemmas.

- `Services/Bootstrap/ASemLemmas.lean:95-243`, including `writeAcct` (`:175-177`), which must also
  update a_o/a_i.
- `Services/Bootstrap/Acc/Wrappers/ReadHost.lean:35-53`
- `Services/Bootstrap/Acc/Wrappers/GetCall.lean:59, 107, 163, 400, 477-516`
- `Services/Bootstrap/Acc/Wrappers/SetCall.lean:42, 85`

`Get.lean`, `Set.lean`, `Remove.lean` and `GrowS.lean` in the same folder have no direct field
access.

### Real proof change

- **None among the existing theorems.**
- The bridging theorem of (A), if wanted, is new work.
- Definitional lemmas about Ω_W, Ω_S and Ω_F that expose the footprint (none exist today beyond
  `writeAcct`) would need the carried-field arithmetic.

### T1 and T2

**T1** (refine, `docs/bootstrap-target.md` §T1) depends on accounts only through Λ: **no change.**

**T2** (`docs/bootstrap-target.md:393-404`) equates Ψ_A with `ASem.outcome`. Both sides run the same
model host functions.

- The statement text is unchanged.
- `ValuesFit` (planned, not yet in Lean; `bootstrap-target.md:423-434`) would range over storage
  values in `entries`. That is a restatement, and request values are tiny.

**What T2 means relative to the paper does change.** Under (A), T2 is a theorem about a model that
is faithful to GP σ only up to C-collision-freedom. Today it is literally faithful to σ. **This is
a change to what the project assumes**, and it is for Adam to decide.

**S5** (`accumulate_local`, `bootstrap-target.md:503-509`, planned) states
`StorageChangesWithin (Spec.ownKeys …)` over unhashed keys. It would be restated over their hashed
keys. Absent collisions the claims are equivalent; with collisions, the restated form is the one
that matches the GP serialization.

**S6** ("balance stays above its threshold") is unchanged.

## 4. Recommendation

**Adopt (A)** (with `preimages` kept and a single `entries` dictionary), and **escalate one point to
Adam** first: (A) makes C-collision-freedom an implicit assumption of the model.

- The paper itself makes and licenses this assumption (merklization.tex:19, 116).
- It would be listed in `docs/whats-proven.md` like the crypto parameter.
- Optionally it would be made explicit by the bridging theorem.

Reject (B): it costs the same, keeps two representations, and either narrows T2 or needs the same
restatements. (C) leaves the 52 traces broken.

### Sequencing with the T2 work in `Services/Bootstrap/Acc/`

1. **Now (small, additive, no claim changes).** Add accessor functions and their lemmas to
   `JAM/Account.lean`, still defined on the current dictionaries:
   - `storageGet`, `storagePut`, `requestGet`, …;
   - `storageGet_put_same` and `storageGet_put_other`, the latter stated with
     `key27 k ≠ key27 k'`, which is trivially derivable today.

   Ask the sessions in `Acc/` to state new lemmas with the accessors. This touches the root module
   (cold rebuild), so batch it with the next PR that already triggers one.
2. **After T2's storage wrappers settle** (`ReadHost`, `GetCall`, `SetCall`, `ASemLemmas`), switch
   the representation in one PR:
   - model definitions, `State.lean`, test loaders;
   - re-prove the four files above against the new accessor definitions;
   - add the T(σ) round-trip check to `Tests/TraceTest.lean` using the fuzz traces.

   Do this between T2 milestones, not under an open T2 PR, so it does not force re-syncs on
   in-flight branches.
3. **Optional, afterwards:** the bridging theorem (k-keyed account ≈ hash-keyed account, under no
   collision on the keys used).

Blocked meanwhile: replaying the 52 traces in jam-lean-target. Genesis-based fuzzing and all T1/T2
work proceed unaffected.
