import VersoManual
import Companion.Source
import JAM.Assurances
import JAM.Guarantee
import JAM.Erasure

open Verso.Genre Manual
open Companion

set_option pp.rawOnError true

#doc (Manual) "§16 Availability assurance" =>
%%%
tag := "assurance"
shortTitle := "§16 Assurance"
file := "assurance"
%%%

§16 of GP v0.8.1 says what a validator must hold before it claims, in an *assurance*, that a
report's data is available. Every timeslot each validator should issue a signed assurance saying
which of the current availability assignments it has received its erasure-coded shards for. It needs
two kinds of shard for an assignment:

* its shard of the report's bundle, which is needed to audit the report and "need not be retained
  after the work-report is considered audited";
* its shard of each exported segment under the report's segments root, which "should be retained for
  28 days and provided to any validator on request".

A shard is shown valid by the report's erasure root and a Merkle proof of inclusion at the right
position. Guarantors should send such proofs with the shards, and a validator should not claim a
shard it has not received and verified with its proof. The section has no equations of its own.

# Where the model implements it
%%%
tag := "assurance-map"
%%%

* *The assurance.* The assurances extrinsic $`\xtassurances`, its signing message
  $`\Xavailable \concat \blake{\encode{\H_\¬parent, a_f}}` with $`\Xavailable = \token{\$jam\_available}` (eqs. (11.11)–(11.15)), and the rule
  that a report becomes available when more than two thirds of the validators assure it
  (eq. (11.16)) are in the {ref "reports-assurances"}[§11 chapter]: {api}`JAM.assuranceMessage`,
  {api}`JAM.checkAssurance` and {api}`JAM.assurances`.
* *The shards.* How the bundle and the exported segments (with their paged proofs) are cut into one
  chunk per validator, and how their hashes and Merkle roots are combined into the erasure root
  $`u` of the availability specifier (eq. (14.19)), is in {ref "work-avspec"}[The availability specifier]
  ({api}`JAM.Guarantee.bundleClub`, {api}`JAM.Guarantee.segmentsClub`, {api}`JAM.Guarantee.erasureRoot`). The erasure code
  $`\fnerasurecode{v}{k}` and its recovery are {ref "erasure"}[Appendix H] ({api}`JAM.Erasure.encode`), and the
  Merkle roots are {ref "merkle"}[Appendix E].
* *The segments root.* A report's segments root $`e` is the constant-depth Merkle root $`\mathcal{M}` of its
  exports (eq. (14.19)); the justifications that prove a segment is under it, and their check, are in
  {ref "merkle-verify"}[Checking a justification].

# Not modelled
%%%
tag := "assurance-not-modelled"
%%%

The model covers the state transition and the deterministic functions it depends on, not how a node
behaves. So it does not model:

* the distribution and fetching of shards, and which validator holds which shard;
* how long a validator keeps its shards, and serving them on request;
* when a validator decides to issue an assurance, or produces its signature (the model checks
  assurances; it holds no secret keys).

The model computes the erasure root, but it has no function that builds or checks the proof that a
shard is included under it.
