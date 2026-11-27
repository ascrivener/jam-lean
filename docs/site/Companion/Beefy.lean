import VersoManual
import Companion.Source
import Companion.Paper
import JAM.History
import JAM.Safrole
import JAM.Theorems.Safrole

open Verso.Genre Manual
open Companion

set_option pp.rawOnError true

#doc (Manual) "§18 Beefy distribution" =>
%%%
tag := "beefy"
shortTitle := "§18 Beefy"
file := "beefy"
%%%

*In the paper:* {gpchapter}`sec:beefy`.

*In brief.* Beefy lets systems outside JAM check what JAM has finalized by checking signatures. For
each finalized block it imports, every validator signs, with the BLS part of its key, the latest
super-peak of the Accumulation Output Log: a Merkle mountain range, kept in the recent history
({ref "history"}[§7]), of the outputs that services yield in accumulation
({ref "accumulation"}[§12]). BLS signatures can be aggregated, so many validators' signatures can be
combined into one concise proof of finality for a third-party system. The paper fixes only what is
signed, and defers the signature and aggregation scheme to an external specification. The model has
no BLS operations, so this chapter is a short map to the parts it does implement.

§18 of GP v0.8.1 asks each validator, for every finalized block it imports, to make a BLS signature
on the BLS12-381 curve affirming the Keccak hash of the block's most recent Beefy MMR, and to publish
it with the signed material. These signatures can be aggregated into concise proofs of finality for
third-party systems; the paper defers the signing and aggregation scheme to an external
specification. The signed commitment of validator $`v` is

{gpeq "18.1"}

{gpeq "18.2"}

It signs, under the BLS component of the validator's key in the posterior active set $`\activeset'`, the
context string followed by the field $`\rh¬accoutlogsuperpeak` of the latest recent-history entry: the super-peak of the
Accumulation Output Log.

# Where the model implements it
%%%
tag := "beefy-map"
%%%

* *The signed material, $`\text{last}(\recenthistory)_{\rh¬accoutlogsuperpeak}`.* Accumulation's output root, the Keccak Merkle root of
  the encoded $`\theta'`, is appended to the Accumulation Output Log $`\recent_B` by the Merkle mountain range
  append $`\mathcal{A}` (eqs. {eq}`7.6`, {eq}`7.7`); the new recent-history entry records its super-peak, $`b = \mathcal{M}_R(\recent'_B)` (eq. {eq}`7.8`). This is
  {api}`JAM.recentHistory`, in the {ref "history-belt"}[§7 chapter], with the mountain-range functions
  {api}`JAM.MMR.append` and {api}`JAM.MMR.superPeak` of {ref "merkle-mmr"}[Appendix E.2]; the field is `accRoot`
  of {api}`JAM.RecentBlock`. Keccak-256, $`\fnkeccak`, is in plain Lean ({ref "primitives-hashing"}[§3.8.1]).
* *The key, $`k_\vk¬bls`.* A validator key is 336 octets, and its BLS component is
  $`k_\vk¬bls = k_{64\dots+144}` (eq. {eq}`6.12`). The model keeps keys as octet sequences ({api}`JAM.ValidatorKey`) and carries
  the BLS component through the state unchanged; only the theorems' view {api}`JAM.ValidatorKey.View`
  names it (field `bls`).

# Not modelled
%%%
tag := "beefy-not-modelled"
%%%

The model does not define the signed commitment $`\accoutcommitment{v}` of eq. {eq}`18.1`, the context string
$`\Xbeefy` of eq. {eq}`18.2`, or BLS signatures: its crypto parameter has no BLS operations. Nor does it model
producing, publishing, distributing or aggregating these signatures. Like the other parts of the paper
that describe node behaviour, this is outside the state transition, which is what the model covers.
