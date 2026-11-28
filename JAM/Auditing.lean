import JAM.Fast.Blake2b
import JAM.Assurances
import JAM.Shuffle
import JAM.Constants
import JAM.Guarantee

/-!
# Auditing and judging (GP v0.8.1 §17, `auditing.tex`)

The deterministic parts of §17 that one validator $v$ computes about one block: which reports it may
have to audit, which of them it must audit in each tranche, what it signs, and when it considers a
report and the block audited. Off-chain logic: nothing here is part of the state transition.

Equations covered (labels of `auditing.tex` where it has them):

* $\mathbf{q}$ (eq. `auditselection`): the reports that just became available, by core (`auditReports`).
* $s_0$ (eq. `initialaudit`): the tranche-0 VRF,
  $\bssignaturebase{}^{[]}_{\kappa_v, b}\langle \mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V) \rangle$, checked
  through the `Crypto` parameter (`initialSeedValid`); $\mathsf{X}_U$ = `$jam_audit` (`Xaudit`).
* $\mathbf{a}_0$: the non-empty items among the first ten of
  $\mathcal{F}(\mathbf{q}, \mathcal{Y}(s_0))$ (`tranche0`, and its core-indexed form
  `tranche0Indexed`).
* $n = \lfloor (\mathcal{T} - \mathsf{P} \cdot \mathbf{H}_T) / \mathsf{A} \rfloor$, $\mathsf{A} = 8$
  (`currentTranche`).
* $S$ (eq. `announcement`): the announcement message
  $\mathsf{X}_I \mathbin{+\!\!+} n \frown \mathbf{x}_n \frown \mathcal{H}(\mathbf{H})$ and its check
  (`announcementMessage`, `announcementValid`); $\mathsf{X}_I$ = `$jam_announce` (`Xannounce`).
* $A_n$, $J_\top$, $J_\bot$: the validator's perception, as input (`View`).
* $s_n(w)$, $a_n(w)$, $\mathbf{a}_n$ (eq. `latertranches`): the later-tranche VRF context, the
  no-show rule with the bias factor $\mathsf{F} = 2$ (`laterSeedValid`, `noShows`, `laterSelected`,
  `laterTranche`).
* $e_n$ (eq. 17.16): the evaluation of a report from a candidate bundle $C(w)$, by decoding and
  checking the bundle and recomputing $\Xi$ (`evaluation`). Recovering $C(w)$ from erasure-coded
  chunks is not composed here (its parts are in `JAM.Erasure`).
* $\mathbf{j}_n$ (eq. `judgments`): the judgment message $\mathsf{X}_{e_n(w)} \frown \mathcal{H}(w)$
  and its check (`judgmentMessage`, `judgmentValid`), with $e_n(w)$ as the input `valid`.
* $U(w)$ and $\mathbf{U}$ (the audited conditions; `audited`, `blockAudited`).
* The link to §10: the supermajority clause of $U$ is the threshold of a good verdict
  (`JAM.Auditing.supermajority_iff_verdictGood` in `JAM.Theorems.Auditing`); a block author's verdict
  from its observed judgments (`formVerdict`); the chain-disregard condition of the best-block
  paragraph (`disregarded`).

## Readings of the paper (also in [`docs/upstream-candidates.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues))

1. **$U$'s $\exists n$ is unbounded.** Read literally, $\exists n : A_n(w) \subseteq J_\top(w)$ holds
   as soon as some tranche has $A_n(w) = \emptyset$, and eq. `latertranches` makes
   $A_n(w) = \emptyset$ for every $n$ after a tranche with no no-shows ($a_n$ needs a positive
   no-show count); tranches not yet reached are also perceived as $\emptyset$. So the first clause
   of $U$ collapses to $J_\bot(w) = \emptyset$. We bound $n$ by the current tranche
   (`audited … current`; the paper notes $A_n$ "cannot be correctly evaluated until $n$ is
   current"), which still accepts a report that no validator announced in some tranche
   $\leq$ current
   (`JAM.Auditing.audited_of_empty_tranche`). `AuditedLiteral` is the literal reading, and
   `JAM.Auditing.auditedLiteral_degenerate` shows the collapse.
2. **$n \geq 256$ in $\mathsf{X}_I \mathbin{+\!\!+} n$ and $\mathcal{H}(w) \mathbin{+\!\!+} n$.**
   $x \mathbin{+\!\!+} i \equiv x \frown [i]$ appends one element (GP §3, `notation.tex`), with
   naturals and octets coerced implicitly, so $n$ is one octet. The coercion is undefined for
   $n \geq 256$; we append $\mathcal{E}_1(n \bmod 2^8)$ there (`UInt8.ofNat`), as Safrole's ticket
   context does for the same notation.
3. **The order of the set in $\mathbf{x}_n$.** $\mathcal{E}$ of a set is its elements "in proper
   order" (Appendix C); the elements are the octet strings $\mathcal{E}_2(w_c) \frown \mathcal{H}(w)$,
   which we order lexicographically (as the model's other sets, `OctetSet`). Since $\mathcal{E}_2$
   is little-endian this is not core order.
4. **The negative-judgment escalation is prose only.** The text says a validator that has received a
   negative judgment must always judge the report, but eq. `latertranches` has no such disjunct.
   `laterTranche` is the equation; `laterTrancheWithNegatives` adds the prose rule.
5. **⅓ in the best-block rule.** The overview says a report is ban-listed when *greater than* ⅓ of
   validators judge it invalid; the best-block paragraph disregards chains with a report that *at
   least* ⅓ judge invalid. `disregarded` follows the latter ($3 \cdot |J_\bot| \geq |\kappa|$).
6. **$\mathcal{H}(w)$, $\mathcal{H}(\mathbf{H})$** are $\mathcal{H}(\mathcal{E}(w))$ and
   $\mathcal{H}(\mathcal{E}(\mathbf{H}))$. This is settled, not a reading: §3.8 passes the inputs of a
   hash function through $\mathcal{E}$.
7. **$|\mathbf{q}| = |\kappa|/3$** (the number of active cores), while $\rho$ has $\mathsf{C}$
   entries; for both chains $|\kappa|/3 = \mathsf{C}$. We read $\rho$ at indices below $|\kappa|/3$,
   missing entries as $\emptyset$.
8. **$\mathcal{T} - \mathsf{P} \cdot \mathbf{H}_T$** is a natural subtraction here; a wall clock
   before the slot's start reads as tranche 0.
9. **The first case of $A_0$** (`TODO: #445` in the source, the line stating $v \in A_0(w)$ for the
   validator's own tranche-0 items, is commented out): $A_n$ is taken as an input view, which a
   validator fills from the verified announcements, its own included.
-/

namespace JAM.Auditing

open JAM.Codec

/-- $\mathsf{X}_U$ = `$jam_audit` (GP §17.3 eq. `initialaudit`, Appendix I.4.5): Bandersnatch audit-selection
    entropy. -/
def Xaudit : List UInt8 := contextString "$jam_audit"

/-- $\mathsf{X}_I$ = `$jam_announce` (GP §17.3 eq. `announcement`, Appendix I.4.5): Ed25519 audit
    announcements. -/
def Xannounce : List UInt8 := contextString "$jam_announce"

#guard Xaudit = "jam_audit".toUTF8.toList
#guard Xannounce = "jam_announce".toUTF8.toList

/-- $\mathcal{H}(w) = \mathcal{H}(\mathcal{E}(w))$ (GP §3.8, Appendix C), the identifier of a work
    report in announcements, judgments and verdicts. -/
def reportHash (w : WorkReport) : List UInt8 :=
  (Blake2b.hash256 ⟨w.encode.toArray⟩).toList

/-! ## Validator sets -/

/-- A set of validator indices, $\subseteq \mathbb{N}_{|\kappa|}$, as its characteristic function;
    only indices below $|\kappa|$ are ever read. -/
abbrev VSet := Nat → Bool

namespace VSet

/-- The set of the indices in a list. -/
def ofList (l : List Nat) : VSet := fun i => l.contains i

/-- $\emptyset$. -/
def empty : VSet := fun _ => false

/-- The members of $s$ below $V$, ascending. -/
def members (V : Nat) (s : VSet) : List Nat := (List.range V).filter s

/-- $|s|$ for $s \subseteq \mathbb{N}_V$. -/
def card (V : Nat) (s : VSet) : Nat := (members V s).length

/-- $s \subseteq t$ within $\mathbb{N}_V$. -/
def Subset (V : Nat) (s t : VSet) : Prop := ∀ i, i < V → s i = true → t i = true

/-- `Subset`, decided. -/
def subsetB (V : Nat) (s t : VSet) : Bool := (List.range V).all fun i => !s i || t i

/-- $s = \emptyset$ within $\mathbb{N}_V$. -/
def isEmptyB (V : Nat) (s : VSet) : Bool := (List.range V).all fun i => !s i

/-- $s \setminus t$. -/
def sdiff (s t : VSet) : VSet := fun i => s i && !t i

end VSet

/-! ## The reports to audit (§17.3) -/

/-- $\mathbf{q} \in [\![ \workreport? ]\!]_{|\kappa|/3}$ (GP §17.3 eq. `auditselection`): for each
    active core $c$, the report of $\rho[c]$ when it is in $\mathbf{R}$ (the reports that just became
    available, compared by encoding), $\emptyset$ otherwise. -/
def auditReports (V : Nat) (ρ : AvailAssignments) (R : List WorkReport) : List (Option WorkReport) :=
  (List.range (V / 3)).map fun c =>
    match ρ.getD c none with
    | some a => if R.any (·.encode == a.guarantee.report.encode) then some a.guarantee.report else none
    | none => none

/-! ## Tranche 0 (§17.3) -/

/-- The context of $s_0$, $\mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V)$ (GP §17.3 eq. `initialaudit`). -/
def initialContext (crypto : Crypto) (vrfSig : List UInt8) : List UInt8 :=
  Xaudit ++ crypto.bsOut vrfSig

/-- $s_0 \in \bssignaturebase{}^{[]}_{\kappa_v, b}\langle \mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V) \rangle$
    (GP §17.3 eq. `initialaudit`; the context is $\mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V)$ and
    the message is empty, per `\bssignature{key}{context}{message}`): $v$'s tranche-0 evidence
    verifies under its Bandersnatch key. -/
def initialSeedValid (crypto : Crypto) (bsKey vrfSig s0 : List UInt8) : Bool :=
  crypto.bsVerify bsKey (initialContext crypto vrfSig) [] s0

/-- The number of cores tranche 0 draws (GP §17.3, "a verifiably random selection of ten cores"). -/
def tranche0Size : Nat := 10

/-- $\mathbf{a}_0 = \{ w \mid w \in \mathcal{F}(\mathbf{q}, \mathcal{Y}(s_0))_{\ldots+10}, w \neq \emptyset \}$
    (GP §17.3), as a sequence in shuffle order; `y` is $\mathcal{Y}(s_0)$. -/
def tranche0 (q : List (Option WorkReport)) (y : List UInt8) : List WorkReport :=
  ((Shuffle.shuffleHash q ⟨y.toArray⟩).take tranche0Size).filterMap id

/-- $\mathbf{a}_0$ with each report's core index: the same draw over $\mathbf{q}$ paired with its indices
    (`JAM.Auditing.tranche0_eq_map_snd` shows the reports agree). -/
def tranche0Indexed (q : List (Option WorkReport)) (y : List UInt8) : List (Nat × WorkReport) :=
  ((Shuffle.shuffleHash (q.zipIdx.map fun (w, c) => (c, w)) ⟨y.toArray⟩).take tranche0Size).filterMap
    fun (c, w) => w.map (c, ·)

/-! ## Tranche timing (§17.3) -/

/-- $n = \lfloor (\mathcal{T} - \mathsf{P} \cdot \mathbf{H}_T) / \mathsf{A} \rfloor$ (GP §17.3), with
    $\mathsf{P} = 6$ and $\mathsf{A} = 8$ seconds: the tranche current at wall-clock time $\mathcal{T}$
    (seconds since the JAM common era) for a block of slot $\mathbf{H}_T$. -/
def currentTranche (wallclock slot : Nat) : Nat :=
  (wallclock - Constants.Cslotseconds * slot) / Constants.Ctrancheseconds

/-! ## Announcements (§17.3) -/

/-- $\mathbf{x}_n = \mathcal{E}(\{ \mathcal{E}_2(w_c) \frown \mathcal{H}(w) \mid w \in \mathbf{a}_n \})$
    (GP §17.3 eq. `announcement`): the set's elements in ascending lexicographic order, with no
    length prefix (Appendix C, set encoding). -/
def announcementItems (a : List WorkReport) : List UInt8 :=
  ((Std.ExtTreeSet.ofList (a.map fun w => fixed 2 w.core ++ reportHash w) : OctetSet).toList).flatten

/-- $\mathsf{X}_I \mathbin{+\!\!+} n \frown \mathbf{x}_n \frown \mathcal{H}(\mathbf{H})$ (GP §17.3 eq.
    `announcement`), $n$ as one octet ($x \mathbin{+\!\!+} i \equiv x \frown [i]$, GP §3), reduced mod $2^8$
    for $n \geq 256$ where the paper's coercion is undefined (reading 2); `headerHash` is
    $\mathcal{H}(\mathbf{H})$. -/
def announcementMessage (n : Nat) (a : List WorkReport) (headerHash : List UInt8) : List UInt8 :=
  Xannounce ++ [UInt8.ofNat n] ++ announcementItems a ++ headerHash

/-- $S \equiv \edsignaturebase_{\kappa_v, e}\langle \mathsf{X}_I \mathbin{+\!\!+} n \frown \mathbf{x}_n \frown \mathcal{H}(\mathbf{H}) \rangle$
    (GP §17.3 eq. `announcement`): an announcement signature verifies under $v$'s Ed25519 key. -/
def announcementValid (crypto : Crypto) (edKey : List UInt8) (n : Nat) (a : List WorkReport)
    (headerHash sig : List UInt8) : Bool :=
  crypto.edVerify edKey (announcementMessage n a headerHash) sig

/-! ## The validator's perception (§17.3) -/

/-- What $v$ knows of the other validators (GP §17.3): $A_n(w)$, the validators required to audit
    $w$ at tranche $n$, from the announcements; $J_\top(w)$ and $J_\bot(w)$, the validators known to
    have judged $w$ valid and invalid, from any tranche. Reports are keyed by $\mathcal{H}(w)$, which
    is how announcements and judgments name them. -/
structure View where
  /-- $A_n(w)$: tranche $n \mapsto \mathcal{H}(w) \mapsto$ validators. -/
  announced : Nat → List UInt8 → VSet
  /-- $J_\top(w)$. -/
  positive : List UInt8 → VSet
  /-- $J_\bot(w)$. -/
  negative : List UInt8 → VSet

/-! ## Later tranches (§17.3 eq. `latertranches`) -/

/-- The context of $s_n(w)$,
    $\mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V) \frown \mathcal{H}(w) \mathbin{+\!\!+} n$ (GP §17.3
    eq. `latertranches`), $n$ as one octet ($x \mathbin{+\!\!+} i \equiv x \frown [i]$, GP §3), reduced mod
    $2^8$ for $n \geq 256$ where the paper's coercion is undefined (reading 2). -/
def laterContext (crypto : Crypto) (vrfSig : List UInt8) (w : WorkReport) (n : Nat) : List UInt8 :=
  Xaudit ++ crypto.bsOut vrfSig ++ reportHash w ++ [UInt8.ofNat n]

/-- $s_n(w) \in \bssignaturebase{}^{[]}_{\kappa_v, b}\langle \mathsf{X}_U \frown \mathcal{Y}(\mathbf{H}_V) \frown \mathcal{H}(w) \mathbin{+\!\!+} n \rangle$
    (GP §17.3 eq. `latertranches`). -/
def laterSeedValid (crypto : Crypto) (bsKey vrfSig : List UInt8) (w : WorkReport) (n : Nat)
    (s : List UInt8) : Bool :=
  crypto.bsVerify bsKey (laterContext crypto vrfSig w n) [] s

/-- $|A_{n-1}(w) \setminus J_\top(w)|$ (GP §17.3 eq. `latertranches`): the no-shows of tranche
    $n - 1$, the validators required to audit $w$ then from whom no positive judgment is known. -/
def noShows (V : Nat) (view : View) (n : Nat) (w : WorkReport) : Nat :=
  VSet.card V (VSet.sdiff (view.announced (n - 1) (reportHash w)) (view.positive (reportHash w)))

/-- $a_n(w) \equiv |\kappa|/(65536 \cdot \mathsf{F}) \cdot \mathcal{E}_2^{-1}(\mathcal{Y}(s_n(w))_{0\ldots+2}) < m$
    (GP §17.3 eq. `latertranches`), with $m$ the no-show count and $\mathsf{F} = 2$
    (`Cauditbiasfactor`), decided exactly as
    $|\kappa| \cdot \mathcal{E}_2^{-1}(\ldots) < 65536 \cdot \mathsf{F} \cdot m$. `y` is
    $\mathcal{Y}(s_n(w))$. Each validator is drawn with probability about
    $\mathsf{F} \cdot m / |\kappa|$, so about $\mathsf{F}$ validators per no-show. -/
def laterSelected (V : Nat) (y : List UInt8) (m : Nat) : Bool :=
  decide (V * PVM.Num.decodeLE (y.take 2) < 65536 * Constants.Cauditbiasfactor * m)

/-- $\mathbf{a}_n \equiv \{ w \mid w \in \mathbf{q}, w \neq \emptyset, a_n(w) \}$ for $n > 0$
    (GP §17.3 eq. `latertranches`); `y w` is $\mathcal{Y}(s_n(w))$. -/
def laterTranche (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport))
    (y : WorkReport → List UInt8) : List WorkReport :=
  (q.filterMap id).filter fun w => laterSelected V (y w) (noShows V view n w)

/-- $\mathbf{a}_n$ with the prose rule of §17.3 added: a report with a known negative judgment is always
    audited ("In the first case, the validator is always required to issue a judgment"). The rule is
    in the prose only, not in eq. `latertranches`; the model adds it. -/
def laterTrancheWithNegatives (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport))
    (y : WorkReport → List UInt8) : List WorkReport :=
  (q.filterMap id).filter fun w =>
    !VSet.isEmptyB V (view.negative (reportHash w)) || laterSelected V (y w) (noShows V view n w)

/-- $\mathbf{a}_n$ for any tranche (GP §17.3): $\mathbf{a}_0$ from $\mathcal{Y}(s_0)$ when $n = 0$,
    eq. `latertranches` otherwise. -/
def tranche (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport)) (y0 : List UInt8)
    (y : WorkReport → List UInt8) : List WorkReport :=
  if n = 0 then tranche0 q y0 else laterTranche V view n q y

/-! ## Evaluation (§17.3 eq. 17.16) -/

/-- $e_n(w)$ (GP §17.3 eq. 17.16): with $C(w)$ = `C` the candidate bundle,
    $e_n(w) \Leftrightarrow M(w, p)$ when some $p$ has $B(p, w_l) = C(w)$, else $\bot$, where
    $M(w, p) \equiv w = \Xi(p, w_c, w_l, (w_s)_n)$. The model decodes and checks $C(w)$
    (`JAM.Guarantee.verifyBundle`: "a failure to decode or verify the bundle implies an invalid
    work-report"), requires the decoded package and data to re-assemble to exactly $C(w)$
    (`JAM.Guarantee.bundle`), and compares $w$ with $\Xi$ (`JAM.Guarantee.computeReport`, over the
    accounts `d`, with the decoded item data), $\nabla$ counting as unequal. -/
def evaluation (params : Params) (d : Accounts) (C : List UInt8) (w : WorkReport) : Bool :=
  match Guarantee.verifyBundle Blake2b.hash256 w.segmentRootLookup C with
  | none => false
  | some b =>
    Guarantee.bundle b.package b.items == C &&
      decide (Guarantee.computeReport params d b.package w.core w.segmentRootLookup
        w.spec.erasureShards b.items = some w)

/-! ## Judgments (§17.3 eq. `judgments`) -/

/-- $\mathsf{X}_{e_n(w)} \frown \mathcal{H}(w)$ (GP §17.3 eq. `judgments`), with
    $\mathsf{X}_\top$ = `$jam_valid`, $\mathsf{X}_\bot$ = `$jam_invalid`:
    the message of a judgment on $w$ whose evaluation gave `valid`. It is the message §10's verdicts
    check (`JAM.checkVerdict`), so a judgment serves directly as a verdict vote. -/
def judgmentMessage (valid : Bool) (w : WorkReport) : List UInt8 :=
  Xvalidif valid ++ reportHash w

/-- A judgment signature
    $\bar{\mathcal{S}}_{\kappa_v, e}(\mathsf{X}_{e_n(w)} \frown \mathcal{H}(w))$ verifies under $v$'s
    Ed25519 key (GP §17.3 eq. `judgments`). -/
def judgmentValid (crypto : Crypto) (edKey : List UInt8) (valid : Bool) (w : WorkReport)
    (sig : List UInt8) : Bool :=
  crypto.edVerify edKey (judgmentMessage valid w) sig

/-! ## The audited conditions (§17.3) -/

/-- $U(w) \Leftrightarrow (J_\bot(w) = \emptyset \land \exists n : A_n(w) \subseteq J_\top(w)) \lor |J_\top(w)| > \tfrac{2}{3}|\kappa|$
    (GP §17.3), with $n$ bounded by the current tranche (reading 1 of the module docstring); `h` is
    $\mathcal{H}(w)$. -/
def Audited (V : Nat) (view : View) (current : Nat) (h : List UInt8) : Prop :=
  (VSet.isEmptyB V (view.negative h) = true ∧
    ∃ n, n ≤ current ∧ VSet.Subset V (view.announced n h) (view.positive h)) ∨
  3 * VSet.card V (view.positive h) > 2 * V

/-- $U(w)$ as the paper writes it, with $n$ unbounded (see `auditedLiteral_degenerate`). -/
def AuditedLiteral (V : Nat) (view : View) (h : List UInt8) : Prop :=
  (VSet.isEmptyB V (view.negative h) = true ∧
    ∃ n, VSet.Subset V (view.announced n h) (view.positive h)) ∨
  3 * VSet.card V (view.positive h) > 2 * V

/-- $U(w)$, decided (`JAM.Auditing.audited_iff` shows it decides `Audited`). -/
def audited (V : Nat) (view : View) (current : Nat) (h : List UInt8) : Bool :=
  (VSet.isEmptyB V (view.negative h) &&
    (List.range (current + 1)).any fun n => VSet.subsetB V (view.announced n h) (view.positive h)) ||
  decide (3 * VSet.card V (view.positive h) > 2 * V)

/-- $\mathbf{U} \Leftrightarrow \forall w \in \mathbf{R} : U(w)$ (GP §17.3): the block is audited
    when every report that became available in it is. -/
def blockAudited (V : Nat) (view : View) (current : Nat) (R : List WorkReport) : Bool :=
  R.all fun w => audited V view current (reportHash w)

/-- A report at least ⅓ of the validators are known to judge invalid (GP §17.3, best-block
    paragraph): chains that accumulate it are disregarded. $3 \cdot |J_\bot(w)| \geq |\kappa|$
    (reading 5). -/
def disregarded (V : Nat) (view : View) (h : List UInt8) : Bool :=
  decide (3 * VSet.card V (view.negative h) ≥ V)

/-! ## Verdicts from observed judgments (§17.3 → §10) -/

/-- A verdict a block author can form from its observed judgments on $w$ (GP §17.3, last paragraph;
    §10.2 eq. `verdicts`): $\lfloor \tfrac{2}{3}|\kappa| \rfloor + 1$ votes, ascending by validator
    index, each backed by a known judgment, giving a defined $V(a, \mathbf{j})$. Tries good (all
    positive), then bad (all negative), then wonky ($\lfloor |\kappa|/3 \rfloor$ positive and the rest
    negative, from validators not counted as positive); the paper fixes no preference. `sig i b`
    supplies the signature of validator $i$'s judgment $b$. The
    result is checked against `JAM.verdictOutcome` and `JAM.orderedUniqByNat` before it is
    returned. -/
def formVerdict (V : Nat) (pos neg : VSet) (sig : Nat → Bool → Blob) :
    Option (Outcome × List Judgment) :=
  let k := 2 * V / 3 + 1
  let mk (b : Bool) (is : List Nat) := is.map fun i => ({ valid := b, index := i, signature := sig i b } : Judgment)
  let P := VSet.members V pos
  let N := VSet.members V neg
  let wonkyPos := P.take (V / 3)
  let wonkyNeg := (N.filter fun i => !wonkyPos.contains i).take (k - V / 3)
  let wonky := (List.range V).filterMap fun i =>
    if wonkyPos.contains i then some ({ valid := true, index := i, signature := sig i true } : Judgment)
    else if wonkyNeg.contains i then some { valid := false, index := i, signature := sig i false }
    else none
  let candidates : List (Outcome × List Judgment) :=
    [(.good, mk true (P.take k)), (.bad, mk false (N.take k)), (.wonky, wonky)]
  candidates.find? fun (o, js) =>
    js.length == k && orderedUniqByNat (·.index) js && verdictOutcome V js == some o

end JAM.Auditing
