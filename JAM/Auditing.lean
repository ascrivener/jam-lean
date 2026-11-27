import JAM.Fast.Blake2b
import JAM.Assurances
import JAM.Shuffle
import JAM.Constants

/-!
# Auditing and judging (GP v0.8.1 §17, `auditing.tex`)

The deterministic parts of §17 that one validator v computes about one block: which reports it may
have to audit, which of them it must audit in each tranche, what it signs, and when it considers a
report and the block audited. Off-chain logic: nothing here is part of the state transition.

Equations covered (labels of `auditing.tex` where it has them):

* **q** (eq. `auditselection`): the reports that just became available, by core (`auditReports`).
* s₀ (eq. `initialaudit`): the tranche-0 VRF, 𝔹^{[]}_{κ_v,b}⟨X_U ⌢ Y(H_V)⟩, checked through the
  `Crypto` parameter (`initialSeedValid`); X_U = `$jam_audit` (`Xaudit`).
* **a**₀: the non-empty items among the first ten of ℱ(**q**, Y(s₀)) (`tranche0`, and its
  core-indexed form `tranche0Indexed`).
* n = ⌊(𝒯 − 𝖯·H_T)/𝖠⌋, 𝖠 = 8 (`currentTranche`).
* S (eq. `announcement`): the announcement message X_I ⧺ n ⌢ **x**_n ⌢ ℋ(H) and its check
  (`announcementMessage`, `announcementValid`); X_I = `$jam_announce` (`Xannounce`).
* A_n, J_⊤, J_⊥: the validator's perception, as input (`View`).
* s_n(w), a_n(w), **a**_n (eq. `latertranches`): the later-tranche VRF context, the no-show rule
  with the bias factor 𝖥 = 2 (`laterSeedValid`, `noShows`, `laterSelected`, `laterTranche`).
* **j**_n (eq. `judgments`): the judgment message X_{e_n(w)} ⌢ ℋ(w) and its check
  (`judgmentMessage`, `judgmentValid`). The evaluation e_n itself (bundle reconstruction and
  Ξ, eq. `computereport`) is an input here.
* U(w) and **U** (the audited conditions; `audited`, `blockAudited`).
* The link to §10: the supermajority clause of U is the threshold of a good verdict
  (`JAM.Auditing.supermajority_iff_verdictGood` in `JAM.Theorems.Auditing`); a block author's verdict
  from its observed judgments (`formVerdict`); the chain-disregard condition of the best-block
  paragraph (`disregarded`).

## Readings of the paper (also in [`docs/upstream-candidates.md`](https://github.com/ascrivener/jam-lean/blob/main/docs/upstream-candidates.md#gray-paper-issues))

1. **U's ∃n is unbounded.** Read literally, `∃ n : A_n(w) ⊆ J_⊤(w)` holds as soon as some tranche
   has A_n(w) = ∅, and eq. `latertranches` makes A_n(w) = ∅ for every n after a tranche with no
   no-shows (a_n needs a positive no-show count); tranches not yet reached are also perceived as ∅.
   So the first clause of U collapses to J_⊥(w) = ∅. We bound n by the current tranche
   (`audited … current`; the paper notes A_n "cannot be correctly evaluated until n is current"),
   which still accepts a report that no validator announced in some tranche ≤ current
   (`JAM.Auditing.audited_of_empty_tranche`). `AuditedLiteral` is the literal reading, and
   `JAM.Auditing.auditedLiteral_degenerate` shows the collapse.
2. **The width of n in X_I ⧺ n and ℋ(w) ⧺ n.** ⧺ appends one element to an octet sequence, but n is
   a natural. We use ℰ(n) (the general natural encoding, Appendix C), which is the single octet n
   for n < 128; Safrole's ticket context uses one octet for the same notation.
3. **The order of the set in x_n.** ℰ of a set is its elements "in proper order" (Appendix C); the
   elements are the octet strings ℰ₂(w_c) ⌢ ℋ(w), which we order lexicographically (as the model's
   other sets, `OctetSet`). Since ℰ₂ is little-endian this is not core order.
4. **The negative-judgment escalation is prose only.** The text says a validator that has received a
   negative judgment must always judge the report, but eq. `latertranches` has no such disjunct.
   `laterTranche` is the equation; `laterTrancheWithNegatives` adds the prose rule.
5. **⅓ in the best-block rule.** The overview says a report is ban-listed when *greater than* ⅓ of
   validators judge it invalid; the best-block paragraph disregards chains with a report that *at
   least* ⅓ judge invalid. `disregarded` follows the latter (3·|J_⊥| ≥ |κ|).
6. **ℋ(w), ℋ(H)** are read as ℋ(ℰ(w)) and ℋ(ℰ(H)), as elsewhere in the paper.
7. **|q| = |κ|/3** (the number of active cores), while ρ has 𝖢 entries; for both chains |κ|/3 = 𝖢.
   We read ρ at indices below |κ|/3, missing entries as ∅.
8. **𝒯 − 𝖯·H_T** is a natural subtraction here; a wall clock before the slot's start reads as
   tranche 0.
9. **The first case of A₀** (`TODO: #445` in the source, the line stating v ∈ A₀(w) for the
   validator's own tranche-0 items, is commented out): A_n is taken as an input view, which a
   validator fills from the verified announcements, its own included.
-/

namespace JAM.Auditing

open JAM.Codec

/-- X_U = `$jam_audit` (GP §17.3 eq. `initialaudit`, Appendix I.4.5): Bandersnatch audit-selection
    entropy. -/
def Xaudit : List UInt8 := contextString "$jam_audit"

/-- X_I = `$jam_announce` (GP §17.3 eq. `announcement`, Appendix I.4.5): Ed25519 audit
    announcements. -/
def Xannounce : List UInt8 := contextString "$jam_announce"

#guard Xaudit = "jam_audit".toUTF8.toList
#guard Xannounce = "jam_announce".toUTF8.toList

/-- ℋ(w) = ℋ(ℰ(w)) (GP §3.8, Appendix C), the identifier of a work report in announcements,
    judgments and verdicts. -/
def reportHash (w : WorkReport) : List UInt8 :=
  (Blake2b.hash256 ⟨w.encode.toArray⟩).toList

/-! ## Validator sets -/

/-- A set of validator indices, ⊆ ℕ_{|κ|}, as its characteristic function; only indices below |κ|
    are ever read. -/
abbrev VSet := Nat → Bool

namespace VSet

/-- The set of the indices in a list. -/
def ofList (l : List Nat) : VSet := fun i => l.contains i

/-- ∅. -/
def empty : VSet := fun _ => false

/-- The members of s below V, ascending. -/
def members (V : Nat) (s : VSet) : List Nat := (List.range V).filter s

/-- |s| for s ⊆ ℕ_V. -/
def card (V : Nat) (s : VSet) : Nat := (members V s).length

/-- s ⊆ t within ℕ_V. -/
def Subset (V : Nat) (s t : VSet) : Prop := ∀ i, i < V → s i = true → t i = true

/-- `Subset`, decided. -/
def subsetB (V : Nat) (s t : VSet) : Bool := (List.range V).all fun i => !s i || t i

/-- s = ∅ within ℕ_V. -/
def isEmptyB (V : Nat) (s : VSet) : Bool := (List.range V).all fun i => !s i

/-- s \ t. -/
def sdiff (s t : VSet) : VSet := fun i => s i && !t i

end VSet

/-! ## The reports to audit (§17.3) -/

/-- **q** ∈ ⟦𝕎?⟧_{|κ|/3} (GP §17.3 eq. `auditselection`): for each active core c, the report of ρ[c]
    when it is in **R** (the reports that just became available, compared by encoding), ∅ otherwise. -/
def auditReports (V : Nat) (ρ : AvailAssignments) (R : List WorkReport) : List (Option WorkReport) :=
  (List.range (V / 3)).map fun c =>
    match ρ.getD c none with
    | some a => if R.any (·.encode == a.guarantee.report.encode) then some a.guarantee.report else none
    | none => none

/-! ## Tranche 0 (§17.3) -/

/-- The context of s₀, X_U ⌢ Y(H_V) (GP §17.3 eq. `initialaudit`). -/
def initialContext (crypto : Crypto) (vrfSig : List UInt8) : List UInt8 :=
  Xaudit ++ crypto.bsOut vrfSig

/-- s₀ ∈ 𝔹^{[]}_{κ_v,b}⟨X_U ⌢ Y(H_V)⟩ (GP §17.3 eq. `initialaudit`; the context is X_U ⌢ Y(H_V) and
    the message is empty, per `\bssignature{key}{context}{message}`): v's tranche-0 evidence
    verifies under its Bandersnatch key. -/
def initialSeedValid (crypto : Crypto) (bsKey vrfSig s0 : List UInt8) : Bool :=
  crypto.bsVerify bsKey (initialContext crypto vrfSig) [] s0

/-- The number of cores tranche 0 draws (GP §17.3, "a verifiably random selection of ten cores"). -/
def tranche0Size : Nat := 10

/-- **a**₀ = {w | w ∈ ℱ(**q**, Y(s₀))_{…+10}, w ≠ ∅} (GP §17.3), as a sequence in shuffle order;
    `y` is Y(s₀). -/
def tranche0 (q : List (Option WorkReport)) (y : List UInt8) : List WorkReport :=
  ((Shuffle.shuffleHash q ⟨y.toArray⟩).take tranche0Size).filterMap id

/-- **a**₀ with each report's core index: the same draw over **q** paired with its indices
    (`JAM.Auditing.tranche0_eq_map_snd` shows the reports agree). -/
def tranche0Indexed (q : List (Option WorkReport)) (y : List UInt8) : List (Nat × WorkReport) :=
  ((Shuffle.shuffleHash (q.zipIdx.map fun (w, c) => (c, w)) ⟨y.toArray⟩).take tranche0Size).filterMap
    fun (c, w) => w.map (c, ·)

/-! ## Tranche timing (§17.3) -/

/-- n = ⌊(𝒯 − 𝖯·H_T)/𝖠⌋ (GP §17.3), with 𝖯 = 6 and 𝖠 = 8 seconds: the tranche current at wall-clock
    time 𝒯 (seconds since the JAM common era) for a block of slot H_T. -/
def currentTranche (wallclock slot : Nat) : Nat :=
  (wallclock - Constants.Cslotseconds * slot) / Constants.Ctrancheseconds

/-! ## Announcements (§17.3) -/

/-- **x**_n = ℰ({ℰ₂(w_c) ⌢ ℋ(w) | w ∈ **a**_n}) (GP §17.3 eq. `announcement`): the set's elements in
    ascending lexicographic order, with no length prefix (Appendix C, set encoding). -/
def announcementItems (a : List WorkReport) : List UInt8 :=
  ((Std.ExtTreeSet.ofList (a.map fun w => fixed 2 w.core ++ reportHash w) : OctetSet).toList).flatten

/-- X_I ⧺ n ⌢ **x**_n ⌢ ℋ(H) (GP §17.3 eq. `announcement`), n as ℰ(n); `headerHash` is ℋ(H). -/
def announcementMessage (n : Nat) (a : List WorkReport) (headerHash : List UInt8) : List UInt8 :=
  Xannounce ++ nat n ++ announcementItems a ++ headerHash

/-- S ≡ 𝔼_{κ_v,e}⟨X_I ⧺ n ⌢ **x**_n ⌢ ℋ(H)⟩ (GP §17.3 eq. `announcement`): an announcement signature
    verifies under v's Ed25519 key. -/
def announcementValid (crypto : Crypto) (edKey : List UInt8) (n : Nat) (a : List WorkReport)
    (headerHash sig : List UInt8) : Bool :=
  crypto.edVerify edKey (announcementMessage n a headerHash) sig

/-! ## The validator's perception (§17.3) -/

/-- What v knows of the other validators (GP §17.3): A_n(w), the validators required to audit w at
    tranche n, from the announcements; J_⊤(w) and J_⊥(w), the validators known to have judged w
    valid and invalid, from any tranche. Reports are keyed by ℋ(w), which is how announcements and
    judgments name them. -/
structure View where
  /-- A_n(w): tranche n ↦ ℋ(w) ↦ validators. -/
  announced : Nat → List UInt8 → VSet
  /-- J_⊤(w). -/
  positive : List UInt8 → VSet
  /-- J_⊥(w). -/
  negative : List UInt8 → VSet

/-! ## Later tranches (§17.3 eq. `latertranches`) -/

/-- The context of s_n(w), X_U ⌢ Y(H_V) ⌢ ℋ(w) ⧺ n (GP §17.3 eq. `latertranches`), n as ℰ(n). -/
def laterContext (crypto : Crypto) (vrfSig : List UInt8) (w : WorkReport) (n : Nat) : List UInt8 :=
  Xaudit ++ crypto.bsOut vrfSig ++ reportHash w ++ nat n

/-- s_n(w) ∈ 𝔹^{[]}_{κ_v,b}⟨X_U ⌢ Y(H_V) ⌢ ℋ(w) ⧺ n⟩ (GP §17.3 eq. `latertranches`). -/
def laterSeedValid (crypto : Crypto) (bsKey vrfSig : List UInt8) (w : WorkReport) (n : Nat)
    (s : List UInt8) : Bool :=
  crypto.bsVerify bsKey (laterContext crypto vrfSig w n) [] s

/-- |A_{n−1}(w) \ J_⊤(w)| (GP §17.3 eq. `latertranches`): the no-shows of tranche n − 1, the
    validators required to audit w then from whom no positive judgment is known. -/
def noShows (V : Nat) (view : View) (n : Nat) (w : WorkReport) : Nat :=
  VSet.card V (VSet.sdiff (view.announced (n - 1) (reportHash w)) (view.positive (reportHash w)))

/-- a_n(w) ≡ |κ|/(65536·𝖥) · ℰ₂⁻¹(Y(s_n(w))_{0…+2}) < m (GP §17.3 eq. `latertranches`), with m the
    no-show count and 𝖥 = 2 (`Cauditbiasfactor`), decided exactly as
    |κ| · ℰ₂⁻¹(…) < 65536 · 𝖥 · m. `y` is Y(s_n(w)). Each validator is drawn with probability about
    𝖥·m/|κ|, so about 𝖥 validators per no-show. -/
def laterSelected (V : Nat) (y : List UInt8) (m : Nat) : Bool :=
  decide (V * PVM.Num.decodeLE (y.take 2) < 65536 * Constants.Cauditbiasfactor * m)

/-- **a**_n ≡ {w | w ∈ **q**, w ≠ ∅, a_n(w)} for n > 0 (GP §17.3 eq. `latertranches`); `y w` is
    Y(s_n(w)). -/
def laterTranche (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport))
    (y : WorkReport → List UInt8) : List WorkReport :=
  (q.filterMap id).filter fun w => laterSelected V (y w) (noShows V view n w)

/-- **a**_n with the prose rule of §17.3 added: a report with a known negative judgment is always
    audited ("In the first case, the validator is always required to issue a judgment"). Not in eq.
    `latertranches`; see reading 4 in the module docstring. -/
def laterTrancheWithNegatives (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport))
    (y : WorkReport → List UInt8) : List WorkReport :=
  (q.filterMap id).filter fun w =>
    !VSet.isEmptyB V (view.negative (reportHash w)) || laterSelected V (y w) (noShows V view n w)

/-- **a**_n for any tranche (GP §17.3): **a**₀ from Y(s₀) when n = 0, eq. `latertranches` otherwise. -/
def tranche (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport)) (y0 : List UInt8)
    (y : WorkReport → List UInt8) : List WorkReport :=
  if n = 0 then tranche0 q y0 else laterTranche V view n q y

/-! ## Judgments (§17.3 eq. `judgments`) -/

/-- X_{e_n(w)} ⌢ ℋ(w) (GP §17.3 eq. `judgments`), with X_⊤ = `$jam_valid`, X_⊥ = `$jam_invalid`:
    the message of a judgment on w whose evaluation gave `valid`. It is the message §10's verdicts
    check (`JAM.checkVerdict`), so a judgment serves directly as a verdict vote. -/
def judgmentMessage (valid : Bool) (w : WorkReport) : List UInt8 :=
  Xvalidif valid ++ reportHash w

/-- A judgment signature 𝒮̄_{κ_v,e}(X_{e_n(w)} ⌢ ℋ(w)) verifies under v's Ed25519 key (GP §17.3 eq.
    `judgments`). -/
def judgmentValid (crypto : Crypto) (edKey : List UInt8) (valid : Bool) (w : WorkReport)
    (sig : List UInt8) : Bool :=
  crypto.edVerify edKey (judgmentMessage valid w) sig

/-! ## The audited conditions (§17.3) -/

/-- U(w) ⇔ (J_⊥(w) = ∅ ∧ ∃ n : A_n(w) ⊆ J_⊤(w)) ∨ |J_⊤(w)| > ⅔|κ| (GP §17.3), with n bounded by the
    current tranche (reading 1 of the module docstring); `h` is ℋ(w). -/
def Audited (V : Nat) (view : View) (current : Nat) (h : List UInt8) : Prop :=
  (VSet.isEmptyB V (view.negative h) = true ∧
    ∃ n, n ≤ current ∧ VSet.Subset V (view.announced n h) (view.positive h)) ∨
  3 * VSet.card V (view.positive h) > 2 * V

/-- U(w) as the paper writes it, with n unbounded (see `auditedLiteral_degenerate`). -/
def AuditedLiteral (V : Nat) (view : View) (h : List UInt8) : Prop :=
  (VSet.isEmptyB V (view.negative h) = true ∧
    ∃ n, VSet.Subset V (view.announced n h) (view.positive h)) ∨
  3 * VSet.card V (view.positive h) > 2 * V

/-- U(w), decided (`JAM.Auditing.audited_iff` shows it decides `Audited`). -/
def audited (V : Nat) (view : View) (current : Nat) (h : List UInt8) : Bool :=
  (VSet.isEmptyB V (view.negative h) &&
    (List.range (current + 1)).any fun n => VSet.subsetB V (view.announced n h) (view.positive h)) ||
  decide (3 * VSet.card V (view.positive h) > 2 * V)

/-- **U** ⇔ ∀ w ∈ **R** : U(w) (GP §17.3): the block is audited when every report that became
    available in it is. -/
def blockAudited (V : Nat) (view : View) (current : Nat) (R : List WorkReport) : Bool :=
  R.all fun w => audited V view current (reportHash w)

/-- A report at least ⅓ of the validators are known to judge invalid (GP §17.3, best-block
    paragraph): chains that accumulate it are disregarded. 3·|J_⊥(w)| ≥ |κ| (reading 5). -/
def disregarded (V : Nat) (view : View) (h : List UInt8) : Bool :=
  decide (3 * VSet.card V (view.negative h) ≥ V)

/-! ## Verdicts from observed judgments (§17.3 → §10) -/

/-- A verdict a block author can form from its observed judgments on w (GP §17.3, last paragraph;
    §10.2 eq. `verdicts`): ⌊⅔|κ|⌋ + 1 votes, ascending by validator index, each backed by a known
    judgment, giving a defined V(a, **j**). Tries good (all positive), then bad (all negative), then
    wonky (⌊|κ|/3⌋ positive and the rest negative, from validators not counted as positive); the
    paper fixes no preference. `sig i b` supplies the signature of validator i's judgment b. The
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
