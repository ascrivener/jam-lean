import JAM.Auditing
import JAM.Theorems.Auditing
import Tests.GuaranteeTest

/-!
# Auditing scenarios (`lake build Tests.AuditingTest`)

Hand-built scenarios for GP v0.8.1 §17 (`JAM.Auditing`): small validator sets, crafted VRF outputs
through a test oracle, checking the reports to audit **q**, tranche-0 selection, tranche timing,
announcements, later-tranche selection and no-show escalation, the audited condition U, the
disregard rule and verdict formation. There are no test vectors for §17; every expected value here is
worked out by hand from the equations. Each `#guard` is evaluated when the file is elaborated, so
building the module runs the tests.

The oracle (`oracle`): a Bandersnatch "signature" is `out ++ key ++ context` with `out` the 32-octet
VRF output it claims, valid when the message is empty and the rest matches; an Ed25519 "signature"
is `key ++ message`. So the tests choose VRF outputs freely and still see every check bite.
-/

namespace JAM.Tests.Auditing

open JAM JAM.Auditing

/-- The test crypto oracle described in the module docstring. -/
def oracle : Crypto where
  edVerify key msg sig := sig == key ++ msg
  bsVerify key ctx msg sig := msg.isEmpty && sig.drop 32 == key ++ ctx
  bsOut sig := sig.take 32

/-- A Bandersnatch signature by `key` on `ctx` with VRF output `out` (32 octets), under `oracle`. -/
def bsSign (out key ctx : List UInt8) : List UInt8 := out ++ key ++ ctx

/-- A 32-octet VRF output starting with the given octets, zero-padded. -/
def vrfOut (pre : List UInt8) : List UInt8 := pre ++ List.replicate (32 - pre.length) 0

def zeroHash : Hash := ⟨(List.replicate 32 (0 : UInt8)).toArray⟩

/-- A work report on core `c`, distinguished by `tag`. -/
def report (c : Nat) (tag : Nat := 0) : WorkReport where
  spec := { packageHash := ⟨(List.replicate 32 (UInt8.ofNat tag)).toArray⟩, bundleLength := 0,
            erasureRoot := zeroHash, erasureShards := 0, segmentRoot := zeroHash, segmentCount := 0 }
  context := { anchorHash := zeroHash, anchorSlot := 0, anchorStateRoot := zeroHash,
               anchorAccOutLog := zeroHash, lookupAnchorHash := zeroHash, lookupAnchorSlot := 0,
               lookupAnchorStateRoot := zeroHash }
  core := c
  authorizerHash := zeroHash
  authGasUsed := 0
  authTrace := .empty
  digests := []

def assign (w : WorkReport) : Option AvailAssignment :=
  some { guarantee := { report := w, slot := 0, credential := [] }, time := 0 }

def sameReports (a b : List WorkReport) : Bool := a.map (·.encode) == b.map (·.encode)

def sameOpt (a b : List (Option WorkReport)) : Bool :=
  a.map (·.map (·.encode)) == b.map (·.map (·.encode))

/-! ## **q** (eq. `auditselection`) -/

-- 9 validators, so 3 active cores. Cores 0, 1 and 2 are engaged; the reports of cores 0 and 2
-- became available, core 1's did not. ρ's extra entry (core 3) is beyond |κ|/3 and is not read.
def w0 := report 0
def w1 := report 1
def w2 := report 2
def ρ9 : AvailAssignments := [assign w0, assign w1, assign w2, assign (report 3)]
def q9 := auditReports 9 ρ9 [w0, w2, report 3]

#guard sameOpt q9 [some w0, none, some w2]
#guard q9.length = 3
-- a report in **R** that ρ no longer holds is not audited
#guard sameOpt (auditReports 9 [none, assign w1, none] [w0]) [none, none, none]

/-! ## Tranche 0 (eq. `initialaudit`) -/

def bsKey : List UInt8 := List.replicate 32 7
def edKey : List UInt8 := List.replicate 32 9
def hv : List UInt8 := bsSign (vrfOut [42]) (List.replicate 32 1) []   -- H_V, any signature
def y0 : List UInt8 := vrfOut [3, 1, 4, 1, 5]
def s0 : List UInt8 := bsSign y0 bsKey (initialContext oracle hv)

#guard initialSeedValid oracle bsKey hv s0
#guard oracle.bsOut s0 = y0
-- the wrong key, or a context without Y(H_V), fails
#guard !initialSeedValid oracle (List.replicate 32 8) hv s0
#guard !initialSeedValid oracle bsKey hv (bsSign y0 bsKey Xaudit)
#guard initialContext oracle hv = "jam_audit".toUTF8.toList ++ vrfOut [42]

-- With 3 cores every non-empty item is within the first ten: **a**₀ = both available reports.
#guard (tranche0 q9 y0).length = 2
#guard (tranche0 q9 y0).all fun w => w.core == 0 || w.core == 2
#guard ((tranche0Indexed q9 y0).map Prod.fst).toArray.qsort (· < ·) = #[0, 2]
-- **a**₀ is ℱ(**q**, Y(s₀)) cut to ten, empties dropped
#guard sameReports (tranche0 q9 y0) (((Shuffle.shuffleHash q9 ⟨y0.toArray⟩).take 10).filterMap id)

-- 60 validators, 20 cores all with an available report: exactly ten distinct cores are drawn,
-- and each drawn core's report is **q**'s.
def ws20 := (List.range 20).map (report ·)
def q20 := auditReports 60 (ws20.map assign) ws20
#guard q20.length = 20
#guard (tranche0 q20 y0).length = 10
#guard ((tranche0Indexed q20 y0).map Prod.fst).eraseDups.length = 10
#guard (tranche0Indexed q20 y0).all fun (c, w) => w.core == c
-- a different VRF output draws a different set
#guard ((tranche0Indexed q20 y0).map Prod.fst) != ((tranche0Indexed q20 (vrfOut [9])).map Prod.fst)
-- 20 cores, only cores 0..4 available: at most those five
def q20sparse := auditReports 60 (ws20.map assign) (ws20.take 5)
#guard (tranche0 q20sparse y0).length ≤ 5
#guard (tranche0 q20sparse y0).all fun w => w.core < 5

/-! ## Tranche timing (𝖠 = 8 s, 𝖯 = 6 s) -/

-- slot 10 starts at 60 s
#guard currentTranche 60 10 = 0
#guard currentTranche 67 10 = 0
#guard currentTranche 68 10 = 1
#guard currentTranche 100 10 = 5
#guard currentTranche 50 10 = 0     -- before the slot: natural subtraction (reading 8)

/-! ## Announcements (eq. `announcement`) -/

def hdr : List UInt8 := List.replicate 32 5   -- ℋ(H)

#guard announcementMessage 0 [w0] hdr =
  "jam_announce".toUTF8.toList ++ [0] ++ [0, 0] ++ reportHash w0 ++ hdr
-- the set is in lexicographic order of ℰ₂(c) ⌢ ℋ(w): core 256 ([0,1]) before core 1 ([1,0])
#guard announcementItems [report 1, report 256] =
  ([0, 1] ++ reportHash (report 256)) ++ ([1, 0] ++ reportHash (report 1))
#guard announcementItems [report 1, report 256] = announcementItems [report 256, report 1]
#guard announcementItems [w0, w0] = announcementItems [w0]
#guard (announcementItems []).isEmpty
-- n as one octet (x ⧺ i ≡ x ⌢ [i]); mod 2^8 from 256 (reading 2)
#guard announcementMessage 127 [] hdr = Xannounce ++ [127] ++ hdr
#guard announcementMessage 128 [] hdr = Xannounce ++ [128] ++ hdr
#guard announcementMessage 255 [] hdr = Xannounce ++ [255] ++ hdr
#guard announcementMessage 257 [] hdr = Xannounce ++ [1] ++ hdr
#guard announcementValid oracle edKey 0 (tranche0 q9 y0) hdr
  (edKey ++ announcementMessage 0 (tranche0 q9 y0) hdr)
#guard !announcementValid oracle edKey 1 (tranche0 q9 y0) hdr
  (edKey ++ announcementMessage 0 (tranche0 q9 y0) hdr)

/-! ## Later tranches and no-show escalation (eq. `latertranches`) -/

def h0 := reportHash w0
def h2 := reportHash w2

/-- A view: tranche 0 announced validators 1, 2, 3 for w0 and 4 for w2; tranche 1 announced 5 for
    w0. `pos` and `neg` give J_⊤ and J_⊥ of w0; w2 has a positive judgment from 4. -/
def view (pos neg : List Nat) (negW2 : List Nat := []) : View where
  announced n h :=
    if n = 0 && h == h0 then VSet.ofList [1, 2, 3]
    else if n = 0 && h == h2 then VSet.ofList [4]
    else if n = 1 && h == h0 then VSet.ofList [5]
    else VSet.empty
  positive h := if h == h0 then VSet.ofList pos else if h == h2 then VSet.ofList [4] else VSet.empty
  negative h := if h == h0 then VSet.ofList neg else if h == h2 then VSet.ofList negW2 else VSet.empty

-- J_⊤(w0) = {1}: validators 2 and 3 are no-shows of tranche 0; w2 has none
#guard noShows 9 (view [1] []) 1 w0 = 2
#guard noShows 9 (view [1] []) 1 w2 = 0
#guard noShows 9 (view [1, 2, 3] []) 1 w0 = 0

-- a_n: |κ| · ℰ₂⁻¹(Y_{0..2}) < 65536 · 𝖥 · m. With |κ| = 9, m = 2: 9·d < 262144, so d ≤ 29127.
#guard laterSelected 9 (vrfOut [0xC7, 0x71]) 2           -- d = 29127
#guard !laterSelected 9 (vrfOut [0xC8, 0x71]) 2          -- d = 29128
#guard !laterSelected 9 (vrfOut [0, 0]) 0                -- no no-shows: never
#guard laterSelected 9 (vrfOut [0xFF, 0xFF]) 9           -- 9 no-shows of 9: always (9·65535 < 65536·18)
-- the octets after the first two do not matter
#guard laterSelected 9 (vrfOut [0xC7, 0x71, 0xFF]) 2

-- Tranche 1, VRF outputs per report: w0 draws d = 100, w2 draws d = 0.
def y1 (w : WorkReport) : List UInt8 := if w.core == 0 then vrfOut [100] else vrfOut [0]

-- two no-shows on w0: w0 escalates; w2 had none, so not even d = 0 selects it
#guard sameReports (laterTranche 9 (view [1] []) 1 q9 y1) [w0]
-- every announced auditor judged: no escalation
#guard (laterTranche 9 (view [1, 2, 3] []) 1 q9 y1).isEmpty
-- a large draw on w0 misses even with two no-shows
#guard (laterTranche 9 (view [1] []) 1 q9 fun _ => vrfOut [0xFF, 0xFF]).isEmpty
-- tranche 2 looks at tranche 1's announcements: validator 5 on w0, a no-show unless 5 judged
#guard noShows 9 (view [1] []) 2 w0 = 1
#guard noShows 9 (view [1, 5] []) 2 w0 = 0
-- the prose rule: a negative judgment on w2 makes it audited in any later tranche
#guard sameReports (laterTrancheWithNegatives 9 (view [1, 2, 3] [] [6]) 1 q9 y1) [w2]
#guard (laterTranche 9 (view [1, 2, 3] [] [6]) 1 q9 y1).isEmpty
-- `tranche` dispatches on n
#guard sameReports (tranche 9 (view [1] []) 0 q9 y0 y1) (tranche0 q9 y0)
#guard sameReports (tranche 9 (view [1] []) 1 q9 y0 y1) [w0]

-- s_n(w)'s context is X_U ⌢ Y(H_V) ⌢ ℋ(w) ⧺ n
#guard laterContext oracle hv w0 1 = Xaudit ++ vrfOut [42] ++ h0 ++ [1]
#guard laterContext oracle hv w0 200 = Xaudit ++ vrfOut [42] ++ h0 ++ [200]
#guard laterContext oracle hv w0 300 = Xaudit ++ vrfOut [42] ++ h0 ++ [44]
#guard laterSeedValid oracle bsKey hv w0 1 (bsSign (vrfOut [100]) bsKey (laterContext oracle hv w0 1))
#guard !laterSeedValid oracle bsKey hv w0 2 (bsSign (vrfOut [100]) bsKey (laterContext oracle hv w0 1))
#guard !laterSeedValid oracle bsKey hv w2 1 (bsSign (vrfOut [100]) bsKey (laterContext oracle hv w0 1))

/-! ## Judgments (eq. `judgments`) -/

#guard judgmentMessage true w0 = "jam_valid".toUTF8.toList ++ h0
#guard judgmentMessage false w0 = "jam_invalid".toUTF8.toList ++ h0
#guard judgmentValid oracle edKey true w0 (edKey ++ judgmentMessage true w0)
#guard !judgmentValid oracle edKey false w0 (edKey ++ judgmentMessage true w0)

/-! ## The audited condition U and **U** -/

-- all tranche-0 auditors of w0 judged positively: audited from tranche 0
#guard audited 9 (view [1, 2, 3] []) 0 h0
-- a no-show (validators 2, 3): not audited in tranche 0 …
#guard !audited 9 (view [1, 4] []) 0 h0
-- … but tranche 1's announced auditor (5) judged positively: audited once tranche 1 is current
#guard !audited 9 (view [1, 5] []) 0 h0
#guard audited 9 (view [1, 5] []) 1 h0
-- one negative judgment blocks it …
#guard !audited 9 (view [1, 2, 3] [6]) 0 h0
#guard !audited 9 (view [1, 2, 3, 5] [6]) 3 h0
-- … unless more than ⅔ of the 9 (so at least 7) judge positively
#guard !audited 9 (view [0, 1, 2, 3, 4, 5] [6]) 0 h0
#guard audited 9 (view [0, 1, 2, 3, 4, 5, 7] [6]) 0 h0
-- a validator outside ℕ_|κ| is not counted
#guard !audited 9 (view [0, 1, 2, 3, 4, 5, 100] [6]) 0 h0
-- reading 1: tranche 2 has nobody announced for w0, so once it is current w0 is audited with
-- the no-shows of tranche 0 still outstanding
#guard audited 9 (view [1] []) 2 h0

#guard blockAudited 9 (view [1, 2, 3] []) 0 [w0, w2]
#guard !blockAudited 9 (view [1] []) 0 [w0, w2]
#guard blockAudited 9 (view [1] []) 0 [w2]
#guard blockAudited 9 (view [1] []) 0 []

-- at least ⅓ negative: disregard (reading 5)
#guard disregarded 9 (view [] [1, 2, 3]) h0
#guard !disregarded 9 (view [] [1, 2]) h0

/-! ## Verdicts (§17.3 → §10) -/

def sig (w : WorkReport) (i : Nat) (b : Bool) : Blob :=
  ⟨(List.replicate 32 (UInt8.ofNat i) ++ judgmentMessage b w).toArray⟩

def outcomeOf : Option (Outcome × List Judgment) → Option Outcome
  | some (o, _) => some o
  | none => none

-- 9 validators: a verdict has ⌊2·9/3⌋ + 1 = 7 votes
#guard outcomeOf (formVerdict 9 (VSet.ofList [0, 1, 2, 3, 4, 5, 6, 7]) VSet.empty (sig w0)) == some .good
#guard outcomeOf (formVerdict 9 VSet.empty (VSet.ofList [0, 1, 2, 3, 4, 5, 6]) (sig w0)) == some .bad
#guard outcomeOf (formVerdict 9 (VSet.ofList [0, 1, 2]) (VSet.ofList [3, 4, 5, 6, 7]) (sig w0)) == some .wonky
-- a validator who judged both ways counts once in a wonky verdict
#guard (formVerdict 9 (VSet.ofList [0, 1, 2]) (VSet.ofList [2, 3, 4, 5]) (sig w0)).isNone
#guard outcomeOf (formVerdict 9 (VSet.ofList [0, 1, 2]) (VSet.ofList [2, 3, 4, 5, 6]) (sig w0)) == some .wonky
#guard (formVerdict 9 (VSet.ofList [0, 1]) (VSet.ofList [3, 4]) (sig w0)).isNone
#guard (formVerdict 9 (VSet.ofList [0, 1, 2]) (VSet.ofList [3, 4, 5, 6, 7]) (sig w0)).all fun (_, js) =>
  js.map (fun j => (j.index, j.valid)) ==
    [(0, true), (1, true), (2, true), (3, false), (4, false), (5, false), (6, false)]

-- End to end: the votes `formVerdict` builds from auditing judgments pass §10's verdict check
-- (`JAM.checkVerdict`, outcome from `JAM.verdicts`) under the oracle, with key [i, i, …, i] (32 octets) for validator i.
def edKeys9 : List (List UInt8) := (List.range 9).map fun i => List.replicate 32 (UInt8.ofNat i)
def disputesIn : DisputesInput := { slot := 0, activeEd := edKeys9, previousEd := edKeys9 }

def verdictFor (w : WorkReport) (pos neg : List Nat) : Option Verdict :=
  (formVerdict 9 (VSet.ofList pos) (VSet.ofList neg) (sig w)).map fun (_, js) =>
    { target := ⟨(reportHash w).toArray⟩, age := 0, votes := js }

def checks (w : WorkReport) (pos neg : List Nat) : Option Outcome :=
  match verdictFor w pos neg with
  | some v => match checkVerdict Params.tiny oracle disputesIn {} v with
    | .ok () => (verdicts Params.tiny disputesIn [v]).bind fun vs => vs.head?.map (·.2)
    | .error _ => none
  | none => none

#guard checks w0 [0, 1, 2, 3, 4, 5, 6] [] == some .good
#guard checks w0 [] [0, 1, 2, 3, 4, 5, 6, 7, 8] == some .bad
#guard checks w0 [6, 7, 8] [0, 1, 2, 3] == some .wonky
-- a judgment signed for another report fails §10's signature check
#guard (match (verdictFor w0 [0, 1, 2, 3, 4, 5, 6] []) with
  | some v => (checkVerdict Params.tiny oracle disputesIn {} { v with target := ⟨h2.toArray⟩ }).isOk
  | none => true) = false

/-! ## Evaluation (eq. 17.16), with the Ξ fixtures of `Tests.GuaranteeTest` -/

namespace Ev
open JAM.Tests.Guarantee (accts pkgE pkg32)
open JAM.Tests.Refine (echo exportThenHalt)

/-- `pkgE e` with 32-octet context hashes, so that its bundle decodes. -/
def pkgD (e : Nat) : WorkPackage := { pkgE e with context := pkg32.context }

/-- C(r): the bundle of `pkgD 0`, which imports and carries nothing. -/
def bundle0 : List UInt8 := Guarantee.bundle (pkgD 0) [⟨[], [], []⟩]

/-- Ξ(p, 1, ∅, 6) for `pkgD e` with refine code `code`. -/
def xiD (code : List UInt8) (e : Nat) : Option WorkReport :=
  Guarantee.computeReport .tiny (accts code) (pkgD e) 1 ∅ 6 [⟨[], [], []⟩]

-- the report Ξ gives for the package evaluates as valid
#guard match xiD echo 0 with
  | some r => evaluation .tiny (accts echo) bundle0 r
  | none => false
-- the same report claiming another core, or another number of shards: invalid
#guard match xiD echo 0 with
  | some r => !evaluation .tiny (accts echo) bundle0 { r with core := 0 } &&
      !evaluation .tiny (accts echo) bundle0 { r with spec := { r.spec with erasureShards := 9 } }
  | none => false
-- a report for a different package (another export count): invalid
#guard match xiD exportThenHalt 1 with
  | some r => !evaluation .tiny (accts exportThenHalt) bundle0 r
  | none => false
-- a bundle with a trailing octet, or truncated: invalid
#guard match xiD echo 0 with
  | some r => !evaluation .tiny (accts echo) (bundle0 ++ [0]) r &&
      !evaluation .tiny (accts echo) bundle0.dropLast r
  | none => false
-- other accounts, so that Ξ gives ∇ (no authorizer code): invalid
#guard match xiD echo 0 with
  | some r => !evaluation .tiny ∅ bundle0 r
  | none => false

end Ev

end JAM.Tests.Auditing
