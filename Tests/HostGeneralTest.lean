import JAM

/-!
# Hand-written tests of the general host functions

Each `#guard` checks one case of a function's definition in GP v0.8.1 Appendix B. These functions
are also exercised end to end by the accumulate vectors once Ψ_A exists.
-/

namespace JAM.Tests.HostGeneral

open PVM JAM

/-- A memory with pages 32 and 33 writable (addresses 0x20000–0x21fff), page 34 read-only. -/
def mem0 : Memory :=
  (Memory.empty.setPages 32 2 (some .write)).setPages 34 1 (some .read)

def base : Nat := 0x20000

def regs (vals : List (Nat × Nat)) : Regs :=
  vals.foldl (fun ω (k, v) => if h : k < 13 then ω.set k (UInt64.ofNat v) else ω) (Vector.replicate 13 0)

def acct : ServiceAccount := { codeHash := List.replicate 32 7, balance := 10000, minAccGas := 5, minMemoGas := 6 }

def r7 {X} (o : HostOut X) : Nat := (o.regs.get 7).toNat

/-! ### gas -/
-- ω'_7 = ϱ − 𝖬_G
#guard r7 (hostGas (X := Unit) 1000 (regs []) mem0 ()) == 1000 - Constants.CgasG
#guard (hostGas (X := Unit) 1000 (regs []) mem0 ()).gas == 1000 - Constants.CgasG
-- out of gas: ∞, all gas consumed (ϱ* = 0, GP v0.8.1 #533; v0.8.0 gave ϱ − g < 0), registers unchanged
#guard (hostGas (X := Unit) 10 (regs [(7, 99)]) mem0 ()).status == .oog
#guard (hostGas (X := Unit) 10 (regs [(7, 99)]) mem0 ()).gas == 0
#guard r7 (hostGas (X := Unit) 10 (regs [(7, 99)]) mem0 ()) == 99

/-! ### grow_heap under the v0.8.1 common rules (#533) -/
-- With an unparsable blob the heap starts at page a = 32; pages 32 and 33 are W, so h = 34.
-- A request that does not grow (ω_7 ≤ h) sets ω'_7 = h and charges 𝖬_{♊,c} ...
#guard (hostGrowHeap (X := Unit) 1000 (regs [(7, 0)]) mem0 ByteArray.empty ()).status == .cont
#guard r7 (hostGrowHeap (X := Unit) 1000 (regs [(7, 0)]) mem0 ByteArray.empty ()) == 34
#guard (hostGrowHeap (X := Unit) 1000 (regs [(7, 0)]) mem0 ByteArray.empty ()).gas ==
  1000 - Constants.CgasGeminiconst
-- ... and since v0.8.1 it runs out of gas like any other call if ϱ < 𝖬_{♊,c}: ∞, ϱ* = 0, ω unchanged.
-- (v0.8.0 continued with ϱ − 𝖬_{♊,c} < 0 and ω'_7 = h.)
#guard (hostGrowHeap (X := Unit) 10 (regs [(7, 0)]) mem0 ByteArray.empty ()).status == .oog
#guard (hostGrowHeap (X := Unit) 10 (regs [(7, 0)]) mem0 ByteArray.empty ()).gas == 0
#guard r7 (hostGrowHeap (X := Unit) 10 (regs [(7, 0)]) mem0 ByteArray.empty ()) == 0
-- Growing to page 36 charges 𝖬_{♊,c} + 2·𝖬_{♊,p} and makes pages 34 and 35 writable.
#guard r7 (hostGrowHeap (X := Unit) 100000 (regs [(7, 36)]) mem0 ByteArray.empty ()) == 36
#guard (hostGrowHeap (X := Unit) 100000 (regs [(7, 36)]) mem0 ByteArray.empty ()).gas ==
  100000 - (Constants.CgasGeminiconst + 2 * Constants.CgasGeminilinear)
#guard (hostGrowHeap (X := Unit) 100000 (regs [(7, 36)]) mem0 ByteArray.empty ()).mem.writable (35 * 4096)
-- Out of gas while growing: ∞, ϱ* = 0, nothing made writable.
#guard (hostGrowHeap (X := Unit) 300 (regs [(7, 36)]) mem0 ByteArray.empty ()).status == .oog
#guard (hostGrowHeap (X := Unit) 300 (regs [(7, 36)]) mem0 ByteArray.empty ()).gas == 0
#guard !(hostGrowHeap (X := Unit) 300 (regs [(7, 36)]) mem0 ByteArray.empty ()).mem.writable (35 * 4096)

/-! ### write and read -/

/-! ### write (an accumulate function in GP v0.8.1) and read -/

/-- Key "k1" at `base`, value "hello" at `base + 16`. -/
def memKV : Memory := (mem0.writeN base "k1".toUTF8.toList).writeN (base + 16) "hello".toUTF8.toList

/-- Accumulation context of service 9 with account `a`, and `others` beside it. -/
def ctxOf (a : ServiceAccount) (others : List (Nat × ServiceAccount) := []) : AccCtx :=
  let x : Implications :=
    { id := 9, nextFree := 0,
      state := { accounts := Std.ExtTreeMap.ofList ((9, a) :: others), staging := [], authQueue := [],
                 manager := 0, assigners := [], delegator := 0, registrar := 0, alwaysAcc := ∅ } }
  (x, x)

/-- The account of service `s` in the regular dimension. -/
def acctOf (o : HostOut AccCtx) (s : Nat := 9) : ServiceAccount := o.ctx.1.state.accounts.getD s default

/-- write to service ω_7 (2^64 − 1: the caller) the key at `base` (2 octets), value at `base + 16`. -/
def writeRegs (vZ : Nat) (d : Nat := 2 ^ 64 - 1) : Regs :=
  regs [(7, d), (8, base), (9, 2), (10, base + 16), (11, vZ)]
def w1 := AccHost.write 100000 (writeRegs 5) memKV (ctxOf acct)

-- a fresh key: ω'_7 = NONE, the storage holds the value, and service 9 is marked modified
#guard w1.status == .cont && r7 w1 == Result.NONE
#guard (acctOf w1).storageGet "k1".toUTF8.toList == some "hello".toUTF8.toList
#guard w1.ctx.1.modified.contains 9
-- a_i and a_o follow GP eq. `deposits`: one item, 34 + |k| + |v| octets
#guard (acctOf w1).items == 1 && (acctOf w1).octets == 34 + 2 + 5
-- overwriting returns the previous length
#guard r7 (AccHost.write 100000 (writeRegs 3) memKV w1.ctx) == 5
-- v_Z = 0 deletes
#guard (acctOf (AccHost.write 100000 (writeRegs 0) memKV w1.ctx)).storageGet "k1".toUTF8.toList == none
#guard (acctOf (AccHost.write 100000 (writeRegs 0) memKV w1.ctx)).items == 0 &&
  (acctOf (AccHost.write 100000 (writeRegs 0) memKV w1.ctx)).octets == 0
-- overwriting replaces the old value's octets: 34 + 2 + 3
#guard (acctOf (AccHost.write 100000 (writeRegs 3) memKV w1.ctx)).items == 1 &&
  (acctOf (AccHost.write 100000 (writeRegs 3) memKV w1.ctx)).octets == 34 + 2 + 3
-- below the threshold balance (b + b' < t): FULL and the account is unchanged
#guard r7 (AccHost.write 100000 (writeRegs 5) memKV (ctxOf { acct with balance := 0 })) == Result.FULL
#guard (acctOf (AccHost.write 100000 (writeRegs 5) memKV (ctxOf { acct with balance := 0 }))).entries.size == 0
-- the supervisor balance counts towards the threshold (GP v0.8.1)
#guard r7 (AccHost.write 100000 (writeRegs 5) memKV (ctxOf { acct with balance := 0, supervisorBalance := 10000 })) ==
  Result.NONE
-- an unreadable key panics
#guard (AccHost.write 100000 (regs [(7, 2 ^ 64 - 1), (8, 0x10), (9, 2)]) memKV (ctxOf acct)).status == .panic
-- another service: WHO if it does not exist; HUH unless the caller is it or its effective supervisor
#guard r7 (AccHost.write 100000 (writeRegs 5 4) memKV (ctxOf acct)) == Result.WHO
#guard r7 (AccHost.write 100000 (writeRegs 5 4) memKV (ctxOf acct [(4, acct)])) == Result.HUH
#guard r7 (AccHost.write 100000 (writeRegs 5 4) memKV
  (ctxOf acct [(4, { acct with supervisor := 9, supervisorCreated := 0 })])) == Result.NONE
-- a supervisor recorded with the wrong creation slot is not effective
#guard r7 (AccHost.write 100000 (writeRegs 5 4) memKV
  (ctxOf acct [(4, { acct with supervisor := 9, supervisorCreated := 1 })])) == Result.HUH
-- write gas: 𝖬_{W,c} + 𝔊(𝖬_{W,k,ℓ}, 2) + 𝔊(𝖬_{W,v,ℓ}, 5)
#guard w1.gas == 100000 - (Constants.CgasWconst + memGas Constants.CgasWkeylinear 2 +
  memGas Constants.CgasWvallinear 5 : Nat)

/-- read the key at `base` from the own account (ω_7 = 2^64 − 1) into `base + 0x100`. -/
def readRegs (f z : Nat) : Regs := regs [(7, 2 ^ 64 - 1), (8, base), (9, 2), (10, base + 0x100), (11, f), (12, z)]
def rd := hostRead (X := Unit) 100000 (readRegs 0 5) memKV (acctOf w1) ∅ ()

#guard r7 rd == 5 && rd.mem.readN (base + 0x100) 5 == "hello".toUTF8.toList
-- offset and length: f = 1, l = 2 → "el"; ω'_7 is still the full length
#guard (hostRead (X := Unit) 100000 (readRegs 1 2) memKV (acctOf w1) ∅ ()).mem.readN (base + 0x100) 3 ==
  "el".toUTF8.toList ++ [0]
-- a missing key: NONE
#guard r7 (hostRead (X := Unit) 100000 (readRegs 0 5) memKV acct ∅ ()) == Result.NONE
-- writing the output into a read-only page panics
#guard (hostRead (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, 2), (10, 34 * 4096), (12, 5)])
  memKV (acctOf w1) ∅ ()).status == .panic
-- another service's storage, through the accounts dictionary
#guard r7 (hostRead (X := Unit) 100000 (regs [(7, 4), (8, base), (9, 2), (10, base + 0x100), (12, 5)])
  memKV acct (Std.ExtTreeMap.ofList [(4, acctOf w1)]) ()) == 5

/-! ### lookup -/

def pre : List UInt8 := "preimage".toUTF8.toList
def h : List UInt8 := (Blake2b.hash256 ⟨pre.toArray⟩).toList
def withPre : ServiceAccount := { acct with preimages := Std.ExtTreeMap.ofList [(h, pre)] }
def memH : Memory := mem0.writeN base h

#guard r7 (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, base + 64), (11, 8)])
  memH withPre ∅ ()) == 8
#guard (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, base + 64), (11, 8)])
  memH withPre ∅ ()).mem.readN (base + 64) 8 == pre
#guard r7 (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, base + 64), (11, 8)])
  memH acct ∅ ()) == Result.NONE
-- the hash must be readable
#guard (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, 0x10), (9, base + 64), (11, 8)])
  memH withPre ∅ ()).status == .panic

/-! ### info -/

-- 32 + 2·4 + 6·8 + 4 + 8 + 3·4 = 112 octets (GP v0.8.1)
#guard (infoValue acct).length == 112
#guard r7 (hostInfo (X := Unit) 100000 (regs [(7, 3), (8, base), (10, 112)]) mem0 acct
  (Std.ExtTreeMap.ofList [(3, acct)]) ()) == 112
#guard r7 (hostInfo (X := Unit) 100000 (regs [(7, 4), (8, base), (10, 112)]) mem0 acct
  (Std.ExtTreeMap.ofList [(3, acct)]) ()) == Result.NONE
-- ω_7 = 2^64 − 1 names the caller's own account
#guard r7 (hostInfo (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (10, 112)]) mem0 acct ∅ ()) == 112

/-! ### fetch -/

-- case 0: the chain parameters, 3·8 + 2 + 2·4 + 4·8 + 4·2 + 4 + 6·2 + 8·4 = 122 octets
#guard (Params.full.encode).length == 122
#guard r7 (hostFetch (X := Unit) 100000 (regs [(7, base), (9, 122), (10, 0)]) mem0 {} ()) == 122
-- an absent item: NONE
#guard r7 (hostFetch (X := Unit) 100000 (regs [(7, base), (9, 32), (10, 1)]) mem0 {} ()) == Result.NONE
-- case 1: the entropy, when provided
#guard (hostFetch (X := Unit) 100000 (regs [(7, base), (9, 32), (10, 1)]) mem0
  { entropy := some (List.replicate 32 9) } ()).mem.readN base 32 == List.replicate 32 9
-- gas for case 0 is 𝖬_{Y,0,c}
#guard (hostFetch (X := Unit) 100000 (regs [(7, base), (9, 122), (10, 0)]) mem0 {} ()).gas ==
  100000 - (Constants.CgasY (some 0)).1

/-! ### accumulate functions with supervisors (GP v0.8.1, #539, #558) -/

def env0 : AccEnv := { params := .tiny, slot := 50, entropy := List.replicate 32 0, inputs := [], code := ⟨#[]⟩ }

/-- Service 4, supervised by 9 (recorded with 9's creation slot 0). -/
def junior : ServiceAccount := { acct with supervisor := 9, supervisorCreated := 0, created := 7 }

-- supervisor: 9 is 4's effective supervisor, so it may hand 4 over to 5 (WHO for an unknown target)
def sv := AccHost.supervisor 100000 (regs [(7, 4), (8, 5)]) mem0 (ctxOf acct [(4, junior), (5, { acct with created := 3 })])
#guard r7 sv == Result.OK && (acctOf sv 4).supervisor == 5 && (acctOf sv 4).supervisorCreated == 3
#guard sv.ctx.1.modified.contains 4
#guard r7 (AccHost.supervisor 100000 (regs [(7, 4), (8, 6)]) mem0 (ctxOf acct [(4, junior)])) == Result.WHO
-- not 4's effective supervisor: HUH
#guard r7 (AccHost.supervisor 100000 (regs [(7, 4), (8, 9)]) mem0 (ctxOf acct [(4, acct)])) == Result.HUH

-- new: the 60 octets c ⌢ ℰ_4(l) ⌢ ℰ_8(g, m, f) at `base`
def newMem (l : Nat) : Memory :=
  mem0.writeN base (List.replicate 32 0xcc ++ Codec.fixed 4 l ++ Codec.fixed 8 1 ++ Codec.fixed 8 2 ++ Codec.fixed 8 0)
def newRegs (mode : Nat) (s : Nat := 2 ^ 64 - 1) : Regs := regs [(7, s), (8, 0), (9, mode), (10, base)]
def rich : ServiceAccount := { acct with balance := 1000000, supervisorBalance := 1000000 }
def n0 := AccHost.new env0 100000 (newRegs 0) (newMem 10) (ctxOf rich)
-- mode 0: paid from the balance into the new account's balance; the new account is supervised by 9
#guard (acctOf n0 (r7 n0)).balance == (acctOf n0 (r7 n0)).minBalance &&
  (acctOf n0 (r7 n0)).supervisorBalance == 0 && (acctOf n0 (r7 n0)).supervisor == 9 &&
  (acctOf n0).balance == 1000000 - (acctOf n0 (r7 n0)).minBalance
-- mode 3: paid from the supervisor balance into the new account's supervisor balance
def n3 := AccHost.new env0 100000 (newRegs 3) (newMem 10) (ctxOf rich)
#guard (acctOf n3 (r7 n3)).balance == 0 &&
  (acctOf n3 (r7 n3)).supervisorBalance == (acctOf n3 (r7 n3)).minBalance &&
  (acctOf n3).supervisorBalance == 1000000 - (acctOf n3 (r7 n3)).minBalance
-- mode 4 and a request length outside ℕ_L = ℕ_{2^32 − 2}: HUH
#guard r7 (AccHost.new env0 100000 (newRegs 4) (newMem 10) (ctxOf rich)) == Result.HUH
#guard r7 (AccHost.new env0 100000 (newRegs 0) (newMem (2 ^ 32 - 2)) (ctxOf rich)) == Result.HUH
-- mode 1 (from the supervisor balance) for a service whose effective supervisor is not the caller: HUH
#guard r7 (AccHost.new env0 100000 (newRegs 1 4) (newMem 10) (ctxOf rich [(4, { rich with supervisor := 4 })])) == Result.HUH

-- transfer with o = 0: an immediate credit; to one's own supervisor balance (mode 2) is allowed
def tRegs (src dst mode amt : Nat) : Regs := regs [(7, src), (8, dst), (9, mode), (10, amt), (11, 0), (12, 0)]
def t2 := AccHost.transfer env0 100000 (tRegs (2 ^ 64 - 1) (2 ^ 64 - 1) 2 100) mem0 (ctxOf rich)
#guard r7 t2 == Result.OK && (acctOf t2).balance == 1000000 - 100 && (acctOf t2).supervisorBalance == 1000000 + 100
-- … but balance to balance (mode 0) of the same service is HUH
#guard r7 (AccHost.transfer env0 100000 (tRegs (2 ^ 64 - 1) (2 ^ 64 - 1) 0 100) mem0 (ctxOf rich)) == Result.HUH
-- an unknown destination: WHO
#guard r7 (AccHost.transfer env0 100000 (tRegs (2 ^ 64 - 1) 77 0 100) mem0 (ctxOf rich)) == Result.WHO

-- eject: only the effective supervisor, of a service with no items not created in this slot
def ej := AccHost.eject env0 100000 (regs [(7, 4)]) mem0 (ctxOf acct [(4, { junior with balance := 5, supervisorBalance := 6 })])
#guard r7 ej == Result.OK && (acctOf ej).balance == acct.balance + 11 && !(ej.ctx.1.state.accounts.contains 4)
#guard r7 (AccHost.eject env0 100000 (regs [(7, 4)]) mem0 (ctxOf acct [(4, { junior with created := 50 })])) == Result.HUH
#guard r7 (AccHost.eject env0 100000 (regs [(7, 4)]) mem0 (ctxOf acct [(4, acct)])) == Result.HUH

-- bless: the delegator (here 9, not the manager 0) hands its role to 5, keeping everything else
def ctxDeleg : AccCtx :=
  let (x, _) := ctxOf acct
  let x := { x with state := { x.state with delegator := 9, assigners := [0, 0] } }
  (x, x)
def bl := AccHost.bless env0 100000 (regs [(7, 2 ^ 64 - 1), (8, 2 ^ 64 - 1), (9, 5), (10, 2 ^ 64 - 1),
  (11, 2 ^ 64 - 1), (12, 0)]) mem0 ctxDeleg
#guard r7 bl == Result.OK && bl.ctx.1.state.delegator == 5 && bl.ctx.1.state.manager == 0
-- … but may not change the manager
#guard r7 (AccHost.bless env0 100000 (regs [(7, 5), (8, 2 ^ 64 - 1), (9, 5), (10, 2 ^ 64 - 1),
  (11, 2 ^ 64 - 1), (12, 0)]) mem0 ctxDeleg) == Result.HUH

/-! ### accumulation with supervisors (GP v0.8.1 eq. `accpar`, `accseq`) -/

def ps0 : PartialState := (ctxOf acct [(4, junior)]).1.state
def outMod (m : List Nat) (g : Nat) : AccOut :=
  ⟨{ ps0 with manager := 77 }, Std.ExtTreeSet.ofList m, [], some [1], g, ∅⟩

-- N: 4's run is discarded when both 4 and its effective supervisor 9 modified 4 (gas use kept)
#guard (discardIfBoth ps0 4 9 (outMod [4] 5) (outMod [4] 6)).state.manager == 0 &&
  (discardIfBoth ps0 4 9 (outMod [4] 5) (outMod [4] 6)).gasUsed == 5 &&
  (discardIfBoth ps0 4 9 (outMod [4] 5) (outMod [4] 6)).yield == none
-- … but kept when the supervisor did not modify 4, or when 4 is its own supervisor
#guard (discardIfBoth ps0 4 9 (outMod [4] 5) (outMod [9] 6)).state.manager == 77
#guard (discardIfBoth ps0 4 4 (outMod [4] 5) (outMod [4] 5)).state.manager == 77

def xfer (dst : Nat) : DeferredTransfer := { source := 1, dest := dst, amount := 1, memo := ⟨#[]⟩, gas := 0 }
-- T: a transfer to 4 waits while 4's effective supervisor 9 accumulates
#guard (partitionXfers [9] ps0.accounts [xfer 4] []).1.length == 0 &&
  (partitionXfers [9] ps0.accounts [xfer 4] []).2.length == 1
-- … goes through otherwise; then a transfer to its junior 4 waits (9 already receives one) …
#guard (partitionXfers [] ps0.accounts [xfer 9, xfer 4] []).1.map (·.dest) == [9] &&
  (partitionXfers [] ps0.accounts [xfer 9, xfer 4] []).2.map (·.dest) == [4]
-- … and so does a transfer to 9 after one to its junior 4
#guard (partitionXfers [] ps0.accounts [xfer 4, xfer 9] []).1.map (·.dest) == [4] &&
  (partitionXfers [] ps0.accounts [xfer 4, xfer 9] []).2.map (·.dest) == [9]

/-! ### transfer: an immediate transfer to the same service counts the credit in **d'** (GP v0.8.1
pvm_invocations.tex:1001–1006, 1021) -/

-- (a) s moves 100 from its balance into its own supervisor balance (x = 2, o = 0) with only 50
-- above its threshold: **d'**[s] = (a_t − 50, 100), b + b' = a_t + 50 ≥ a_t, so OK.
def nearT : ServiceAccount := { acct with balance := acct.minBalance + 50, supervisorBalance := 0 }
def tSelf2 := AccHost.transfer env0 100000 (tRegs (2 ^ 64 - 1) (2 ^ 64 - 1) 2 100) mem0 (ctxOf nearT)
#guard r7 tSelf2 == Result.OK && (acctOf tSelf2).balance == acct.minBalance - 50 &&
  (acctOf tSelf2).supervisorBalance == 100 && tSelf2.ctx.1.modified.contains 9
-- … but not more than its balance: b − 200 < 0, CASH
#guard r7 (AccHost.transfer env0 100000 (tRegs (2 ^ 64 - 1) (2 ^ 64 - 1) 2 (acct.minBalance + 51)) mem0
  (ctxOf nearT)) == Result.CASH
-- (b) 9, the effective supervisor of junior 4, moves 100 of 4's supervisor balance into 4's balance
-- (x = 1) while 4's balance alone is 50 below its threshold: **d'**[4] = (a_t + 50, 0), OK.
def juniorNear : ServiceAccount :=
  { junior with balance := junior.minBalance - 50, supervisorBalance := 100 }
def tSelf1 := AccHost.transfer env0 100000 (tRegs 4 4 1 100) mem0 (ctxOf acct [(4, juniorNear)])
#guard r7 tSelf1 == Result.OK && (acctOf tSelf1 4).balance == junior.minBalance + 50 &&
  (acctOf tSelf1 4).supervisorBalance == 0 && tSelf1.ctx.1.modified.contains 4
-- … while a deferred transfer to itself (o ≠ 0) credits nothing yet, so the debit alone counts: CASH
#guard r7 (AccHost.transfer env0 100000 (regs [(7, 4), (8, 4), (9, 1), (10, 100), (11, 6), (12, base)])
  mem0 (ctxOf acct [(4, juniorNear)])) == Result.CASH

/-! ### new: the CASH boundary when the supervisor pays from a junior's supervisor balance, and the
registrar's FULL (GP v0.8.1 Ω_N) -/

/-- a_t of the account `new` creates from `newMem 10` (gratis 0): items 2, octets 81 + 10. -/
def newT : Nat := Constants.Cbasedeposit + 2 * Constants.Citemdeposit + (81 + 10) * Constants.Cbytedeposit
-- 9 funds a new account from junior 4's supervisor balance (x = 1): afterwards 4 has b + b' = its
-- threshold exactly, OK …
def jFund (sb : Nat) : ServiceAccount :=
  { junior with balance := junior.minBalance - 1, supervisorBalance := sb }
#guard r7 (AccHost.new env0 100000 (newRegs 1 4) (newMem 10) (ctxOf rich [(4, jFund (newT + 1))])) != Result.CASH
#guard (acctOf (AccHost.new env0 100000 (newRegs 1 4) (newMem 10) (ctxOf rich [(4, jFund (newT + 1))])) 4).supervisorBalance == 1
-- … one less and it is CASH
#guard r7 (AccHost.new env0 100000 (newRegs 1 4) (newMem 10) (ctxOf rich [(4, jFund newT)])) == Result.CASH
-- the registrar asking for a protected id that exists: FULL
def ctxReg (others : List (Nat × ServiceAccount)) : AccCtx :=
  let (x, _) := ctxOf rich others
  let x := { x with state := { x.state with registrar := 9 } }
  (x, x)
#guard r7 (AccHost.new env0 100000 (regs [(7, 2 ^ 64 - 1), (8, 4), (9, 0), (10, base)]) (newMem 10)
  (ctxReg [(4, acct)])) == Result.FULL
#guard r7 (AccHost.new env0 100000 (regs [(7, 2 ^ 64 - 1), (8, 5), (9, 0), (10, base)]) (newMem 10)
  (ctxReg [(4, acct)])) == 5

/-! ### Δ_*, Δ_+ and θ' with hand-assembled services (GP v0.8.1 eqs. `accpar`, `accseq`,
`finalstateaccumulation`)

Each service is a PVM program entered at ı = 5 (eq. `accinvocation`): five `fallthrough`s, then a
list of steps, each `load_imm_64` into registers or `ecalli n`, then `jump_ind ω₀ + 0`, which halts
(Y sets ω₀ = 2^32 − 2^16). Its read-only data sits at 𝖹_Z = 0x10000. The services accumulate on free
gas (χ_Z), so no work reports are needed. -/

/-- A step of a test service. -/
inductive TOp where
  | set (r v : Nat)
  | call (n : Nat)

/-- The instructions: `fallthrough` ×5, the steps, `jump_ind ω₀ + 0`. -/
def svcInstrs (ops : List TOp) : List (List UInt8) :=
  List.replicate 5 [1] ++ ops.map (fun
    | .set r v => [20, r.toUInt8] ++ Num.encodeLE 8 v
    | .call n => [10, n.toUInt8]) ++ [[50, 0]]

/-- k: one bit per code octet, set at each instruction's start, least significant bit first. -/
def startBits (xs : List (List UInt8)) : List UInt8 :=
  let bits := xs.flatMap fun i => true :: List.replicate (i.length - 1) false
  (List.range ((bits.length + 7) / 8)).map fun j =>
    (List.range 8).foldl (fun acc b =>
      if bits.getD (8 * j + b) false then acc ||| ((1 : UInt8) <<< b.toUInt8) else acc) 0

/-- The standard program (GP v0.8.1 eq. `jamblobformat`, empty metadata) of a step list. -/
def svcProgram (ops : List TOp) (ro : List UInt8) : List UInt8 :=
  let xs := svcInstrs ops
  let c := xs.flatten
  let p := [0, 0] ++ Codec.nat c.length ++ c ++ startBits xs
  [0] ++ Num.encodeLE 3 ro.length ++ Num.encodeLE 3 0 ++ Num.encodeLE 2 0 ++ Num.encodeLE 3 4096 ++
    ro ++ Num.encodeLE 4 p.length ++ p

def roBase : Nat := 0x10000
def none64 : Nat := 2 ^ 64 - 1

/-- A rich account whose code is `code` (none: no code). -/
def svc (code : Option (List UInt8)) (sup supCreated : Nat := 0) : ServiceAccount :=
  match code with
  | none => { rich with codeHash := List.replicate 32 1, minMemoGas := 0, supervisor := sup,
                        supervisorCreated := supCreated }
  | some c =>
    let h := (Blake2b.hash256 ⟨c.toArray⟩).toList
    { rich with codeHash := h, preimages := Std.ExtTreeMap.ofList [(h, c)], minMemoGas := 0,
                supervisor := sup, supervisorCreated := supCreated }

/-- The partial state with these accounts, all of them always-accumulated with 10^6 gas
    (`free`), manager `m` and delegator `v`. -/
def psOf (as : List (Nat × ServiceAccount)) (free : List Nat) (m v : Nat := 0) : PartialState :=
  { accounts := Std.ExtTreeMap.ofList as, staging := [], authQueue := [[], []], manager := m,
    assigners := [0, 0], delegator := v, registrar := 0,
    alwaysAcc := Std.ExtTreeMap.ofList (free.map (·, 1000000)) }

/-- The prior state for `accAt`: slot 9, nothing queued or accumulated. -/
def accPre (e : PartialState) : AccState :=
  { slot := 9, entropy := List.replicate 32 0, ready := List.replicate 12 []
    accumulated := List.replicate 12 ∅, pstate := e }

/-- The accumulation STF at slot 10 (prior slot 9) with no reports. None of these tests creates
    a new service, so it never fails (`accOk` checks that); on an error it would return the prior
    state with no outputs, which the checks below would catch. -/
def accAt (e : PartialState) : AccResult :=
  match accumulate .tiny (accPre e) 10 [] with
  | .ok r => r
  | .error _ => { state := accPre e, root := [], stats := [] }

/-- The accumulation STF succeeds on this state. -/
def accOk (e : PartialState) : Bool :=
  match accumulate .tiny (accPre e) 10 [] with
  | .ok _ => true
  | .error _ => false

-- yield = 27, checkpoint = 19, transfer = 22, write = 5, provide = 28, bless = 16
/-- A deferred transfer to itself of 0 with gas limit `l`, the memo read at 0x10000. -/
def selfXfer (l : Nat) : List TOp :=
  [.set 7 none64, .set 8 none64, .set 9 0, .set 10 0, .set 11 l, .set 12 roBase, .call 22]

/-! θ': service 20 yields the first 32 octets of its arguments ℰ(t, s, |**i**|) = [10, 20, |**i**|, 0, …]
(ω_7 points there on entry). Round 1 (free gas, no inputs) it also sends itself two transfers of
gas 5000, with a checkpoint after each step; round 2 (two inputs, gas 10000) has gas for only one,
round 3 (one input, gas 5000) for none. So it yields [10, 20, 0, …], then [10, 20, 2, …], then
[10, 20, 1, …], and θ' lists them by hash, not by round. -/
def argYield : List UInt8 :=
  svcProgram ([.call 27, .call 19] ++ selfXfer 5000 ++ [.call 19] ++ selfXfer 5000) (List.replicate 128 0)
def hArgs (k : Nat) : List UInt8 := [10, 20, k.toUInt8] ++ List.replicate 29 0
def thetaRes := accAt (psOf [(20, svc (some argYield))] [20])
#guard accOk (psOf [(20, svc (some argYield))] [20])
#guard thetaRes.outputs == [(20, hArgs 0), (20, hArgs 1), (20, hArgs 2)]
#guard thetaRes.root ==
  Merkle.root Keccak.keccak256 ([0, 1, 2].map fun k => Codec.fixed 4 20 ++ hArgs k)
-- three rounds' transfers: two from round 1, one from round 2
#guard thetaRes.stats == [(20, (0, 3, (thetaRes.stats.lookup 20).elim 0 (·.2.2)))]

/-! … and a service yielding the same hash in two rounds appears once. It yields the 32 octets at
0x10000, then sends itself a transfer of gas 5000, which round 2 cannot afford. -/
def constHash : List UInt8 := List.replicate 32 0xab
def constYield : List UInt8 :=
  svcProgram ([.set 7 roBase, .call 27, .call 19] ++ selfXfer 5000) (constHash ++ List.replicate 96 0)
def dupRes := accAt (psOf [(20, svc (some constYield))] [20])
#guard dupRes.outputs == [(20, constHash)]
#guard (dupRes.stats.lookup 20).map (·.2.1) == some 1

/-! N: junior 31 and its effective supervisor 30 both write 31's key "k". 31 also yields and provides
a preimage for its own request; its run is discarded (GP v0.8.1 eq. `accpar`, with the input state
for N(**o**)'s post-state, note v0.8.1-A1): 31's storage holds 30's value, 31 yields nothing, but its
gas use and its provision stay. -/
def pre4 : List UInt8 := [1, 2, 3, 4]
def hPre4 : List UInt8 := (Blake2b.hash256 ⟨pre4.toArray⟩).toList
/-- ro: "k" at 0, "J" at 1, the preimage at 2, a hash to yield at 32. -/
def juniorCode : List UInt8 :=
  svcProgram [.set 7 none64, .set 8 roBase, .set 9 1, .set 10 (roBase + 1), .set 11 1, .call 5,
           .set 7 none64, .set 8 (roBase + 2), .set 9 4, .call 28,
           .set 7 (roBase + 32), .call 27]
    ("kJ".toUTF8.toList ++ pre4 ++ List.replicate 26 0 ++ constHash)
/-- 30 writes "U" under 31's key "k". -/
def supCode : List UInt8 :=
  svcProgram [.set 7 31, .set 8 roBase, .set 9 1, .set 10 (roBase + 1), .set 11 1, .call 5] "kU".toUTF8.toList
def junior31 : ServiceAccount := (svc (some juniorCode) 30 0).requestSet hPre4 4 []
def nRes (sup : Option (List UInt8)) := accAt (psOf [(30, svc sup), (31, junior31)] [30, 31])
#guard accOk (psOf [(30, svc (some supCode)), (31, junior31)] [30, 31])
def acctIn (r : AccResult) (s : Nat) : ServiceAccount := r.state.pstate.accounts.getD s default
-- both write: 31's run is discarded
#guard (acctIn (nRes (some supCode)) 31).storageGet "k".toUTF8.toList == some "U".toUTF8.toList
#guard (nRes (some supCode)).outputs == []
#guard ((nRes (some supCode)).stats.lookup 31).elim 0 (·.2.2) > 0
#guard (acctIn (nRes (some supCode)) 31).requestGet hPre4 4 == some [10]
#guard (acctIn (nRes (some supCode)) 31).preimages.get? hPre4 == some pre4
-- the supervisor does nothing: 31's run stands
#guard (acctIn (nRes none) 31).storageGet "k".toUTF8.toList == some "J".toUTF8.toList
#guard (nRes none).outputs == [(31, constHash)]

/-! T over rounds: 40 sends 7 to junior 42 and then 7 to its effective supervisor 41 (neither has
code). Round 2 takes the transfer to 42; the one to 41 waits for round 3 (T's second disjunct), so
**u** lists 42 before 41 although 41 < 42. -/
def payBoth : List UInt8 :=
  svcProgram [.set 7 none64, .set 8 42, .set 9 0, .set 10 7, .set 11 0, .set 12 roBase, .call 22,
           .set 7 none64, .set 8 41, .set 9 0, .set 10 7, .set 11 0, .set 12 roBase, .call 22]
    (List.replicate 128 0)
def tPs := psOf [(40, svc (some payBoth)), (41, svc none), (42, svc none 41 0)] [40]
def tSeq := match accSeq .tiny (List.replicate 32 0) 10 20 2000000 [] [] tPs tPs.alwaysAcc with
  | .ok x => x
  | .error _ => (0, tPs, [], [], [])
#guard accOk tPs
#guard tSeq.2.2.2.1.map (·.1) == [40, 42, 41]
#guard tSeq.2.2.2.2.map (·.dest) == [42, 41]
#guard (tSeq.2.1.accounts.getD 41 default).balance == rich.balance + 7 &&
  (tSeq.2.1.accounts.getD 42 default).balance == rich.balance + 7
#guard ((accAt tPs).stats.lookup 41).map (·.2.1) == some 1 &&
  ((accAt tPs).stats.lookup 42).map (·.2.1) == some 1
#guard (acctIn (accAt tPs) 41).lastAcc == 10 && (acctIn (accAt tPs) 42).lastAcc == 10

/-! Ψ_A: a transfer flagged for the destination's supervisor balance credits b', marks the service
modified and, with no code, uses no gas (GP v0.8.1 eq. `accinvocation`). -/
def supXfer : DeferredTransfer :=
  { source := 1, dest := 43, destSupervisor := true, amount := 5, memo := ⟨#[]⟩, gas := 0 }
def psiSup := psiA .tiny (List.replicate 32 0) (psOf [(43, svc none)] []) 10 43 0 [.transfer supXfer]
#guard (psiSup.state.accounts.getD 43 default).supervisorBalance == rich.supervisorBalance + 5 &&
  (psiSup.state.accounts.getD 43 default).balance == rich.balance &&
  psiSup.modified.contains 43 && psiSup.gasUsed == 0

/-! Ψ_A's gas saturates at 2^64 − 1 (note v0.8.1-A61): with free gas 2^64 − 1 (which the manager may
bless, χ_Z) and an incoming transfer of gas 1, Δ_1's g = 2^64 is outside ℕ_G. Ψ_M runs with
2^64 − 1, so service 44 yields its hash; wrapping to 0 would run out of gas at once and yield
nothing. -/
def bigXfer : DeferredTransfer :=
  { source := 1, dest := 44, destSupervisor := false, amount := 0, memo := ⟨#[]⟩, gas := 1 }
def yieldConst : List UInt8 := svcProgram [.set 7 roBase, .call 27] constHash
def bigOne := accOne .tiny (List.replicate 32 0) 10 (psOf [(44, svc (some yieldConst))] []) [bigXfer] []
  (Std.ExtTreeMap.ofList [(44, 2 ^ 64 - 1)]) 44
#guard bigOne.yield == some constHash
#guard 0 < bigOne.gasUsed && bigOne.gasUsed ≤ 2 ^ 64 - 1

/-! R: manager 50 and delegator 51 both bless the delegator role in one round, 50 to 60 and 51 to
61: the manager's choice wins (GP v0.8.1 eq. `accpar`, R); with a manager that does nothing, 51's. -/
def blessV (v : Nat) : List UInt8 :=
  svcProgram [.set 7 none64, .set 8 none64, .set 9 v, .set 10 none64, .set 11 none64, .set 12 0,
           .call 16] []
#guard (accAt (psOf [(50, svc (some (blessV 60))), (51, svc (some (blessV 61)))] [50, 51] 50 51)).state.pstate.delegator == 60
#guard (accAt (psOf [(50, svc none), (51, svc (some (blessV 61)))] [50, 51] 50 51)).state.pstate.delegator == 61

/-! ### new-service index conflicts in Δ_* (GP v0.8.1 §12.2, the paragraph after I and Y): two
services creating the same new index make the block invalid; distinct new indices are collected,
and indices already in **d** are not new. -/

def dOld : Accounts := Std.ExtTreeMap.ofList [(1, acct)]
-- service A's post-state holds 1 (existing) and new 100; service B's holds 1 and new 200
def outA : Accounts := Std.ExtTreeMap.ofList [(1, acct), (100, junior)]
def outB : Accounts := Std.ExtTreeMap.ofList [(1, rich), (200, rich)]
#guard match collectNew dOld [outA, outB] with
  | .ok n => n.keys == [100, 200] && (n.get? 100).map (·.balance) == some junior.balance
  | .error _ => false
-- both create 100: a conflict
def outC : Accounts := Std.ExtTreeMap.ofList [(1, acct), (100, rich)]
#guard match collectNew dOld [outA, outC] with
  | .error e => e == .newServiceConflict 100
  | .ok _ => false
-- … even if both create the same account
#guard match collectNew dOld [outA, outA] with
  | .error e => e == .newServiceConflict 100
  | .ok _ => false
-- no service creates anything: nothing new
#guard match collectNew dOld [dOld, dOld] with | .ok n => n.isEmpty | .error _ => false

/-! ### the preimages extrinsic bounds (GP v0.8.1 eq. `xtpreimages`, `maxxtpreimagesdatasize`) -/

def pErr (xs : List (Nat × List UInt8)) : Option PreimageError :=
  match preimages ∅ ∅ xs 0 with | .ok _ => none | .error e => some e
#guard pErr (List.replicate (Constants.Cmaxxtpreimageslen + 1) (0, [])) == some .tooMany
#guard pErr [(0, List.replicate (Constants.Cmaxxtpreimagesdatasize + 1) 0)] == some .tooMuchData
#guard pErr [] == none

end JAM.Tests.HostGeneral
