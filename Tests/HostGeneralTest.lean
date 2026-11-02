import JAM

/-!
# Hand-written tests of the general host functions

Each `#guard` checks one case of a function's definition in GP v0.8.0 Appendix B. These functions
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
-- out of gas: ∞, ϱ' = ϱ − g < 0, registers unchanged
#guard (hostGas (X := Unit) 10 (regs [(7, 99)]) mem0 ()).status == .oog
#guard (hostGas (X := Unit) 10 (regs [(7, 99)]) mem0 ()).gas == 10 - (Constants.CgasG : Int)
#guard r7 (hostGas (X := Unit) 10 (regs [(7, 99)]) mem0 ()) == 99

/-! ### write and read -/

/-- Key "k1" at `base`, value "hello" at `base + 16`. -/
def memKV : Memory := (mem0.writeN base "k1".toUTF8.toList).writeN (base + 16) "hello".toUTF8.toList

def writeRegs (vZ : Nat) : Regs := regs [(7, base), (8, 2), (9, base + 16), (10, vZ)]
def w1 := hostWrite 100000 (writeRegs 5) memKV acct

-- a fresh key: ω'_7 = NONE, and the storage holds the value
#guard w1.status == .cont && r7 w1 == Result.NONE
#guard w1.ctx.storage.get? "k1".toUTF8.toList == some "hello".toUTF8.toList
-- overwriting returns the previous length
#guard r7 (hostWrite 100000 (writeRegs 3) memKV w1.ctx) == 5
-- v_Z = 0 deletes
#guard (hostWrite 100000 (writeRegs 0) memKV w1.ctx).ctx.storage.get? "k1".toUTF8.toList == none
-- below the threshold balance: FULL and the account is unchanged
#guard r7 (hostWrite 100000 (writeRegs 5) memKV { acct with balance := 0 }) == Result.FULL
#guard ((hostWrite 100000 (writeRegs 5) memKV { acct with balance := 0 }).ctx.storage.size) == 0
-- an unreadable key panics
#guard (hostWrite 100000 (regs [(7, 0x10), (8, 2)]) memKV acct).status == .panic
-- write gas: 𝖬_{W,c} + 𝔊(𝖬_{W,k,ℓ}, 2) + 𝔊(𝖬_{W,v,ℓ}, 5)
#guard w1.gas == 100000 - (Constants.CgasWconst + memGas Constants.CgasWkeylinear 2 +
  memGas Constants.CgasWvallinear 5 : Nat)

/-- read the key at `base` from the own account (ω_7 = 2^64 − 1) into `base + 0x100`. -/
def readRegs (f z : Nat) : Regs := regs [(7, 2 ^ 64 - 1), (8, base), (9, 2), (10, base + 0x100), (11, f), (12, z)]
def rd := hostRead (X := Unit) 100000 (readRegs 0 5) memKV w1.ctx 9 ∅ ()

#guard r7 rd == 5 && rd.mem.readN (base + 0x100) 5 == "hello".toUTF8.toList
-- offset and length: f = 1, l = 2 → "el"; ω'_7 is still the full length
#guard (hostRead (X := Unit) 100000 (readRegs 1 2) memKV w1.ctx 9 ∅ ()).mem.readN (base + 0x100) 3 ==
  "el".toUTF8.toList ++ [0]
-- a missing key: NONE
#guard r7 (hostRead (X := Unit) 100000 (readRegs 0 5) memKV acct 9 ∅ ()) == Result.NONE
-- writing the output into a read-only page panics
#guard (hostRead (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, 2), (10, 34 * 4096), (12, 5)])
  memKV w1.ctx 9 ∅ ()).status == .panic
-- another service's storage, through the accounts dictionary
#guard r7 (hostRead (X := Unit) 100000 (regs [(7, 4), (8, base), (9, 2), (10, base + 0x100), (12, 5)])
  memKV acct 9 (Std.ExtTreeMap.ofList [(4, w1.ctx)]) ()) == 5

/-! ### lookup -/

def pre : List UInt8 := "preimage".toUTF8.toList
def h : List UInt8 := (Blake2b.hash256 ⟨pre.toArray⟩).toList
def withPre : ServiceAccount := { acct with preimages := Std.ExtTreeMap.ofList [(h, pre)] }
def memH : Memory := mem0.writeN base h

#guard r7 (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, base + 64), (11, 8)])
  memH withPre 1 ∅ ()) == 8
#guard (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, base + 64), (11, 8)])
  memH withPre 1 ∅ ()).mem.readN (base + 64) 8 == pre
#guard r7 (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, base), (9, base + 64), (11, 8)])
  memH acct 1 ∅ ()) == Result.NONE
-- the hash must be readable
#guard (hostLookup (X := Unit) 100000 (regs [(7, 2 ^ 64 - 1), (8, 0x10), (9, base + 64), (11, 8)])
  memH withPre 1 ∅ ()).status == .panic

/-! ### info -/

-- 32 + 5·8 + 4 + 8 + 3·4 = 96 octets
#guard (infoValue acct).length == 96
#guard r7 (hostInfo (X := Unit) 100000 (regs [(7, 3), (8, base), (10, 96)]) mem0 3
  (Std.ExtTreeMap.ofList [(3, acct)]) ()) == 96
#guard r7 (hostInfo (X := Unit) 100000 (regs [(7, 4), (8, base), (10, 96)]) mem0 3
  (Std.ExtTreeMap.ofList [(3, acct)]) ()) == Result.NONE

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

end JAM.Tests.HostGeneral
