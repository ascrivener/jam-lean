import JAM

/-!
# Hand-written tests of the refine host functions, Ψ_R and Ψ_I

No vectors exercise refine or is-authorized at the pinned commits, so each check here is one case
of a definition in GP v0.8.0 Appendix B (`sec:refinefunctions`, eqs. `refinvocation`,
`isauthinvocation`). The `#guard`s run compiled code; the `example`s at the end are checked by the
kernel.
-/

namespace JAM.Tests.Refine

open PVM JAM RefineHost

/-- A memory with pages 32 and 33 writable (addresses 0x20000–0x21fff), page 34 read-only. -/
def mem0 : Memory :=
  (Memory.empty.setPages 32 2 (some .write)).setPages 34 1 (some .read)

def base : Nat := 0x20000

def regs (vals : List (Nat × Nat)) : Regs :=
  vals.foldl (fun ω (k, v) => if h : k < 13 then ω.set k (UInt64.ofNat v) else ω) (Vector.replicate 13 0)

def r7 {X} (o : HostOut X) : Nat := (o.regs.get 7).toNat
def r8 {X} (o : HostOut X) : Nat := (o.regs.get 8).toNat

def ctx0 : RefineCtx := (∅, [])

/-- An inner program: `ecalli 42; trap`. PVM blob: |j| = 0, z = 0, |c| = 3, c = [10, 42, 0],
    k = 0b101. -/
def inner : List UInt8 := [0, 0, 3, 10, 42, 0, 5]

def memInner : Memory := mem0.writeN base inner

/-- `machine` on the program at `base`, starting at instruction `i`. -/
def mk (c : RefineCtx) (i : Nat := 0) : HostOut RefineCtx :=
  machine 100000 (regs [(7, base), (8, inner.length), (9, i)]) memInner c

/-! ### machine -/

-- The first machine gets id 0, the next id 1.
#guard (mk ctx0).status == .cont && r7 (mk ctx0) == 0 && (mk ctx0).ctx.1.contains 0
#guard r7 (mk (mk ctx0).ctx) == 1
-- The new machine has the program, an empty RAM, the given counter and an uncharged block.
#guard ((mk ctx0).ctx.1.get? 0).map (fun vm => (vm.code.toList, vm.pc, vm.charged, vm.ram.pages.size)) ==
  some (inner, 0, false, 0)
-- The smallest free id is reused after an expunge.
#guard r7 (mk ((expunge 1000 (regs [(7, 0)]) mem0 (mk (mk ctx0).ctx).ctx).ctx)) == 0
-- A start that is not an instruction boundary: deblob fails, HUH.
#guard r7 (mk ctx0 1) == Result.HUH && (mk ctx0 1).ctx.1.size == 0
-- An unreadable program panics.
#guard (machine 100000 (regs [(7, 0x100), (8, 7)]) memInner ctx0).status == .panic
-- With 63 machines: FULL (before the memory check).
def full63 : RefineCtx := ((List.range 63).foldl (fun m k => m.insert k ⟨⟨#[]⟩, Memory.empty, 0, false⟩) ∅, [])
#guard r7 (machine 100000 (regs [(7, 0x100), (8, 7)]) memInner full63) == Result.FULL
-- Gas: 𝖬_{M,c} + 𝔊(𝖬_{M,ℓ}, p_Z).
#guard (mk ctx0).gas == 100000 - (Constants.CgasMconst + memGas Constants.CgasMlinear inner.length : Nat)

/-! ### invoke -/

/-- The invoke block at `base + 0x100`: ℰ_8(g_R) ⌢ ℰ_8(**w**). -/
def invokeBlock (gR : Nat) (w : List Nat := List.replicate 13 0) : List UInt8 :=
  Codec.fixed 8 gR ++ (w.map (Codec.fixed 8)).flatten

def withMachine : RefineCtx := (mk ctx0).ctx

def inv (gas gR : Nat) (c : RefineCtx := withMachine) (n : Nat := 0) : HostOut RefineCtx :=
  invoke gas (regs [(7, n), (8, base + 0x100)]) (mem0.writeN (base + 0x100) (invokeBlock gR)) c

def inv1 := inv 100000 1000

-- The inner machine stops at `ecalli 42`: HOST, ω'_8 = 42, and its counter moves past the
-- instruction (ı' + skip(ı') + 1 = 2).
#guard inv1.status == .cont && r7 inv1 == HOST && r8 inv1 == 42
#guard (inv1.ctx.1.get? 0).map (·.pc) == some 2
-- The gas left by the inner run is written back and returned to the caller:
-- ϱ' = ϱ − (𝖬_K + g_R) + g_R'.
def gR' : Nat := Num.decodeLE (inv1.mem.readN (base + 0x100) 8)
#guard gR' < 1000 && inv1.gas == (100000 - Constants.CgasK - 1000 + gR' : Nat)
-- Invoking it again runs the `trap`: PANIC.
#guard r7 (invoke 100000 (regs [(7, 0), (8, base + 0x100)]) inv1.mem inv1.ctx) == PANIC
-- Out of inner gas: OOG, and nothing is returned.
#guard r7 (inv 100000 0) == OOG
-- An unknown machine: WHO; an unwritable block: ☇.
#guard r7 (inv 100000 1000 withMachine 5) == Result.WHO
#guard (invoke 100000 (regs [(7, 0), (8, 34 * 4096)]) mem0 withMachine).status == .panic
-- ϱ < 𝖬_K + g_R: ∞, with ϱ' = ϱ − g.
#guard (inv 1500 1000).status == .oog && (inv 1500 1000).gas == (1500 : Int) - (Constants.CgasK + 1000)

/-! ### pages, poke and peek -/

def pg (n p c r : Nat) (cx : RefineCtx := withMachine) : HostOut RefineCtx :=
  pages 100000 (regs [(7, n), (8, p), (9, c), (10, r)]) mem0 cx

-- Make pages 16 and 17 of machine 0 writable.
def rw := pg 0 16 2 2
#guard r7 rw == Result.OK && (rw.ctx.1.get? 0).map (fun vm => vm.ram.writable (16 * 4096 + 5000)) == some true
-- p < 16, r > 4, and pages past 2^32: HUH. An unknown machine: WHO.
#guard r7 (pg 0 15 1 2) == Result.HUH && r7 (pg 0 16 1 5) == Result.HUH
#guard r7 (pg 0 (2 ^ 20 - 1) 1 2) == Result.HUH && r7 (pg 9 16 1 2) == Result.WHO
-- Changing the mode of an inaccessible page (r ∈ {3, 4}): HUH.
#guard r7 (pg 0 16 1 3) == Result.HUH
-- Gas by mode.
#guard (pg 0 16 2 2).gas == 100000 - (Constants.CgasZallocconst + 2 * Constants.CgasZalloclinear : Nat)
#guard (pg 0 16 1 7).gas == 100000 - (Constants.CgasZinvalid : Nat)

/-- Data at `base + 0x200` to poke into machine 0's page 16. -/
def memData : Memory := mem0.writeN (base + 0x200) [1, 2, 3, 4]

def pk := poke 100000 (regs [(7, 0), (8, base + 0x200), (9, 16 * 4096), (10, 4)]) memData rw.ctx
#guard r7 pk == Result.OK
#guard (pk.ctx.1.get? 0).map (fun vm => vm.ram.readN (16 * 4096) 4) == some [1, 2, 3, 4]
-- Poking an inaccessible inner page: OOB; an unknown machine: WHO; an unreadable source: ☇.
#guard r7 (poke 100000 (regs [(7, 0), (8, base + 0x200), (9, 40 * 4096), (10, 4)]) memData rw.ctx) == Result.OOB
#guard r7 (poke 100000 (regs [(7, 3), (8, base + 0x200), (9, 16 * 4096), (10, 4)]) memData rw.ctx) == Result.WHO
#guard (poke 100000 (regs [(7, 0), (8, 0x100), (9, 16 * 4096), (10, 4)]) memData rw.ctx).status == .panic

def pe := peek 100000 (regs [(7, 0), (8, base + 0x300), (9, 16 * 4096), (10, 4)]) mem0 pk.ctx
#guard r7 pe == Result.OK && pe.mem.readN (base + 0x300) 4 == [1, 2, 3, 4]
-- Peeking into a read-only page of ours: ☇; from an inaccessible inner page: OOB.
#guard (peek 100000 (regs [(7, 0), (8, 34 * 4096), (9, 16 * 4096), (10, 4)]) mem0 pk.ctx).status == .panic
#guard r7 (peek 100000 (regs [(7, 0), (8, base), (9, 40 * 4096), (10, 4)]) mem0 pk.ctx) == Result.OOB

-- Making the pages read-only keeps their data (r = 3); freeing them (r = 0) zeroes it.
def ro := pg 0 16 2 3 pk.ctx
#guard r7 ro == Result.OK
#guard (ro.ctx.1.get? 0).map (fun vm => (vm.ram.readN (16 * 4096) 4, vm.ram.writable (16 * 4096), vm.ram.readable (16 * 4096))) ==
  some ([1, 2, 3, 4], false, true)
def freed := pg 0 16 2 0 pk.ctx
#guard (freed.ctx.1.get? 0).map (fun vm => (vm.ram.readN (16 * 4096) 4, vm.ram.readable (16 * 4096))) ==
  some ([0, 0, 0, 0], false)
-- Re-allocating (r = 2) also zeroes.
#guard ((pg 0 16 2 2 pk.ctx).ctx.1.get? 0).map (fun vm => vm.ram.readN (16 * 4096) 4) == some [0, 0, 0, 0]

/-! ### expunge -/

-- Expunge returns the machine's counter (2, after the host call) and removes it.
def ex := expunge 1000 (regs [(7, 0)]) mem0 inv1.ctx
#guard r7 ex == 2 && ex.ctx.1.size == 0
#guard r7 (expunge 1000 (regs [(7, 0)]) mem0 ex.ctx) == Result.WHO

/-! ### export -/

def exp1 := exportSeg 100000 (regs [(7, base + 0x200), (8, 4)]) memData 10 ctx0
-- The segment is zero-padded to 𝖶_G and its index is ς + |**e**|.
#guard r7 exp1 == 10 && exp1.ctx.2 == [[1, 2, 3, 4] ++ List.replicate (Constants.Csegmentsize - 4) 0]
#guard r7 (exportSeg 100000 (regs [(7, base + 0x200), (8, 4)]) memData 10 exp1.ctx) == 11
-- A longer length is cut to 𝖶_G.
#guard ((exportSeg 100000 (regs [(7, base), (8, 99999)]) mem0 0 ctx0).ctx.2.map (·.length)) == [Constants.Csegmentsize]
-- ς + |**e**| ≥ 𝖶_X: FULL. Unreadable: ☇.
#guard r7 (exportSeg 100000 (regs [(7, base), (8, 4)]) mem0 Constants.Cmaxpackageexports ctx0) == Result.FULL
#guard (exportSeg 100000 (regs [(7, 0x100), (8, 4)]) mem0 0 ctx0).status == .panic

/-! ### historical_lookup -/

def pre : List UInt8 := "preimage".toUTF8.toList
def h : List UInt8 := (Blake2b.hash256 ⟨pre.toArray⟩).toList

/-- An account whose preimage was available from slot 5 until slot 9. -/
def acct : ServiceAccount :=
  { codeHash := List.replicate 32 7, balance := 10000, minAccGas := 5, minMemoGas := 6,
    preimages := Std.ExtTreeMap.ofList [(h, pre)], requests := Std.ExtTreeMap.ofList [((h, pre.length), [5, 9])] }

def accts : Accounts := Std.ExtTreeMap.ofList [(3, acct)]
def memH : Memory := mem0.writeN base h

def hl (w7 t : Nat) : HostOut Unit :=
  historicalLookup 100000 (regs [(7, w7), (8, base), (9, base + 0x100), (10, 0), (11, 100)]) memH 3 accts t ()

-- Available at slot 6: the preimage, through ω_7 = 2^64 − 1 (the service itself) or its id.
#guard r7 (hl (2 ^ 64 - 1) 6) == pre.length && (hl (2 ^ 64 - 1) 6).mem.readN (base + 0x100) pre.length == pre
#guard r7 (hl 3 6) == pre.length
-- Not available at slot 9 or before slot 5: NONE. An unknown service: NONE.
#guard r7 (hl 3 9) == Result.NONE && r7 (hl 3 4) == Result.NONE && r7 (hl 8 6) == Result.NONE
-- An unreadable hash: ☇.
#guard (historicalLookup (X := Unit) 100000 (regs [(7, 3), (8, 0x100)]) memH 3 accts 6 ()).status == .panic

/-! ### Dispatch -/

def env0 : Env :=
  { params := .tiny, service := 3, accounts := accts, lookupSlot := 6, code := ⟨#[]⟩, exportOffset := 0,
    fetch := {} }

-- Accumulate-only ids are unknown to refine: WHAT, charging 𝖬_∅.
#guard r7 (dispatch env0 15 1000 (regs []) mem0 ctx0) == Result.WHAT
#guard (dispatch env0 15 1000 (regs []) mem0 ctx0).gas == (1000 - Constants.Cgasunknown : Nat)
-- `lookup` (3) is not available to refine either.
#guard r7 (dispatch env0 3 1000 (regs []) mem0 ctx0) == Result.WHAT

/-! ### Ψ_R end to end -/

/-- A JAM blob (GP eq. `conditions`) with no data, no heap and a one-page stack. -/
def jam (p : List UInt8) : List UInt8 :=
  Codec.fixed 3 0 ++ Codec.fixed 3 0 ++ Codec.fixed 2 0 ++ Codec.fixed 3 4096 ++ Codec.fixed 4 p.length ++ p

/-- `jump_ind ω₀ + 0`: halts with the arguments as output. -/
def echo : List UInt8 := jam [0, 0, 2, 50, 0, 1]
/-- `ecalli 8; jump_ind ω₀ + 0`: exports the arguments, then halts. -/
def exportThenHalt : List UInt8 := jam [0, 0, 4, 10, 8, 50, 0, 5]
/-- `ecalli 8; trap`: exports, then panics. -/
def exportThenTrap : List UInt8 := jam [0, 0, 3, 10, 8, 0, 5]

def codeHash : List UInt8 := List.replicate 32 0xcc

/-- Service 3 with code `code` (metadata "m"), requested and available from slot 0. -/
def svc (code : List UInt8) : Accounts :=
  let pre := Codec.nat 1 ++ [0x6d] ++ code
  Std.ExtTreeMap.ofList [(3, { acct with codeHash, preimages := Std.ExtTreeMap.ofList [(codeHash, pre)],
                                         requests := Std.ExtTreeMap.ofList [((codeHash, pre.length), [0])] })]

def item : WorkItem :=
  { service := 3, codeHash := ⟨codeHash.toArray⟩, payload := ⟨#[7, 8, 9]⟩, refineGasLimit := 100000,
    accumulateGasLimit := 0, exportCount := 1, importSegments := [], extrinsics := [] }

def pkg : WorkPackage :=
  { authToken := ⟨#[]⟩, authCodeHost := 3, authCodeHash := ⟨codeHash.toArray⟩, authConfig := ⟨#[]⟩,
    context := { anchorHash := ⟨#[]⟩, anchorSlot := 0, anchorStateRoot := ⟨#[]⟩, anchorAccOutLog := ⟨#[]⟩,
                 lookupAnchorHash := ⟨#[]⟩, lookupAnchorSlot := 10, lookupAnchorStateRoot := ⟨#[]⟩ },
    items := [item] }

def refine (code : List UInt8) (core : Nat := 1) : RefineOut :=
  psiR .tiny (svc code) core 0 pkg [] [[]] [[]] 0

def okBytes : WorkResult → Option (List UInt8)
  | .ok b => some b.toList
  | _ => none

/-- **a** = ℰ(c, i, w_s, ↕w_y, ℋ(p)). -/
def args (core : Nat) : List UInt8 :=
  Codec.nat core ++ Codec.nat 0 ++ Codec.nat 3 ++ Codec.var ⟨#[7, 8, 9]⟩ ++
    (Blake2b.hash256 ⟨pkg.encode.toArray⟩).toList

-- The echo service returns its arguments, and uses some gas.
#guard okBytes (refine echo).result == some (args 1)
#guard okBytes (refine echo 2).result == some (args 2)
#guard (refine echo).exports.isEmpty && (refine echo).gasUsed > 0
-- Exports are kept on success: one segment, the arguments zero-padded.
#guard (refine exportThenHalt).exports == [args 1 ++ List.replicate (Constants.Csegmentsize - (args 1).length) 0]
-- ...and dropped on ☇.
#guard (match (refine exportThenTrap).result with | .err .panic => true | _ => false) &&
  (refine exportThenTrap).exports.isEmpty
-- No such service, or code not available at the lookup anchor: BAD with no gas used.
#guard (match (psiR .tiny ∅ 0 0 pkg [] [[]] [[]] 0).result with | .err .bad => true | _ => false)
#guard (match (psiR .tiny (svc echo) 0 0 { pkg with context.lookupAnchorSlot := 0 } [] [[]] [[]] 0).result with
  | .ok _ => true | _ => false)

/-! ### Ψ_I end to end -/

-- is-authorized knows only gas, grow_heap and fetch.
#guard r7 (dispatchI .tiny pkg ⟨#[]⟩ 9 1000 (regs []) mem0 ()) == Result.WHAT

-- The authorizer `echo` returns ℰ_2(c).
#guard okBytes (psiI .tiny (svc echo) pkg 5).1 == some [5, 0]
-- No code: BAD. Code over 𝖶_A: BIG.
#guard (match (psiI .tiny ∅ pkg 5).1 with | .err .bad => true | _ => false)
def bigCode : List UInt8 := echo ++ List.replicate Constants.Cmaxauthcodesize 0
#guard (match (psiI .tiny (svc bigCode) pkg 5).1 with | .err .big => true | _ => false)

/-! ### Kernel-checked -/

example : okBytes (psiI .tiny (svc echo) pkg 513).1 = some [1, 2] := by decide +kernel
example : r7 inv1 = HOST ∧ r8 inv1 = 42 := by decide +kernel

end JAM.Tests.Refine
