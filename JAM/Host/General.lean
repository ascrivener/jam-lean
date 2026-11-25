import PVM.Invocation
import JAM.Account
import JAM.Params
import JAM.Work

/-!
# General host functions (GP v0.8.0 Appendix B, `sec:generalfunctions`)

`gas` (Ω_G), `grow_heap` (Ω_♊), `fetch` (Ω_Y), `lookup` (Ω_L), `read` (Ω_R), `write` (Ω_W) and
`info` (Ω_I), each transcribed from its row of the paper's table.

The common rules (GP Appendix B, before the table):
* ϱ' ≡ ϱ − g unless a function defines ϱ' itself;
* (ε', ω', μ', **s**') ≡ (∞, ω, μ, **s**) if ϱ < g, and otherwise (▸, ω, μ, **s**) except as indicated.

Gas here is ℤ_G, as in the paper's host functions, so on ∞ the returned ϱ' = ϱ − g may be negative.
-/

namespace JAM

open PVM

/-- ε' of a host function: ▸, ∎, ☇ or ∞. -/
abbrev HostStatus := PVM.HostStatus

/-- The result of a host function: (ε', ϱ', ω', μ', x'), with ϱ' ∈ ℤ_G. -/
structure HostOut (X : Type) where
  status : HostStatus
  gas : Int
  regs : Regs
  mem : Memory
  ctx : X

-- The host-call result constants (GP Appendix B "Host-Call Result Constants").
namespace Result
def NONE : Nat := 2 ^ 64 - 1
def WHAT : Nat := 2 ^ 64 - 2
def OOB : Nat := 2 ^ 64 - 3
def WHO : Nat := 2 ^ 64 - 4
def FULL : Nat := 2 ^ 64 - 5
def CORE : Nat := 2 ^ 64 - 6
def CASH : Nat := 2 ^ 64 - 7
def LOW : Nat := 2 ^ 64 - 8
def HUH : Nat := 2 ^ 64 - 9
def OK : Nat := 0
end Result

/-- 𝔊(L, ℓ) = ⌈L·ℓ / 1024⌉, memory-sized gas (GP eq. `fnmemgas`). -/
def memGas (L ℓ : Nat) : Nat := (L * ℓ + 1023) / 1024

/-- ℕ_{a…+n} ⊆ 𝕍*_μ, checked page by page like `Memory.rangeReadable`. -/
def _root_.PVM.Memory.rangeWritable (μ : Memory) (a n : Nat) : Bool :=
  n == 0 ||
    (a + n ≤ 2 ^ 32 &&
      let first := a / pageSize
      let last := (a + n - 1) / pageSize
      (List.range (last + 1 - first)).all fun k => μ.writable ((first + k) * pageSize))

/-- Set ω_7. -/
def setR7 (ω : Regs) (v : Nat) : Regs := ω.set 7 (UInt64.ofNat v)

/-- Register `k` as a natural. -/
def reg (ω : Regs) (k : Fin 13) : Nat := (ω.get k).toNat

/-- Apply the common rules: charge `g`, report ∞ (state unchanged) if ϱ < g, otherwise run `body`
    with the default (▸, ϱ − g, ω, μ, x). -/
def charged {X : Type} (g : Nat) (gas : Nat) (ω : Regs) (μ : Memory) (x : X)
    (body : HostOut X → HostOut X) : HostOut X :=
  if gas < g then ⟨.oog, (gas : Int) - g, ω, μ, x⟩
  else body ⟨.cont, (gas : Int) - g, ω, μ, x⟩

/-- The shared tail of `fetch`, `lookup`, `read` and `info`: given the value **v** (∅ as `none`,
    ∇ as `.error`), the offset `f₀` and length `z` registers and the output address `o`:
    ☇ if **v** = ∇ or ℕ_{o…+l} ⊄ 𝕍*_μ; NONE if **v** = ∅; otherwise ω'_7 = |**v**| and
    μ'_{o…+l} = **v**_{f…+l}, where f = min(f₀, |**v**|) and l = min(z, |**v**| − f).
    For **v** = ∅ we take |**v**| = 0, so l = 0. -/
def writeValue {X : Type} (out : HostOut X) (v : Except Unit (Option (List UInt8)))
    (o f₀ z : Nat) : HostOut X :=
  let len := match v with | .ok (some v) => v.length | _ => 0
  let f := min f₀ len
  let l := min z (len - f)
  match v with
  | .error () => { out with status := .panic }
  | .ok v =>
    if !out.mem.rangeWritable o l then { out with status := .panic }
    else match v with
      | none => { out with regs := setR7 out.regs Result.NONE }
      | some v =>
        { out with regs := setR7 out.regs v.length, mem := out.mem.writeN o ((v.drop f).take l) }

/-! ## Ω_G, `gas` = 0 -/

/-- Ω_G: ω'_7 ≡ ϱ', with g = 𝖬_G. -/
def hostGas {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (x : X) : HostOut X :=
  charged Constants.CgasG gas ω μ x fun out => { out with regs := setR7 ω out.gas.toNat }

/-! ## Ω_♊, `grow_heap` = 1 -/

/-- The heap's page bounds for a standard program (eq. `conditions`): the first heap page
    a = (2𝖹_Z + Q(|**o**|)) / 𝖹_P and the bound b below the stack. -/
def heapBounds (jam : ByteArray) : Nat × Nat :=
  let (roLen, stack) := match JamBlob.parse? jam with
    | some jb => (jb.ro.size, jb.stackSize)
    | none => (0, 0)
  ((2 * zoneSize + roundZone roLen) / pageSize,
   (2 ^ 32 - 3 * zoneSize - inputSize - roundPage stack) / pageSize)

/-- The gas-free part of Ω_♊: the heap bounds a and b, the current heap top h = a + c (c the
    writable pages in ℕ_{a…b}) and the requested top w = ω_7. -/
def growHeapCore (ω : Regs) (μ : Memory) (jam : ByteArray) : Nat × Nat × Nat × Nat :=
  let (a, b) := heapBounds jam
  -- c = |{p ∈ ℕ_{a…b} | (μ_**a**)[p] = W}|
  let c := (List.range (b - a)).countP fun k => μ.pages.get? (a + k) == some .write
  (a, b, a + c, reg ω 7)


/-! ### Fast compiled form of `growHeapCore`

`growHeapCore` counts the W pages by looking up every page index in ℕ_{a…b}, up to about 10^6 map
lookups per `grow_heap`. `growHeapCoreFast` counts them from the page map's own entries instead.
They are proved equal and registered with `@[csimp]`, so compiled code uses the fast form while the
kernel and every theorem see `growHeapCore`. -/

/-- The number of pages in ℕ_{a…b} that `pages` marks W, counted from the map's own entries. -/
def countWritable (pages : Std.ExtTreeMap Nat Access) (a b : Nat) : Nat :=
  pages.foldl (fun n k v => if a ≤ k ∧ k < b ∧ v = .write then n + 1 else n) 0

private theorem foldl_countP_succ {α : Type} (p : α → Bool) (l : List α) (n : Nat) :
    l.foldl (fun n x => if p x then n + 1 else n) n = n + l.countP p := by
  induction l generalizing n with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    cases p x <;> simp <;> omega

theorem countWritable_eq (pages : Std.ExtTreeMap Nat Access) (a b : Nat) :
    countWritable pages a b
      = (List.range (b - a)).countP fun k => pages.get? (a + k) == some .write := by
  have h1 : countWritable pages a b = pages.toList.countP
      (fun e => decide (a ≤ e.1 ∧ e.1 < b ∧ e.2 = .write)) := by
    unfold countWritable
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    have := foldl_countP_succ (fun e : Nat × Access => decide (a ≤ e.1 ∧ e.1 < b ∧ e.2 = .write))
      pages.toList 0
    simp only [decide_eq_true_eq, Nat.zero_add] at this
    exact this
  have h2 : (List.range (b - a)).countP (fun k => pages.get? (a + k) == some .write)
      = (List.range' a (b - a)).countP (fun k => pages.get? k == some .write) := by
    rw [List.range'_eq_map_range, List.countP_map]
    rfl
  rw [h1, h2, List.countP_eq_length_filter, List.countP_eq_length_filter, ← List.length_map
    (f := Prod.fst)]
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup _ _).2
  · intro k
    simp only [List.mem_map, List.mem_filter, List.mem_range', decide_eq_true_eq,
      Std.ExtTreeMap.get?_eq_getElem?, beq_iff_eq, Nat.one_mul]
    constructor
    · rintro ⟨⟨k', v⟩, ⟨hm, hk, hb, hv⟩, rfl⟩
      subst hv
      exact ⟨⟨k' - a, by omega, by omega⟩, Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.1 hm⟩
    · rintro ⟨⟨i, hi, rfl⟩, hm⟩
      exact ⟨⟨a + i, .write⟩, ⟨Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.2 hm, by omega, by omega, rfl⟩, rfl⟩
  · apply List.Pairwise.map _ _ (List.Pairwise.filter _ Std.ExtTreeMap.distinct_keys_toList)
    intro x y h hxy
    exact h (by rw [hxy]; exact Nat.compare_eq_eq.2 rfl)
  · exact (List.nodup_range' ).filter _

/-- `growHeapCore`, counting the W pages with `countWritable`. -/
def growHeapCoreFast (ω : Regs) (μ : Memory) (jam : ByteArray) : Nat × Nat × Nat × Nat :=
  let (a, b) := heapBounds jam
  (a, b, a + countWritable μ.pages a b, reg ω 7)

@[csimp] theorem growHeapCore_eq_growHeapCoreFast : @growHeapCore = @growHeapCoreFast := by
  funext ω μ jam
  simp only [growHeapCore, growHeapCoreFast, countWritable_eq]

/-- Ω_♊(ϱ, ω, μ, **p**): grow the read-write region of a standard program (eq. `conditions`) to
    page ω_7, charging 𝖬_{♊,c} + (ω_7 − h)·𝖬_{♊,p}. The function defines (ε', ϱ', ω'_7) itself, and
    then (μ'_**a**)_{a…ω'_7} = [W, …]. -/
def hostGrowHeap {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (jam : ByteArray) (x : X) :
    HostOut X :=
  let (a, b, h, w) := growHeapCore ω μ jam
  let g := Constants.CgasGeminiconst + (w - h) * Constants.CgasGeminilinear
  let (st, gas', r7) : HostStatus × Int × Nat :=
    if w ≤ h ∨ w > b then (.cont, (gas : Int) - Constants.CgasGeminiconst, h)
    else if gas < g then (.oog, gas, h)
    else (.cont, (gas : Int) - g, w)
  ⟨st, gas', setR7 ω r7, μ.setPages a (r7 - a) (some .write), x⟩

/-! ## Ω_Y, `fetch` = 2 -/

/-- The context `fetch` reads from (GP Appendix B, Ω_Y's arguments): the work package p, entropy n,
    authorizer trace **r**, item index i, imports ī, extrinsics x̄ and accumulation inputs **i**;
    any may be ∅ (`none`) depending on the invocation. -/
structure FetchContext where
  params : Params := .full
  package : Option WorkPackage := none
  entropy : Option (List UInt8) := none
  authTrace : Option (List UInt8) := none
  itemIndex : Option Nat := none
  imports : Option (List (List (List UInt8))) := none
  extrinsics : Option (List (List (List UInt8))) := none
  accInputs : Option (List AccumulateInput) := none

/-- S(w): the summary of a work item that `fetch` cases 11 and 12 return. -/
def itemSummary (w : WorkItem) : List UInt8 :=
  Codec.fixed 4 w.service ++ Codec.blob w.codeHash ++ Codec.fixed 8 w.refineGasLimit ++
    Codec.fixed 8 w.accumulateGasLimit ++ Codec.fixed 2 w.exportCount ++
    Codec.fixed 2 w.importSegments.length ++ Codec.fixed 2 w.extrinsics.length ++
    Codec.fixed 4 w.payload.size

/-- **v** of Ω_Y for case ω_10 with arguments ω_11, ω_12. -/
def fetchValue (cx : FetchContext) (c a b : Nat) : Option (List UInt8) :=
  let nth {α} (xs : List α) (k : Nat) : Option α := xs[k]?
  match c with
  | 0 => some cx.params.encode
  | 1 => cx.entropy
  | 2 => cx.authTrace
  | 3 => do let x ← cx.extrinsics; let xs ← nth x a; nth xs b
  | 4 => do let x ← cx.extrinsics; let i ← cx.itemIndex; let xs ← nth x i; nth xs a
  | 5 => do let x ← cx.imports; let xs ← nth x a; nth xs b
  | 6 => do let x ← cx.imports; let i ← cx.itemIndex; let xs ← nth x i; nth xs a
  | 7 => cx.package.map (·.encode)
  | 8 => cx.package.map (·.authConfig.toList)
  | 9 => cx.package.map (·.authToken.toList)
  | 10 => cx.package.map (·.context.encode)
  | 11 => cx.package.map fun p => Codec.varSeq itemSummary p.items
  | 12 => do let p ← cx.package; let w ← nth p.items a; some (itemSummary w)
  | 13 => do let p ← cx.package; let w ← nth p.items a; some w.payload.toList
  | 14 => cx.accInputs.map (Codec.varSeq AccumulateInput.encode)
  | 15 => do let is ← cx.accInputs; let i ← nth is a; some i.encode
  | _ => none

/-- Ω_Y: write the requested item, with g = 𝖬_{Y,c,c} + 𝔊(𝖬_{Y,c,ℓ}, ω_9). -/
def hostFetch {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (cx : FetchContext) (x : X) :
    HostOut X :=
  let c := reg ω 10
  let (gc, gl) := Constants.CgasY (if c < 16 then some c else none)
  let g := gc + memGas gl (reg ω 9)
  charged g gas ω μ x fun out =>
    writeValue out (.ok (fetchValue cx c (reg ω 11) (reg ω 12))) (reg ω 7) (reg ω 8) (reg ω 9)

/-! ## Ω_L, `lookup` = 3 (an accumulate function in GP v0.8.1)

`lookup`, `read` and `info` are accumulate functions in GP v0.8.1 (§B, "Accumulate Functions");
`write` is defined with the accumulation context in `JAM/Accumulate.lean`. These three only read the
context, so they take the accumulating service's account **x**_s and the accounts **d** = (x_e)_d. -/

/-- The account ω_7 names (GP v0.8.1, Ω_L, Ω_R, Ω_I): **x**_s for ω_7 = 2^64 − 1, otherwise
    **d**[ω_7] if any. -/
def namedAccount (self : ServiceAccount) (d : Accounts) (w : Nat) : Option ServiceAccount :=
  if w = 2 ^ 64 - 1 then some self else d.get? w

/-- Ω_L(ϱ, ω, μ, (x, y)) (GP v0.8.1): look up the preimage of the 32-octet hash at ω_8 in the
    named account, with g = 𝖬_{L,c} + 𝔊(𝖬_{L,ℓ}, ω_11). -/
def hostLookup {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount)
    (d : Accounts) (x : X) : HostOut X :=
  let g := Constants.CgasLconst + memGas Constants.CgasLlinear (reg ω 11)
  charged g gas ω μ x fun out =>
    let h := reg ω 8
    let v : Except Unit (Option (List UInt8)) :=
      if !μ.rangeReadable h 32 then .error ()
      else .ok ((namedAccount self d (reg ω 7)).bind fun a => a.preimages.get? (μ.readN h 32))
    writeValue out v (reg ω 9) (reg ω 10) (reg ω 11)

/-! ## Ω_R, `read` = 4 -/

/-- Ω_R(ϱ, ω, μ, (x, y)) (GP v0.8.1): read the storage value under the key at ω_8 (length ω_9) of
    the named account, with g = 𝖬_{R,c} + 𝔊(𝖬_{R,k,ℓ}, ω_9) + 𝔊(𝖬_{R,v,ℓ}, ω_12). -/
def hostRead {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount)
    (d : Accounts) (x : X) : HostOut X :=
  let kO := reg ω 8
  let kZ := reg ω 9
  let g := Constants.CgasRconst + memGas Constants.CgasRkeylinear kZ +
    memGas Constants.CgasRvallinear (reg ω 12)
  charged g gas ω μ x fun out =>
    let v : Except Unit (Option (List UInt8)) :=
      if !μ.rangeReadable kO kZ then .error ()
      else .ok ((namedAccount self d (reg ω 7)).bind fun a => a.storageGet (μ.readN kO kZ))
    writeValue out v (reg ω 10) (reg ω 11) (reg ω 12)

/-! ## Ω_I, `info` = 6 -/

/-- The octets `info` returns for an account (GP v0.8.1, Ω_I):
    ℰ(c, ℰ_4(u, u'), ℰ_8(b, b', t, g, m, o), ℰ_4(i), ℰ_8(f), ℰ_4(r, a, p)), with u the supervisor,
    u' its creation slot and b' the supervisor balance. -/
def infoValue (a : ServiceAccount) : List UInt8 :=
  let e := Codec.fixed
  a.codeHash ++ e 4 a.supervisor ++ e 4 a.supervisorCreated ++ e 8 a.balance ++
    e 8 a.supervisorBalance ++ e 8 a.minBalance ++ e 8 a.minAccGas ++ e 8 a.minMemoGas ++
    e 8 a.octets ++ e 4 a.items ++ e 8 a.gratis ++ e 4 a.created ++ e 4 a.lastAcc ++ e 4 a.parent

/-- Ω_I(ϱ, ω, μ, (x, y)) (GP v0.8.1): information about the named account, with g = 𝖬_I. -/
def hostInfo {X : Type} (gas : Nat) (ω : Regs) (μ : Memory) (self : ServiceAccount)
    (d : Accounts) (x : X) : HostOut X :=
  charged Constants.CgasI gas ω μ x fun out =>
    writeValue out (.ok ((namedAccount self d (reg ω 7)).map infoValue)) (reg ω 8) (reg ω 9)
      (reg ω 10)

end JAM
