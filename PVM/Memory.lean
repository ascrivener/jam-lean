import Std.Data.ExtTreeMap
import PVM.Basic

/-!
# RAM (GP v0.8.0 §4.7, eq. `pvmmemory`) and the memory-access exception ε^μ (§A.4)

𝕄 ≡ (**v** ∈ 𝔹_{2^32}, **a** ∈ ⟦{W, R, ∅}⟧_p), p = 2^32 / 𝖹_P, 𝖹_P = 2^12.

We represent both components as extensional finite maps (`Std.ExtTreeMap`, so that two
memories with the same lookups are equal):

* `bytes` maps addresses in ℕ_{2^32} to octets; absent addresses hold 0;
* `pages` maps page indices to `Access.read` (R) or `Access.write` (W); absent pages are
  inaccessible (∅).

Subscripts are cyclic (μ^↺, GP §3 notation): the octet at index `i` is **v**[i mod 2^32].
-/

namespace PVM

/-- 𝖹_P = 2^12, the PVM page size (GP §4.7 `sec:virtualmachineandgas`, eq. `pvmmemory`). -/
def pageSize : Nat := 2 ^ 12

/-- A page's access mode: R (read-only) or W (read-write); ∅ is absence from the map. -/
inductive Access where
  | read
  | write
  deriving DecidableEq, Repr

/-- PVM RAM μ ∈ 𝕄. -/
structure Memory where
  /-- **v**: non-zero octets by address in ℕ_{2^32}; absent addresses hold 0. -/
  bytes : Std.ExtTreeMap Nat UInt8 := ∅
  /-- **a**: access mode by page index; absent pages are inaccessible. -/
  pages : Std.ExtTreeMap Nat Access := ∅

namespace Memory

/-- The empty RAM: all octets zero, all pages inaccessible. -/
def empty : Memory := {}

/-- i ∈ 𝕍_μ, the readable indices (GP eq. `pvmmemory`): μ_**a**[⌊i / 𝖹_P⌋] ≠ ∅. -/
def readable (μ : Memory) (i : Nat) : Bool := (μ.pages.get? (i / pageSize)).isSome

/-- i ∈ 𝕍*_μ, the writable indices (GP eq. `pvmmemory`): μ_**a**[⌊i / 𝖹_P⌋] = W. -/
def writable (μ : Memory) (i : Nat) : Bool := μ.pages.get? (i / pageSize) == some .write

/-- μ^↺_i, the octet at index `i mod 2^32`. -/
def read (μ : Memory) (i : Nat) : UInt8 := μ.bytes.getD (i % two32) 0

/-- μ'^↺_i = v. -/
def write (μ : Memory) (i : Nat) (v : UInt8) : Memory :=
  { μ with bytes := μ.bytes.insert (i % two32) v }

/-- μ^↺_{a…+n}. -/
def readN (μ : Memory) (a n : Nat) : List UInt8 := (List.range n).map fun k => μ.read (a + k)

/-- μ'^↺_{a…+|bs|} = bs. -/
def writeN (μ : Memory) (a : Nat) : List UInt8 → Memory
  | [] => μ
  | b :: bs => (μ.write a b).writeN (a + 1) bs

/-- Set the access mode of the pages `first, …, first + count - 1`. -/
def setPages (μ : Memory) (first count : Nat) (acc : Option Access) : Memory :=
  { μ with pages := (List.range count).foldl (fun m k =>
      match acc with
      | some a => m.insert (first + k) a
      | none => m.erase (first + k)) μ.pages }

/-! ### Read-after-write -/

@[simp] theorem read_write_self (μ : Memory) (i : Nat) (v : UInt8) : (μ.write i v).read i = v := by
  simp [read, write]

theorem read_write_of_ne (μ : Memory) {i j : Nat} (v : UInt8) (h : i % two32 ≠ j % two32) :
    (μ.write i v).read j = μ.read j := by
  simp only [read, write, Std.ExtTreeMap.getD_insert]
  have : compare (i % two32) (j % two32) ≠ .eq := by
    simpa [Nat.compare_eq_eq] using h
  simp [this]

/-- Reading after a write: the written octet at the written index, the old octet elsewhere. -/
theorem read_write (μ : Memory) (i j : Nat) (v : UInt8) :
    (μ.write i v).read j = if i % two32 = j % two32 then v else μ.read j := by
  split
  · rename_i h
    simp only [read, write, h, Std.ExtTreeMap.getD_insert_self]
  · exact read_write_of_ne μ v ‹_›

@[simp] theorem write_pages (μ : Memory) (i : Nat) (v : UInt8) : (μ.write i v).pages = μ.pages := rfl

@[simp] theorem readable_write (μ : Memory) (i j : Nat) (v : UInt8) :
    (μ.write i v).readable j = μ.readable j := rfl

@[simp] theorem writable_write (μ : Memory) (i j : Nat) (v : UInt8) :
    (μ.write i v).writable j = μ.writable j := rfl

@[simp] theorem writeN_nil (μ : Memory) (a : Nat) : μ.writeN a [] = μ := rfl

@[simp] theorem writeN_cons (μ : Memory) (a : Nat) (b : UInt8) (bs : List UInt8) :
    μ.writeN a (b :: bs) = (μ.write a b).writeN (a + 1) bs := rfl

@[simp] theorem writeN_pages (μ : Memory) (a : Nat) (bs : List UInt8) :
    (μ.writeN a bs).pages = μ.pages := by
  induction bs generalizing μ a with
  | nil => rfl
  | cons b bs ih => simp [ih]

theorem add_mod_ne (a m N : Nat) (h0 : 0 < m) (h : m < N) : (a + m) % N ≠ a % N := by
  intro heq
  have h1 := Nat.sub_mod_eq_zero_of_mod_eq heq
  rw [show a + m - a = m by omega, Nat.mod_eq_of_lt h] at h1
  omega

/-- A multi-octet write leaves indices outside the written window unchanged. -/
theorem read_writeN_of_not_mem (μ : Memory) (a : Nat) (bs : List UInt8) (j : Nat)
    (h : ∀ k < bs.length, (a + k) % two32 ≠ j % two32) :
    (μ.writeN a bs).read j = μ.read j := by
  induction bs generalizing μ a with
  | nil => rfl
  | cons b bs ih =>
    simp only [writeN_cons]
    rw [ih]
    · exact read_write_of_ne μ b (by simpa using h 0 (by simp))
    · intro k hk
      have := h (k + 1) (by simp; omega)
      rwa [show a + (k + 1) = a + 1 + k by omega] at this

/-- After writing `bs` at `a` (at most 2^32 octets, so the write does not wrap onto itself),
    the octet at `a + k` is `bs[k]`. -/
theorem read_writeN_at (μ : Memory) (a : Nat) (bs : List UInt8) (hlen : bs.length ≤ two32)
    (k : Nat) (hk : k < bs.length) : (μ.writeN a bs).read (a + k) = bs[k] := by
  induction bs generalizing μ a k with
  | nil => simp at hk
  | cons b bs ih =>
    simp only [List.length_cons] at hlen hk
    simp only [writeN_cons]
    cases k with
    | zero =>
      rw [read_writeN_of_not_mem]
      · simp
      · intro k' hk'
        rw [show a + 1 + k' = a + (k' + 1) by omega]
        exact add_mod_ne a (k' + 1) two32 (by omega) (by omega)
    | succ k =>
      rw [show a + (k + 1) = a + 1 + k by omega, ih _ _ (by omega) k (by omega)]
      simp

/-- Reading back a multi-octet write (of at most 2^32 octets) gives the written octets. -/
theorem readN_writeN (μ : Memory) (a : Nat) (bs : List UInt8) (hlen : bs.length ≤ two32) :
    (μ.writeN a bs).readN a bs.length = bs := by
  apply List.ext_getElem
  · simp [readN]
  · intro k h1 h2
    simp only [readN, List.getElem_map, List.getElem_range]
    exact read_writeN_at μ a bs hlen k h2

end Memory

/-- The exceptional state ε^μ caused by memory access (GP §A.4):

    ε^μ = ▸ if **x** = ∅; ☇ if min(**x**) mod 2^32 < 2^16; F × 𝖹_P⌊min(**x**) mod 2^32 ÷ 𝖹_P⌋ otherwise,
    where **x** = {x | x ∈ **r** ∧ x mod 2^32 ∉ 𝕍_μ ∨ x ∈ **w** ∧ x mod 2^32 ∉ 𝕍*_μ}.

    `none` is ▸, `some none` is ☇ (panic), and `some (some a)` is a fault at page address `a`.

    The prose of §A.4 says an index below 2^16 always panics "regardless of the apparent
    (in)accessibility"; the formula, which we follow, only considers inaccessible indices
    (README, note 3). -/
def memoryException (μ : Memory) (r w : List Nat) : Option (Option Nat) :=
  let x := r.filter (fun i => !μ.readable (i % two32)) ++ w.filter (fun i => !μ.writable (i % two32))
  match x.min? with
  | none => none
  | some m => if m % two32 < 2 ^ 16 then some none else some (some (pageSize * (m % two32 / pageSize)))

end PVM
