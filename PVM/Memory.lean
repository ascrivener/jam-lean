import Std.Data.ExtTreeMap
import PVM.Basic

/-!
# RAM (GP v0.8.1 §4.7, eq. `pvmmemory`) and the memory-access exception $\varepsilon^\mu$ (§A.4)

$\mathbb{M} \equiv (\mathbf{v} \in \mathbb{B}_{2^{32}}, \mathbf{a} \in [\![ \{W, R, \emptyset\} ]\!]_p)$, $p = 2^{32} / \mathsf{Z}_P$, $\mathsf{Z}_P = 2^{12}$.

We represent both components as extensional finite maps (`Std.ExtTreeMap`, so that two maps
with the same lookups are equal):

* `bytes` maps addresses in $\mathbb{N}_{2^{32}}$ to octets; absent addresses hold 0. An entry may
  hold an explicit 0 (`write` inserts whatever it writes), so a 0 octet has two representations;
* `pages` maps page indices to `Access.read` ($R$) or `Access.write` ($W$); absent pages are
  inaccessible ($\emptyset$).

Subscripts are cyclic ($\mu^\circlearrowleft$, GP §3 notation): the octet at index `i` is $\mathbf{v}[i \bmod 2^{32}]$.

Equality of `Memory` is therefore finer than the paper's equality of $\mu$: two memories with the
same pages and the same `read` at every index are the same $\mu$ but may differ as `Memory` (an
explicit 0 against an absent address). Everything the model observes goes through `read`,
`readable` and `writable`, so the difference is never observable; `Memory.Equiv` is the paper's
equality, and `read`, `readN`, `readable`, `writable` and `write` respect it.
-/

namespace PVM

/-- $\mathsf{Z}_P = 2^{12}$, the PVM page size (GP §4.7 `sec:virtualmachineandgas`, eq. `pvmmemory`). -/
def pageSize : Nat := 2 ^ 12

/-- A page's access mode: $R$ (read-only) or $W$ (read-write); $\emptyset$ is absence from the map. -/
inductive Access where
  | read
  | write
  deriving DecidableEq, Repr

/-- PVM RAM $\mu \in \mathbb{M}$. -/
structure Memory where
  /-- $\mathbf{v}$: octets by address in $\mathbb{N}_{2^{32}}$; absent addresses hold 0, and an
      entry may also hold an explicit 0. -/
  bytes : Std.ExtTreeMap Nat UInt8 := ∅
  /-- $\mathbf{a}$: access mode by page index; absent pages are inaccessible. -/
  pages : Std.ExtTreeMap Nat Access := ∅

namespace Memory

/-- The empty RAM: all octets zero, all pages inaccessible. -/
def empty : Memory := {}

/-- $i \in \mathbb{V}_\mu$, the readable indices (GP eq. `pvmmemory`): $\mu_{\mathbf{a}}[\lfloor i / \mathsf{Z}_P \rfloor] \ne \emptyset$. -/
def readable (μ : Memory) (i : Nat) : Bool := (μ.pages.get? (i / pageSize)).isSome

/-- $i \in \mathbb{V}^{\ast}_\mu$, the writable indices (GP eq. `pvmmemory`): $\mu_{\mathbf{a}}[\lfloor i / \mathsf{Z}_P \rfloor] = W$. -/
def writable (μ : Memory) (i : Nat) : Bool := μ.pages.get? (i / pageSize) == some .write

/-- $\mu^\circlearrowleft_i$, the octet at index $i \bmod 2^{32}$. -/
def read (μ : Memory) (i : Nat) : UInt8 := μ.bytes.getD (i % two32) 0

/-- $\mu'^\circlearrowleft_i = v$. -/
def write (μ : Memory) (i : Nat) (v : UInt8) : Memory :=
  { μ with bytes := μ.bytes.insert (i % two32) v }

/-- $\mu^\circlearrowleft_{a \dots + n}$. -/
def readN (μ : Memory) (a n : Nat) : List UInt8 := (List.range n).map fun k => μ.read (a + k)

/-- $\mu'^\circlearrowleft_{a \dots + |bs|} = bs$. -/
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

/-! ### The paper's equality of RAM -/

/-- $\mu = \mu'$ in the paper's sense: the same access modes and the same octet at every index.
    Finer than `=` on `Memory` only in how a 0 octet is stored (see the module docstring). -/
def Equiv (μ ν : Memory) : Prop := μ.pages = ν.pages ∧ ∀ i, μ.read i = ν.read i

theorem Equiv.refl (μ : Memory) : μ.Equiv μ := ⟨rfl, fun _ => rfl⟩

theorem Equiv.symm {μ ν : Memory} (h : μ.Equiv ν) : ν.Equiv μ :=
  ⟨h.1.symm, fun i => (h.2 i).symm⟩

theorem Equiv.trans {μ ν ρ : Memory} (h₁ : μ.Equiv ν) (h₂ : ν.Equiv ρ) : μ.Equiv ρ :=
  ⟨h₁.1.trans h₂.1, fun i => (h₁.2 i).trans (h₂.2 i)⟩

theorem Equiv.read_eq {μ ν : Memory} (h : μ.Equiv ν) (i : Nat) : μ.read i = ν.read i := h.2 i

theorem Equiv.readN_eq {μ ν : Memory} (h : μ.Equiv ν) (a n : Nat) : μ.readN a n = ν.readN a n := by
  simp [readN, h.2]

theorem Equiv.readable_eq {μ ν : Memory} (h : μ.Equiv ν) (i : Nat) : μ.readable i = ν.readable i := by
  simp [readable, h.1]

theorem Equiv.writable_eq {μ ν : Memory} (h : μ.Equiv ν) (i : Nat) : μ.writable i = ν.writable i := by
  simp [writable, h.1]

theorem Equiv.write {μ ν : Memory} (h : μ.Equiv ν) (i : Nat) (v : UInt8) :
    (μ.write i v).Equiv (ν.write i v) := by
  refine ⟨h.1, fun j => ?_⟩
  rw [read_write, read_write, h.2 j]

/-- Writing the octet already there gives the same RAM in the paper's sense (though as a `Memory`
    the write may turn an absent 0 into an explicit one). -/
theorem write_read_equiv (μ : Memory) (i : Nat) : (μ.write i (μ.read i)).Equiv μ := by
  refine ⟨rfl, fun j => ?_⟩
  rw [read_write]
  split
  · rename_i h; simp only [read, h]
  · rfl

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

/-- After writing `bs` at `a` (at most $2^{32}$ octets, so the write does not wrap onto itself),
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

/-- Reading back a multi-octet write (of at most $2^{32}$ octets) gives the written octets. -/
theorem readN_writeN (μ : Memory) (a : Nat) (bs : List UInt8) (hlen : bs.length ≤ two32) :
    (μ.writeN a bs).readN a bs.length = bs := by
  apply List.ext_getElem
  · simp [readN]
  · intro k h1 h2
    simp only [readN, List.getElem_map, List.getElem_range]
    exact read_writeN_at μ a bs hlen k h2

end Memory

/-- The exceptional state $\varepsilon^\mu$ caused by memory access (GP §A.4, eq. (A.9)):

    $\varepsilon^\mu = \blacktriangleright$ if $\mathbf{x} = \emptyset$; ☇ if $\min(\mathbf{x}) \bmod 2^{32} < 2^{16}$;
    $\Finv \times \mathsf{Z}_P \lfloor \min(\mathbf{x}) \bmod 2^{32} \div \mathsf{Z}_P \rfloor$ otherwise, where
    $\mathbf{x} = \{ x \mid x \in \mathbf{r} \wedge x \bmod 2^{32} \notin \mathbb{V}_\mu \vee x \in \mathbf{w} \wedge x \bmod 2^{32} \notin \mathbb{V}^{\ast}_\mu \}$.

    `none` is $\blacktriangleright$, `some none` is ☇ (panic), and `some (some a)` is a fault at page address `a`.

    The prose of §A.4 says an index below $2^{16}$ always panics "regardless of the apparent
    (in)accessibility"; the formula, which we follow, only considers inaccessible indices
    (note 3 in `docs/upstream-candidates.md#gray-paper-issues`). -/
def memoryException (μ : Memory) (r w : List Nat) : Option (Option Nat) :=
  let x := r.filter (fun i => !μ.readable (i % two32)) ++ w.filter (fun i => !μ.writable (i % two32))
  match x.min? with
  | none => none
  | some m => if m % two32 < 2 ^ 16 then some none else some (some (pageSize * (m % two32 / pageSize)))

end PVM
