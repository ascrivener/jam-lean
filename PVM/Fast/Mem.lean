import Std.Data.HashMap
import PVM.Memory

/-!
# A page-chunked overlay on the spec RAM, for fast execution

The spec RAM `Memory` (GP v0.8.1 §4.7, eq. `pvmmemory`) keeps one tree entry per written octet.
`FastMem` keeps a spec `Memory` as its *base* and an overlay of the octets written since: a hash
map from page index $\lfloor i / \mathsf{Z}_P \rfloor$ to a `Page`, which holds the page's $\mathsf{Z}_P$ octets and a mask of the
ones written. A write updates the overlay's page in place (when the overlay is not shared), so it
costs a hash lookup and two octet writes instead of a tree insertion. Reads look in the overlay
first and fall back to the base. Access modes are never changed by $\Psi$, so they stay in the base.

`FastMem.toMemory` writes the overlay back into the base. It is the abstraction function: every
operation here is proved to commute with it (`toMemory_write`, `read_eq`, …), and
`toMemory_ofMemory` says that a spec memory survives the round trip unchanged.
-/

namespace PVM

/-- A page of the overlay: its $\mathsf{Z}_P$ octets, a mask (non-zero = written), and the offsets written
    (each once), so that writing the page back costs one insertion per written octet. -/
structure Page where
  data : ByteArray
  mark : ByteArray
  offs : List Nat
  hdata : data.size = pageSize
  hmark : mark.size = pageSize
  hoffs : ∀ o, mark[o]! ≠ 0 → o ∈ offs

namespace Page

theorem replicate_getElem! (n o : Nat) : (⟨Array.replicate n 0⟩ : ByteArray)[o]! = 0 := by
  by_cases h : o < n
  · rw [getElem!_pos _ o (by simpa [ByteArray.size] using h)]
    simp [ByteArray.getElem_eq_getElem_data]
  · rw [getElem!_neg _ o (by simpa [ByteArray.size] using h)]; rfl

/-- A page with no octet written. -/
def blank : Page :=
  { data := ⟨Array.replicate pageSize 0⟩, mark := ⟨Array.replicate pageSize 0⟩, offs := [],
    hdata := by simp [ByteArray.size], hmark := by simp [ByteArray.size],
    hoffs := by intro o h; simp [replicate_getElem!] at h }

/-- The overlay's octet at offset `o`, if it was written. -/
@[inline] def get? (pg : Page) (o : Nat) : Option UInt8 :=
  if pg.mark[o]! != 0 then some pg.data[o]! else none

theorem set_hoffs (pg : Page) (o : Nat) :
    ∀ o', (pg.mark.set! o 1)[o']! ≠ 0 → o' ∈ (if pg.mark[o]! != 0 then pg.offs else o :: pg.offs) := by
  intro o' h
  by_cases e : o = o'
  · subst e
    by_cases hm : pg.mark[o]! != 0
    · simp only [hm, ↓reduceIte]; exact pg.hoffs o (by simpa using hm)
    · simp [hm]
  · rw [ByteArray.getElem!_set!_ne _ _ _ _ e] at h
    have := pg.hoffs o' h
    split <;> simp [this]

/-- Write octet `v` at offset `o` ($< \mathsf{Z}_P$). -/
@[inline] def set (pg : Page) (o : Nat) (v : UInt8) : Page :=
  -- read the mask before updating it, so that the update happens in place
  let offs := if pg.mark[o]! != 0 then pg.offs else o :: pg.offs
  { data := pg.data.set! o v, mark := pg.mark.set! o 1, offs,
    hdata := by simp [pg.hdata], hmark := by simp [pg.hmark], hoffs := set_hoffs pg o }

theorem mem_offs (pg : Page) (o : Nat) (h : pg.get? o ≠ none) : o ∈ pg.offs := by
  apply pg.hoffs
  intro h0; apply h; simp [get?, h0]

theorem get?_blank (o : Nat) : blank.get? o = none := by
  simp [get?, blank, replicate_getElem!]

theorem get?_set (pg : Page) (o o' : Nat) (v : UInt8) (h : o < pageSize) :
    (pg.set o v).get? o' = if o = o' then some v else pg.get? o' := by
  unfold get? set
  have hd : o < pg.data.size := by rw [pg.hdata]; exact h
  have hm : o < pg.mark.size := by rw [pg.hmark]; exact h
  by_cases e : o = o'
  · subst e; simp [ByteArray.getElem!_set!_self _ _ _ hd, ByteArray.getElem!_set!_self _ _ _ hm]
  · simp [e, ByteArray.getElem!_set!_ne _ _ _ _ e]

end Page

/-- The spec RAM `base` with an overlay of written octets by page. -/
structure FastMem where
  base : Memory
  dirty : Std.HashMap Nat Page

namespace FastMem

/-- A spec memory, with an empty overlay. -/
@[inline] def ofMemory (μ : Memory) : FastMem := { base := μ, dirty := ∅ }

/-- The overlay's octet at the address `k` ($< 2^{32}$), if written. -/
def view (F : FastMem) (k : Nat) : Option UInt8 :=
  match F.dirty[k / pageSize]? with
  | some pg => pg.get? (k % pageSize)
  | none => none

/-- $i \bmod 2^{32}$, through a 32-bit word (the literal $2^{32}$ is not a small constant). -/
@[inline] def mod32 (i : Nat) : Nat := (UInt32.ofNat i).toNat

theorem mod32_eq (i : Nat) : mod32 i = i % two32 := UInt32.toNat_ofNat'

/-- $\mu^{\circlearrowleft}_i$. -/
@[inline] def read (F : FastMem) (i : Nat) : UInt8 :=
  let k := mod32 i
  match F.dirty[k / pageSize]? with
  | some pg => match pg.get? (k % pageSize) with
    | some v => v
    | none => F.base.bytes.getD k 0
  | none => F.base.bytes.getD k 0

/-- $\mu'^{\circlearrowleft}_i = v$. -/
@[inline] def write (F : FastMem) (i : Nat) (v : UInt8) : FastMem :=
  let k := mod32 i
  { F with dirty := F.dirty.alter (k / pageSize) fun o => some ((o.getD .blank).set (k % pageSize) v) }

/-- $\mu^{\circlearrowleft}_{a \dots +n}$. -/
def readN (F : FastMem) (a n : Nat) : List UInt8 := (List.range n).map fun k => F.read (a + k)

/-- $\mu'^{\circlearrowleft}_{a \dots +|bs|} = bs$. -/
def writeN (F : FastMem) (a : Nat) : List UInt8 → FastMem
  | [] => F
  | b :: bs => (F.write a b).writeN (a + 1) bs

/-- $\mathcal{E}_n^{-1}(\mu^{\circlearrowleft}_{a \dots +n})$, without building the list. -/
def readLE (F : FastMem) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (F.read a).toNat + 256 * F.readLE (a + 1) n

/-- $\mu'^{\circlearrowleft}_{a \dots +n} = \mathcal{E}_n(v)$, without building the list. -/
def writeLE (F : FastMem) (a : Nat) : Nat → Nat → FastMem
  | 0, _ => F
  | n + 1, v => (F.write a (UInt8.ofNat (v % 256))).writeLE (a + 1) n (v / 256)

/-! ### Writing the overlay back -/

/-- One octet of `flushPage`. -/
@[inline] def flushStep (p : Nat) (pg : Page) (m : Std.ExtTreeMap Nat UInt8) (o : Nat) :
    Std.ExtTreeMap Nat UInt8 :=
  if o < pageSize then
    match pg.get? o with
    | some v => m.insert (p * pageSize + o) v
    | none => m
  else m

/-- Insert the written octets of page `p` into `m`. -/
def flushPage (m : Std.ExtTreeMap Nat UInt8) (p : Nat) (pg : Page) : Std.ExtTreeMap Nat UInt8 :=
  pg.offs.foldl (flushStep p pg) m

/-- The spec memory this `FastMem` stands for: the overlay written into the base. -/
def toMemory (F : FastMem) : Memory :=
  { F.base with bytes := F.dirty.fold (fun m p pg => flushPage m p pg) F.base.bytes }

/-! ### Proofs -/

theorem pageSize_pos : 0 < pageSize := by decide

theorem div_mod_eq_iff {k p o : Nat} (ho : o < pageSize) :
    (k / pageSize = p ∧ k % pageSize = o) ↔ k = p * pageSize + o := by
  constructor
  · rintro ⟨h1, h2⟩
    have := Nat.div_add_mod k pageSize
    rw [← h1, ← h2]; rw [Nat.mul_comm]; omega
  · rintro rfl
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ pageSize_pos, Nat.div_eq_of_lt ho]; simp
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem flushStep_get (p : Nat) (pg : Page) (m : Std.ExtTreeMap Nat UInt8) (o k : Nat) :
    (flushStep p pg m o)[k]? =
    if k / pageSize = p ∧ k % pageSize = o then
      match pg.get? o with
      | some v => some v
      | none => m[k]?
    else m[k]? := by
  unfold flushStep
  by_cases ho : o < pageSize
  · simp only [ho, ↓reduceIte]
    by_cases e : k = p * pageSize + o
    · have := (div_mod_eq_iff ho).mpr e
      simp only [this, and_self, ↓reduceIte]
      split <;> simp [Std.ExtTreeMap.getElem?_insert, e]
    · have hne : ¬ (k / pageSize = p ∧ k % pageSize = o) := fun h => e ((div_mod_eq_iff ho).mp h)
      simp only [hne, ↓reduceIte]
      split
      · have : compare (p * pageSize + o) k ≠ .eq := by simp [Nat.compare_eq_eq]; omega
        simp [Std.ExtTreeMap.getElem?_insert, this]
      · rfl
  · have : ¬ (k / pageSize = p ∧ k % pageSize = o) := by
      rintro ⟨-, h⟩; exact ho (h ▸ Nat.mod_lt _ pageSize_pos)
    simp [ho, this]

theorem foldl_flushStep (p : Nat) (pg : Page) (l : List Nat) (m : Std.ExtTreeMap Nat UInt8)
    (k : Nat) :
    (l.foldl (flushStep p pg) m)[k]? =
    if k / pageSize = p ∧ k % pageSize ∈ l then
      match pg.get? (k % pageSize) with
      | some v => some v
      | none => m[k]?
    else m[k]? := by
  induction l generalizing m with
  | nil => simp
  | cons o l ih =>
    rw [List.foldl_cons, ih, flushStep_get]
    by_cases h1 : k / pageSize = p
    · by_cases h2 : k % pageSize = o
      · subst h2
        cases pg.get? (k % pageSize) <;> simp [h1]
      · by_cases h3 : k % pageSize ∈ l
        · simp [h1, h2, h3]
        · simp [h1, h2, h3]
    · simp [h1]

theorem flushPage_get (m : Std.ExtTreeMap Nat UInt8) (p : Nat) (pg : Page) (k : Nat) :
    (flushPage m p pg)[k]? =
    if k / pageSize = p then
      match pg.get? (k % pageSize) with
      | some v => some v
      | none => m[k]?
    else m[k]? := by
  unfold flushPage
  rw [foldl_flushStep]
  by_cases h1 : k / pageSize = p
  · by_cases h2 : k % pageSize ∈ pg.offs
    · simp [h1, h2]
    · have : pg.get? (k % pageSize) = none := by
        cases hg : pg.get? (k % pageSize) with
        | none => rfl
        | some v => exact absurd (pg.mem_offs _ (by simp [hg])) h2
      simp [h1, h2, this]
  · simp [h1]

theorem foldl_flush_list (l : List (Nat × Page)) (hl : l.Pairwise (fun a b => a.1 ≠ b.1))
    (m : Std.ExtTreeMap Nat UInt8) (k : Nat) :
    (l.foldl (fun m x => flushPage m x.1 x.2) m)[k]? =
    match l.find? (fun x => x.1 == k / pageSize) with
    | some x => match x.2.get? (k % pageSize) with
      | some v => some v
      | none => m[k]?
    | none => m[k]? := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih (List.pairwise_cons.mp hl).2]
    by_cases e : x.1 = k / pageSize
    · have hnone : l.find? (fun y => y.1 == k / pageSize) = none := by
        rw [List.find?_eq_none]
        intro y hy
        have := (List.pairwise_cons.mp hl).1 y hy
        simp; omega
      simp [hnone, List.find?_cons, e, flushPage_get]
    · have hx : (x.1 == k / pageSize) = false := by simpa using e
      rw [List.find?_cons, hx]
      simp only
      split <;> simp [flushPage_get, Ne.symm e]

theorem toMemory_bytes_get (F : FastMem) (k : Nat) :
    F.toMemory.bytes[k]? =
    match F.dirty[k / pageSize]? with
    | some pg => match pg.get? (k % pageSize) with
      | some v => some v
      | none => F.base.bytes[k]?
    | none => F.base.bytes[k]? := by
  unfold toMemory
  simp only [Std.HashMap.fold_eq_foldl_toList]
  rw [foldl_flush_list _ (by
    have := Std.HashMap.distinct_keys_toList (m := F.dirty)
    refine this.imp ?_
    intro a b h; simpa using h)]
  cases h : F.dirty[k / pageSize]? with
  | none =>
    have : F.dirty.toList.find? (fun x => x.1 == k / pageSize) = none := by
      rw [List.find?_eq_none]
      intro y hy
      have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hy
      intro e; simp at e; rw [e] at this; simp_all
    simp [this]
  | some pg =>
    have hm : (k / pageSize, pg) ∈ F.dirty.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h
    cases hf : F.dirty.toList.find? (fun x => x.1 == k / pageSize) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf _ hm)
    | some y =>
      have hy := List.mem_of_find?_eq_some hf
      have hk := List.find?_some hf
      simp at hk
      have := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hy
      rw [hk, h] at this
      cases this
      simp

@[simp] theorem toMemory_pages (F : FastMem) : F.toMemory.pages = F.base.pages := rfl

@[simp] theorem toMemory_ofMemory (μ : Memory) : (ofMemory μ).toMemory = μ := by
  have : (ofMemory μ).toMemory.bytes = μ.bytes := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    rw [toMemory_bytes_get]
    simp [ofMemory]
  cases μ
  simp only [toMemory, ofMemory] at this ⊢
  simp [this]

theorem read_eq (F : FastMem) (i : Nat) : F.read i = F.toMemory.read i := by
  simp only [read, mod32_eq, Memory.read, Std.ExtTreeMap.getD_eq_getD_getElem?, toMemory_bytes_get]
  split
  · split <;> simp_all
  · rfl

theorem toMemory_write (F : FastMem) (i : Nat) (v : UInt8) :
    (F.write i v).toMemory = F.toMemory.write i v := by
  have hb : (F.write i v).toMemory.bytes = (F.toMemory.write i v).bytes := by
    apply Std.ExtTreeMap.ext_getElem?
    intro k
    simp only [Memory.write, Std.ExtTreeMap.getElem?_insert, toMemory_bytes_get]
    have hlt : i % two32 % pageSize < pageSize := Nat.mod_lt _ pageSize_pos
    simp only [write, mod32_eq, Std.HashMap.getElem?_alter]
    by_cases e : i % two32 = k
    · subst e
      simp [Page.get?_set _ _ _ _ hlt]
    · have hc : compare (i % two32) k ≠ .eq := by simpa [Nat.compare_eq_eq] using e
      simp only [hc, ↓reduceIte]
      by_cases hp : i % two32 / pageSize = k / pageSize
      · have ho : i % two32 % pageSize ≠ k % pageSize := by
          intro ho; apply e
          have h1 := Nat.div_add_mod (i % two32) pageSize
          rw [hp, ho] at h1
          have h2 := Nat.div_add_mod k pageSize
          omega
        simp only [hp, beq_self_eq_true, ↓reduceIte, Page.get?_set _ _ _ _ hlt, ho]
        cases F.dirty[k / pageSize]? <;> simp [Page.get?_blank]
      · have : (i % two32 / pageSize == k / pageSize) = false := by simpa using hp
        simp [this]
  cases F
  simp only [toMemory, write, mod32_eq, Memory.write] at hb ⊢
  simp [hb]

@[simp] theorem write_base (F : FastMem) (i : Nat) (v : UInt8) : (F.write i v).base = F.base := rfl

theorem readN_eq (F : FastMem) (a n : Nat) : F.readN a n = F.toMemory.readN a n := by
  simp [readN, Memory.readN, read_eq]

theorem readLE_eq (F : FastMem) (a n : Nat) : F.readLE a n = Num.decodeLE (F.readN a n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readLE, readN, List.range_succ_eq_map, List.map_cons, List.map_map, Num.decodeLE, ih]
    simp only [Nat.add_zero]
    congr 3
    apply List.map_congr_left
    intro k _; simp only [Function.comp, Nat.succ_eq_add_one]; congr 1; omega

theorem writeLE_eq (F : FastMem) (a n v : Nat) : F.writeLE a n v = F.writeN a (Num.encodeLE n v) := by
  induction n generalizing F a v with
  | zero => rfl
  | succ n ih => simp [writeLE, writeN, Num.encodeLE, ih]

theorem toMemory_writeN (F : FastMem) (a : Nat) (bs : List UInt8) :
    (F.writeN a bs).toMemory = F.toMemory.writeN a bs := by
  induction bs generalizing F a with
  | nil => rfl
  | cons b bs ih => simp [writeN, ih, toMemory_write]

@[simp] theorem writeN_base (F : FastMem) (a : Nat) (bs : List UInt8) :
    (F.writeN a bs).base = F.base := by
  induction bs generalizing F a with
  | nil => rfl
  | cons b bs ih => simp [writeN, ih]

end FastMem

/-- $\varepsilon^\mu$ only depends on the access modes. -/
theorem memoryException_pages {μ ν : Memory} (h : μ.pages = ν.pages) (r w : List Nat) :
    memoryException μ r w = memoryException ν r w := by
  simp [memoryException, Memory.readable, Memory.writable, h]

end PVM
