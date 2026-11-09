import Services.Bootstrap.SpecLemmas.Codec

/-!
# S1: the recent-work-item ring

The ring half of S1 (`docs/bootstrap-target.md`, "Safety properties"): the occupied slots of
bootstrap's recent-work-item ring are `[0, c)`, or all of them, where c is the stored counter.
`addRecent` (`add_recent_work_item`) preserves it.

The spec says nothing about what the host does with storage. Here a minimal model of it, `Store`,
interprets the three storage operations (`read`, `write`, `remove`; GP appendix B, `read` and `write`) on a map from keys
to values; any other operation stops the run. This is enough for `addRecent`, which makes no other
host call. In the model a write always succeeds: in `addRecent` every write is `store`, which panics
if the write fails, and a panicked accumulate is rolled back to its last checkpoint, so a run that
completes is one in which every write succeeded.
-/

namespace Services.Bootstrap.Spec
open JAM.Codec (nat fixed)

/-- A service's storage: the value under each key, if any. -/
abbrev Store := Bytes → Option Bytes

/-- σ with key k set to v (`none`: removed). -/
def Store.set (σ : Store) (k : Bytes) (v : Option Bytes) : Store := fun k' => if k' = k then v else σ k'

/-- Run a program whose only host calls are storage operations, against storage σ: the result and
    the final storage, or `none` if it panics or makes any other host call. -/
def Store.run {α : Type} : Prog AOp α → Store → Option (α × Store)
  | .pure a, σ => some (a, σ)
  | .panic, _ => none
  | .call (.read k) f, σ => Store.run (f (σ k)) σ
  | .call (.write k v) f, σ => Store.run (f (.ok ())) (σ.set k (some v))
  | .call (.remove k) f, σ => Store.run (f ()) (σ.set k none)
  | .call _ _, _ => none

@[simp] theorem Store.run_pure {α : Type} (a : α) (σ : Store) :
    Store.run (pure a : Prog AOp α) σ = some (a, σ) := rfl

theorem Store.run_bind {α β : Type} (p : Prog AOp α) (g : α → Prog AOp β) (σ : Store) :
    Store.run (p >>= g) σ = (Store.run p σ).bind (fun r => Store.run (g r.1) r.2) := by
  induction p generalizing σ with
  | pure a => rfl
  | panic => rfl
  | call o k ih =>
    cases o <;> first | rfl | exact ih _ _

/-- The parser `addRecent` and `removeRecentFrom` use for a ring slot (`RecentWorkItem`). -/
def recentDec : Dec (Bytes × Nat) := do return (← Dec.take 32, ← Dec.fixedN 2)

/-- The stored counter, as `addRecent` reads it (absent or undecodable reads as 0). -/
def counter (σ : Store) : Nat := ((σ Key.counter.encode).bind (decode (Dec.fixedN 4))).getD 0

/-- Ring slot i, as `addRecent` reads it. -/
def slot (σ : Store) (i : Nat) : Option (Bytes × Nat) := (σ (Key.recent i).encode).bind (decode recentDec)

/-- Slot i holds an entry. -/
def occupied (σ : Store) (i : Nat) : Prop := (slot σ i).isSome

/-- **S1, ring half.** The counter c is a slot, and the occupied slots below `maxRecent` are
    exactly `[0, c)`, or all of them. -/
def RingInv (C : Consts) (σ : Store) : Prop :=
  counter σ < C.maxRecent ∧
    ((∀ i < C.maxRecent, occupied σ i ↔ i < counter σ) ∨ ∀ i < C.maxRecent, occupied σ i)

/-! ### Parsers -/

theorem Dec.bind_of_none {α β : Type} {p : Dec α} {f : α → Dec β} {s : Bytes}
    (h : p.run s = none) : (p >>= f).run s = none := by
  simp only [StateT.run_bind, h]; rfl

theorem Dec.take_some {n : Nat} {s b s' : Bytes} (h : (Dec.take n).run s = some (b, s')) :
    b.length = n := by
  simp only [Dec.take, StateT.run] at h
  split at h
  · cases h; simp; omega
  · cases h

theorem Dec.fixedN_some {l : Nat} {s s' : Bytes} {x : Nat} (h : (Dec.fixedN l).run s = some (x, s')) :
    x < 2 ^ (8 * l) := by
  rcases ht : (Dec.take l).run s with _ | ⟨b, s''⟩
  · rw [Dec.fixedN, Dec.bind_of_none ht] at h; cases h
  rw [Dec.fixedN, Dec.bind_of_run ht] at h
  cases h
  have := PVM.decodeLE_lt b
  rw [Dec.take_some ht] at this
  rw [Nat.pow_mul]; simpa using this

/-! ### Keys -/

theorem Key.recent_ne_counter (i : Nat) : (Key.recent i).encode ≠ Key.counter.encode := by
  simp [Key.encode]

theorem Key.results_ne_recent (p : Bytes) (it i : Nat) : (Key.results p it).encode ≠ (Key.recent i).encode := by
  simp [Key.encode]

theorem Key.results_ne_counter (p : Bytes) (it : Nat) : (Key.results p it).encode ≠ Key.counter.encode := by
  simp [Key.encode]

theorem Key.results_inj {q q' : Bytes} {j j' : Nat} (h : q.length = 32 ∧ j < 2 ^ 16)
    (h' : q'.length = 32 ∧ j' < 2 ^ 16) (e : (Key.results q j).encode = (Key.results q' j').encode) :
    (q, j) = (q', j') := by
  simp only [Key.encode, List.cons_append, List.nil_append, List.cons.injEq, true_and] at e
  obtain ⟨rfl, e2⟩ := List.append_inj e (h.1.trans h'.1.symm)
  have := congrArg PVM.Num.decodeLE e2
  simp only [JAM.Codec.fixed, PVM.Num.decodeLE_encodeLE] at this
  rw [Nat.mod_eq_of_lt h.2, Nat.mod_eq_of_lt h'.2] at this
  rw [this]

theorem Key.recent_inj {i j : Nat} (hi : i < 2 ^ 32) (hj : j < 2 ^ 32)
    (h : (Key.recent i).encode = (Key.recent j).encode) : i = j := by
  simp only [Key.encode, List.cons_append, List.nil_append, List.cons.injEq, true_and] at h
  have := congrArg PVM.Num.decodeLE h
  simp only [JAM.Codec.fixed, PVM.Num.decodeLE_encodeLE] at this
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this

/-! ### Decoding what `addRecent` writes -/

theorem decode_recent (p : Bytes) (it : Nat) (hp : p.length = 32) :
    decode recentDec (encodeRecent p it) = some (p, it % 2 ^ 16) := by
  have : encodeRecent p it = p ++ (fixed 2 it ++ []) := by simp [encodeRecent]
  rw [this]
  simp only [decode, recentDec, Dec.bind_take _ _ _ _ hp, Dec.bind_fixedN, Dec.run_pure', Option.map_some]

theorem decode_counter (x : Nat) (hx : x < 2 ^ 32) : decode (Dec.fixedN 4) (fixed 4 x) = some x := by
  have : fixed 4 x = fixed 4 x ++ [] := by simp
  rw [this]
  simp only [decode, Dec.fixedN_run, Option.map_some, Nat.mod_eq_of_lt (show x < 2 ^ (8 * 4) from hx)]

/-! ### `addRecent` -/

/-- What a completed `addRecent` leaves: the replaced entry's results removed (if slot c was
    occupied), slot c holding the new entry, and the counter at c + 1 mod `maxRecent`. -/
theorem addRecent_run (C : Consts) (p : Bytes) (it : Nat) (σ σ' : Store) (u : Unit)
    (h : Store.run (addRecent C p it) σ = some (u, σ')) :
    let c := counter σ
    let σ₁ := match slot σ c with
      | some (q, j) => σ.set (Key.results q j).encode none
      | none => σ
    σ' = (σ₁.set (Key.recent c).encode (some (encodeRecent p it))).set Key.counter.encode
      (some (fixed 4 ((c + 1) % C.maxRecent))) := by
  intro c σ₁
  simp only [addRecent, load, store, orPanic, Store.run_bind, Prog.op, Store.run, Option.bind_some,
    Store.run_pure] at h
  change Store.run (match slot σ c with
    | some (q, j) => _
    | none => _) _ = _ at h
  rcases hs : slot σ c with _ | ⟨q, j⟩ <;> rw [hs] at h <;>
    simp only [Store.run_bind, Store.run, Store.run_pure, Option.bind_some, Option.some.injEq,
      Prod.mk.injEq] at h <;> simp only [σ₁, hs] <;> exact h.2.symm

/-! ### Reading the storage `addRecent` leaves -/

theorem set_ne (σ : Store) {k k' : Bytes} (v : Option Bytes) (h : k' ≠ k) : σ.set k v k' = σ k' := by
  simp [Store.set, h]

theorem set_eq (σ : Store) (k : Bytes) (v : Option Bytes) : σ.set k v k = v := by
  simp [Store.set]

/-- The storage `addRecent` leaves, read under bootstrap's own keys. -/
theorem addRecent_counter (C : Consts) (p : Bytes) (it : Nat) (σ σ' : Store) (u : Unit)
    (hM0 : 0 < C.maxRecent) (hM : C.maxRecent ≤ 2 ^ 32)
    (h : Store.run (addRecent C p it) σ = some (u, σ')) :
    counter σ' = (counter σ + 1) % C.maxRecent := by
  have : (counter σ + 1) % C.maxRecent < 2 ^ 32 := by
    have := Nat.mod_lt (counter σ + 1) hM0; omega
  rw [addRecent_run C p it σ σ' u h]
  show ((Store.set _ Key.counter.encode _ Key.counter.encode).bind _).getD 0 = _
  rw [set_eq, Option.bind_some, decode_counter _ this]; rfl

/-- Slot i after `addRecent`: the new entry at the old counter, every other slot below 2^32 as it
    was. -/
theorem addRecent_slot (C : Consts) (p : Bytes) (it : Nat) (σ σ' : Store) (u : Unit)
    (hp : p.length = 32) (h : Store.run (addRecent C p it) σ = some (u, σ')) (i : Nat)
    (hi : i < 2 ^ 32) (hc : counter σ < 2 ^ 32) :
    slot σ' i = if i = counter σ then some (p, it % 2 ^ 16) else slot σ i := by
  rw [addRecent_run C p it σ σ' u h]
  unfold slot
  rw [set_ne _ _ (Key.recent_ne_counter i)]
  by_cases he : i = counter σ
  · subst he; rw [Dec.ite_pos' rfl, set_eq, Option.bind_some, decode_recent p it hp]
  · rw [Dec.ite_neg' he, set_ne _ _ (fun e => he (Key.recent_inj hi hc e))]
    generalize (σ (Key.recent (counter σ)).encode).bind (decode recentDec) = o
    rcases o with _ | ⟨q, j⟩
    · rfl
    · show (σ.set (Key.results q j).encode none (Key.recent i).encode).bind _ = _
      rw [set_ne _ _ (Key.results_ne_recent q j i).symm]

/-- **S1 (ring half) is preserved by `addRecent`**: if the occupied slots are `[0, c)` or all of them
    before, they are `[0, c')` or all of them after, where c' is the new counter. Assumes the ring
    has between 1 and 2^32 slots (on chain `maxRecent` = 2·𝖢·𝖨) and the package hash is 32 octets
    (as it is when `onWorkItem` calls `addRecent`: `Dec.item` reads it with `take 32`). -/
theorem addRecent_ringInv (C : Consts) (p : Bytes) (it : Nat) (σ σ' : Store) (u : Unit)
    (hM0 : 0 < C.maxRecent) (hM : C.maxRecent ≤ 2 ^ 32) (hp : p.length = 32)
    (hinv : RingInv C σ) (h : Store.run (addRecent C p it) σ = some (u, σ')) : RingInv C σ' := by
  obtain ⟨hc, hocc⟩ := hinv
  have hcnt := addRecent_counter C p it σ σ' u hM0 hM h
  have hslot : ∀ i < C.maxRecent, occupied σ' i ↔ i = counter σ ∨ occupied σ i := by
    intro i hi
    simp only [occupied, addRecent_slot C p it σ σ' u hp h i (by omega) (by omega)]
    by_cases he : i = counter σ <;> simp [he]
  refine ⟨hcnt ▸ Nat.mod_lt _ hM0, ?_⟩
  rcases hocc with ha | hb
  · by_cases hlast : counter σ + 1 < C.maxRecent
    · left
      intro i hi
      rw [hslot i hi, ha i hi, hcnt, Nat.mod_eq_of_lt hlast]
      omega
    · right
      intro i hi
      rw [hslot i hi, ha i hi]
      omega
  · right
    intro i hi
    exact (hslot i hi).2 (Or.inr (hb i hi))

/-! ### The results half

S1's other half says each occupied slot's results key is present. `addRecent` alone does not
preserve it: it fills slot c before the new entry's results are stored (`onWorkItem` stores them
next), and it removes the results of the entry it replaces, which another slot may also hold. What
it does preserve is every other slot's results key. -/

/-- Each occupied slot below `maxRecent` has its results key present. -/
def ResultsInv (C : Consts) (σ : Store) : Prop :=
  ∀ i < C.maxRecent, ∀ q j, slot σ i = some (q, j) → (σ (Key.results q j).encode).isSome

theorem slot_some {σ : Store} {i : Nat} {q : Bytes} {j : Nat} (h : slot σ i = some (q, j)) :
    q.length = 32 ∧ j < 2 ^ 16 := by
  unfold slot at h
  generalize σ (Key.recent i).encode = o at h
  rcases o with _ | b
  · cases h
  simp only [Option.bind_some, decode, recentDec] at h
  rcases ht : (Dec.take 32).run b with _ | ⟨q', b'⟩
  · rw [Dec.bind_of_none ht] at h; cases h
  rcases hf : (Dec.fixedN 2).run b' with _ | ⟨j', b''⟩
  · rw [Dec.bind_of_run ht, Dec.bind_of_none hf] at h; cases h
  rw [Dec.bind_of_run ht, Dec.bind_of_run hf] at h
  simp only [Dec.run_pure', Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨Dec.take_some ht, Dec.fixedN_some hf⟩

/-- **`addRecent` keeps the results key of every other slot**: after `addRecent`, an occupied slot
    other than the one written still has its results key, unless it holds the entry that was
    replaced. -/
theorem addRecent_results (C : Consts) (p : Bytes) (it : Nat) (σ σ' : Store) (u : Unit)
    (hM : C.maxRecent ≤ 2 ^ 32) (hp : p.length = 32) (hc : counter σ < C.maxRecent)
    (hres : ResultsInv C σ) (h : Store.run (addRecent C p it) σ = some (u, σ')) :
    ∀ i < C.maxRecent, i ≠ counter σ → ∀ q j, slot σ' i = some (q, j) →
      slot σ (counter σ) ≠ some (q, j) → (σ' (Key.results q j).encode).isSome := by
  intro i hi hne q j hs hold
  rw [addRecent_slot C p it σ σ' u hp h i (by omega) (by omega), Dec.ite_neg' hne] at hs
  have hpres := hres i hi q j hs
  rw [addRecent_run C p it σ σ' u h]
  rw [set_ne _ _ (Key.results_ne_counter q j), set_ne _ _ (Key.results_ne_recent q j _)]
  rcases heq : slot σ (counter σ) with _ | ⟨q0, j0⟩
  · simpa only [heq] using hpres
  · have hk : (Key.results q j).encode ≠ (Key.results q0 j0).encode := fun e =>
      hold (heq.trans (by rw [Key.results_inj (slot_some heq) (slot_some hs) e.symm]))
    simpa only [heq, set_ne _ _ hk] using hpres

end Services.Bootstrap.Spec
