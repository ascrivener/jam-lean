import ErasureProofs.Field

/-!
# The model's tables agree with the field (GP v0.8.1 §H.2)

`JAM.Erasure.GF` computes with tables built by loops (`expTable`, `logTable`, `toFieldTable`,
`ofFieldTable`). The tables are never evaluated here: each loop is rewritten to a fold and its
result is described by an invariant. From that:

* `GF.add`, `GF.mul` and `GF.inv` are +, · and ⁻¹ of `K` through `φ` (`φ_add`, `φ_mul`, `φ_inv`);
* `toField` and `ofField` (the Cantor basis, §H.2) are mutually inverse bijections of the numbers
  below 2¹⁶ (`ofField_toField`, `toField_ofField`).
-/

open Polynomial

namespace JAM.Erasure.Proofs

/-- Numbers below 2¹⁶, the representatives of field elements and words. -/
abbrev W (a : ℕ) : Prop := a < 65536

/-! ## Loops as folds -/

theorem forIn_range0 {β : Type} (n : ℕ) (init : β) (f : ℕ → β → Id (ForInStep β)) :
    forIn [0:n] init f = forIn (List.range' 0 n) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; simp [Std.Legacy.Range.size]

theorem ite_pure' {β : Type} {c : Prop} [Decidable c] (a b : β) :
    (if c then (pure a : Id β) else pure b) = pure (if c then a else b) := by split <;> rfl

theorem ite_yield {β : Type} {c : Prop} [Decidable c] (a b : β) :
    (if c then ForInStep.yield a else ForInStep.yield b) = ForInStep.yield (if c then a else b) := by
  split <;> rfl

/-- `GF.expTable`'s loop, for any length (stated generically so that no large literal is reduced). -/
theorem exp_loop (n m : ℕ) : (Id.run do
    let mut t : Array Nat := Array.mkEmpty m
    let mut x := 1
    for _ in [0:n] do
      t := t.push x
      x := x <<< 1
      if x &&& 0x10000 ≠ 0 then x := x ^^^ GF.poly
    return t) = ((List.range' 0 n).foldl (fun b _ => (b.1.push b.2, xt b.2))
      (Array.mkEmpty m, 1)).1 := by
  have hb : ∀ (b : Array ℕ × ℕ), (if b.2 <<< 1 &&& 65536 ≠ 0 then (b.1.push b.2, b.2 <<< 1 ^^^ GF.poly)
      else (b.1.push b.2, b.2 <<< 1)) = (b.1.push b.2, xt b.2) := by
    intro b; unfold xt; split <;> rfl
  simp only [Id.run, forIn_range0, ite_pure', ite_yield, List.forIn_pure_yield_eq_foldl, hb]
  rfl

theorem exp_fold (l : List ℕ) (t : Array ℕ) (x : ℕ) :
    (l.foldl (fun b _ => (b.1.push b.2, xt b.2)) (t, x)).1.toList =
      t.toList ++ (List.range l.length).map (fun i => xt^[i] x) := by
  induction l generalizing t x with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map, Array.toList_push,
      List.append_assoc, List.map_cons, List.map_map]
    congr 2

/-- The i-th power of α as a number: `xt` applied i times to 1. -/
def E (i : ℕ) : ℕ := xt^[i] 1

theorem expTable_eq : GF.expTable = ((List.range 65535).map E).toArray := by
  have h : GF.expTable = ((List.range' 0 65535).foldl (fun b _ => (b.1.push b.2, xt b.2))
      (Array.mkEmpty 65535, 1)).1 := exp_loop 65535 65535
  apply Array.ext'
  rw [h, exp_fold, List.length_range', List.toList_toArray]
  simp only [Array.mkEmpty_eq, Array.toList_empty, List.nil_append]
  rfl

theorem toArray_map_get {β γ : Type} [Inhabited γ] (l : List β) (g : β → γ) {i : ℕ}
    (hi : i < l.length) :
    (l.map g).toArray[i]! = g l[i] := by
  rw [getElem!_pos (l.map g).toArray i (by simpa using hi)]
  simp only [List.getElem_toArray, List.getElem_map]

theorem expTable_get {i : ℕ} (hi : i < 65535) : GF.expTable[i]! = E i := by
  rw [expTable_eq, toArray_map_get _ _ (by rw [List.length_range]; exact hi), List.getElem_range]

theorem E_lt (i : ℕ) : E i < 65536 := iterate_xt_lt i

theorem φ_E (i : ℕ) : φ (E i) = α ^ i := φ_iterate_xt i

theorem E_ne_zero (i : ℕ) : E i ≠ 0 := by
  intro h; have := φ_E i; rw [h, φ_zero] at this; exact α_pow_ne_zero i this.symm

theorem E_injOn {i j : ℕ} (hi : i < 65535) (hj : j < 65535) (h : E i = E j) : i = j :=
  α_pow_injOn hi hj (by rw [← φ_E, ← φ_E, h])

/-- Every nonzero number below 2¹⁶ is a power of α. -/
theorem exists_E {a : ℕ} (ha : a < 65536) (h0 : a ≠ 0) : ∃ i < 65535, E i = a := by
  have hx : φ a ≠ 0 := fun h => h0 (φ_injOn ha (by decide) (by rw [h, φ_zero]))
  obtain ⟨i, hi, he⟩ := eq_α_pow hx
  exact ⟨i, hi, φ_injOn (E_lt i) ha (by rw [φ_E, he])⟩

theorem α_pow_mod (n : ℕ) : α ^ (n % 65535) = α ^ n := by
  conv => rhs; rw [← Nat.div_add_mod n 65535, pow_add, pow_mul, α_pow_65535, one_pow, one_mul]

/-! ## Writing a table with `set!` -/

theorem get_set (t : Array ℕ) (i a v : ℕ) (hi : i < t.size) :
    (t.set! i v)[a]! = if i = a then v else t[a]! := by
  simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds]
  by_cases h : i = a
  · subst h; simp [hi]
  · simp [h]

theorem size_set_fold (e : ℕ → ℕ) (l : List ℕ) (t : Array ℕ) :
    (l.foldl (fun t i => t.set! (e i) i) t).size = t.size := by
  induction l generalizing t with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih]; simp

theorem get_set_fold_other (e : ℕ → ℕ) (l : List ℕ) (t : Array ℕ) (a : ℕ)
    (hl : ∀ i ∈ l, e i < t.size) (ha : ∀ i ∈ l, e i ≠ a) :
    (l.foldl (fun t i => t.set! (e i) i) t)[a]! = t[a]! := by
  induction l generalizing t with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    · rw [get_set _ _ _ _ (hl b (by simp)), if_neg (ha b (by simp))]
    · intro i hi; rw [Array.size_set!]; exact hl i (by simp [hi])
    · intro i hi; exact ha i (by simp [hi])

theorem get_set_fold_hit (e : ℕ → ℕ) (l : List ℕ) (t : Array ℕ) (hn : l.Nodup)
    (hl : ∀ i ∈ l, e i < t.size) (hinj : ∀ i ∈ l, ∀ j ∈ l, e i = e j → i = j) {j : ℕ}
    (hj : j ∈ l) : (l.foldl (fun t i => t.set! (e i) i) t)[e j]! = j := by
  induction l generalizing t with
  | nil => simp at hj
  | cons b l ih =>
    rw [List.foldl_cons]
    rw [List.nodup_cons] at hn
    by_cases hb : j = b
    · subst hb
      rw [get_set_fold_other]
      · rw [get_set _ _ _ _ (hl j (by simp)), if_pos rfl]
      · intro i hi; rw [Array.size_set!]; exact hl i (by simp [hi])
      · intro i hi h
        exact hn.1 (hinj i (by simp [hi]) j (by simp) h ▸ hi)
    · apply ih _ hn.2
      · intro i hi; rw [Array.size_set!]; exact hl i (by simp [hi])
      · intro i hi k hk h; exact hinj i (by simp [hi]) k (by simp [hk]) h
      · simpa [hb] using hj

/-- `GF.logTable`'s loop, for any sizes. -/
theorem log_loop (n m : ℕ) (e : ℕ → ℕ) : (Id.run do
    let mut t : Array Nat := Array.replicate m 0
    for i in [0:n] do
      t := t.set! (e i) i
    return t) = (List.range' 0 n).foldl (fun t i => t.set! (e i) i) (Array.replicate m 0) := by
  simp only [Id.run, forIn_range0, List.forIn_pure_yield_eq_foldl]
  rfl

theorem logTable_eq : GF.logTable =
    (List.range' 0 65535).foldl (fun t i => t.set! GF.expTable[i]! i) (Array.replicate 65536 0) :=
  log_loop 65535 65536 (fun i => GF.expTable[i]!)

theorem logTable_E {i : ℕ} (hi : i < 65535) : GF.logTable[E i]! = i := by
  rw [logTable_eq, ← expTable_get hi]
  apply get_set_fold_hit
  · exact List.nodup_range'
  · intro j hj
    rw [List.mem_range'_1] at hj
    rw [expTable_get (by omega), Array.size_replicate]; exact E_lt j
  · intro a ha b hb h
    rw [List.mem_range'_1] at ha hb
    rw [expTable_get (by omega), expTable_get (by omega)] at h
    exact E_injOn (by omega) (by omega) h
  · rw [List.mem_range'_1]; omega

theorem logTable_zero : GF.logTable[0]! = 0 := by
  rw [logTable_eq, get_set_fold_other]
  · simp
  · intro j hj
    rw [List.mem_range'_1] at hj
    rw [expTable_get (by omega), Array.size_replicate]; exact E_lt j
  · intro j hj
    rw [List.mem_range'_1] at hj
    rw [expTable_get (by omega)]; exact E_ne_zero j

/-! ## The field operations -/

theorem add_lt {a b : ℕ} (ha : W a) (hb : W b) : W (GF.add a b) := xor_lt ha hb

theorem φ_add (a b : ℕ) : φ (GF.add a b) = φ a + φ b := φ_xor a b

theorem mul_lt (a b : ℕ) : W (GF.mul a b) := by
  unfold GF.mul
  split
  · decide
  · rw [expTable_get (Nat.mod_lt _ (by norm_num))]; exact E_lt _

theorem φ_mul {a b : ℕ} (ha : W a) (hb : W b) : φ (GF.mul a b) = φ a * φ b := by
  unfold GF.mul
  split
  · rename_i h
    rcases h with rfl | rfl <;> simp
  · rename_i h
    push_neg at h
    obtain ⟨i, hi, rfl⟩ := exists_E ha h.1
    obtain ⟨j, hj, rfl⟩ := exists_E hb h.2
    rw [logTable_E hi, logTable_E hj, expTable_get (Nat.mod_lt _ (by norm_num)), φ_E,
      α_pow_mod, φ_E, φ_E, pow_add]

theorem inv_lt (a : ℕ) : W (GF.inv a) := by
  unfold GF.inv
  rw [expTable_get (Nat.mod_lt _ (by norm_num))]; exact E_lt _

theorem φ_inv {a : ℕ} (ha : W a) (h0 : a ≠ 0) : φ (GF.inv a) = (φ a)⁻¹ := by
  obtain ⟨i, hi, rfl⟩ := exists_E ha h0
  unfold GF.inv
  rw [logTable_E hi, expTable_get (Nat.mod_lt _ (by norm_num)), φ_E, α_pow_mod, φ_E]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, Nat.sub_add_cancel hi.le, α_pow_65535]

theorem φ_ne_zero {a : ℕ} (ha : W a) (h0 : a ≠ 0) : φ a ≠ 0 :=
  fun h => h0 (φ_injOn ha (by decide) (by rw [h, φ_zero]))

/-! ## The Cantor basis -/

/-- The F₂-linear map sending bit j (j < 16) to `c j`, in the shape of `GF.toFieldTable`. -/
def lin (c : ℕ → ℕ) (m : ℕ) : ℕ :=
  (List.range 16).foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0

theorem lin_fold (c : ℕ → ℕ) (m : ℕ) (l : List ℕ) (acc : ℕ) :
    l.foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) acc =
      acc ^^^ l.foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (if m.testBit a then 0 ^^^ c a else 0)]
    split <;> simp [Nat.xor_assoc]

theorem lin_cons (c : ℕ → ℕ) (m : ℕ) (a : ℕ) (l : List ℕ) :
    (a :: l).foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0 =
      (if m.testBit a then c a else 0) ^^^
        l.foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0 := by
  rw [List.foldl_cons, lin_fold]
  split <;> simp

theorem xor_cancel_aux (c P Q : ℕ) : c ^^^ P ^^^ (c ^^^ Q) = P ^^^ Q := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
  cases c.testBit i <;> cases P.testBit i <;> cases Q.testBit i <;> rfl

theorem linL_xor (c : ℕ → ℕ) (a b : ℕ) (l : List ℕ) :
    l.foldl (fun acc j => if (a ^^^ b).testBit j then acc ^^^ c j else acc) 0 =
      l.foldl (fun acc j => if a.testBit j then acc ^^^ c j else acc) 0 ^^^
        l.foldl (fun acc j => if b.testBit j then acc ^^^ c j else acc) 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [lin_cons, lin_cons, lin_cons, ih, Nat.testBit_xor]
    cases a.testBit x <;> cases b.testBit x <;> simp only [Bool.xor_true, Bool.xor_false,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true, if_false] <;>
      first
        | ac_rfl
        | rw [Nat.zero_xor, xor_cancel_aux]

theorem lin_xor (c : ℕ → ℕ) (a b : ℕ) : lin c (a ^^^ b) = lin c a ^^^ lin c b := linL_xor c a b _

theorem lin_zero (c : ℕ → ℕ) : lin c 0 = 0 := by
  unfold lin; induction (List.range 16) with
  | nil => rfl
  | cons a l ih => rw [lin_cons, ih]; simp

theorem linL_compose (c : ℕ → ℕ) (g : ℕ → ℕ) (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b)
    (m : ℕ) (l : List ℕ) :
    g (l.foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0) =
      l.foldl (fun acc j => if m.testBit j then acc ^^^ g (c j) else acc) 0 := by
  have hg0 : g 0 = 0 := by have := hg 0 0; simpa using this
  induction l with
  | nil => exact hg0
  | cons x l ih =>
    rw [lin_cons, lin_cons, hg, ih]
    split <;> simp [hg0]

theorem linL_congr (c c' : ℕ → ℕ) (m : ℕ) (l : List ℕ) (h : ∀ j ∈ l, c j = c' j) :
    l.foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0 =
      l.foldl (fun acc j => if m.testBit j then acc ^^^ c' j else acc) 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [lin_cons, lin_cons, ih (fun j hj => h j (by simp [hj])), h x (by simp)]

theorem lin_compose (c : ℕ → ℕ) (g : ℕ → ℕ) (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b) (m : ℕ) :
    g (lin c m) = lin (fun j => g (c j)) m := linL_compose c g hg m _

theorem lin_congr (c c' : ℕ → ℕ) (m : ℕ) (h : ∀ j < 16, c j = c' j) : lin c m = lin c' m :=
  linL_congr c c' m _ (fun j hj => h j (List.mem_range.1 hj))

theorem linL_testBit (m i n : ℕ) :
    ((List.range n).foldl (fun acc j => if m.testBit j then acc ^^^ 2 ^ j else acc) 0).testBit i =
      (decide (i < n) && m.testBit i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split
    · rename_i hb
      rw [Nat.testBit_xor, ih, Nat.testBit_two_pow]
      by_cases hin : i = n
      · subst hin; simp [hb]
      · have : (n = i) = False := propext ⟨fun h => hin h.symm, False.elim⟩
        simp only [this, decide_false, Bool.xor_false]
        by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega]
        · simp [hi, show ¬ i < n + 1 by omega]
    · rename_i hb
      rw [ih]
      by_cases hin : i = n
      · subst hin; simp [hb]
      · by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega]
        · simp [hi, show ¬ i < n + 1 by omega]

theorem lin_two_pow {m : ℕ} (hm : W m) : lin (2 ^ ·) m = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold lin
  rw [linL_testBit]
  by_cases hi : i < 16
  · simp [hi]
  · simp [hi, testBit_of_lt hm (show 16 ≤ i by omega)]

theorem linL_lt (c : ℕ → ℕ) (m : ℕ) (l : List ℕ) (hc : ∀ j ∈ l, W (c j)) :
    W (l.foldl (fun acc j => if m.testBit j then acc ^^^ c j else acc) 0) := by
  induction l with
  | nil => exact (by decide : (0 : ℕ) < 65536)
  | cons x l ih =>
    rw [lin_cons]
    apply xor_lt
    · split
      · exact hc x (by simp)
      · exact (by decide : (0 : ℕ) < 65536)
    · exact ih (fun j hj => hc j (by simp [hj]))

theorem lin_lt (c : ℕ → ℕ) (m : ℕ) (hc : ∀ j < 16, W (c j)) : W (lin c m) :=
  linL_lt c m _ (fun j hj => hc j (List.mem_range.1 hj))

/-- The Cantor basis vectors v_j as numbers. -/
def cantorC (j : ℕ) : ℕ := GF.cantor[j]!

/-- The inverse of the Cantor-basis map: column j is the number whose Cantor coordinates are
    the bits of 2^j (computed once; `cantorInv_spec` checks it). -/
def cantorInvCols : List ℕ :=
  [1, 18064, 26072, 25296, 22324, 17904, 21432, 7736, 31918, 20024, 26376, 49756, 31332, 40620,
    4388, 21050]

def cantorInvC (j : ℕ) : ℕ := cantorInvCols[j]!

theorem cantor_check₁ : ∀ j < 16, lin cantorInvC (cantorC j) = 2 ^ j := by decide +kernel

theorem cantor_check₂ : ∀ j < 16, lin cantorC (cantorInvC j) = 2 ^ j := by decide +kernel

theorem cantorC_lt : ∀ j < 16, W (cantorC j) := by decide +kernel

theorem cantorInvC_lt : ∀ j < 16, W (cantorInvC j) := by decide +kernel

theorem lin_inv_lin {c c' : ℕ → ℕ} (h : ∀ j < 16, lin c' (c j) = 2 ^ j) {m : ℕ} (hm : W m) :
    lin c' (lin c m) = m := by
  rw [lin_compose c _ (lin_xor c'), lin_congr _ (2 ^ ·) m h]
  exact lin_two_pow hm

theorem toFieldTable_get {m : ℕ} (hm : W m) : GF.toFieldTable[m]! = lin cantorC m := by
  simp [GF.toFieldTable, hm, lin, cantorC]

theorem toField_eq {m : ℕ} (hm : W m) : toField m = lin cantorC m := by
  rw [toField, Nat.mod_eq_of_lt hm, toFieldTable_get hm]

theorem toField_lt (m : ℕ) : W (toField m) := by
  rw [toField, toFieldTable_get (Nat.mod_lt _ (by norm_num))]; exact lin_lt _ _ cantorC_lt

theorem toField_injOn {a b : ℕ} (ha : W a) (hb : W b) (h : toField a = toField b) : a = b := by
  rw [toField_eq ha, toField_eq hb] at h
  rw [← lin_inv_lin cantor_check₁ ha, ← lin_inv_lin cantor_check₁ hb, h]

theorem of_loop (n m : ℕ) (e : ℕ → ℕ) : (Id.run do
    let mut t : Array Nat := Array.replicate m 0
    for i in [0:n] do
      t := t.set! (e i) i
    return t) = (List.range' 0 n).foldl (fun t i => t.set! (e i) i) (Array.replicate m 0) :=
  log_loop n m e

theorem ofFieldTable_eq : GF.ofFieldTable =
    (List.range' 0 65536).foldl (fun t i => t.set! GF.toFieldTable[i]! i)
      (Array.replicate 65536 0) :=
  of_loop 65536 65536 (fun i => GF.toFieldTable[i]!)

theorem ofField_toField {m : ℕ} (hm : W m) : ofField (toField m) = m := by
  rw [ofField, Nat.mod_eq_of_lt (toField_lt m), toField, Nat.mod_eq_of_lt hm, ofFieldTable_eq]
  apply get_set_fold_hit
  · exact List.nodup_range'
  · intro j hj
    rw [List.mem_range'_1] at hj
    have := toField_lt j
    rw [toField, Nat.mod_eq_of_lt (by omega)] at this
    rw [Array.size_replicate]; exact this
  · intro a ha b hb h
    rw [List.mem_range'_1] at ha hb
    have h' : toField a = toField b := by
      rw [toField, toField, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact h
    exact toField_injOn (by simp; omega) (by simp; omega) h'
  · rw [List.mem_range'_1]; omega

theorem toField_ofField {y : ℕ} (hy : W y) : toField (ofField y) = y := by
  have hm : W (lin cantorInvC y) := lin_lt _ _ cantorInvC_lt
  have : toField (lin cantorInvC y) = y := by rw [toField_eq hm]; exact lin_inv_lin cantor_check₂ hy
  rw [← this, ofField_toField hm]

theorem ofField_lt {y : ℕ} (hy : W y) : W (ofField y) := by
  have hm : W (lin cantorInvC y) := lin_lt _ _ cantorInvC_lt
  have : toField (lin cantorInvC y) = y := by rw [toField_eq hm]; exact lin_inv_lin cantor_check₂ hy
  rw [← this, ofField_toField hm]; exact hm

theorem toField_zero : toField 0 = 0 := by
  rw [toField_eq (by decide)]; exact lin_zero _

end JAM.Erasure.Proofs
