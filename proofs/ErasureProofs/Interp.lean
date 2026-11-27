import ErasureProofs.Tables

/-!
# The model's interpolation is Lagrange interpolation (GP v0.8.1 §H.3)

`JAM.Erasure.lagrange src tgt` builds, for each target index t, the row L_s(x_t) of Lagrange
weights for the source points x_s (barycentric form, with an indicator row when x_t is a source
point), and `interpolate` applies it to words. Through `φ ∘ toField` this is evaluation of
Mathlib's `Lagrange.interpolate` at x_t (`interpolate_lagrange`), whenever the source indices are
distinct numbers below 2¹⁶.
-/

open Polynomial

namespace JAM.Erasure.Proofs

/-- The field element of an index or word (GP §H.2: m̃, through the Cantor basis). -/
noncomputable def X (i : ℕ) : K := φ (toField i)

theorem one_add_one_K : (1 : K) + 1 = 0 := by
  rw [← φ_one, ← φ_xor]; simp

theorem add_eq_sub_K (a b : K) : a + b = a - b := by
  have : b = -b := eq_neg_of_add_eq_zero_left (by
    rw [← mul_one b, ← mul_add, one_add_one_K, mul_zero])
  rw [sub_eq_add_neg, ← this]

theorem add_ne_zero_K {a b : K} (h : a ≠ b) : a + b ≠ 0 := by
  rw [add_eq_sub_K]; exact sub_ne_zero.2 h

theorem getElem!_eq {β : Type} [Inhabited β] (l : List β) {i : ℕ} (hi : i < l.length) :
    l[i]! = l[i] := getElem!_pos l i hi

theorem arr_getElem!_eq {β : Type} [Inhabited β] (a : Array β) {i : ℕ} (hi : i < a.size) :
    a[i]! = a[i] := getElem!_pos a i hi

/-! ## The folds inside `lagrange` and `interpolate` -/

/-- The step of the weight loop: multiply by x_s − x_r except at r = s. -/
def wstep (xsv s : ℕ) : ℕ × ℕ → ℕ → ℕ × ℕ := fun x xr =>
  (if x.2 = s then x.1 else GF.mul x.1 (GF.add xsv xr), x.2 + 1)

theorem wstep_fold (xsv s : ℕ) (hxs : W xsv) (L : List ℕ) (hL : ∀ y ∈ L, W y) (a r0 : ℕ)
    (ha : W a) :
    W (L.foldl (wstep xsv s) (a, r0)).1 ∧
    φ (L.foldl (wstep xsv s) (a, r0)).1 =
      φ a * ∏ k ∈ Finset.range L.length, (if r0 + k = s then 1 else φ xsv + φ L[k]!) := by
  induction L generalizing a r0 with
  | nil => simp [ha]
  | cons y L ih =>
    have hy : W y := hL y (by simp)
    have hL' : ∀ z ∈ L, W z := fun z hz => hL z (by simp [hz])
    rw [List.foldl_cons]
    have hstep : wstep xsv s (a, r0) y =
        (if r0 = s then a else GF.mul a (GF.add xsv y), r0 + 1) := rfl
    have ha' : W (if r0 = s then a else GF.mul a (GF.add xsv y)) := by
      split
      · exact ha
      · exact mul_lt _ _
    obtain ⟨h1, h2⟩ := ih hL' _ (r0 + 1) ha'
    rw [hstep]
    refine ⟨h1, ?_⟩
    rw [h2, List.length_cons, Finset.prod_range_succ']
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.add_zero]
    have hk : ∀ k, r0 + 1 + k = r0 + (k + 1) := fun k => by omega
    simp only [hk]
    split
    · simp
    · rw [φ_mul ha (add_lt hxs hy), φ_add]; ring

theorem nodal_fold (x : ℕ) (hx : W x) (L : List ℕ) (hL : ∀ y ∈ L, W y) (a : ℕ) (ha : W a) :
    W (L.foldl (fun acc xr => GF.mul acc (GF.add x xr)) a) ∧
    φ (L.foldl (fun acc xr => GF.mul acc (GF.add x xr)) a) =
      φ a * ∏ k ∈ Finset.range L.length, (φ x + φ L[k]!) := by
  induction L generalizing a with
  | nil => simp [ha]
  | cons y L ih =>
    have hy : W y := hL y (by simp)
    obtain ⟨h1, h2⟩ := ih (fun z hz => hL z (by simp [hz])) _ (mul_lt a (GF.add x y))
    rw [List.foldl_cons]
    refine ⟨h1, ?_⟩
    rw [h2, List.length_cons, Finset.prod_range_succ', φ_mul ha (add_lt hx hy), φ_add]
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    ring

theorem interp_fold (row ys : Array ℕ) (n : ℕ) (hrow : ∀ s < n, W row[s]!)
    (hys : ∀ s < n, W ys[s]!) :
    W ((List.range n).foldl (fun acc s => GF.add acc (GF.mul row[s]! ys[s]!)) 0) ∧
    φ ((List.range n).foldl (fun acc s => GF.add acc (GF.mul row[s]! ys[s]!)) 0) =
      ∑ s ∈ Finset.range n, φ row[s]! * φ ys[s]! := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fun s hs => hrow s (by omega)) (fun s hs => hys s (by omega))
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨add_lt h1 (mul_lt _ _), ?_⟩
    rw [φ_add, h2, φ_mul (hrow n (by omega)) (hys n (by omega)), Finset.sum_range_succ]

/-! ## Rows of `lagrange` -/

/-- The nodes of `lagrange src _`: x_k for the k-th source index. -/
noncomputable def nodes (src : List ℕ) (k : ℕ) : K := X src[k]!

theorem nodes_injOn (src : List ℕ) (hsrc : src.Nodup) (hW : ∀ i ∈ src, W i) :
    Set.InjOn (nodes src) ↑(Finset.range src.length) := by
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  unfold nodes X at h
  rw [getElem!_eq src ha, getElem!_eq src hb] at h
  have h1 := φ_injOn (toField_lt _) (toField_lt _) h
  have h2 := toField_injOn (hW _ (List.getElem_mem ha)) (hW _ (List.getElem_mem hb)) h1
  exact (hsrc.getElem_inj_iff).1 h2

theorem srcF_get (src : List ℕ) {k : ℕ} (hk : k < src.length) :
    (src.map toField)[k]! = toField src[k]! := by
  rw [getElem!_eq _ (by simpa using hk), List.getElem_map, getElem!_eq src hk]

theorem srcF_W (src : List ℕ) : ∀ y ∈ src.map toField, W y := by
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨i, _, rfl⟩ := hy
  exact toField_lt i

theorem prod_ite_erase (n s : ℕ) (g : ℕ → K) :
    ∏ k ∈ Finset.range n, (if k = s then 1 else g k) = ∏ k ∈ (Finset.range n).erase s, g k := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.filter_ne']

/-- Row q of `lagrange src tgt` holds the values at x_{tgt[q]} of the Lagrange basis
    polynomials of the source points. -/
theorem lagrange_row (src tgt : List ℕ) (hsrc : src.Nodup) (hW : ∀ i ∈ src, W i) {q : ℕ}
    (hq : q < tgt.length) :
    ((lagrange src tgt)[q]!).size = src.length ∧
    ∀ s < src.length, W ((lagrange src tgt)[q]!)[s]! ∧
      φ ((lagrange src tgt)[q]!)[s]! =
        eval (X tgt[q]) (Lagrange.basis (Finset.range src.length) (nodes src) s) := by
  have hinj := nodes_injOn src hsrc hW
  rw [lagrange_eq_old]
  dsimp only
  rw [toArray_map_get _ _ hq]
  split
  · -- x_t is the source point s₀: the indicator row
    rename_i s0 hs0
    rw [Array.findIdx?_eq_some_iff_getElem] at hs0
    obtain ⟨hs0n, hbeq, _⟩ := hs0
    simp only [List.size_toArray, List.length_map] at hs0n
    have hx : X tgt[q] = nodes src s0 := by
      unfold nodes X
      simp only [List.getElem_toArray, List.getElem_map, beq_iff_eq] at hbeq
      rw [getElem!_eq src hs0n, hbeq]
    refine ⟨by simp, fun s hs => ?_⟩
    rw [arr_getElem!_eq _ (by simpa using hs)]
    simp only [Array.getElem_map, Array.getElem_range]
    rw [hx]
    split
    · rename_i h; subst h
      exact ⟨by decide, by rw [φ_one, Lagrange.eval_basis_self hinj (by simpa using hs0n)]⟩
    · rename_i h
      exact ⟨by decide, by
        rw [φ_zero, Lagrange.eval_basis_of_ne h (by simpa using hs0n)]⟩
  · -- x_t is not a source point: the barycentric form
    rename_i hnone
    rw [Array.findIdx?_eq_none_iff] at hnone
    refine ⟨by simp, fun s hs => ?_⟩
    rw [arr_getElem!_eq _ (by simpa using hs)]
    simp only [Array.getElem_map, Array.getElem_range]
    have hxs : X tgt[q] ≠ nodes src s := by
      intro h
      unfold nodes X at h
      rw [getElem!_eq src hs] at h
      have h' := φ_injOn (toField_lt _) (toField_lt _) h
      have := hnone (toField src[s])
        (by rw [List.mem_toArray, List.mem_map]; exact ⟨src[s], List.getElem_mem hs, rfl⟩)
      simp [h'] at this
    try simp only [List.toList_toArray]
    -- the pieces
    have hxW : W (toField tgt[q]) := toField_lt _
    have hsW : W (toField src[s]) := toField_lt _
    obtain ⟨hlW, hl⟩ := nodal_fold _ hxW _ (srcF_W src) 1 (by decide)
    have hwfold := wstep_fold (toField src[s]) s hsW _ (srcF_W src) 1 0 (by decide)
    have hxsE : (Array.mapIdx (fun s xsv => GF.inv (Array.foldl (fun x xr =>
        (if x.2 = s then x.1 else GF.mul x.1 (GF.add xsv xr), x.2 + 1)) (1, 0)
        (List.map toField src).toArray).1) (List.map toField src).toArray)[s]! =
        GF.inv (List.foldl (wstep (toField src[s]) s) (1, 0) (List.map toField src)).1 := by
      rw [arr_getElem!_eq _ (by simpa using hs), Array.getElem_mapIdx, ← Array.foldl_toList,
        List.toList_toArray]
      simp only [List.getElem_toArray, List.getElem_map]
      rfl
    rw [hxsE, ← Array.foldl_toList, List.toList_toArray]
    obtain ⟨hwW, hw⟩ := hwfold
    simp only [List.length_map, zero_add] at hw hl
    -- the weight's argument is nonzero
    have hprod_ne : φ (List.foldl (wstep (toField src[s]) s) (1, 0) (List.map toField src)).1 ≠ 0 := by
      rw [hw, φ_one, one_mul, Finset.prod_ne_zero_iff]
      intro k hk
      split
      · exact one_ne_zero
      · rename_i hks
        apply add_ne_zero_K
        intro h
        have hk' := Finset.mem_range.1 hk
        rw [srcF_get src hk'] at h
        apply hks
        have := hinj (Finset.mem_coe.2 (Finset.mem_range.2 hs)) (Finset.mem_coe.2 hk)
          (by unfold nodes X; rw [getElem!_eq src hs]; exact h)
        exact this.symm
    have hnz : (List.foldl (wstep (toField src[s]) s) (1, 0) (List.map toField src)).1 ≠ 0 :=
      fun h => hprod_ne (by rw [h, φ_zero])
    have hadd_ne : GF.add (toField tgt[q]) ((List.map toField src).toArray[s]!) ≠ 0 := by
      intro h
      have := congrArg φ h
      rw [φ_add, φ_zero, arr_getElem!_eq _ (by simpa using hs)] at this
      simp only [List.getElem_toArray, List.getElem_map] at this
      apply add_ne_zero_K hxs
      unfold nodes X; rw [getElem!_eq src hs]; exact this
    have haddW : W (GF.add (toField tgt[q]) ((List.map toField src).toArray[s]!)) :=
      add_lt hxW (by rw [arr_getElem!_eq _ (by simpa using hs)]; simp [toField_lt])
    refine ⟨mul_lt _ _, ?_⟩
    rw [φ_mul hlW (mul_lt _ _), φ_mul (inv_lt _) (inv_lt _), φ_inv hwW hnz, φ_inv haddW hadd_ne,
      hl, hw, φ_add, arr_getElem!_eq _ (by simpa using hs)]
    simp only [List.getElem_toArray, List.getElem_map, φ_one, one_mul]
    rw [Lagrange.eval_basis_not_at_node (Finset.mem_range.2 hs) hxs, Lagrange.eval_nodal]
    unfold Lagrange.nodalWeight
    rw [Finset.prod_inv_distrib]
    have e1 : ∏ k ∈ Finset.range src.length, (φ (toField tgt[q]) + φ (List.map toField src)[k]!) =
        ∏ i ∈ Finset.range src.length, (X tgt[q] - nodes src i) := by
      apply Finset.prod_congr rfl; intro k hk
      rw [srcF_get src (Finset.mem_range.1 hk), add_eq_sub_K]; rfl
    have e2 : ∏ k ∈ Finset.range src.length,
        (if k = s then 1 else φ (toField src[s]) + φ (List.map toField src)[k]!) =
        ∏ j ∈ (Finset.range src.length).erase s, (nodes src s - nodes src j) := by
      rw [prod_ite_erase]
      apply Finset.prod_congr rfl; intro k hk
      rw [srcF_get src (Finset.mem_range.1 (Finset.mem_of_mem_erase hk)), add_eq_sub_K]
      unfold nodes X; rw [getElem!_eq src hs]
    have e3 : φ (toField tgt[q]) + φ (toField src[s]) = X tgt[q] - nodes src s := by
      rw [add_eq_sub_K]; unfold nodes X; rw [getElem!_eq src hs]
    rw [e1, e2, e3]

/-! ## `interpolate` -/

theorem interpolate_get (m : Array (Array ℕ)) (words : Array ℕ) {q : ℕ} (hq : q < m.size) :
    (interpolate m words)[q]! = ofField ((List.range (m[q]!).size).foldl
      (fun acc s => GF.add acc (GF.mul (m[q]!)[s]! (words.map toField)[s]!)) 0) := by
  rw [interpolate_eq_old]
  rw [arr_getElem!_eq _ (by simpa using hq), Array.getElem_map, arr_getElem!_eq _ hq]

theorem lagrange_size (src tgt : List ℕ) : (lagrange src tgt).size = tgt.length := by
  rw [lagrange_eq_old]; simp

/-- `interpolate (lagrange src tgt) words` evaluates, at x_t for each target index t, the
    polynomial of degree < |src| through the points (x_{src[k]}, words[k]~): Mathlib's
    `Lagrange.interpolate`. The source indices must be distinct and below 2¹⁶. -/
theorem interpolate_lagrange (src tgt : List ℕ) (words : Array ℕ) (hsrc : src.Nodup)
    (hW : ∀ i ∈ src, W i) (hwords : words.size = src.length) {q : ℕ} (hq : q < tgt.length) :
    W ((interpolate (lagrange src tgt) words)[q]!) ∧
    X ((interpolate (lagrange src tgt) words)[q]!) =
      eval (X tgt[q]) (Lagrange.interpolate (Finset.range src.length) (nodes src)
        (fun k => X words[k]!)) := by
  obtain ⟨hsize, hrow⟩ := lagrange_row src tgt hsrc hW hq
  rw [interpolate_get _ _ (by rw [lagrange_size]; exact hq), hsize]
  have hys : ∀ s < src.length, (words.map toField)[s]! = toField words[s]! := by
    intro s hs
    rw [arr_getElem!_eq _ (by simp; omega), Array.getElem_map, arr_getElem!_eq _ (by omega)]
  obtain ⟨hfW, hf⟩ := interp_fold ((lagrange src tgt)[q]!) (words.map toField) src.length
    (fun s hs => (hrow s hs).1) (fun s hs => by rw [hys s hs]; exact toField_lt _)
  refine ⟨ofField_lt hfW, ?_⟩
  unfold X
  rw [toField_ofField hfW, hf, Lagrange.interpolate_apply, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := Finset.mem_range.1 hs
  rw [(hrow s hs').2, hys s hs', eval_mul, eval_C, mul_comm]
  rfl

/-! ## Reads in bounds

`JAM.Erasure` reads its tables and arrays with `getD … 0`. Every read is in bounds where the model
makes it: the tables have their full sizes, a field element is below 2¹⁶, and the arrays read in
`lagrange`, `interpolate`, `encodeWith` and `recover` are as long as the index range. So the default
is never used. -/

theorem expTable_size : GF.expTable.size = 65535 := by rw [expTable_eq]; simp

theorem logTable_size : GF.logTable.size = 65536 := by rw [logTable_eq, size_set_fold]; simp

theorem toFieldTable_size : GF.toFieldTable.size = 65536 := by simp [GF.toFieldTable]

theorem ofFieldTable_size : GF.ofFieldTable.size = 65536 := by rw [ofFieldTable_eq, size_set_fold]; simp

theorem cantor_size : GF.cantor.size = 16 := by simp [GF.cantor, GF.cantorExponents]

/-- `GF.logTable`'s loop reads `expTable` at i < 2¹⁶ − 1. -/
theorem logTable_reads {i : ℕ} (hi : i < 65535) : i < GF.expTable.size := by
  rw [expTable_size]; exact hi

/-- `GF.mul` reads the logarithm table at its (nonzero) field-element arguments, and the
    exponential table below 2¹⁶ − 1. -/
theorem mul_reads {a b : ℕ} (ha : W a) (hb : W b) :
    a < GF.logTable.size ∧ b < GF.logTable.size ∧
      (GF.logTable.getD a 0 + GF.logTable.getD b 0) % 65535 < GF.expTable.size := by
  rw [logTable_size, expTable_size]; exact ⟨ha, hb, Nat.mod_lt _ (by norm_num)⟩

/-- `GF.inv` reads the logarithm table at its field-element argument. -/
theorem inv_reads {a : ℕ} (ha : W a) :
    a < GF.logTable.size ∧ (65535 - GF.logTable.getD a 0) % 65535 < GF.expTable.size := by
  rw [logTable_size, expTable_size]; exact ⟨ha, Nat.mod_lt _ (by norm_num)⟩

/-- `GF.toFieldTable` reads the Cantor basis at j < 16. -/
theorem toFieldTable_reads {j : ℕ} (hj : j < 16) : j < GF.cantor.size := by
  rw [cantor_size]; exact hj

/-- `GF.ofFieldTable`'s loop and `GF.cantorIsBasis` read `toFieldTable` below 2¹⁶ and
    `ofFieldTable` at its entries. -/
theorem ofFieldTable_reads {m : ℕ} (hm : W m) :
    m < GF.toFieldTable.size ∧ GF.toFieldTable.getD m 0 < GF.ofFieldTable.size := by
  refine ⟨by rw [toFieldTable_size]; exact hm, ?_⟩
  have h := toField_lt m
  rw [toField_eq_old, Nat.mod_eq_of_lt hm, Array.getElem!_eq_getD] at h
  rw [ofFieldTable_size]; exact h

/-- `toField` and `ofField` read their tables below 2¹⁶. -/
theorem toField_reads (m : ℕ) : m % 65536 < GF.toFieldTable.size ∧ m % 65536 < GF.ofFieldTable.size := by
  rw [toFieldTable_size, ofFieldTable_size]; exact ⟨Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num)⟩

/-- `lagrange` reads the weights and the nodes at s < |nodes|. -/
theorem lagrange_reads (xs : Array ℕ) (f : ℕ → ℕ → ℕ) {s : ℕ} (hs : s < xs.size) :
    s < (xs.mapIdx f).size ∧ s < xs.size := by
  simp [hs]

/-- `interpolate` reads the source words at s below a row's length; the rows of `lagrange src _`
    are |src| long (`lagrange_row`), which is the number of words `encodeWith` and `recover`
    pass. -/
theorem interpolate_reads (row words : Array ℕ) (h : row.size ≤ words.size) {s : ℕ}
    (hs : s < row.size) : s < row.size ∧ s < (words.map toField).size := by
  simp; omega

/-- `encodeWith` and `recover` read each interpolated piece at an index below the number of rows of
    the weights. -/
theorem interpolate_size (m : Array (Array ℕ)) (w : Array ℕ) : (interpolate m w).size = m.size := by
  simp [interpolate]

theorem recover_reads (src : List ℕ) (w : Array ℕ) {d j : ℕ} (hj : j < d) :
    j < (interpolate (lagrange src (List.range d)) w).size := by
  rw [interpolate_size, lagrange_size, List.length_range]; exact hj

/-- `word` reads octets 2kj + 2p and 2kj + 2p + 1 of the 2kd octets `encodeWith` splits, and
    octets 2p and 2p + 1 of a 2k-octet chunk in `recover`, for p < k and j < d. -/
theorem word_reads {k d j p : ℕ} (hp : p < k) (hj : j < d) :
    2 * k * j + 2 * p + 1 < 2 * k * d ∧ 2 * p + 1 < 2 * k := by
  constructor
  · have : 2 * k * j + 2 * k ≤ 2 * k * d := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
    omega
  · omega

end JAM.Erasure.Proofs
