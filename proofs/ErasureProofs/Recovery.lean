import ErasureProofs.Interp

/-!
# Recovery inverts encoding (GP v0.8.1 Appendix H, §H.3 as amended by GP #580)

For v validators, d = R(v) and d' = 2^⌈log₂ d⌉ (`originalShards`, `paddedShards`), `encode v`
splits the data into pieces of d message words, takes for each piece the polynomial p of degree
< d' through the message words at 0̃, …, (d−1)~ and zeroes at d̃, …, (d'−1)~, and gives validator
i the word p(g(i)~) (`codeIndex`). `recover v` takes any d of the chunks with their validator
indices, adds the d' − d known zeroes, and interpolates back.

* `encode_word`: every word of every chunk is an evaluation of the piece's polynomial
  `msgPoly`, of degree < d' (`msgPoly_degree_lt`). Any d' distinct points therefore determine it
  (Mathlib's `Lagrange.eq_interpolate_of_eval_eq`): the code is MDS.
* `recover_encode`: for v ≤ 2¹⁵ (so all code indices are distinct field points), any R(v)
  distinct validator indices below v, in any order, with their chunks from `encode v data`,
  recover `data`. `recover_encode_full` (v = 1023, R = 342) and `recover_encode_tiny` (v = 6,
  R = 3) are the two chains of the test vectors.
-/

open Polynomial

namespace JAM.Erasure.Proofs

/-! ## Lists and octets -/

theorem flatMap_getElem? {α β : Type} (L : List α) (f : α → List β) (m : ℕ)
    (hf : ∀ a ∈ L, (f a).length = m) (j r : ℕ) (hr : r < m) :
    (L.flatMap f)[m * j + r]? = L[j]?.bind (fun a => (f a)[r]?) := by
  induction L generalizing j with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons]
    have ha := hf a (by simp)
    cases j with
    | zero =>
      rw [Nat.mul_zero, Nat.zero_add, List.getElem?_append_left (by omega)]
      simp
    | succ j =>
      rw [List.getElem?_append_right (by rw [ha]; nlinarith)]
      have : m * (j + 1) + r - (f a).length = m * j + r := by rw [ha, Nat.mul_succ]; omega
      rw [this, ih (fun b hb => hf b (by simp [hb]))]
      simp

theorem length_flatMap_const {α β : Type} (L : List α) (f : α → List β) (m : ℕ)
    (hf : ∀ a ∈ L, (f a).length = m) : (L.flatMap f).length = m * L.length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.flatMap_cons, List.length_append, hf a (by simp), ih (fun b hb => hf b (by simp [hb])),
      List.length_cons]
    ring

theorem length_wordOctets (c : ℕ) : (wordOctets c).length = 2 := rfl

theorem get!_mk (L : List UInt8) (o : ℕ) : (ByteArray.mk L.toArray).get! o = L[o]! := by
  simp [ByteArray.get!]

theorem word_wordOctets {c : ℕ} (hc : W c) (L : List UInt8) (o : ℕ)
    (h0 : L[o]? = some (UInt8.ofNat c)) (h1 : L[o + 1]? = some (UInt8.ofNat (c / 256))) :
    word (ByteArray.mk L.toArray) o = c := by
  rw [word_eq_old]
  rw [get!_mk, get!_mk, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, h0, h1]
  simp only [Option.getD_some, UInt8.toNat_ofNat']
  omega

theorem wordOctets_word (b : ByteArray) (o e : ℕ) (he : e < 2) :
    (wordOctets (word b o))[e]? = some (b.get! (o + e)) := by
  unfold wordOctets; rw [word_eq_old]
  rcases (by omega : e = 0 ∨ e = 1) with rfl | rfl
  · simp only [List.getElem?_cons_zero, Nat.add_zero, Option.some.injEq]
    rw [← UInt8.toNat_inj, UInt8.toNat_ofNat']
    have := (b.get! o).toNat_lt; omega
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    rw [← UInt8.toNat_inj, UInt8.toNat_ofNat']
    have := (b.get! o).toNat_lt; have := (b.get! (o + 1)).toNat_lt; omega

theorem eraseDups_of_nodup {L : List ℕ} (h : L.Nodup) : L.eraseDups = L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.nodup_cons] at h
    rw [List.eraseDups_cons]
    have : List.filter (fun b => !b == a) L = L := by
      rw [List.filter_eq_self]
      intro b hb
      have : b ≠ a := fun hab => h.1 (hab ▸ hb)
      simp [this]
    rw [this, ih h.2]

/-! ## The parameters R(v), d' and g -/

theorem foldl_max_ge (l : List ℕ) (a x : ℕ) (hx : x ∈ l ∨ x ≤ a) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simpa using hx
  | cons y l ih =>
    rw [List.foldl_cons]
    apply ih
    rcases hx with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (le_max_right _ _)
      · exact Or.inl h
    · exact Or.inr (le_trans h (le_max_left _ _))

theorem foldl_max_le (l : List ℕ) (a b : ℕ) (ha : a ≤ b) (hl : ∀ y ∈ l, y ≤ b) :
    l.foldl max a ≤ b := by
  induction l generalizing a with
  | nil => exact ha
  | cons y l ih =>
    rw [List.foldl_cons]
    exact ih _ (max_le ha (hl y (by simp))) (fun z hz => hl z (by simp [hz]))

theorem originalShards_pos (v : ℕ) : 0 < originalShards v := by
  unfold originalShards
  apply lt_of_lt_of_le (show 0 < 1 by norm_num)
  apply foldl_max_ge
  left
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, by norm_num, by decide⟩

theorem originalShards_le (v : ℕ) : originalShards v ≤ v / 3 + 1 := by
  unfold originalShards
  apply foldl_max_le _ _ _ (Nat.zero_le _)
  intro y hy
  simp only [List.mem_filter, List.mem_range] at hy
  omega

theorem padded_loop (d : ℕ) :
    paddedShards d = (List.range' 0 d).foldl (fun n _ => if n < d then 2 * n else n) 1 := by
  unfold paddedShards
  simp only [Id.run, forIn_range0, ite_pure', ite_yield, List.forIn_pure_yield_eq_foldl]
  rfl

theorem padded_inv (d : ℕ) (l : List ℕ) (n k : ℕ) (h1 : 1 ≤ n) (h2 : n < 2 * d)
    (h3 : d ≤ n ∨ n = 2 ^ k) :
    let n' := l.foldl (fun n _ => if n < d then 2 * n else n) n
    1 ≤ n' ∧ n' < 2 * d ∧ (d ≤ n' ∨ n' = 2 ^ (k + l.length)) := by
  induction l generalizing n k with
  | nil => exact ⟨h1, h2, h3⟩
  | cons a l ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (if n < d then 2 * n else n) (k + 1)
    rw [show k + 1 + l.length = k + (l.length + 1) by omega] at this
    apply this
    · split <;> omega
    · split <;> omega
    · split
      · rename_i hnd
        rcases h3 with h | h
        · omega
        · right; rw [h, pow_succ]; ring
      · left; omega

/-- d ≤ d' < 2d (GP v0.8.1 §H.3: d' = 2^⌈log₂ d⌉). -/
theorem paddedShards_bounds {d : ℕ} (hd : 0 < d) : d ≤ paddedShards d ∧ paddedShards d < 2 * d := by
  rw [padded_loop]
  obtain ⟨_, h2, h3⟩ := padded_inv d (List.range' 0 d) 1 0 le_rfl (by omega) (Or.inr rfl)
  refine ⟨?_, h2⟩
  rcases h3 with h | h
  · exact h
  · rw [h, List.length_range', zero_add]; exact Nat.lt_two_pow_self.le

theorem codeIndex_lt {d n j v : ℕ} (hdn : d ≤ n) (hn : paddedShards d = n) (hj : j < v) :
    codeIndex d j < v + n - d := by
  unfold codeIndex; rw [hn]; split <;> omega

theorem codeIndex_inj {d n a b : ℕ} (hdn : d ≤ n) (hn : paddedShards d = n)
    (h : codeIndex d a = codeIndex d b) : a = b := by
  unfold codeIndex at h; rw [hn] at h; split at h <;> split at h <;> omega

theorem codeIndex_not_mem {d n j : ℕ} (hdn : d ≤ n) (hn : paddedShards d = n) :
    codeIndex d j < d ∨ n ≤ codeIndex d j := by
  unfold codeIndex; rw [hn]; split <;> omega

theorem codeIndex_of_lt {d j : ℕ} (hj : j < d) : codeIndex d j = j := by
  unfold codeIndex; rw [if_pos hj]

/-! ## Field points -/

theorem X_injOn {a b : ℕ} (ha : W a) (hb : W b) (h : X a = X b) : a = b :=
  toField_injOn ha hb (φ_injOn (toField_lt a) (toField_lt b) h)

@[simp] theorem X_zero : X 0 = 0 := by unfold X; rw [toField_zero, φ_zero]

theorem nodes_range {n k : ℕ} (hk : k < n) : nodes (List.range n) k = X k := by
  unfold nodes; rw [getElem!_eq _ (by simpa using hk), List.getElem_range]

theorem range_W {n : ℕ} (hn : n ≤ 65536) : ∀ i ∈ List.range n, W i := by
  intro i hi; rw [List.mem_range] at hi; unfold W; omega

/-! ## Encoding -/

section
variable (v : ℕ) (data : ByteArray)

/-- The message words of piece p (out of k), padded with d' − d zeroes (the words `encodeWith`
    interpolates from). -/
def msgWords (k p : ℕ) : Array ℕ :=
  (Array.range (paddedShards (originalShards v))).map fun j =>
    if j < originalShards v then word data (2 * k * j + 2 * p) else 0

/-- The coded words of the pieces: piece p, then one word per validator. -/
def encPieces (k : ℕ) : List (Array ℕ) :=
  (List.range k).map fun p => interpolate (encodeWeights v) (msgWords v data k p)

/-- The polynomial of piece p, of degree < d': message word j at j̃ for j < d, zero at
    d̃, …, (d'−1)~ (GP v0.8.1 §H.3). -/
noncomputable def msgPoly (k p : ℕ) : K[X] :=
  Lagrange.interpolate (Finset.range (paddedShards (originalShards v)))
    (nodes (List.range (paddedShards (originalShards v)))) (fun j => X (msgWords v data k p)[j]!)

end

theorem encodeWeights_size (v : ℕ) : (encodeWeights v).size = v := by
  unfold encodeWeights; rw [lagrange_size]; simp

theorem encode_eq {v : ℕ} {data : ByteArray} {chunks : List ByteArray}
    (henc : encode v data = some chunks) :
    data.size % (2 * originalShards v) = 0 ∧
    chunks = (List.range v).map fun i =>
      ByteArray.mk (((encPieces v data (data.size / (2 * originalShards v))).flatMap
        fun ws => wordOctets ws[i]!).toArray) := by
  unfold encode at henc; rw [encodeWith_eq_old] at henc
  split at henc
  · exact absurd henc (by simp)
  · rename_i h
    push_neg at h
    refine ⟨h.2, ?_⟩
    simp only [Option.some.injEq] at henc
    rw [← henc, encodeWeights_size]
    rfl

theorem msgPoly_degree_lt (v : ℕ) (data : ByteArray) (k p : ℕ) (hv : v ≤ 32768) :
    (msgPoly v data k p).degree < paddedShards (originalShards v) := by
  have hd := originalShards_pos v
  have hb := paddedShards_bounds hd
  have hle := originalShards_le v
  have := Lagrange.degree_interpolate_lt (s := Finset.range (paddedShards (originalShards v)))
    (v := nodes (List.range (paddedShards (originalShards v))))
    (fun j => X (msgWords v data k p)[j]!)
    (by
      have := nodes_injOn (List.range (paddedShards (originalShards v))) List.nodup_range
        (range_W (by omega))
      simpa using this)
  rw [Finset.card_range] at this
  exact this

/-- Every coded word is an evaluation of the piece polynomial: validator i's word of piece p is
    `msgPoly` at g(i)~ (GP v0.8.1 §H.3). -/
theorem encode_word (v : ℕ) (data : ByteArray) (k : ℕ) (hv : v ≤ 32768) {p i : ℕ} (hp : p < k)
    (hi : i < v) :
    W ((encPieces v data k)[p]!)[i]! ∧
    X ((encPieces v data k)[p]!)[i]! = eval (X (codeIndex (originalShards v) i))
      (msgPoly v data k p) := by
  have hd := originalShards_pos v
  have hb := paddedShards_bounds hd
  have hle := originalShards_le v
  unfold encPieces
  rw [getElem!_eq _ (by simpa using hp), List.getElem_map, List.getElem_range]
  have := interpolate_lagrange (List.range (paddedShards (originalShards v)))
    ((List.range v).map (codeIndex (originalShards v))) (msgWords v data k p) List.nodup_range
    (range_W (by omega)) (by simp [msgWords]) (q := i) (by simpa using hi)
  simp only [List.getElem_map, List.getElem_range, List.length_range] at this
  exact this

theorem chunk_word {v : ℕ} {data : ByteArray} {k : ℕ} (hv : v ≤ 32768) {p i : ℕ} (hp : p < k)
    (hi : i < v) :
    word (ByteArray.mk (((encPieces v data k).flatMap fun ws => wordOctets ws[i]!).toArray))
      (2 * p) = ((encPieces v data k)[p]!)[i]! := by
  have hlen : ∀ ws ∈ encPieces v data k, (wordOctets ws[i]!).length = 2 := fun _ _ => rfl
  have hpk : p < (encPieces v data k).length := by simp [encPieces, hp]
  apply word_wordOctets (encode_word v data k hv hp hi).1
  · rw [show 2 * p = 2 * p + 0 from rfl, flatMap_getElem? _ _ 2 hlen p 0 (by norm_num),
      List.getElem?_eq_getElem hpk, getElem!_eq _ hpk]
    rfl
  · rw [flatMap_getElem? _ _ 2 hlen p 1 (by norm_num), List.getElem?_eq_getElem hpk,
      getElem!_eq _ hpk]
    rfl

theorem chunk_size {v : ℕ} {data : ByteArray} {k i : ℕ} :
    (ByteArray.mk (((encPieces v data k).flatMap fun ws => wordOctets ws[i]!).toArray)).size =
      2 * k := by
  show (((encPieces v data k).flatMap fun ws => wordOctets ws[i]!).toArray).size = 2 * k
  rw [List.size_toArray, length_flatMap_const _ _ 2 (fun _ _ => rfl)]
  simp [encPieces]

/-! ## Recovery -/

/-- **Recovery inverts encoding** (GP v0.8.1 eqs. `erasurecoding`, `erasurecodinginv`, §H.3 as
    amended by GP #580). For v ≤ 2¹⁵ validators, if `encode v data = some chunks`, then any
    R(v) distinct validator indices below v, in any order, with their chunks, give back `data`. -/
theorem recover_encode {v : ℕ} (hv : v ≤ 32768) {data : ByteArray} {chunks : List ByteArray}
    (henc : encode v data = some chunks) {J : List ℕ} (hJ : J.Nodup)
    (hlen : J.length = originalShards v) (hJv : ∀ j ∈ J, j < v) :
    recover v (J.map fun j => (chunks[j]!, j)) = some data := by
  obtain ⟨hmod, hchunks⟩ := encode_eq henc
  have hd := originalShards_pos v
  have hle := originalShards_le v
  set d := originalShards v with hd_def
  obtain ⟨hdn, hn2⟩ := paddedShards_bounds hd
  set n := paddedShards d with hn_def
  set k := data.size / (2 * d) with hk_def
  have hsize : data.size = 2 * k * d := by
    have := Nat.div_add_mod data.size (2 * d); rw [hmod] at this; rw [hk_def]; linarith
  -- the chunks
  have hchunk : ∀ j < v, chunks[j]! =
      ByteArray.mk (((encPieces v data k).flatMap fun ws => wordOctets ws[j]!).toArray) := by
    intro j hj
    rw [hchunks, getElem!_eq _ (by simpa using hj), List.getElem_map, List.getElem_range]
  have hcsize : ∀ j < v, (chunks[j]!).size = 2 * k := fun j hj => by rw [hchunk j hj]; exact chunk_size
  have hcword : ∀ j < v, ∀ p < k, word (chunks[j]!) (2 * p) = ((encPieces v data k)[p]!)[j]! :=
    fun j hj p hp => by rw [hchunk j hj]; exact chunk_word hv hp hj
  -- the recovery source points
  set src := J.map (codeIndex d) ++ (List.range (n - d)).map (d + ·) with hsrc_def
  have hsrc_len : src.length = n := by simp [hsrc_def, hlen]; omega
  have hsrc_nodup : src.Nodup := by
    rw [hsrc_def, List.nodup_append]
    refine ⟨hJ.map (fun a b h => codeIndex_inj hdn rfl h), ?_, ?_⟩
    · exact List.nodup_range.map (fun a b h => by omega)
    · intro a ha b hb hab
      simp only [List.mem_map, List.mem_range] at ha hb
      obtain ⟨j, _, rfl⟩ := ha
      obtain ⟨i, hi, rfl⟩ := hb
      rcases codeIndex_not_mem (j := j) hdn rfl with h | h <;> omega
  have hsrc_W : ∀ i ∈ src, W i := by
    intro i hi
    rw [hsrc_def, List.mem_append] at hi
    unfold W
    rcases hi with hi | hi
    · simp only [List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      have := codeIndex_lt hdn rfl (hJv j hj); omega
    · simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨i, hi, rfl⟩ := hi; omega
  have hsrc_get : ∀ t < n, src[t]! = if t < d then codeIndex d J[t]! else t := by
    intro t ht
    rw [List.getElem!_eq_getElem?_getD, hsrc_def]
    split
    · rename_i htd
      rw [List.getElem?_append_left (by simp [hlen]; omega), List.getElem?_map,
        List.getElem?_eq_getElem (by omega), getElem!_eq _ (by omega)]
      rfl
    · rename_i htd
      rw [List.getElem?_append_right (by simp [hlen]; omega), List.getElem?_map,
        List.length_map, hlen, List.getElem?_range (by omega)]
      simp only [Option.map_some, Option.getD_some]
      omega
  -- reduce `recover`
  cases J with
  | nil => simp at hlen; omega
  | cons j0 J' =>
  have hj0 : j0 < v := hJv j0 (by simp)
  -- the recovery words of piece p: the received words, then d' − d zeroes
  set JJ := j0 :: J' with hJJ
  let words2 : ℕ → Array ℕ := fun p =>
    (JJ.map fun j => word chunks[j]! (2 * p)).toArray ++ Array.replicate (n - d) 0
  have hw2size : ∀ p, (words2 p).size = n := by
    intro p; simp [words2, hlen]; omega
  have hw2get : ∀ p, ∀ t < n, (words2 p)[t]! = if t < d then word chunks[JJ[t]!]! (2 * p) else 0 := by
    intro p t ht
    rw [arr_getElem!_eq _ (by rw [hw2size]; exact ht)]
    simp only [words2]
    split
    · rename_i htd
      rw [Array.getElem_append_left (by simp [hlen]; omega)]
      simp only [List.getElem_toArray, List.getElem_map]
      rw [getElem!_eq JJ (by omega)]
    · rename_i htd
      rw [Array.getElem_append_right (by simp [hlen]; omega)]
      simp
  have hJJ_lt : ∀ t < d, JJ[t]! < v := by
    intro t ht; rw [getElem!_eq JJ (by omega)]; exact hJv _ (List.getElem_mem _)
  -- the main step: the recovered word j of piece p is message word j
  have hmain : ∀ p < k, ∀ j < d,
      (interpolate (lagrange src (List.range d)) (words2 p))[j]! = word data (2 * k * j + 2 * p) := by
    intro p hp j hj
    obtain ⟨hresW, hres⟩ := interpolate_lagrange src (List.range d) (words2 p) hsrc_nodup hsrc_W
      (by rw [hw2size, hsrc_len]) (q := j) (by simpa using hj)
    have hinjn := nodes_injOn (List.range n) List.nodup_range (range_W (by omega))
    simp only [List.length_range] at hinjn
    have hR : Lagrange.interpolate (Finset.range src.length) (nodes src)
        (fun t => X (words2 p)[t]!) = msgPoly v data k p := by
      symm
      apply Lagrange.eq_interpolate_of_eval_eq _ (nodes_injOn src hsrc_nodup hsrc_W)
      · rw [Finset.card_range, hsrc_len]; exact msgPoly_degree_lt v data k p hv
      · intro t ht
        rw [Finset.mem_range, hsrc_len] at ht
        unfold nodes
        rw [hsrc_get t ht, hw2get p t ht]
        split
        · rename_i htd
          rw [hcword _ (hJJ_lt t htd) p hp]
          exact ((encode_word v data k hv hp (hJJ_lt t htd)).2).symm
        · rename_i htd
          rw [X_zero, ← nodes_range ht]
          unfold msgPoly
          rw [Lagrange.eval_interpolate_at_node _ hinjn (Finset.mem_range.2 ht)]
          simp only [msgWords]
          rw [arr_getElem!_eq _ (by simpa using ht)]
          simp only [Array.getElem_map, Array.getElem_range]
          rw [if_neg (by rw [← hd_def]; exact htd), X_zero]
    simp only [List.getElem_range] at hres
    rw [hR, ← nodes_range (show j < n by omega)] at hres
    unfold msgPoly at hres
    rw [Lagrange.eval_interpolate_at_node _ hinjn (Finset.mem_range.2 (by omega))] at hres
    have hmw : (msgWords v data k p)[j]! = word data (2 * k * j + 2 * p) := by
      unfold msgWords
      rw [arr_getElem!_eq _ (by simp only [Array.size_map, Array.size_range, ← hd_def, ← hn_def]; omega)]
      simp only [Array.getElem_map, Array.getElem_range]
      rw [if_pos (by rw [← hd_def]; exact hj)]
    rw [hmw] at hres
    apply X_injOn hresW _ hres
    rw [word_eq_old]; unfold W
    have := (data.get! (2 * k * j + 2 * p)).toNat_lt
    have := (data.get! (2 * k * j + 2 * p + 1)).toNat_lt
    omega
  -- reduce `recover`
  rw [recover_eq_old]
  simp only [← hd_def, ← hn_def, List.map_map, Function.comp_def]
  split
  · rename_i heq; simp [hJJ] at heq
  rename_i x0 s0 tl heq
  have hx0 : x0 = chunks[j0]! := by
    simp [hJJ] at heq; rw [List.getElem!_eq_getElem?_getD]; exact heq.1.1.symm
  subst hx0
  rw [if_neg]
  swap
  · simp only [not_or, ne_eq, Decidable.not_not, Bool.not_eq_true, List.any_eq_false,
      decide_eq_false_iff_not, List.length_cons, List.length_map]
    refine ⟨by simpa using hlen, ?_, ?_, ?_, ?_⟩
    · rw [show List.map (fun x : ℕ => x) JJ = JJ from List.map_id JJ, eraseDups_of_nodup hJ, hlen]
    · intro x hx
      exact not_le.2 (hJv x (by simpa using hx))
    · rw [hcsize j0 hj0]; omega
    · intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      rw [hcsize j (hJv j hj), hcsize j0 hj0]
  rw [hcsize j0 hj0, show 2 * k / 2 = k by omega]
  congr 1
  apply ByteArray.ext
  have hmain' : ∀ p < k, ∀ j < d, (interpolate (lagrange (List.map (fun x => codeIndex d x) JJ ++
      List.map (fun x => d + x) (List.range (n - d))) (List.range d))
      ((List.map (fun x => word chunks[x]! (2 * p)) JJ).toArray ++ Array.replicate (n - d) 0))[j]! =
      word data (2 * k * j + 2 * p) := hmain
  have hinner : ∀ j : ℕ, (List.flatMap (fun ws => wordOctets ws[j]!) (List.map (fun p =>
      interpolate (lagrange (List.map (fun x => codeIndex d x) JJ ++
        List.map (fun x => d + x) (List.range (n - d))) (List.range d))
        ((List.map (fun x => word chunks[x]! (2 * p)) JJ).toArray ++ Array.replicate (n - d) 0))
      (List.range k))).length = 2 * k := by
    intro j
    rw [length_flatMap_const _ _ 2 (fun _ _ => rfl)]; simp
  have key : ∀ o < 2 * k * d, (List.flatMap (fun j => List.flatMap (fun ws => wordOctets ws[j]!)
      (List.map (fun p => interpolate (lagrange (List.map (fun x => codeIndex d x) JJ ++
        List.map (fun x => d + x) (List.range (n - d))) (List.range d))
        ((List.map (fun x => word chunks[x]! (2 * p)) JJ).toArray ++ Array.replicate (n - d) 0))
      (List.range k))) (List.range d))[o]? = some (data.get! o) := by
    intro o ho
    have hk0 : 0 < 2 * k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h] at ho; simp at ho
      · omega
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 2 * k ∧ o = 2 * k * j + r :=
      ⟨o / (2 * k), o % (2 * k), Nat.mod_lt _ hk0, (Nat.div_add_mod o (2 * k)).symm⟩
    have hj : j < d := by
      by_contra h
      push_neg at h
      have : 2 * k * d ≤ 2 * k * j := Nat.mul_le_mul_left _ h
      omega
    obtain ⟨p, e, he, rfl⟩ : ∃ p e, e < 2 ∧ r = 2 * p + e :=
      ⟨r / 2, r % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod r 2).symm⟩
    have hp : p < k := by omega
    rw [flatMap_getElem? _ _ (2 * k) (fun j _ => hinner j) j _ hr, List.getElem?_range hj,
      Option.bind_some, flatMap_getElem? _ _ 2 (fun _ _ => rfl) p e he, List.getElem?_map,
      List.getElem?_range hp, Option.map_some, Option.bind_some, hmain' p hp j hj,
      wordOctets_word _ _ _ he]
    congr 2
    ring
  apply Array.ext
  · rw [List.size_toArray, length_flatMap_const _ _ (2 * k) (fun j _ => hinner j),
      List.length_range, show data.data.size = data.size from rfl, hsize]
  · intro o h1 h2
    rw [List.getElem_toArray]
    have := key o (by rw [List.size_toArray] at h1; rw [length_flatMap_const _ _ (2 * k)
      (fun j _ => hinner j), List.length_range] at h1; exact h1)
    rw [List.getElem?_eq_getElem (by simpa using h1)] at this
    rw [Option.some.inj this]
    show data.data[o]! = data.data[o]
    exact getElem!_pos data.data o h2

/-- `encode v` succeeds exactly on data whose size is a multiple of 2·R(v), and then gives one
    chunk per validator. -/
theorem encode_isSome_iff (v : ℕ) (data : ByteArray) :
    (encode v data).isSome ↔ data.size % (2 * originalShards v) = 0 := by
  have hd := originalShards_pos v
  unfold encode encodeWith
  split
  · rename_i h
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rcases h with h | h
    · omega
    · exact h
  · rename_i h
    push_neg at h
    simp [h.2]

theorem encode_length {v : ℕ} {data : ByteArray} {chunks : List ByteArray}
    (henc : encode v data = some chunks) : chunks.length = v := by
  rw [(encode_eq henc).2]; simp

/-- **Erasure-code recovery** (GP v0.8.1 Appendix H): for v ≤ 2¹⁵ validators and data whose size
    is a multiple of 2·R(v), `encode v` gives v chunks, and any R(v) of them, at distinct
    validator indices in any order, recover the data. -/
theorem erasure_recovery {v : ℕ} (hv : v ≤ 32768) (data : ByteArray)
    (hsize : data.size % (2 * originalShards v) = 0) :
    ∃ chunks, encode v data = some chunks ∧ chunks.length = v ∧
      ∀ J : List ℕ, J.Nodup → J.length = originalShards v → (∀ j ∈ J, j < v) →
        recover v (J.map fun j => (chunks[j]!, j)) = some data := by
  obtain ⟨chunks, hc⟩ := Option.isSome_iff_exists.1 ((encode_isSome_iff v data).2 hsize)
  exact ⟨chunks, hc, encode_length hc, fun J hJ hlen hJv => recover_encode hv hc hJ hlen hJv⟩

/-- The full chain: 1023 validators, any 342 chunks. -/
theorem recover_encode_full {data : ByteArray} {chunks : List ByteArray}
    (henc : encode 1023 data = some chunks) {J : List ℕ} (hJ : J.Nodup) (hlen : J.length = 342)
    (hJv : ∀ j ∈ J, j < 1023) : recover 1023 (J.map fun j => (chunks[j]!, j)) = some data :=
  recover_encode (by norm_num) henc hJ (by rw [hlen]; decide) hJv

/-- The tiny chain: 6 validators, any 3 chunks. -/
theorem recover_encode_tiny {data : ByteArray} {chunks : List ByteArray}
    (henc : encode 6 data = some chunks) {J : List ℕ} (hJ : J.Nodup) (hlen : J.length = 3)
    (hJv : ∀ j ∈ J, j < 6) : recover 6 (J.map fun j => (chunks[j]!, j)) = some data :=
  recover_encode (by norm_num) henc hJ (by rw [hlen]; decide) hJv

end JAM.Erasure.Proofs
