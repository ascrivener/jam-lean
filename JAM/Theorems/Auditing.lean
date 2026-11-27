import JAM.Auditing

/-!
# Auditing invariants (GP v0.8.1 §17)

Facts about `JAM.Auditing`, stated against its definitions.

* **$\mathcal{F}$** (Appendix F) commutes with `map` (`shuffle_map`) and is a permutation
  (`shuffle_perm`).
* **Tranche 0** (§17.3): $\mathbf{a}_0$ is the report half of its core-indexed form
  (`tranche0_eq_map_snd`), has at most ten items (`tranche0_length_le`), names each core at most
  once (`tranche0Indexed_nodup_cores`), and every $(c, w)$ it selects has $\mathbf{q}[c] = w$
  (`tranche0Indexed_mem`).
* **Later tranches** (eq. `latertranches`): no no-shows, no selection (`laterSelected_zero`,
  `laterTranche_eq_nil`); selection is monotone in the no-show count (`laterSelected_mono`);
  $\mathbf{a}_n$ draws only from $\mathbf{q}$ (`laterTranche_sublist`) and the prose
  negative-judgment rule only adds reports (`laterTranche_subset_withNegatives`).
* **$\mathbf{U}$** (§17.3): `audited` decides `Audited` (`audited_iff`); it is monotone in
  $J_\top$ (`audited_mono_positive`) and in the current tranche (`audited_mono_current`), but not in
  $J_\bot$: one negative judgment revokes it below the supermajority (`audited_false_of_negative`).
  The literal reading with $n$ unbounded collapses (`auditedLiteral_degenerate`), and the bounded
  one accepts a report nobody announced in some tranche (`audited_of_empty_tranche`).
* **§10 link**: $|J_\top| > \frac{2}{3}|\kappa|$ is exactly the good-verdict count
  $\lfloor \frac{2}{3}|\kappa| \rfloor + 1$ (`supermajority_iff_verdictGood`); `formVerdict` returns
  only votes §10 accepts the count, order and outcome of, each backed by an observed judgment
  (`formVerdict_sound`), and finds a good verdict whenever enough positive judgments are known
  (`formVerdict_good_complete`); an auditing judgment signs the message a verdict vote is checked
  against (`judgmentMessage_eq`).
-/

namespace JAM.Auditing

open Shuffle

/-! ## $\mathcal{F}$ -/

/-- $\mathcal{F}(\text{map } f\, \mathbf{s}, \mathbf{r}) = \text{map } f\, \mathcal{F}(\mathbf{s},
    \mathbf{r})$: the shuffle's draws do not depend on the values. -/
theorem shuffle_map {α β : Type} (f : α → β) (s : List α) (r : List Nat) :
    shuffle (s.map f) r = (shuffle s r).map f := by
  fun_induction shuffle s r with
  | case1 r => simp [shuffle]
  | case2 x xs r s i last ih =>
    simp only [List.map_cons]
    rw [shuffle]
    have hl : (f x :: xs.map f).getLast (List.cons_ne_nil _ _) = f last := by
      simp only [last, s]
      have := List.getLast_map (f := f) (l := x :: xs) (by simp)
      simpa using this
    rw [hl]
    have hs : (f x :: List.map f xs).set (r.headD 0 % (f x :: List.map f xs).length) (f last)
        = (s.set i last).map f := by
      simp [s, i, ← List.map_cons, List.map_set]
    rw [hs, List.length_map, ← List.map_take, ih]
    congr 1
    simp only [List.getD_eq_getElem?_getD, s, i, List.length_cons, List.length_map]
    rw [← List.map_cons, List.getElem?_map]
    cases (x :: xs)[r.headD 0 % (xs.length + 1)]? <;> rfl

/-- One step of $\mathcal{F}$ (GP eq. `suffle`) permutes: $\mathbf{s} \sim \mathbf{s}_i ::
    (\mathbf{s} \text{ with } \mathbf{s}_i \text{ replaced by the last element, cut to } l - 1)$. -/
theorem perm_swap_step {α : Type} (l : List α) (h : l ≠ []) (i : Nat) (hi : i < l.length) :
    l.Perm (l[i] :: (l.set i (l.getLast h)).take (l.length - 1)) := by
  obtain ⟨d, a, hl⟩ := List.eq_nil_or_concat l |>.resolve_left h
  rw [List.concat_eq_append] at hl
  subst hl
  have hgl : (d ++ [a]).getLast h = a := by simp
  rw [hgl]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rcases Nat.lt_or_ge i d.length with hlt | hge
  · rw [List.set_append_left _ _ hlt, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp), List.getElem_append_left hlt]
    have hd : d = d.take i ++ d[i] :: d.drop (i + 1) := by
      simp
    have hset : d.set i a = d.take i ++ a :: d.drop (i + 1) := by
      rw [List.set_eq_take_append_cons_drop]; simp [hlt]
    rw [hset]
    conv => lhs; rw [hd]
    simp only [List.append_assoc, List.cons_append]
    refine List.perm_middle.trans (List.Perm.cons _ ?_)
    refine List.Perm.trans ?_ List.perm_middle.symm
    simpa using List.perm_append_singleton a (d.take i ++ d.drop (i + 1))
  · have hi' : i = d.length := by simp at hi; omega
    subst hi'
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem_cons_zero, List.set_append_right _ _ (Nat.le_refl _),
      List.set_cons_zero, List.take_left']
    exact List.perm_append_singleton a d

/-- $\mathcal{F}(\mathbf{s}, \mathbf{r})$ is a permutation of $\mathbf{s}$ (GP Appendix F). -/
theorem shuffle_perm {α : Type} (s : List α) (r : List Nat) : (shuffle s r).Perm s := by
  fun_induction shuffle s r with
  | case1 r => simp
  | case2 x xs r s i last ih =>
    have hi : i < s.length := Nat.mod_lt _ (by simp [s])
    have hg : s.getD i x = s[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hg]
    refine (List.Perm.cons _ ih).trans ?_
    have := perm_swap_step s (List.cons_ne_nil x xs) i hi
    simpa [s] using this.symm

/-! ## Tranche 0 -/

private theorem filterMap_indexed_snd {α : Type} (l : List (Nat × Option α)) :
    (l.filterMap fun (c, w) => w.map (c, ·)).map Prod.snd = (l.map Prod.snd).filterMap id := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨c, w⟩ := p
    cases w <;> simp_all

/-- The indexed $\mathbf{q}$, $(c, \mathbf{q}_c)$ for each core $c$. -/
private abbrev indexedQ (q : List (Option WorkReport)) : List (Nat × Option WorkReport) :=
  q.zipIdx.map fun (w, c) => (c, w)

/-- $\mathbf{a}_0$ is the report half of its core-indexed form. -/
theorem tranche0_eq_map_snd (q : List (Option WorkReport)) (y : List UInt8) :
    tranche0 q y = (tranche0Indexed q y).map Prod.snd := by
  unfold tranche0 tranche0Indexed shuffleHash
  rw [filterMap_indexed_snd, List.map_take, ← shuffle_map]
  have h1 : (q.zipIdx.map fun (w, c) => (c, w)).map Prod.snd = q := by
    simp [List.map_map, Function.comp_def]
  rw [h1]
  simp

/-- $|\mathbf{a}_0| \le 10$. -/
theorem tranche0Indexed_length_le (q : List (Option WorkReport)) (y : List UInt8) :
    (tranche0Indexed q y).length ≤ 10 := by
  unfold tranche0Indexed
  refine Nat.le_trans (List.length_filterMap_le _ _) ?_
  simp only [List.length_take, tranche0Size]
  exact Nat.min_le_left _ _

/-- $|\mathbf{a}_0| \le 10$ (GP §17.3, "a verifiably random selection of ten cores"). -/
theorem tranche0_length_le (q : List (Option WorkReport)) (y : List UInt8) :
    (tranche0 q y).length ≤ 10 := by
  rw [tranche0_eq_map_snd, List.length_map]; exact tranche0Indexed_length_le q y

private theorem filterMap_indexed_fst_sublist {α : Type} (l : List (Nat × Option α)) :
    ((l.filterMap fun (c, w) => w.map (c, ·)).map Prod.fst).Sublist (l.map Prod.fst) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨c, w⟩ := p
    cases w with
    | none => simpa using ih.cons c
    | some w => simpa using ih.cons_cons c

/-- Tranche 0 selects each core at most once. -/
theorem tranche0Indexed_nodup_cores (q : List (Option WorkReport)) (y : List UInt8) :
    ((tranche0Indexed q y).map Prod.fst).Nodup := by
  unfold tranche0Indexed shuffleHash
  refine List.Nodup.sublist (filterMap_indexed_fst_sublist _) ?_
  have hL : ((indexedQ q).map Prod.fst).Nodup := by
    have : (indexedQ q).map Prod.fst = List.range' 0 q.length := by
      rw [← List.zipIdx_map_snd 0 q]; simp [List.map_map, Function.comp_def]
    rw [this]; exact List.nodup_range'
  have hS := ((shuffle_perm (indexedQ q) (seqFromHash (indexedQ q).length
    ⟨y.toArray⟩)).map Prod.fst).nodup_iff.mpr hL
  rw [List.map_take]
  exact hS.sublist (List.take_sublist _ _)

/-- Every $(c, w)$ tranche 0 selects has $\mathbf{q}[c] = w$. -/
theorem tranche0Indexed_mem (q : List (Option WorkReport)) (y : List UInt8) (c : Nat)
    (w : WorkReport) (h : (c, w) ∈ tranche0Indexed q y) : q[c]? = some (some w) := by
  unfold tranche0Indexed shuffleHash at h
  obtain ⟨⟨c', w'⟩, hm, he⟩ := List.mem_filterMap.mp h
  cases w' with
  | none => simp at he
  | some w' =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hm' := (shuffle_perm _ _).mem_iff.mp (List.mem_of_mem_take hm)
    obtain ⟨⟨w'', c''⟩, hz, he'⟩ := List.mem_map.mp hm'
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exact List.mk_mem_zipIdx_iff_getElem?.mp hz

/-! ## Later tranches -/

/-- With no no-shows $a_n(w)$ is false. -/
theorem laterSelected_zero (V : Nat) (y : List UInt8) : laterSelected V y 0 = false := by
  simp [laterSelected]

/-- $a_n(w)$ is monotone in the no-show count. -/
theorem laterSelected_mono (V : Nat) (y : List UInt8) {m m' : Nat} (hm : m ≤ m')
    (h : laterSelected V y m = true) : laterSelected V y m' = true := by
  simp only [laterSelected, decide_eq_true_eq] at *
  exact Nat.lt_of_lt_of_le h (Nat.mul_le_mul_left _ hm)

/-- No no-shows in tranche $n - 1$ for any report of $\mathbf{q}$: $\mathbf{a}_n$ is empty. -/
theorem laterTranche_eq_nil (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport))
    (y : WorkReport → List UInt8) (h : ∀ w ∈ q.filterMap id, noShows V view n w = 0) :
    laterTranche V view n q y = [] := by
  unfold laterTranche
  rw [List.filter_eq_nil_iff]
  intro w hw
  rw [h w hw, laterSelected_zero]; simp

/-- $\mathbf{a}_n$ draws only from $\mathbf{q}$. -/
theorem laterTranche_sublist (V : Nat) (view : View) (n : Nat) (q : List (Option WorkReport))
    (y : WorkReport → List UInt8) : (laterTranche V view n q y).Sublist (q.filterMap id) :=
  List.filter_sublist

/-- The prose negative-judgment rule only adds reports to $\mathbf{a}_n$. -/
theorem laterTranche_subset_withNegatives (V : Nat) (view : View) (n : Nat)
    (q : List (Option WorkReport)) (y : WorkReport → List UInt8) :
    ∀ w ∈ laterTranche V view n q y, w ∈ laterTrancheWithNegatives V view n q y := by
  intro w hw
  simp only [laterTranche, laterTrancheWithNegatives, List.mem_filter] at *
  exact ⟨hw.1, by simp [hw.2]⟩

/-! ## Validator sets -/

theorem VSet.subsetB_iff (V : Nat) (s t : VSet) : VSet.subsetB V s t = true ↔ VSet.Subset V s t := by
  simp only [VSet.subsetB, VSet.Subset, List.all_eq_true, List.mem_range]
  refine ⟨fun h i hi hs => ?_, fun h i hi => ?_⟩
  · have := h i hi; simp_all
  · cases hs : s i <;> simp [h i hi, hs]

theorem VSet.isEmptyB_iff (V : Nat) (s : VSet) : VSet.isEmptyB V s = true ↔ ∀ i, i < V → s i = false := by
  simp [VSet.isEmptyB, List.all_eq_true, List.mem_range]

private theorem filter_sublist_of_imp {α : Type} (p q : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, p x = true → q x = true) → (l.filter p).Sublist (l.filter q)
  | [], _ => by simp
  | x :: l, h => by
    have ih := filter_sublist_of_imp p q l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x = true
    · have hq := h x List.mem_cons_self hp
      simp only [List.filter_cons, hp, hq, ite_true]; exact ih.cons_cons _
    · simp only [List.filter_cons, Bool.not_eq_true] at hp ⊢
      rw [hp]; simp only [Bool.false_eq_true, ite_false]
      split
      · exact ih.cons _
      · exact ih

/-- $|s| \le |t|$ when $s \subseteq t$ within $\mathbb{N}_V$. -/
theorem VSet.card_mono (V : Nat) {s t : VSet} (h : VSet.Subset V s t) :
    VSet.card V s ≤ VSet.card V t := by
  unfold VSet.card VSet.members
  refine (filter_sublist_of_imp s t _ fun i hi => h i (List.mem_range.mp hi)).length_le

theorem VSet.Subset.trans {V : Nat} {s t u : VSet} (h1 : VSet.Subset V s t)
    (h2 : VSet.Subset V t u) : VSet.Subset V s u :=
  fun i hi hs => h2 i hi (h1 i hi hs)

/-! ## The audited conditions -/

/-- `audited` decides $U(w)$. -/
theorem audited_iff (V : Nat) (view : View) (current : Nat) (h : List UInt8) :
    audited V view current h = true ↔ Audited V view current h := by
  simp only [audited, Audited, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    List.mem_range, decide_eq_true_eq, VSet.subsetB_iff]
  constructor
  · rintro (⟨hn, n, hn', hs⟩ | hc)
    · exact Or.inl ⟨hn, n, by omega, hs⟩
    · exact Or.inr hc
  · rintro (⟨hn, n, hn', hs⟩ | hc)
    · exact Or.inl ⟨hn, n, by omega, hs⟩
    · exact Or.inr hc

/-- $U(w)$ is monotone in $J_\top(w)$: more positive judgments never un-audit a report. -/
theorem audited_mono_positive (V : Nat) (view view' : View) (current : Nat) (h : List UInt8)
    (hA : view'.announced = view.announced) (hN : view'.negative h = view.negative h)
    (hP : VSet.Subset V (view.positive h) (view'.positive h))
    (hU : audited V view current h = true) : audited V view' current h = true := by
  rw [audited_iff] at *
  rcases hU with ⟨hn, n, hn', hs⟩ | hc
  · exact Or.inl ⟨hN ▸ hn, n, hn', hA ▸ hs.trans hP⟩
  · exact Or.inr (Nat.lt_of_lt_of_le hc (Nat.mul_le_mul_left _ (VSet.card_mono V hP)))

/-- $U(w)$ stays true as tranches pass. -/
theorem audited_mono_current (V : Nat) (view : View) {c c' : Nat} (h : List UInt8)
    (hc : c ≤ c') (hU : audited V view c h = true) : audited V view c' h = true := by
  rw [audited_iff] at *
  rcases hU with ⟨hn, n, hn', hs⟩ | hs
  · exact Or.inl ⟨hn, n, Nat.le_trans hn' hc, hs⟩
  · exact Or.inr hs

/-- $U(w)$ is not monotone in $J_\bot(w)$: below the supermajority, one negative judgment makes a
    report unaudited, whatever the announcements. -/
theorem audited_false_of_negative (V : Nat) (view : View) (current : Nat) (h : List UInt8)
    (i : Nat) (hi : i < V) (hneg : view.negative h i = true)
    (hc : 3 * VSet.card V (view.positive h) ≤ 2 * V) : audited V view current h = false := by
  have : ¬ Audited V view current h := by
    rintro (⟨hn, _⟩ | hs)
    · have := (VSet.isEmptyB_iff V _).mp hn i hi; simp_all
    · omega
  cases hU : audited V view current h
  · rfl
  · exact absurd ((audited_iff V view current h).mp hU) this

/-- The literal $U(w)$, with $n$ unbounded: once some tranche $m$ has $A_m(w) = \emptyset$ (as every
    tranche after one without no-shows has, by eq. `latertranches`), its first clause is just
    $J_\bot(w) = \emptyset$. -/
theorem auditedLiteral_degenerate (V : Nat) (view : View) (h : List UInt8)
    (hm : ∃ m, VSet.isEmptyB V (view.announced m h) = true) :
    AuditedLiteral V view h ↔
      VSet.isEmptyB V (view.negative h) = true ∨ 3 * VSet.card V (view.positive h) > 2 * V := by
  obtain ⟨m, hm⟩ := hm
  have hsub : VSet.Subset V (view.announced m h) (view.positive h) := fun i hi hs => by
    have := (VSet.isEmptyB_iff V _).mp hm i hi; simp_all
  unfold AuditedLiteral
  constructor
  · rintro (⟨hn, _⟩ | hc)
    · exact Or.inl hn
    · exact Or.inr hc
  · rintro (hn | hc)
    · exact Or.inl ⟨hn, m, hsub⟩
    · exact Or.inr hc

/-- The bounded $U(w)$ still holds for a report with no negative judgment that nobody announced in
    some tranche up to the current one, with no positive judgment at all. -/
theorem audited_of_empty_tranche (V : Nat) (view : View) (current n : Nat) (h : List UInt8)
    (hn : n ≤ current) (hA : VSet.isEmptyB V (view.announced n h) = true)
    (hN : VSet.isEmptyB V (view.negative h) = true) : audited V view current h = true := by
  rw [audited_iff]
  refine Or.inl ⟨hN, n, hn, fun i hi hs => ?_⟩
  have := (VSet.isEmptyB_iff V _).mp hA i hi; simp_all

/-- $\mathbf{U} \Leftrightarrow \forall w \in \mathbf{R} : U(w)$. -/
theorem blockAudited_iff (V : Nat) (view : View) (current : Nat) (R : List WorkReport) :
    blockAudited V view current R = true ↔ ∀ w ∈ R, Audited V view current (reportHash w) := by
  simp [blockAudited, List.all_eq_true, audited_iff]

/-! ## The link to §10 -/

/-- $|J_\top(w)| > \frac{2}{3}|\kappa|$ ($U$'s second clause) is exactly the count of positive votes
    a good verdict needs, $\lfloor \frac{2}{3}|\kappa| \rfloor + 1$ (GP §10.2 eq. `verdicts`,
    `JAM.verdictOutcome`). -/
theorem supermajority_iff_verdictGood (V t : Nat) : 3 * t > 2 * V ↔ 2 * V / 3 + 1 ≤ t := by
  omega

/-- An auditing judgment on $w$ signs $\mathsf{X}_{e} \frown \mathcal{H}(w)$, the message
    `JAM.checkVerdict` checks a verdict vote on target $\mathcal{H}(w)$ against. -/
theorem judgmentMessage_eq (valid : Bool) (w : WorkReport) :
    judgmentMessage valid w = Xvalidif valid ++ reportHash w := rfl

/-- What `formVerdict` returns is a vote set §10 accepts the shape of:
    $\lfloor \frac{2}{3}|\kappa| \rfloor + 1$ votes, strictly ascending by validator index, with
    $V(a, \mathbf{j})$ defined and equal to the claimed outcome; and each vote is a judgment the
    author has seen (positive votes from $J_\top$, negative from $J_\bot$, indices below
    $|\kappa|$). Signatures are whatever `sig` supplies; their checks are not claimed. -/
theorem formVerdict_sound (V : Nat) (pos neg : VSet) (sig : Nat → Bool → Blob) (o : Outcome)
    (js : List Judgment) (h : formVerdict V pos neg sig = some (o, js)) :
    js.length = 2 * V / 3 + 1 ∧ orderedUniqByNat (·.index) js = true ∧
      verdictOutcome V js = some o ∧
      ∀ j ∈ js, j.index < V ∧ (j.valid = true → pos j.index = true) ∧
        (j.valid = false → neg j.index = true) := by
  unfold formVerdict at h
  have hp := List.find?_some h
  have hmem := List.mem_of_find?_eq_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨hl, ho⟩, hv⟩ := hp
  have hv' : verdictOutcome V js = some o := by
    revert hv
    cases verdictOutcome V js with
    | none => intro h; exact absurd h (by cases o <;> decide)
    | some o' => cases o <;> cases o' <;> first | (intro; rfl) | (intro h; exact absurd h (by decide))
  refine ⟨hl, ho, hv', ?_⟩
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  intro j hj
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := List.mem_of_mem_take hi
    simp only [VSet.members, List.mem_filter, List.mem_range] at this
    exact ⟨this.1, fun _ => this.2, by simp⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := List.mem_of_mem_take hi
    simp only [VSet.members, List.mem_filter, List.mem_range] at this
    exact ⟨this.1, by simp, fun _ => this.2⟩
  · obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hj
    rw [List.mem_range] at hi
    split at he
    · rename_i hc
      simp only [Option.some.injEq] at he
      subst he
      have := List.mem_of_mem_take (List.contains_iff_mem.mp hc)
      simp only [VSet.members, List.mem_filter, List.mem_range] at this
      exact ⟨hi, fun _ => this.2, by simp⟩
    · split at he
      · rename_i _ hc
        simp only [Option.some.injEq] at he
        subst he
        have := List.mem_of_mem_take (List.contains_iff_mem.mp hc)
        simp only [List.mem_filter, VSet.members, List.mem_range] at this
        exact ⟨hi, by simp, fun _ => this.1.2⟩
      · simp at he

private theorem orderedUniqByNat_of_pairwise {α : Type} (key : α → Nat) :
    ∀ l : List α, (l.map key).Pairwise (· < ·) → orderedUniqByNat key l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: rest, h => by
    simp only [List.map_cons, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [orderedUniqByNat, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h.1.1, orderedUniqByNat_of_pairwise key (b :: rest) ?_⟩
    simp only [List.map_cons, List.pairwise_cons]
    exact h.2

/-- With at least $\lfloor \frac{2}{3}|\kappa| \rfloor + 1$ positive judgments known, `formVerdict`
    gives a good verdict. -/
theorem formVerdict_good_complete (V : Nat) (pos neg : VSet) (sig : Nat → Bool → Blob)
    (h : 2 * V / 3 + 1 ≤ VSet.card V pos) : ∃ js, formVerdict V pos neg sig = some (.good, js) := by
  unfold formVerdict
  dsimp only
  refine ⟨_, List.find?_cons_of_pos ?_⟩
  have hlen : ((VSet.members V pos).take (2 * V / 3 + 1)).length = 2 * V / 3 + 1 := by
    rw [List.length_take]; exact Nat.min_eq_left h
  have hpw : ((VSet.members V pos).take (2 * V / 3 + 1)).Pairwise (· < ·) :=
    ((List.pairwise_lt_range).filter _).sublist (List.take_sublist _ _)
  simp only [Bool.and_eq_true, beq_iff_eq, List.length_map, hlen, true_and]
  refine ⟨orderedUniqByNat_of_pairwise _ _ ?_, ?_⟩
  · simpa [List.map_map, Function.comp_def] using hpw
  · have : verdictOutcome V (((VSet.members V pos).take (2 * V / 3 + 1)).map fun i =>
        ({ valid := true, index := i, signature := sig i true } : Judgment)) = some .good := by
      have hf : (((VSet.members V pos).take (2 * V / 3 + 1)).map fun i =>
          ({ valid := true, index := i, signature := sig i true } : Judgment)).filter (·.valid) =
          ((VSet.members V pos).take (2 * V / 3 + 1)).map fun i =>
          ({ valid := true, index := i, signature := sig i true } : Judgment) := by
        rw [List.filter_eq_self]
        intro a ha
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        rfl
      simp only [verdictOutcome]
      rw [hf, List.length_map, hlen]
      simp
    rw [this]; rfl

end JAM.Auditing
