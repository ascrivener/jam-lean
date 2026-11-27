import JAM.BestChain

/-!
# Best-chain facts (GP v0.8.1 §19)

Facts about `JAM.BestChain`, stated against its definitions.

* **Best heads** (§19): h is a best head iff it is the hash of a known acceptable block whose m is
  at least that of every acceptable block (`mem_bestHeads_iff`); so a best head is acceptable
  (`bestHead?_acceptable`), extends the finalized block, (19.1) (`bestHead?_extends_finalized`), and
  maximises (19.4) (`bestHead?_maximal`).
* **Order independence**: with unique hashes, reordering the store changes neither P (`lookup_perm`),
  𝐀 (`ancestry_congr`), acceptability (`acceptable_perm`), m (`metric_perm`), nor the set of best
  heads (`mem_bestHeads_perm`).
* **Existence**: the finalized block is acceptable under either audit reading when it is audited
  and none of its ancestors is disregarded (`finalized_acceptable`), and then a best head exists
  (`bestHeads_ne_nil`).
* **Readings**: the `chain` reading of (19.2) is stricter than `head` (`acceptable_head_of_chain`).
* **m** (19.4): a child adds its own 𝐓 to its parent's m (`metric_child`).
-/

namespace JAM.BestChain

variable {H : Type} [DecidableEq H]

/-! ## 𝐀 and P -/

theorem ancestry_eq (bs : List (BlockInfo H)) (b : BlockInfo H) :
    ancestry bs b = b :: match lookup bs b.parent with
      | some p => if p.slot < b.slot then ancestry bs p else []
      | none => [] :=
  ancestry.eq_1 bs b

theorem head_mem_ancestry (bs : List (BlockInfo H)) (b : BlockInfo H) : b ∈ ancestry bs b := by
  rw [ancestry_eq]; exact List.mem_cons_self

/-- (19.4) along one parent link: m(H) = m(P(H)) + 𝐓(H). -/
theorem metric_child (bs : List (BlockInfo H)) (b p : BlockInfo H)
    (hp : lookup bs b.parent = some p) (hlt : p.slot < b.slot) :
    metric bs b = metric bs p + (if b.ticketed then 1 else 0) := by
  unfold metric
  rw [ancestry_eq bs b, hp]
  simp only [hlt, ite_true, List.countP_cons]

theorem lookup_some_mem {bs : List (BlockInfo H)} {h : H} {b : BlockInfo H}
    (hl : lookup bs h = some b) : b ∈ bs ∧ b.hash = h := by
  unfold lookup at hl
  exact ⟨List.mem_of_find?_eq_some hl, by simpa using List.find?_some hl⟩

theorem lookup_eq_some_iff {bs : List (BlockInfo H)} (hnd : (bs.map (·.hash)).Nodup) (h : H)
    (b : BlockInfo H) : lookup bs h = some b ↔ b ∈ bs ∧ b.hash = h := by
  refine ⟨lookup_some_mem, ?_⟩
  induction bs with
  | nil => intro ⟨hm, _⟩; cases hm
  | cons x tl ih =>
    intro ⟨hm, hh⟩
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    unfold lookup at ih ⊢
    rw [List.find?_cons]
    by_cases hx : x.hash = h
    · simp only [hx, decide_true]
      rcases List.mem_cons.mp hm with rfl | hm'
      · rfl
      · exact absurd ⟨b, hm', hh.trans hx.symm⟩ hnd.1
    · simp only [hx, decide_false]
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact absurd hh hx
      · exact ih hnd.2 ⟨hm', hh⟩

theorem lookup_perm {bs bs' : List (BlockInfo H)} (hp : bs.Perm bs')
    (hnd : (bs.map (·.hash)).Nodup) (h : H) : lookup bs h = lookup bs' h := by
  have hnd' : (bs'.map (·.hash)).Nodup := (hp.map _).nodup_iff.mp hnd
  apply Option.ext
  intro b
  rw [lookup_eq_some_iff hnd, lookup_eq_some_iff hnd', hp.mem_iff]

/-- 𝐀 depends on the store only through P. -/
theorem ancestry_congr {bs bs' : List (BlockInfo H)} (hl : ∀ h, lookup bs h = lookup bs' h)
    (b : BlockInfo H) : ancestry bs b = ancestry bs' b := by
  rw [ancestry_eq bs b, ancestry_eq bs' b, hl]
  congr 1
  split
  · rename_i p _
    split
    · rename_i hlt
      exact ancestry_congr hl p
    · rfl
  · rfl
termination_by b.slot

theorem any_perm {α : Type} {l l' : List α} (hp : l.Perm l') (f : α → Bool) :
    l.any f = l'.any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, hp.mem_iff]

theorem metric_perm {bs bs' : List (BlockInfo H)} (hp : bs.Perm bs')
    (hnd : (bs.map (·.hash)).Nodup) (b : BlockInfo H) : metric bs b = metric bs' b := by
  unfold metric; rw [ancestry_congr (lookup_perm hp hnd)]

theorem acceptable_perm {bs bs' : List (BlockInfo H)} (hp : bs.Perm bs')
    (hnd : (bs.map (·.hash)).Nodup) (r : AuditReading) (fin : H) (b : BlockInfo H) :
    acceptable r bs fin b = acceptable r bs' fin b := by
  have hl := lookup_perm hp hnd
  have he : ∀ a, equivocates bs a = equivocates bs' a := fun a => any_perm hp _
  unfold acceptable finalizedAncestors
  simp only [ancestry_congr hl, hl, he]

/-! ## The best heads -/

theorem le_foldl_max (l : List Nat) (a x : Nat) (hx : x ∈ l ∨ x ≤ a) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simpa using hx
  | cons y tl ih =>
    simp only [List.foldl_cons]
    apply ih
    rcases hx with hx | hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inr (Nat.le_max_right _ _)
      · exact Or.inl hx
    · exact Or.inr (Nat.le_trans hx (Nat.le_max_left _ _))

theorem foldl_max_cases (l : List Nat) (a : Nat) : l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l generalizing a with
  | nil => exact Or.inl rfl
  | cons y tl ih =>
    simp only [List.foldl_cons]
    rcases ih (max a y) with h | h
    · rw [h]
      rcases Nat.le_total a y with hay | hay
      · exact Or.inr (by rw [Nat.max_eq_right hay]; exact List.mem_cons_self)
      · exact Or.inl (Nat.max_eq_left hay)
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The best heads (GP §19): exactly the hashes of known acceptable blocks whose m (19.4) is at
    least that of every acceptable block. -/
theorem mem_bestHeads_iff (r : AuditReading) (bs : List (BlockInfo H)) (fin h : H) :
    h ∈ bestHeads r bs fin ↔
      ∃ b ∈ bs, b.hash = h ∧ acceptable r bs fin b = true ∧
        ∀ b' ∈ bs, acceptable r bs fin b' = true → metric bs b' ≤ metric bs b := by
  unfold bestHeads maxMetric
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨⟨hb, hacc⟩, hm⟩, rfl⟩
    refine ⟨b, hb, rfl, hacc, fun b' hb' hacc' => ?_⟩
    rw [hm]
    exact le_foldl_max _ _ _ (Or.inl (List.mem_map.mpr ⟨b', List.mem_filter.mpr ⟨hb', hacc'⟩, rfl⟩))
  · rintro ⟨b, hb, rfl, hacc, hmax⟩
    refine ⟨b, ⟨⟨hb, hacc⟩, ?_⟩, rfl⟩
    apply Nat.le_antisymm
    · exact le_foldl_max _ _ _ (Or.inl (List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨hb, hacc⟩, rfl⟩))
    · rcases foldl_max_cases ((bs.filter (acceptable r bs fin)).map (metric bs)) 0 with h0 | hm
      · rw [h0]; exact Nat.zero_le _
      · obtain ⟨b'', hb'', he⟩ := List.mem_map.mp hm
        obtain ⟨hb''bs, hacc''⟩ := List.mem_filter.mp hb''
        rw [← he]; exact hmax b'' hb''bs hacc''

/-- With unique hashes, the best heads do not depend on the order of the store. -/
theorem mem_bestHeads_perm {bs bs' : List (BlockInfo H)} (hp : bs.Perm bs')
    (hnd : (bs.map (·.hash)).Nodup) (r : AuditReading) (fin h : H) :
    h ∈ bestHeads r bs fin ↔ h ∈ bestHeads r bs' fin := by
  rw [mem_bestHeads_iff, mem_bestHeads_iff]
  simp only [acceptable_perm hp hnd, metric_perm hp hnd, hp.mem_iff]

theorem acceptable_extends_finalized {r : AuditReading} {bs : List (BlockInfo H)} {fin : H}
    {b : BlockInfo H} (h : acceptable r bs fin b = true) :
    fin ∈ (ancestry bs b).map (·.hash) := by
  unfold acceptable at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem acceptable_head_of_chain {bs : List (BlockInfo H)} {fin : H} {b : BlockInfo H}
    (h : acceptable .chain bs fin b = true) : acceptable .head bs fin b = true := by
  unfold acceptable at h ⊢
  simp only [Bool.and_eq_true, Bool.and_true] at h ⊢
  exact ⟨⟨h.1.1.1, h.1.2⟩, h.2⟩

theorem bestHead?_mem {r : AuditReading} {bs : List (BlockInfo H)} {fin h : H}
    (hb : bestHead? r bs fin = some h) : h ∈ bestHeads r bs fin := by
  unfold bestHead? at hb
  exact List.mem_of_head? hb

/-- A best head is the hash of a known acceptable block. -/
theorem bestHead?_acceptable {r : AuditReading} {bs : List (BlockInfo H)} {fin h : H}
    (hb : bestHead? r bs fin = some h) :
    ∃ b ∈ bs, b.hash = h ∧ acceptable r bs fin b = true := by
  obtain ⟨b, hbs, hh, hacc, _⟩ := (mem_bestHeads_iff r bs fin h).mp (bestHead?_mem hb)
  exact ⟨b, hbs, hh, hacc⟩

/-- (19.1) for a best head: the finalized block is among its ancestors. -/
theorem bestHead?_extends_finalized {r : AuditReading} {bs : List (BlockInfo H)} {fin h : H}
    (hb : bestHead? r bs fin = some h) :
    ∃ b ∈ bs, b.hash = h ∧ fin ∈ (ancestry bs b).map (·.hash) := by
  obtain ⟨b, hbs, hh, hacc⟩ := bestHead?_acceptable hb
  exact ⟨b, hbs, hh, acceptable_extends_finalized hacc⟩

/-- (19.4) for a best head: no acceptable block has a larger m. -/
theorem bestHead?_maximal {r : AuditReading} {bs : List (BlockInfo H)} {fin h : H}
    (hb : bestHead? r bs fin = some h) :
    ∃ b ∈ bs, b.hash = h ∧
      ∀ b' ∈ bs, acceptable r bs fin b' = true → metric bs b' ≤ metric bs b := by
  obtain ⟨b, hbs, hh, _, hmax⟩ := (mem_bestHeads_iff r bs fin h).mp (bestHead?_mem hb)
  exact ⟨b, hbs, hh, hmax⟩

/-- The finalized block is acceptable under either reading of (19.2) when it is audited and none
    of its ancestors is disregarded: (19.3) is vacuous on finalized ancestors. -/
theorem finalized_acceptable (r : AuditReading) {bs : List (BlockInfo H)} {fin : H}
    {f : BlockInfo H} (hf : lookup bs fin = some f) (hU : f.audited = true)
    (hd : ∀ a ∈ ancestry bs f, a.disregarded = false) : acceptable r bs fin f = true := by
  have hfin : f.hash = fin := (lookup_some_mem hf).2
  have hF : ∀ a ∈ ancestry bs f, a.hash ∈ finalizedAncestors bs fin := by
    intro a ha
    unfold finalizedAncestors
    rw [hf]
    exact List.mem_map_of_mem ha
  unfold acceptable
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  refine ⟨⟨⟨⟨?_, hU⟩, ?_⟩, fun a ha => Or.inl (hF a ha)⟩, hd⟩
  · rw [← hfin]; exact List.mem_map_of_mem (head_mem_ancestry bs f)
  · cases r
    · rfl
    · simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact fun a ha => Or.inl (hF a ha)

/-- A best head exists when the finalized block is known, audited and has no disregarded
    ancestor. -/
theorem bestHeads_ne_nil (r : AuditReading) {bs : List (BlockInfo H)} {fin : H} {f : BlockInfo H}
    (hf : lookup bs fin = some f) (hU : f.audited = true)
    (hd : ∀ a ∈ ancestry bs f, a.disregarded = false) : bestHeads r bs fin ≠ [] := by
  have hacc := finalized_acceptable r hf hU hd
  have hfb : f ∈ bs := (lookup_some_mem hf).1
  intro hnil
  unfold bestHeads maxMetric at hnil
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq] at hnil
  -- Some acceptable block attains the maximum, contradicting the empty filter.
  rcases foldl_max_cases ((bs.filter (acceptable r bs fin)).map (metric bs)) 0 with h0 | hm
  · -- The maximum is 0, so f itself (with m(f) ≤ 0) attains it.
    have hle : metric bs f ≤ ((bs.filter (acceptable r bs fin)).map (metric bs)).foldl max 0 :=
      le_foldl_max _ _ _ (Or.inl (List.mem_map.mpr ⟨f, List.mem_filter.mpr ⟨hfb, hacc⟩, rfl⟩))
    rw [h0] at hle
    exact hnil f (List.mem_filter.mpr ⟨hfb, hacc⟩) (by rw [h0]; omega)
  · obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact hnil b hb he

end JAM.BestChain
