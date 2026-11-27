import JAM.Safrole

/-!
# Safrole invariants (GP v0.8.1 §6)

Facts about `JAM.safrole` and its parts, stated against the definitions in `JAM/Safrole.lean`
without changing them.

* **The outside-in sequencer $Z$** (§6.5, `outsideIn`) is a permutation of its input
  (`outsideIn_perm`), so it keeps length (`length_outsideIn`).
* **The order on identifiers** (`octetLt`) is a strict total order (`octetLt_irrefl`,
  `octetLt_trans`, `octetLt_trichotomy`), and `strictlyOrdered` is the pairwise form of it
  (`strictlyOrdered_iff`).
* **The ticket accumulator $\gamma'_A$** (§6.7, eqs. (6.5), (6.36)): after a successful transition
  it has at most $\mathsf{E}$ tickets (`safrole_accumulator_length`); if the prior $\gamma_A$ has
  unique identifiers (which $\gamma'_A$ then has again, so this is an invariant), $\gamma'_A$ is
  strictly sorted by identifier and its identifiers are unique (`safrole_accumulator_sorted`).
* **The seal-key sequence $\gamma'_S$** (eq. `slotkeysequence`): on an epoch change it has exactly
  $\mathsf{E}$ entries in both the ticket and the fallback case, and a $\gamma_S$ of $\mathsf{E}$
  entries stays one (`safrole_sealKeys_length`).
* **The entry-index bound $n$** (eq. `ticketsextrinsic`, `maxAttempts`) is
  $\lceil 2\mathsf{E}/|\gamma'_P| \rceil$ when $\gamma'_P$ is non-empty (`maxAttempts_spec`). In
  the paper every validator sequence has a length in
  $\mathbb{V} = \{3c \mid c \in \mathbb{N}_{2 \dots \mathsf{C}+1}\}$, "a multiple of 3 between 6
  and $3\mathsf{C}$" (eqs. `validatorkeys`, `valcount`), so $|\gamma'_P| \ge 6$ and the case
  $|\gamma'_P| = 0$ does not arise; the model's lists carry no length, and there $n = 0$ (Lean's
  $x / 0 = 0$), so a successful transition with an empty $\gamma'_P$ admits no tickets
  (`safrole_tickets_nil_of_pending_nil`).
* **$\eta'$, $\tau'$ and the validator sets**: $\eta'$ has four entries (and four 32-octet hashes if
  $\eta$ had), $\tau' = \mathbf{H}_T > \tau$, $\iota$ is unchanged, and on an epoch change
  $\kappa' = \gamma_P$, $\lambda' = \kappa$ (`safrole_shape`, `safrole_eta_wf`).
-/

namespace JAM

/-! ## The outside-in sequencer $Z$ -/

/-- The index $Z$ reads at position $i$ of a sequence of length $n$: $i/2$ at even $i$,
    $n - 1 - \lfloor i/2 \rfloor$ at odd $i$. -/
def outsideInIdx (n i : Nat) : Nat := if i % 2 = 0 then i / 2 else n - 1 - i / 2

theorem outsideInIdx_lt {n i : Nat} (h : i < n) : outsideInIdx n i < n := by
  unfold outsideInIdx; split <;> omega

theorem outsideInIdx_inj {n i j : Nat} (hi : i < n) (hj : j < n)
    (h : outsideInIdx n i = outsideInIdx n j) : i = j := by
  unfold outsideInIdx at h; split at h <;> split at h <;> omega

theorem outsideInIdx_surj {n j : Nat} (hj : j < n) : ∃ i, i < n ∧ outsideInIdx n i = j := by
  by_cases h : 2 * j < n
  · exact ⟨2 * j, h, by unfold outsideInIdx; split <;> omega⟩
  · exact ⟨2 * (n - 1 - j) + 1, by omega, by unfold outsideInIdx; split <;> omega⟩

private theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α} (hl : l.Nodup)
    (hf : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.nodup_cons, List.mem_map]
    refine ⟨?_, ih hl.2 fun a ha b hb => hf a (by simp [ha]) b (by simp [hb])⟩
    rintro ⟨y, hy, hxy⟩
    exact hl.1 (hf y (by simp [hy]) x (by simp) hxy ▸ hy)

/-- The indices $Z$ reads are a permutation of $\mathbb{N}_n$. -/
theorem range_map_outsideInIdx_perm (n : Nat) :
    ((List.range n).map (outsideInIdx n)).Perm (List.range n) := by
  rw [List.perm_ext_iff_of_nodup
    (nodup_map_of_inj List.nodup_range fun a ha b hb h =>
      outsideInIdx_inj (List.mem_range.1 ha) (List.mem_range.1 hb) h) List.nodup_range]
  intro a
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact outsideInIdx_lt hi
  · intro ha; exact outsideInIdx_surj ha

private theorem filterMap_getElem?_range' {α : Type} (s : List α) :
    ∀ m k, k + m = s.length → (List.range' k m).filterMap (fun j => s[j]?) = s.drop k
  | 0, k, h => by simp [List.drop_of_length_le (by omega : s.length ≤ k)]
  | m + 1, k, h => by
    have hk : k < s.length := by omega
    rw [List.range'_succ, List.filterMap_cons, List.getElem?_eq_getElem hk,
      List.drop_eq_getElem_cons hk, filterMap_getElem?_range' s m (k + 1) (by omega)]

private theorem filterMap_getElem?_range {α : Type} (s : List α) :
    (List.range s.length).filterMap (fun j => s[j]?) = s := by
  rw [List.range_eq_range', filterMap_getElem?_range' s _ 0 (by omega), List.drop_zero]

/-- $Z$ reads $s$ at the indices `outsideInIdx`. -/
theorem outsideIn_eq {α : Type} (s : List α) :
    outsideIn s =
      ((List.range s.length).map (outsideInIdx s.length)).filterMap (fun j => s[j]?) := by
  rw [List.filterMap_map]; unfold outsideIn outsideInIdx
  congr 1; funext i; simp only [Function.comp]; split <;> rfl

/-- $Z$ is a permutation of its input (GP §6.5). -/
theorem outsideIn_perm {α : Type} (s : List α) : (outsideIn s).Perm s := by
  rw [outsideIn_eq]
  exact ((range_map_outsideInIdx_perm _).filterMap _).trans (by rw [filterMap_getElem?_range s])

/-- $Z$ keeps length. -/
@[simp] theorem length_outsideIn {α : Type} (s : List α) : (outsideIn s).length = s.length :=
  (outsideIn_perm s).length_eq

/-! ## The order on identifiers -/

theorem octetLt_irrefl : ∀ a : List UInt8, octetLt a a = false
  | [] => rfl
  | x :: xs => by simp [octetLt, octetLt_irrefl xs, UInt8.lt_irrefl]

theorem octetLt_trans :
    ∀ a b c : List UInt8, octetLt a b = true → octetLt b c = true → octetLt a c = true
  | [], [], _, h, _ => by simp [octetLt] at h
  | [], _ :: _, [], _, h => by simp [octetLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [octetLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [octetLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [octetLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact .inl (UInt8.lt_trans h1 h2)
    · exact .inl h1
    · exact .inl h2
    · exact .inr ⟨rfl, octetLt_trans xs ys zs h1 h2⟩

theorem octetLt_trichotomy :
    ∀ a b : List UInt8, octetLt a b = true ∨ a = b ∨ octetLt b a = true
  | [], [] => .inr (.inl rfl)
  | [], _ :: _ => .inl rfl
  | _ :: _, [] => .inr (.inr rfl)
  | x :: xs, y :: ys => by
    simp only [octetLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.cons.injEq]
    have hx : x < y ∨ x = y ∨ y < x := by
      rw [UInt8.lt_iff_toNat_lt, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj]; omega
    rcases hx with h | rfl | h
    · exact .inl (.inl h)
    · rcases octetLt_trichotomy xs ys with h | rfl | h
      · exact .inl (.inr ⟨rfl, h⟩)
      · exact .inr (.inl ⟨rfl, rfl⟩)
      · exact .inr (.inr (.inr ⟨rfl, h⟩))
    · exact .inr (.inr (.inl h))

theorem octetLt_asymm {a b : List UInt8} (h : octetLt a b = true) : octetLt b a = false := by
  cases h' : octetLt b a
  · rfl
  · have := octetLt_trans a b a h h'; rw [octetLt_irrefl] at this; exact absurd this (by simp)

/-- Tickets ordered strictly by identifier. -/
abbrev TicketLt (a b : Ticket) : Prop := octetLt a.id.toList b.id.toList = true

/-- `strictlyOrdered` is the pairwise strict order. -/
theorem strictlyOrdered_iff (l : List Ticket) : strictlyOrdered l = true ↔ l.Pairwise TicketLt := by
  induction l with
  | nil => simp [strictlyOrdered]
  | cons a l ih =>
    cases l with
    | nil => simp [strictlyOrdered]
    | cons b rest =>
      simp only [strictlyOrdered, Bool.and_eq_true, ih, List.pairwise_cons, List.mem_cons]
      constructor
      · rintro ⟨hab, hb, hrest⟩
        refine ⟨?_, hb, hrest⟩
        rintro x (rfl | hx)
        · exact hab
        · exact octetLt_trans _ _ _ hab (hb x hx)
      · rintro ⟨ha, hb, hrest⟩
        exact ⟨ha b (.inl rfl), hb, hrest⟩

/-- A strictly ordered list has unique identifiers. -/
theorem nodup_ids_of_pairwise {l : List Ticket} (h : l.Pairwise TicketLt) :
    (l.map (·.id.toList)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  refine h.imp fun {a b} hab heq => ?_
  rw [TicketLt, heq, octetLt_irrefl] at hab; exact absurd hab (by simp)

/-! ## Unfolding a successful transition -/

private theorem bind_ok_iff {ε α β} {x : Except ε α} {f : α → Except ε β} {r : β} :
    (x >>= f) = .ok r ↔ ∃ v, x = .ok v ∧ f v = .ok r := by
  cases x <;> simp [bind, Except.bind]

private theorem throw_ok_iff {ε α} {e : ε} {r : α} : (throw e : Except ε α) = .ok r ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

private theorem pure_ok_iff {ε α} {a r : α} : (pure a : Except ε α) = .ok r ↔ a = r := by
  simp [pure, Except.pure]

private theorem ite_eq_iff' {α} {p : Prop} [Decidable p] {a b r : α} :
    (if p then a else b) = r ↔ (p ∧ a = r) ∨ (¬p ∧ b = r) := by
  by_cases hp : p <;> simp [hp]

/-- A loop that throws on the first element failing a check succeeds only if every element passes. -/
private theorem forIn_guard_ok {α ε : Type} {l : List α} {p : α → Prop} [DecidablePred p] {e : ε}
    {v : PUnit} :
    (forIn l PUnit.unit fun t (_ : PUnit) =>
        if p t then (do throw e; pure (ForInStep.yield PUnit.unit))
        else (pure (ForInStep.yield PUnit.unit) : Except ε (ForInStep PUnit))) = Except.ok v →
    ∀ t ∈ l, ¬p t := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro h t ht
    rw [List.forIn_cons] at h
    by_cases hp : p a
    · simp [hp, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [hp, ite_false] at h
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hp
      · exact ih h t ht

/-- $\mathbf{n}$, the tickets of $\mathbf{E}_T$ with their identifiers (GP §6.7), as `safrole`
    computes them. -/
def newTickets (c : Crypto) (i : SafroleInput) : List Ticket :=
  i.tickets.map fun t => ({ id := ⟨(c.bsRingOut t.proof.toList).toArray⟩, attempt := t.attempt } : Ticket)

/-- The epoch changes: $e' > e$. -/
abbrev epochChange (params : Params) (s : SafroleState) (i : SafroleInput) : Prop :=
  i.slot / params.epochLen > s.tau / params.epochLen

/-- What a successful `safrole` checked, and the posterior fields these theorems use. Every
    conjunct is read off the definition. -/
theorem safrole_ok {params : Params} {c : Crypto} {s s' : SafroleState} {i : SafroleInput}
    {o : SafroleOutput} (h : safrole params c s i = .ok (s', o)) :
    s.tau < i.slot ∧
    (∀ t ∈ i.tickets, t.attempt < maxAttempts params s'.pending) ∧
    strictlyOrdered (newTickets c i) = true ∧
    (∀ t ∈ newTickets c i, ∀ b ∈ s.accumulator, t.id.toList ≠ b.id.toList) ∧
    s'.accumulator = ((newTickets c i ++ (if epochChange params s i then [] else s.accumulator)).mergeSort
        fun a b => !octetLt b.id.toList a.id.toList).take params.epochLen ∧
    s'.tau = i.slot ∧ s'.staging = s.staging ∧
    s'.pending = (if epochChange params s i then offendersFilter i.offenders s.staging
      else s.pending) ∧
    s'.active = (if epochChange params s i then s.pending else s.active) ∧
    s'.prev = (if epochChange params s i then s.active else s.prev) ∧
    s'.eta = [blake (s.eta.getD 0 [] ++ i.entropy),
      if epochChange params s i then s.eta.getD 0 [] else s.eta.getD 1 [],
      if epochChange params s i then s.eta.getD 1 [] else s.eta.getD 2 [],
      if epochChange params s i then s.eta.getD 2 [] else s.eta.getD 3 []] ∧
    s'.sealKeys =
      (if i.slot / params.epochLen = s.tau / params.epochLen + 1 ∧
          s.tau % params.epochLen ≥ params.epochTailStart ∧
          s.accumulator.length = params.epochLen then
        SealKeys.tickets (outsideIn s.accumulator)
      else if i.slot / params.epochLen = s.tau / params.epochLen then s.sealKeys
      else SealKeys.keys (fallbackKeys params
        (if epochChange params s i then s.eta.getD 1 [] else s.eta.getD 2 [])
        (if epochChange params s i then s.pending else s.active))) ∧
    o.ticketsMark =
      (if i.slot / params.epochLen = s.tau / params.epochLen ∧
          s.tau % params.epochLen < params.epochTailStart ∧
          params.epochTailStart ≤ i.slot % params.epochLen ∧
          s.accumulator.length = params.epochLen then some (outsideIn s.accumulator)
      else none) := by
  unfold safrole at h
  simp only [bind_ok_iff, throw_ok_iff, pure_ok_iff, ite_eq_iff', false_and, and_false,
    exists_false, false_or] at h
  obtain ⟨hslot, -, _, hfor1, _, -, hord, hdup, -, hres⟩ := h
  rw [Prod.mk.injEq] at hres
  obtain ⟨rfl, rfl⟩ := hres
  have hfor1 := forIn_guard_ok hfor1
  refine ⟨by omega, fun t ht => ?_, by simpa [newTickets] using hord, ?_, ?_, rfl, rfl, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have := hfor1 t ht; dsimp only at this ⊢; split <;> simp_all <;> omega
  · intro t ht b hb heq
    apply hdup
    simp only [List.any_eq_true, beq_iff_eq]
    exact ⟨t, by simpa [newTickets] using ht, b, hb, heq⟩
  all_goals (try (split <;> rfl))
  all_goals by_cases hc : epochChange params s i <;> simp [hc]

/-! ## The ticket accumulator $\gamma'_A$ -/

/-- $\gamma'_A$ has at most $\mathsf{E}$ tickets (GP eq. (6.5), `ticketaccumulatorsealticketsspec`:
    $\gamma_A \in [\![ T ]\!]_{:\mathsf{E}}$; $\gamma'_A$ keeps the $\mathsf{E}$ lowest of the merge, eq. (6.36)). -/
theorem safrole_accumulator_length {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o)) :
    s'.accumulator.length ≤ params.epochLen := by
  rw [(safrole_ok h).2.2.2.2.1]; exact List.length_take_le _ _

private theorem ticketLe_trans (a b d : Ticket) :
    (!octetLt b.id.toList a.id.toList) = true → (!octetLt d.id.toList b.id.toList) = true →
    (!octetLt d.id.toList a.id.toList) = true := by
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true]
  intro h1 h2
  cases h3 : octetLt d.id.toList a.id.toList
  · rfl
  · rcases octetLt_trichotomy b.id.toList a.id.toList with h | h | h
    · rw [h1] at h; exact absurd h (by simp)
    · rw [h] at h2; rw [h2] at h3; exact absurd h3 (by simp)
    · rw [octetLt_trans _ _ _ h3 h] at h2; exact absurd h2 (by simp)

private theorem ticketLe_total (a b : Ticket) :
    ((!octetLt b.id.toList a.id.toList) || (!octetLt a.id.toList b.id.toList)) = true := by
  cases h : octetLt b.id.toList a.id.toList
  · rfl
  · simp [octetLt_asymm h]

/-- If the prior $\gamma_A$ has unique identifiers, $\gamma'_A$ is strictly sorted by identifier and has
    unique identifiers (GP §6.7, eq. (6.36): $\gamma'_A$ is sorted by $y$; eq. (6.35): $\mathbf{n}$ is
    disjoint from $\gamma_A$). On an epoch change $\gamma_A$ is discarded and the hypothesis is not used; otherwise it is
    the conclusion of this theorem for the previous block, so these properties are invariant. -/
theorem safrole_accumulator_sorted {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    (hprior : (s.accumulator.map (·.id.toList)).Nodup) :
    strictlyOrdered s'.accumulator = true ∧ (s'.accumulator.map (·.id.toList)).Nodup := by
  obtain ⟨-, -, hord, hdup, hacc, -⟩ := safrole_ok h
  rw [strictlyOrdered_iff] at hord
  let base := if epochChange params s i then [] else s.accumulator
  have hbase : (base.map (·.id.toList)).Nodup := by
    by_cases hc : epochChange params s i
    · simp [base, hc]
    · simpa [base, hc] using hprior
  have hbase_sub : ∀ b ∈ base, b ∈ s.accumulator := by
    intro b hb; by_cases hc : epochChange params s i
    · simp [base, hc] at hb
    · simpa [base, hc] using hb
  have hL : ((newTickets c i ++ base).map (·.id.toList)).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨nodup_ids_of_pairwise hord, hbase, ?_⟩
    simp only [List.mem_map]
    rintro _ ⟨t, ht, rfl⟩ _ ⟨b, hb, rfl⟩
    exact hdup t ht b (hbase_sub b hb)
  let M := (newTickets c i ++ base).mergeSort fun a b => !octetLt b.id.toList a.id.toList
  have hMle := List.pairwise_mergeSort ticketLe_trans ticketLe_total (newTickets c i ++ base)
  have hMnd : (M.map (·.id.toList)).Nodup :=
    ((List.mergeSort_perm _ _).map _).nodup_iff.2 hL
  have hM : M.Pairwise TicketLt := by
    have := hMle.and (List.pairwise_map.1 hMnd)
    refine this.imp fun {a b} ⟨hle, hne⟩ => ?_
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hle
    rcases octetLt_trichotomy a.id.toList b.id.toList with h | h | h
    · exact h
    · exact absurd h hne
    · rw [hle] at h; exact absurd h (by simp)
  have hsub : s'.accumulator.Sublist M := by rw [hacc]; exact List.take_sublist _ _
  have hP := hM.sublist hsub
  exact ⟨(strictlyOrdered_iff _).2 hP, nodup_ids_of_pairwise hP⟩

/-- A strictly ordered $\gamma_A$ has unique identifiers, so strict order alone is invariant. -/
theorem safrole_accumulator_strictlyOrdered {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    (hprior : strictlyOrdered s.accumulator = true) : strictlyOrdered s'.accumulator = true :=
  (safrole_accumulator_sorted h (nodup_ids_of_pairwise ((strictlyOrdered_iff _).1 hprior))).1

/-! ## The seal-key sequence $\gamma'_S$ -/

/-- $|\gamma_S|$: the number of tickets or keys. -/
def SealKeys.length : SealKeys → Nat
  | .tickets t => t.length
  | .keys k => k.length

@[simp] theorem length_fallbackKeys (params : Params) (r : List UInt8) (k : List ValidatorKey) :
    (fallbackKeys params r k).length = params.epochLen := by
  simp [fallbackKeys]

/-- $\gamma'_S$ has $\mathsf{E}$ entries whenever it is recomputed, in the ticket case $Z(\gamma_A)$ and the
    fallback case $F(\eta'_2, \kappa')$ alike (GP eqs. (6.26), (6.28)); within an epoch it is $\gamma_S$, so a
    $\gamma_S$ of $\mathsf{E}$ entries stays one. -/
theorem safrole_sealKeys_length {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o)) :
    (i.slot / params.epochLen ≠ s.tau / params.epochLen →
      s'.sealKeys.length = params.epochLen) ∧
    (s.sealKeys.length = params.epochLen → s'.sealKeys.length = params.epochLen) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hseal, -⟩ := safrole_ok h
  rw [hseal]
  constructor
  · intro hne
    split
    · next hc => simp [SealKeys.length, hc.2.2]
    · simp [SealKeys.length]
  · intro hS
    split
    · next hc => simp [SealKeys.length, hc.2.2]
    · split
      · exact hS
      · simp [SealKeys.length]

/-- $\mathbf{H}_W$, when present, is $Z(\gamma_A)$ with $\mathsf{E}$ tickets (GP eq. (6.30), `winningticketsmarker`). -/
theorem safrole_ticketsMark_length {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    {w : List Ticket} (hw : o.ticketsMark = some w) :
    w.length = params.epochLen ∧ w.Perm s.accumulator := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hmark⟩ := safrole_ok h
  rw [hmark] at hw
  split at hw
  · next hc => cases hw; exact ⟨by simp [hc.2.2.2], outsideIn_perm _⟩
  · cases hw

/-! ## The entry-index bound $n$ -/

@[simp] theorem maxAttempts_nil (params : Params) : maxAttempts params [] = 0 := by
  simp [maxAttempts]

/-- For non-empty $\gamma'_P$, $n = \lceil 2\mathsf{E}/|\gamma'_P| \rceil$: the least $n$ with
    $2\mathsf{E} \le n \cdot |\gamma'_P|$ (GP eq. (6.31), `ticketsextrinsic`). -/
theorem maxAttempts_spec (params : Params) {p : List ValidatorKey} (hp : 0 < p.length) :
    2 * params.epochLen ≤ maxAttempts params p * p.length ∧
    ∀ m, 2 * params.epochLen ≤ m * p.length → maxAttempts params p ≤ m := by
  unfold maxAttempts
  generalize p.length = k at hp ⊢
  generalize 2 * params.epochLen = a
  have hdm := Nat.div_add_mod (a + k - 1) k
  have hr := Nat.mod_lt (a + k - 1) hp
  generalize (a + k - 1) / k = q at hdm ⊢
  generalize (a + k - 1) % k = r at hdm hr
  have hqk : q * k = k * q := Nat.mul_comm _ _
  refine ⟨by omega, fun m hm => ?_⟩
  refine Nat.le_of_not_lt fun hlt => ?_
  have := Nat.mul_le_mul_right k (Nat.succ_le_of_lt hlt)
  rw [Nat.succ_mul] at this
  omega

/-- In the paper $|\gamma'_P|$ is a multiple of 3 between 6 and $3\mathsf{C}$ (eqs. `validatorkeys`,
    `valcount`), so never 0. The model's $\gamma'_P$ is a list of any length; when it is empty
    $n = 0$, and a successful transition then admits no tickets. -/
theorem safrole_tickets_nil_of_pending_nil {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    (hp : s'.pending = []) : i.tickets = [] := by
  obtain ⟨-, hatt, -⟩ := safrole_ok h
  rw [hp, maxAttempts_nil] at hatt
  cases ht : i.tickets with
  | nil => rfl
  | cons t _ => exact absurd (hatt t (by simp [ht])) (Nat.not_lt_zero _)

/-- Every ticket of a successful $\mathbf{E}_T$ has an entry index below $n$. -/
theorem safrole_attempt_lt {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o)) :
    ∀ t ∈ i.tickets, t.attempt < maxAttempts params s'.pending :=
  (safrole_ok h).2.1

/-- $n \le 256$ whenever $2\mathsf{E} \le 256 \cdot |\gamma'_P|$. -/
theorem maxAttempts_le_256 (params : Params) {p : List ValidatorKey} (hp : 0 < p.length)
    (h : 2 * params.epochLen ≤ 256 * p.length) : maxAttempts params p ≤ 256 :=
  (maxAttempts_spec params hp).2 256 h

/-- The entry index fits the one octet `ticketContext` appends: on a successful transition with
    $2\mathsf{E} \le 256 \cdot |\gamma'_P|$, every $e$ of $\mathbf{E}_T$ is below 256, so `UInt8.ofNat e` does not truncate. -/
theorem safrole_attempt_fits {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    (hp : 2 * params.epochLen ≤ 256 * s'.pending.length) :
    ∀ t ∈ i.tickets, t.attempt < 256 ∧ (UInt8.ofNat t.attempt).toNat = t.attempt := by
  intro t ht
  have hlt := safrole_attempt_lt h t ht
  have hpos : 0 < s'.pending.length := by
    cases hq : s'.pending with
    | nil => rw [hq, maxAttempts_nil] at hlt; exact absurd hlt (Nat.not_lt_zero _)
    | cons _ _ => simp
  have h256 := maxAttempts_le_256 params hpos hp
  refine ⟨by omega, ?_⟩
  rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)

/-- With the paper's $|\gamma'_P| \ge 6$ (eq. `valcount`), the condition holds for $\mathsf{E} \le 768$, so for
    both the full chain ($\mathsf{E} = 600$) and the tiny one ($\mathsf{E} = 12$). -/
theorem attempt_fits_of_six (params : Params) {p : List ValidatorKey} (h6 : 6 ≤ p.length)
    (hE : params.epochLen ≤ 768) : 2 * params.epochLen ≤ 256 * p.length := by
  omega

/-! ## $\eta'$, $\tau'$ and the validator sets -/

private theorem byteArray_toList_eq_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  suffices h : ∀ i r, ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i by
    simpa [ByteArray.toList] using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct bs with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop, ite_eq_left h, ih]
    have hi : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.reverse_cons, List.append_assoc, List.drop_eq_getElem_cons hi]
    rw [List.singleton_append]
    have hb : bs.get! i = bs.data.toList[i] := by
      show bs.data[i]! = bs.data.toList[i]
      simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
    rw [hb]
  | case2 i r h =>
    rw [ByteArray.toList.loop, ite_eq_right h]
    have : bs.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp [List.drop_eq_nil_of_le this]

/-- $\mathcal{H}$ yields 32 octets. -/
@[simp] theorem length_blake (m : List UInt8) : (blake m).length = 32 := by
  simp [blake, Blake2b.hash256, Blake2b.hash, byteArray_toList_eq_data]

/-- The shape of the posterior: $\tau' = \mathbf{H}_T > \tau$; $\eta'$ has four entries,
    $\eta'_0 = \mathcal{H}(\eta_0 \frown \mathcal{Y}(\mathbf{H}_V))$ of 32 octets; $\iota' = \iota$;
    and on an epoch change $\kappa' = \gamma_P$, $\lambda' = \kappa$ and $\gamma'_P = \Phi(\iota)$,
    otherwise all three are unchanged (GP §5 eq. `timeslotindex`, §6.3, §6.4). -/
theorem safrole_shape {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o)) :
    s.tau < s'.tau ∧ s'.tau = i.slot ∧ s'.eta.length = 4 ∧
    s'.eta[0]? = some (blake (s.eta.getD 0 [] ++ i.entropy)) ∧ s'.staging = s.staging ∧
    (epochChange params s i → s'.active = s.pending ∧ s'.prev = s.active ∧
      s'.pending = offendersFilter i.offenders s.staging) ∧
    (¬epochChange params s i → s'.active = s.active ∧ s'.prev = s.prev ∧
      s'.pending = s.pending) := by
  obtain ⟨hlt, -, -, -, -, htau, hstg, hpend, hact, hprev, heta, -⟩ := safrole_ok h
  refine ⟨htau ▸ hlt, htau, by simp [heta], by simp [heta], hstg, fun hc => ?_, fun hc => ?_⟩
  · simp [hact, hprev, hpend, hc]
  · simp [hact, hprev, hpend, hc]

/-- If $\eta$ is four 32-octet hashes, so is $\eta'$ ($\eta \in [\![ \mathbb{H} ]\!]_4$, GP eq.
    `entropycomposition`); then no `getD` in the transition falls back to its default. -/
theorem safrole_eta_wf {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    (hlen : s.eta.length = 4) (hhash : ∀ x ∈ s.eta, x.length = 32) :
    s'.eta.length = 4 ∧ ∀ x ∈ s'.eta, x.length = 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, heta, -⟩ := safrole_ok h
  have hk : ∀ k, k < 4 → (s.eta.getD k []).length = 32 := fun k hk => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact hhash _ (List.getElem_mem _)
  refine ⟨by simp [heta], ?_⟩
  rw [heta]
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact length_blake _
  all_goals (split <;> exact hk _ (by omega))

/-! ## Typed views

The model keeps the public representation: a validator key is `List UInt8` and $\eta$ is
`List (List UInt8)`, read with `getD`. These views give the paper's types,
$\mathbb{K} = \mathbb{B}_{336}$ split into its components (GP §6.3: $k_b = k_{0 \cdots +32}$,
$k_e = k_{32 \cdots +32}$, $k_l = k_{64 \cdots +144}$, $k_m = k_{208 \cdots +128}$) and
$\eta \in [\![ \mathbb{H} ]\!]_4$ with $\mathbb{H} = \mathbb{B}_{32}$, with conversions that are
inverse to each other on well-formed values, and show that the transition keeps values
well-formed. -/

/-- A validator key in components: Bandersnatch $k_b$, Ed25519 $k_e$, BLS $k_l$, metadata $k_m$. -/
structure ValidatorKey.View where
  bs : Vector UInt8 32
  ed : Vector UInt8 32
  bls : Vector UInt8 144
  metadata : Vector UInt8 128

namespace ValidatorKey

/-- The octets of a structured key, $k = k_b \frown k_e \frown k_l \frown k_m$. -/
def ofView (v : View) : ValidatorKey := v.bs.toList ++ v.ed.toList ++ v.bls.toList ++ v.metadata.toList

private def slice (k : List UInt8) (o n : Nat) (h : o + n ≤ k.length) : Vector UInt8 n :=
  ⟨((k.drop o).take n).toArray, by simp; omega⟩

/-- The components of a key of 336 octets. -/
def toView (k : ValidatorKey) (h : k.length = 336) : View :=
  ⟨slice k 0 32 (by omega), slice k 32 32 (by omega), slice k 64 144 (by omega),
    slice k 208 128 (by omega)⟩

@[simp] theorem length_ofView (v : View) : (ofView v).length = 336 := by
  simp [ofView]

/-- The view's Bandersnatch component is `ValidatorKey.bs`. -/
theorem toView_bs (k : ValidatorKey) (h : k.length = 336) : (toView k h).bs.toList = k.bs := by
  simp [toView, slice, ValidatorKey.bs]

/-- The view's Ed25519 component is `ValidatorKey.ed`. -/
theorem toView_ed (k : ValidatorKey) (h : k.length = 336) : (toView k h).ed.toList = k.ed := by
  simp [toView, slice, ValidatorKey.ed]

theorem ofView_bs (v : View) : (ofView v).bs = v.bs.toList := by
  simp [ofView, ValidatorKey.bs, List.append_assoc]

theorem ofView_ed (v : View) : (ofView v).ed = v.ed.toList := by
  simp [ofView, ValidatorKey.ed, List.append_assoc]

theorem ofView_toView (k : ValidatorKey) (h : k.length = 336) : ofView (toView k h) = k := by
  simp only [ofView, toView, slice, Vector.toList_mk, List.drop_zero]
  have e1 : (k.drop 32).take 32 ++ ((k.drop 64).take 144 ++ (k.drop 208).take 128) = k.drop 32 := by
    conv => rhs; rw [← List.take_append_drop 32 (k.drop 32)]
    congr 1
    rw [List.drop_drop]
    conv => rhs; rw [← List.take_append_drop 144 (k.drop 64)]
    congr 1
    rw [List.drop_drop, List.take_of_length_le (by simp; omega)]
  rw [List.append_assoc, List.append_assoc, e1, List.take_append_drop]

theorem toView_ofView (v : View) : toView (ofView v) (length_ofView v) = v := by
  obtain ⟨b, e, l, m⟩ := v
  simp only [toView, slice, ofView, View.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Vector.toList_inj.1 <;> simp [List.append_assoc]
  · rw [show 64 = (b.toList ++ e.toList).length by simp, ← List.append_assoc, List.drop_left,
      List.take_left' (by simp)]
  · rw [show 208 = (b.toList ++ e.toList ++ l.toList).length by simp, ← List.append_assoc,
      ← List.append_assoc, List.drop_left, List.take_of_length_le (by simp)]

/-- $\nullvalkey$ is well-formed. -/
@[simp] theorem length_null : null.length = 336 := by
  show nullValidatorKey.length = 336
  simp only [nullValidatorKey, List.length_append, List.length_replicate, keySize, nullEdKey,
    List.length_cons]

end ValidatorKey

/-- $\Phi$ keeps keys well-formed. -/
theorem offendersFilter_wf (offenders : List (List UInt8)) {k : List ValidatorKey}
    (h : ∀ v ∈ k, v.length = 336) : ∀ v ∈ offendersFilter offenders k, v.length = 336 := by
  intro v hv
  simp only [offendersFilter, List.mem_map] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  split
  · exact ValidatorKey.length_null
  · exact h w hw

/-- $\eta$ as four 32-octet hashes, for an $\eta$ of that shape. -/
def etaView (eta : List (List UInt8)) (hlen : eta.length = 4) (hhash : ∀ x ∈ eta, x.length = 32) :
    Fin 4 → Vector UInt8 32 :=
  fun k => ⟨(eta[k.val]'(by omega)).toArray, by simp [hhash _ (List.getElem_mem _)]⟩

/-- On a well-formed $\eta$, `getD k []` (as the transition reads $\eta$) is the view's $k$-th
    hash. -/
theorem getD_eq_etaView (eta : List (List UInt8)) (hlen : eta.length = 4)
    (hhash : ∀ x ∈ eta, x.length = 32) (k : Fin 4) :
    eta.getD k.val [] = (etaView eta hlen hhash k).toList := by
  simp [etaView, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k.val < eta.length by omega)]

/-- Well-formed Safrole state: $\eta$ is four 32-octet hashes and every key of $\iota$, $\gamma_P$,
    $\kappa$, $\lambda$ is 336 octets (GP eqs. `entropycomposition`, `validatorkeys`). -/
structure SafroleState.WF (s : SafroleState) : Prop where
  eta_length : s.eta.length = 4
  eta_hash : ∀ x ∈ s.eta, x.length = 32
  staging : ∀ k ∈ s.staging, k.length = 336
  pending : ∀ k ∈ s.pending, k.length = 336
  active : ∀ k ∈ s.active, k.length = 336
  prev : ∀ k ∈ s.prev, k.length = 336

/-- The transition keeps the state well-formed. -/
theorem safrole_wf {params : Params} {c : Crypto} {s s' : SafroleState}
    {i : SafroleInput} {o : SafroleOutput} (h : safrole params c s i = .ok (s', o))
    (hs : s.WF) : s'.WF := by
  obtain ⟨-, -, -, -, -, -, hstg, hpend, hact, hprev, -⟩ := safrole_ok h
  have heta := safrole_eta_wf h hs.eta_length hs.eta_hash
  refine ⟨heta.1, heta.2, hstg ▸ hs.staging, ?_, ?_, ?_⟩
  · rw [hpend]; split
    · exact offendersFilter_wf _ hs.staging
    · exact hs.pending
  · rw [hact]; split
    · exact hs.pending
    · exact hs.active
  · rw [hprev]; split
    · exact hs.active
    · exact hs.prev

end JAM
