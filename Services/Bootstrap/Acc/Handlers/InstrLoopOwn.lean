import Services.Bootstrap.Acc.Handlers.InstrLoopHyp

/-!
# R5, the instruction loop: moving a result

Spec `onWorkItem`'s `results := results ++ [r]` (GP v0.8.0 Appendix B, Ω_W; bootstrap's own loop). A
handler leaves its `Result` r in the frame at sp + 1000; the tail copies its 144 octets onto the results
`Vec`. `ResultAtP.copy` carries `ResultAtP` (`ResultsAvoid.lean`) from address a in μ to address a′ in μ′,
when the 144 octets are equal and the chunks holding r's buffers keep their data.
-/

namespace Services.Bootstrap.Acc.Handlers.Results

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Spec Services.Bootstrap.Decode.LoopA
open JAM.Codec (fixed)

variable {μ μ' : Memory} {C C' : Chunk → Prop}

/-- **A result moves with its 144 octets**: if the octets at a′ in μ′ are those at a in μ, and every chunk
    satisfying C satisfies C′ with its data kept, the result at a (chunks C) is at a′ (chunks C′). -/
theorem ResultAtP.copy (hC : ∀ d, C d → C' d ∧ ∀ a, InData d a → μ'.read a = μ.read a) {a a' : Nat}
    (he : ∀ o, o < 144 → μ'.read (a' + o) = μ.read (a + o)) {r : Spec.Result}
    (h : ResultAtP μ C a r) : ResultAtP μ' C' a' r := by
  have e : ∀ o n, o + n ≤ 144 → μ'.readN (a' + o) n = μ.readN (a + o) n := fun o n h =>
    readN_congr2 fun j hj => by
      rw [show a' + o + j = a' + (o + j) by omega, show a + o + j = a + (o + j) by omega]
      exact he _ (by omega)
  have e0 : μ'.readN a' 1 = μ.readN a 1 := by simpa using e 0 1 (by omega)
  have vec : ∀ o bs, o + 24 ≤ 144 → VecAtP μ C (a + o) bs → VecAtP μ' C' (a' + o) bs := by
    intro o bs ho hv
    obtain ⟨cap, ptr, m0, m8, m16, md, hd⟩ := hv
    obtain ⟨hd', ed⟩ := InHeapP.mono hC hd
    refine ⟨cap, ptr, (e o 8 (by omega)).trans m0, ?_, ?_, ed.trans md, hd'⟩
    · rw [show a' + o + 8 = a' + (o + 8) by omega, e (o + 8) 8 (by omega), ← m8]; congr 1
    · rw [show a' + o + 16 = a' + (o + 16) by omega, e (o + 16) 8 (by omega), ← m16]; congr 1
  cases r with
  | error er => exact ⟨e0.trans h.1, by rw [e 1 1 (by omega)]; exact h.2⟩
  | ok r =>
    cases r with
    | unit => exact e0.trans h
    | serviceId i => exact ⟨e0.trans h.1, (e 4 4 (by omega)).trans h.2.1, h.2.2⟩
    | length n => exact ⟨e0.trans h.1, (e 4 4 (by omega)).trans h.2.1, h.2.2⟩
    | transferred d am m =>
      obtain ⟨h0, h4, hd, h8, ha', hl, h16⟩ := h
      exact ⟨e0.trans h0, (e 4 4 (by omega)).trans h4, hd, (e 8 8 (by omega)).trans h8, ha', hl,
        (e 16 128 (by omega)).trans h16⟩
    | hash hh => exact ⟨e0.trans h.1, h.2.1, (e 1 32 (by omega)).trans h.2.2⟩
    | data d => exact ⟨e0.trans h.1, vec 8 d (by omega) h.2⟩
    | dataVec ds =>
      obtain ⟨h0, cap, ptr, m8, m16, m24, hp, hj⟩ := h
      refine ⟨e0.trans h0, cap, ptr, (e 8 8 (by omega)).trans m8, (e 16 8 (by omega)).trans m16,
        (e 24 8 (by omega)).trans m24, (InHeapP.mono hC hp).1, fun j hj' => ?_⟩
      exact VecAtP.mono hC (hp.sub (by omega) (by
        have : 24 * j + 24 ≤ 24 * ds.length := by have := Nat.mul_le_mul_left 24 (Nat.succ_le_of_lt hj'); omega
        omega)) (hj j hj')

/-- `ResultAtP` gives `ResultAt` when C's chunks are allocated in st. -/
theorem ResultAtP.toAt' {st : State} (hC : ∀ d, C d → d ∈ chunks st ∧ d.used = true) {a : Nat}
    {r : Spec.Result} (h : ResultAtP μ C a r) : ResultAt μ st a r := by
  cases r with
  | error e => exact h
  | ok r => exact OkAtP.toAt hC h

end Services.Bootstrap.Acc.Handlers.Results

namespace Services.Bootstrap.Acc.Handlers.InstrRep

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 2000000

/-- The buffers the `IntoIter` frees, with one more instruction: the first slot's `foot`, then the rest
    from the next slot on. -/
theorem iterFree_succ (B : InstrRep) (μ : Memory) (v m : Nat) :
    iterFree B μ v (m + 1) = B.foot (slot μ (rdN μ (v + 8) 8) 0) ++
      (((List.range m).flatMap fun k => B.foot (slot μ (rdN μ (v + 8) 8) (k + 1))) ++
        optBuf (rdN μ (v + 16) 8) (rdN μ v 8)) := by
  unfold iterFree
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.append_assoc]

/-- **The `IntoIter` after one instruction**: from `IterOwn` for i :: is at (μ, st), with the cursor
    advanced by one slot (buf, cap and end kept) in μ′, and every buffer the `IntoIter` still owns
    (`iterFree` but the first slot's `foot`) kept in st′ with its data, `IterOwn` holds for is at
    (μ′, st′), and the old `iterFree` is the first slot's `foot` followed by the new one. -/
theorem IterOwn.step {B : InstrRep} {μ μ' : Memory} {st st' : State} {v : Nat} {i : Spec.Instr}
    {is : List Spec.Instr} (I : IterOwn B μ st v (i :: is))
    (hcur : rdN μ' (v + 8) 8 = rdN μ (v + 8) 8 + 232) (hend : rdN μ' (v + 24) 8 = rdN μ (v + 24) 8)
    (hbuf : rdN μ' v 8 = rdN μ v 8) (hcap : rdN μ' (v + 16) 8 = rdN μ (v + 16) 8)
    (hk : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ iterFree B μ v (is.length + 1) →
      d.addr + 32 ∉ B.foot (slot μ (rdN μ (v + 8) 8) 0) →
      d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a) :
    IterOwn B μ' st' v is ∧
      iterFree B μ v (is.length + 1) = B.foot (slot μ (rdN μ (v + 8) 8) 0) ++ iterFree B μ' v is.length := by
  have hlen : (i :: is).length = is.length + 1 := rfl
  have hE := I.hend
  rw [hlen] at hE
  obtain ⟨hc0, d, hd, hu, hdq, hbc, hed⟩ := I.slots (List.cons_ne_nil _ _)
  have hnd := I.nodup
  rw [hlen, iterFree_succ] at hnd
  have hmem : rdN μ v 8 ∈ iterFree B μ v (is.length + 1) := by
    rw [iterFree_succ]; simp [optBuf, hc0]
  have hnot : rdN μ v 8 ∉ B.foot (slot μ (rdN μ (v + 8) 8) 0) := by
    intro h
    have := (List.nodup_append.1 hnd).2.2 _ h (rdN μ v 8) (List.mem_append_right _ (by simp [optBuf, hc0]))
    exact this rfl
  obtain ⟨hd', hkd⟩ := hk d hd hu (by rw [hdq]; exact hmem) (by rw [hdq]; exact hnot)
  -- the slots are kept
  have hsl : ∀ k, k < is.length → slot μ' (rdN μ' (v + 8) 8) k = slot μ (rdN μ (v + 8) 8) (k + 1) := by
    intro k hk'
    unfold slot
    rw [hcur]
    refine readN_congr2 fun j hj => ?_
    rw [show rdN μ (v + 8) 8 + 232 + 232 * k + j = rdN μ (v + 8) 8 + 232 * (k + 1) + j by omega]
    refine hkd _ ⟨by omega, ?_⟩
    have : 232 * (k + 1) + 232 ≤ 232 * (is.length + 1) := by
      have := Nat.mul_le_mul_left 232 (Nat.succ_le_of_lt (Nat.succ_lt_succ hk')); omega
    omega
  have hrest : iterFree B μ' v is.length =
      ((List.range is.length).flatMap fun k => B.foot (slot μ (rdN μ (v + 8) 8) (k + 1))) ++
        optBuf (rdN μ (v + 16) 8) (rdN μ v 8) := by
    unfold iterFree
    rw [hcap, hbuf]
    have gen : ∀ l : List Nat, (∀ k ∈ l, k < is.length) →
        (l.flatMap fun k => B.foot (slot μ' (rdN μ' (v + 8) 8) k)) =
          l.flatMap fun k => B.foot (slot μ (rdN μ (v + 8) 8) (k + 1)) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a t ih =>
        intro h
        simp only [List.flatMap_cons]
        rw [hsl a (h a (List.mem_cons_self ..)), ih (fun k hk => h k (List.mem_cons_of_mem _ hk))]
    rw [gen _ (fun k hk => List.mem_range.1 hk)]
  have hnd' := (List.nodup_append.1 hnd).2.1
  have kept : ∀ q ∈ iterFree B μ' v is.length, ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = q ∧
      d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a := by
    intro q hq
    rw [hrest] at hq
    have hq1 : q ∈ iterFree B μ v (is.length + 1) := by rw [iterFree_succ]; exact List.mem_append_right _ hq
    obtain ⟨e, he, heu, heq⟩ := I.owned q (by rw [hlen]; exact hq1)
    have hq2 : q ∉ B.foot (slot μ (rdN μ (v + 8) 8) 0) := fun h =>
      (List.nodup_append.1 hnd).2.2 _ h _ hq rfl
    exact ⟨e, he, heu, heq, hk e he heu (by rw [heq]; exact hq1) (by rw [heq]; exact hq2)⟩
  refine ⟨⟨?_, fun k hk' => ?_, by rw [hrest]; exact hnd', fun q hq => ?_, fun _ => ?_⟩,
    by rw [iterFree_succ, hrest]⟩
  · rw [hend, hcur]; omega
  · rw [hsl k hk']
    have hr := I.rep (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at hr
    refine B.frame _ _ μ μ' st' hr fun q hq => ?_
    have hq' : q ∈ iterFree B μ' v is.length := by
      rw [hrest]; exact List.mem_append_left _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk', hq⟩)
    obtain ⟨e, -, heu, heq, he', hke⟩ := kept q hq'
    exact ⟨e, he', heu, heq, hke⟩
  · obtain ⟨e, -, heu, heq, he', -⟩ := kept q hq
    exact ⟨e, he', heu, heq⟩
  · refine ⟨by rw [hcap]; exact hc0, d, hd', hu, by rw [hbuf]; exact hdq, ?_, ?_⟩
    · rw [hbuf, hcur]; omega
    · rw [hend]; exact hed

end Services.Bootstrap.Acc.Handlers.InstrRep

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Alloc Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.ResultsDrop

set_option maxHeartbeats 2000000

section Push

variable {μ μ' : Memory} {st st' : State} {rp rp' n : Nat}

/-- A word read at a′ in μ′ equals the word at a in μ when the octets are equal. -/
theorem rdN_move {a a' m : Nat} (h : ∀ j, j < m → μ'.read (a' + j) = μ.read (a + j)) : rdN μ' a' m = rdN μ a m := by
  unfold rdN; rw [readN_congr2 h]

/-- The items moved from rp (in μ) to rp′ (in μ′): their words. -/
theorem item_move (hmv : ∀ k, k < 144 * n → μ'.read (rp' + k) = μ.read (rp + k)) {i o m : Nat} (hi : i < n)
    (hom : o + m ≤ 144) : rdN μ' (rp' + 144 * i + o) m = rdN μ (rp + 144 * i + o) m :=
  rdN_move fun j hj => by
    have : 144 * i + 144 ≤ 144 * n := by have := Nat.mul_le_mul_left 144 (Nat.succ_le_of_lt hi); omega
    rw [show rp' + 144 * i + o + j = rp' + (144 * i + o + j) by omega,
      show rp + 144 * i + o + j = rp + (144 * i + o + j) by omega]
    exact hmv _ (by omega)

theorem itemPtrs_move (O : ResultsOwn μ st rp n) (hmv : ∀ k, k < 144 * n → μ'.read (rp' + k) = μ.read (rp + k))
    (hk : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ resPtrs μ rp n → d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a) {i : Nat} (hi : i < n) :
    itemPtrs μ' (rp' + 144 * i) = itemPtrs μ (rp + 144 * i) := by
  have e0 := item_move hmv hi (o := 0) (m := 1) (by omega)
  simp only [Nat.add_zero] at e0
  have e8 := item_move hmv hi (o := 8) (m := 8) (by omega)
  have e16 := item_move hmv hi (o := 16) (m := 8) (by omega)
  have e24 := item_move hmv hi (o := 24) (m := 8) (by omega)
  unfold itemPtrs
  rw [e0, e8, e16, e24]
  by_cases h5 : rdN μ (rp + 144 * i) 1 = 5
  · rw [if_pos h5, if_pos h5]
  · rw [if_neg h5, if_neg h5]
    by_cases hv : 6 ≤ rdN μ (rp + 144 * i) 1 ∧ rdN μ (rp + 144 * i) 1 < 255
    · rw [if_pos hv, if_pos hv]
      suffices hin : innerPtrs μ' (rdN μ (rp + 144 * i + 16) 8) (rdN μ (rp + 144 * i + 24) 8) =
          innerPtrs μ (rdN μ (rp + 144 * i + 16) 8) (rdN μ (rp + 144 * i + 24) 8) by rw [hin]
      by_cases hL : rdN μ (rp + 144 * i + 24) 8 = 0
      · rw [hL]; simp [innerPtrs]
      · obtain ⟨hc, d, hd, hu, hq, hend⟩ := O.2.2.2 i hi hv.1 hv.2 hL
        have hmem : d.addr + 32 ∈ resPtrs μ rp n := by
          unfold resPtrs
          refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, ?_⟩
          unfold itemPtrs
          rw [if_neg h5, if_pos hv, hq]
          exact List.mem_append_right _ (by simp [hc])
        have hk' := (hk d hd hu hmem).2
        apply innerPtrs_congr
        intro j hj
        exact ⟨rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩,
          rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩⟩
    · rw [if_neg hv, if_neg hv]

theorem resPtrs_move (O : ResultsOwn μ st rp n) (hmv : ∀ k, k < 144 * n → μ'.read (rp' + k) = μ.read (rp + k))
    (hk : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ resPtrs μ rp n → d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a) : ∀ k, k ≤ n → resPtrs μ' rp' k = resPtrs μ rp k
  | 0, _ => by simp [resPtrs]
  | k + 1, h => by
    rw [resPtrs_succ, resPtrs_succ, resPtrs_move O hmv hk k (by omega), itemPtrs_move O hmv hk (by omega)]

/-- **`ResultsOwn` after a push** (GP v0.8.0 Appendix B, Ω_W's results; bootstrap's `Vec::push`): the n
    items moved from rp to rp′ (their owned buffers kept with their data in st′), a new item at
    rp′ + 144·n owning its buffers in chunks C of st′ (`ItemOwn`), the owned buffers pairwise distinct,
    and every item octet in a chunk d′ of st′ that is not owned: `ResultsOwn` for n + 1 items at rp′. -/
theorem ResultsOwn.push (O : ResultsOwn μ st rp n) (hmv : ∀ k, k < 144 * n → μ'.read (rp' + k) = μ.read (rp + k))
    (hk : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ resPtrs μ rp n → d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a)
    {C : Chunk → Prop} (hI : ItemOwn μ' C (rp' + 144 * n)) (hC : ∀ d, C d → d ∈ chunks st' ∧ d.used = true)
    (hnd : (resPtrs μ rp n ++ itemPtrs μ' (rp' + 144 * n)).Nodup)
    (hbuf : ∃ d' ∈ chunks st', d'.used = true ∧ (∀ k, k < 144 * (n + 1) → InData d' (rp' + k)) ∧
      d'.addr + 32 ∉ resPtrs μ rp n ++ itemPtrs μ' (rp' + 144 * n)) :
    ResultsOwn μ' st' rp' (n + 1) := by
  have hr : resPtrs μ' rp' (n + 1) = resPtrs μ rp n ++ itemPtrs μ' (rp' + 144 * n) := by
    rw [resPtrs_succ, resPtrs_move O hmv hk n (Nat.le_refl _)]
  obtain ⟨d', hd', hu', hin', hn'⟩ := hbuf
  refine ⟨hr ▸ hnd, fun q hq => ?_, fun k hk' => ⟨d', hd', hu', hin' k hk', hr ▸ hn'⟩, fun i hi h6 h255 hL => ?_⟩
  · rw [hr] at hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨d, hd, hu, ha⟩ := O.2.1 q hq
      exact ⟨d, (hk d hd hu (ha ▸ hq)).1, hu, ha⟩
    · obtain ⟨d, hCd, ha⟩ := hI.2.1 q hq
      exact ⟨d, (hC d hCd).1, (hC d hCd).2, ha⟩
  · rcases Nat.lt_or_ge i n with hin | hin
    · have e0 := item_move hmv hin (o := 0) (m := 1) (by omega)
      simp only [Nat.add_zero] at e0
      rw [item_move hmv hin (o := 8) (m := 8) (by omega), item_move hmv hin (o := 16) (m := 8) (by omega)]
      rw [item_move hmv hin (o := 24) (m := 8) (by omega)] at hL ⊢
      rw [e0] at h6 h255
      obtain ⟨hc, d, hd, hu, hq, hend⟩ := O.2.2.2 i hin h6 h255 hL
      have h5 : rdN μ (rp + 144 * i) 1 ≠ 5 := by omega
      have hmem : d.addr + 32 ∈ resPtrs μ rp n := by
        unfold resPtrs
        refine List.mem_flatMap.2 ⟨i, List.mem_range.2 hin, ?_⟩
        unfold itemPtrs
        rw [if_neg h5, if_pos ⟨h6, h255⟩, hq]
        exact List.mem_append_right _ (by simp [hc])
      exact ⟨hc, d, (hk d hd hu hmem).1, hu, hq, hend⟩
    · have hi' : i = n := by omega
      subst hi'
      obtain ⟨hc, d, hCd, hq, hend⟩ := hI.2.2 h6 h255 hL
      exact ⟨hc, d, (hC d hCd).1, (hC d hCd).2, hq, hend⟩

end Push


section Pay

open Services.Bootstrap.Acc.Handlers.Results

variable {μ μ' : Memory} {st st' : State} {rp rp' : Nat}

/-- **The results' payloads avoid F**: each item's payload buffers (the chunks `ResultAtP` names) are
    allocated chunks of st whose data address is not in F. The item octets themselves are not covered. -/
def PayAvoid (μ : Memory) (st : State) (rp : Nat) (rs : List Spec.Result) (F : List Nat) : Prop :=
  ∀ j (hj : j < rs.length), ResultAtP μ (AvoidC st F) (rp + 144 * j) rs[j]

/-- **`PayAvoid` after a push**: the items moved from rp to rp′, their payload chunks kept (avoiding F′), and
    the new result at rp′ + 144·|rs| with payloads avoiding F′. -/
theorem PayAvoid.push {rs : List Spec.Result} {r : Spec.Result} {F F' : List Nat} (hp : PayAvoid μ st rp rs F)
    (hmv : ∀ k, k < 144 * rs.length → μ'.read (rp' + k) = μ.read (rp + k))
    (hC : ∀ d, AvoidC st F d → AvoidC st' F' d ∧ ∀ a, InData d a → μ'.read a = μ.read a)
    (hr : ResultAtP μ' (AvoidC st' F') (rp' + 144 * rs.length) r) : PayAvoid μ' st' rp' (rs ++ [r]) F' := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j rs.length with hjn | hjn
  · rw [List.getElem_append_left hjn]
    refine ResultAtP.copy hC (fun o ho => ?_) (hp j hjn)
    have : 144 * j + 144 ≤ 144 * rs.length := by have := Nat.mul_le_mul_left 144 (Nat.succ_le_of_lt hjn); omega
    rw [show rp' + 144 * j + o = rp' + (144 * j + o) by omega, show rp + 144 * j + o = rp + (144 * j + o) by omega]
    exact hmv _ (by omega)
  · have hj' : j = rs.length := by omega
    subst hj'
    rw [List.getElem_append_right (Nat.le_refl _)]
    simpa using hr

/-- `PayAvoid` with the item octets in chunks avoiding F is `ResultsAvoid`. -/
theorem PayAvoid.toAvoid {rs : List Spec.Result} {F : List Nat} (hp : PayAvoid μ st rp rs F)
    (hb : InHeapP (AvoidC st F) rp (144 * rs.length)) : ResultsAvoid μ st rp rs F := ⟨hb, hp⟩

/-- `PayAvoid` for a larger F gives it for a smaller one. -/
theorem PayAvoid.mono {rs : List Spec.Result} {F F' : List Nat} (hp : PayAvoid μ st rp rs F)
    (hF : ∀ q, q ∈ F' → q ∈ F) : PayAvoid μ st rp rs F' := fun j hj =>
  ResultAtP.copy (μ' := μ) (fun d hd => ⟨⟨hd.1, hd.2.1, fun h => hd.2.2 (hF _ h)⟩, fun _ _ => rfl⟩)
    (fun _ _ => rfl) (hp j hj)

end Pay


section ItemCopy

variable {μ μ' : Memory} {C C' : Chunk → Prop}

/-- **An item's buffers move with its 144 octets**: copied from a (in μ) to a′ (in μ′), with the chunks C
    kept as C′ with their data, the item owns the same buffers (`itemPtrs`) and `ItemOwn` holds at a′. -/
theorem ItemOwn.copy {a a' : Nat} (he : ∀ o, o < 144 → μ'.read (a' + o) = μ.read (a + o))
    (hC : ∀ d, C d → C' d ∧ ∀ x, InData d x → μ'.read x = μ.read x) (hI : ItemOwn μ C a) :
    itemPtrs μ' a' = itemPtrs μ a ∧ ItemOwn μ' C' a' := by
  have w : ∀ o m, o + m ≤ 144 → rdN μ' (a' + o) m = rdN μ (a + o) m := fun o m h =>
    rdN_move fun j hj => by
      rw [show a' + o + j = a' + (o + j) by omega, show a + o + j = a + (o + j) by omega]; exact he _ (by omega)
  have e0 : rdN μ' a' 1 = rdN μ a 1 := by simpa using w 0 1 (by omega)
  have e8 := w 8 8 (by omega)
  have e16 := w 16 8 (by omega)
  have e24 := w 24 8 (by omega)
  have hp : itemPtrs μ' a' = itemPtrs μ a := by
    unfold itemPtrs
    rw [e0, e8, e16, e24]
    by_cases h5 : rdN μ a 1 = 5
    · rw [if_pos h5, if_pos h5]
    · rw [if_neg h5, if_neg h5]
      by_cases hv : 6 ≤ rdN μ a 1 ∧ rdN μ a 1 < 255
      · rw [if_pos hv, if_pos hv]
        suffices hin : innerPtrs μ' (rdN μ (a + 16) 8) (rdN μ (a + 24) 8) =
            innerPtrs μ (rdN μ (a + 16) 8) (rdN μ (a + 24) 8) by rw [hin]
        by_cases hL : rdN μ (a + 24) 8 = 0
        · rw [hL]; simp [innerPtrs]
        · obtain ⟨-, d, hCd, hq, hend⟩ := hI.2.2 hv.1 hv.2 hL
          have hk' := (hC d hCd).2
          apply innerPtrs_congr
          intro j hj
          exact ⟨rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩,
            rdN_frame fun l hl => hk' _ ⟨by omega, by omega⟩⟩
      · rw [if_neg hv, if_neg hv]
  refine ⟨hp, hp ▸ hI.1, fun q hq => ?_, fun h6 h255 hL => ?_⟩
  · obtain ⟨d, hCd, ha⟩ := hI.2.1 q (hp ▸ hq)
    exact ⟨d, (hC d hCd).1, ha⟩
  · rw [e0] at h6 h255; rw [e24] at hL
    rw [e8, e16, e24]
    obtain ⟨hc, d, hCd, hq, hend⟩ := hI.2.2 h6 h255 hL
    exact ⟨hc, d, (hC d hCd).1, hq, hend⟩

end ItemCopy

end Services.Bootstrap.Acc.Handlers.InstrLoop
