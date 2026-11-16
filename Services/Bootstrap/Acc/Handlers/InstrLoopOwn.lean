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
    (μ′, st′). -/
theorem IterOwn.step {B : InstrRep} {μ μ' : Memory} {st st' : State} {v : Nat} {i : Spec.Instr}
    {is : List Spec.Instr} (I : IterOwn B μ st v (i :: is))
    (hcur : rdN μ' (v + 8) 8 = rdN μ (v + 8) 8 + 232) (hend : rdN μ' (v + 24) 8 = rdN μ (v + 24) 8)
    (hbuf : rdN μ' v 8 = rdN μ v 8) (hcap : rdN μ' (v + 16) 8 = rdN μ (v + 16) 8)
    (hk : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ iterFree B μ v (is.length + 1) →
      d.addr + 32 ∉ B.foot (slot μ (rdN μ (v + 8) 8) 0) →
      d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a) :
    IterOwn B μ' st' v is := by
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
  refine ⟨?_, fun k hk' => ?_, by rw [hrest]; exact hnd', fun q hq => ?_, fun _ => ?_⟩
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
