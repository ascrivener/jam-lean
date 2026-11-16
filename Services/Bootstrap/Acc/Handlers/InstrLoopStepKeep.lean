import Services.Bootstrap.Acc.Handlers.InstrLoopStep

/-!
# R5, the instruction loop: the old chunks after one instruction

`LoopAt.stepKeep`, from `LoopAt.step`'s premises: the buffers the `IntoIter`'s drop frees after the
instruction are among those before it, and every allocated chunk of the head's state that is not the
instruction's buffer, the results buffer or a result's buffer is kept with its data and is neither a new
result's buffer nor the new results buffer. The loop's invariant (`LoopInv`) uses it to keep the chunks
the entry owns outside the instructions (GP v0.8.0 Appendix B, Ω_W's loop; bootstrap's own loop).
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Alloc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results
  Services.Bootstrap.Acc.Handlers.InstrRep Services.Bootstrap.Acc.Handlers.RowEleven
  Services.Bootstrap.Acc.Handlers.ResultsDrop

set_option maxHeartbeats 4000000

/-- What one body keeps of the head's chunks (memory μ, state st; after: μ′, st′, with is left and n
    results before): the drop's buffers shrink, and every allocated chunk of st outside the instruction's
    buffers, the results buffer and the results' buffers is kept with its data and avoids the new
    results' buffers and the new results buffer. -/
def StepKeep (B : InstrRep) (sp : Nat) (is : List Spec.Instr) (n : Nat) (μ : Memory) (st : State)
    (μ' : Memory) (st' : State) : Prop :=
  (∀ q ∈ iterFree B μ' (sp + 472) is.length, q ∈ iterFree B μ (sp + 472) (is.length + 1)) ∧
  ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ B.foot (slot μ (rdN μ (sp + 480) 8) 0) →
    d.addr + 32 ∉ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) →
    d.addr + 32 ∉ resPtrs μ (rdN μ (sp + 456) 8) n →
    d ∈ chunks st' ∧ (∀ a, InData d a → μ'.read a = μ.read a) ∧
    d.addr + 32 ∉ resPtrs μ' (rdN μ' (sp + 456) 8) (n + 1) ∧ d.addr + 32 ≠ rdN μ' (sp + 456) 8

theorem LoopAt.stepKeep {B : InstrRep} {code : ByteArray} {pb S0 S1 sp : Nat} {i : Spec.Instr}
    {is : List Spec.Instr} {rs : List Spec.Result} {zs : Bool} {μ μ' : Memory}
    {st st' : State} {rp' : Nat}
    (L : LoopAt B code pb S0 S1 sp (i :: is) rs zs μ st) (H' : HeapCtxC code pb S0 S1 μ' st')
    (hcur : rdN μ' (sp + 472 + 8) 8 = rdN μ (sp + 472 + 8) 8 + 232)
    (hend : rdN μ' (sp + 472 + 24) 8 = rdN μ (sp + 472 + 24) 8)
    (hbuf : rdN μ' (sp + 472) 8 = rdN μ (sp + 472) 8)
    (hcapI : rdN μ' (sp + 472 + 16) 8 = rdN μ (sp + 472 + 16) 8)
    (m456 : rdN μ' (sp + 456) 8 = rp')
    (hkeep : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0) →
      d.addr + 32 ∉ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) →
      d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a)
    (hmv : ∀ k, k < 144 * rs.length → μ'.read (rp' + k) = μ.read (rdN μ (sp + 456) 8 + k))
    (hd' : ∃ d' ∈ chunks st', d'.used = true ∧ d'.addr + 32 = rp' ∧
      ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0) →
        d.addr + 32 ∉ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) → d ≠ d')
    (hown : ItemOwn μ' (NewC st st' (B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0)) rp') (rp' + 144 * rs.length)) :
    StepKeep B sp is rs.length μ st μ' st' := by
  have hT := L.T
  have hn := L.hn
  rw [show sp + 472 + 8 = sp + 480 by omega] at hcur hkeep hd' hown
  generalize hF : B.foot (slot μ (rdN μ (sp + 480) 8) 0) = F at hkeep hown hd'
  generalize hrp : rdN μ (sp + 456) 8 = rp at hkeep hmv hd'
  generalize hcp : rdN μ (sp + 448) 8 = cp at hkeep hd'
  have hnd := L.hnd
  obtain ⟨d', hd'm, hd'u, hd'a, hd'n⟩ := hd'
  have hnotRP : ∀ q ∈ iterFree B μ (sp + 472) (is.length + 1), q ∉ optBuf cp rp := fun q h1 h3 =>
    nd_dis hnd h1 (List.mem_append_right _ (by
      unfold tailBufs; rw [hcp, hrp]; simp only [List.mem_append]; exact .inl (.inl h3)))
  obtain ⟨-, hIF⟩ := InstrRep.IterOwn.step L.I hcur hend hbuf hcapI
    (fun d hd hu h1 h2 => hkeep d hd hu (by rw [← hF]; rw [show sp + 472 + 8 = sp + 480 by omega] at h2; exact h2)
      (hnotRP _ h1))
  have O0 : ResultsOwn μ st rp rs.length := by rw [← hrp, ← hn]; exact hT.O
  -- the results' buffers are neither F nor the results buffer
  have eTF : tailFree μ sp = resPtrs μ rp rs.length ++ (optBuf cp rp ++ optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) ++
      optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8)) := by
    unfold tailFree tailBufs; rw [hcp, hrp, hn]
  have hnd' := hnd
  rw [show (i :: is).length = is.length + 1 from rfl, hIF, show sp + 472 + 8 = sp + 480 by omega, hF, eTF] at hnd'
  have hRF : ∀ q ∈ resPtrs μ rp rs.length, q ∉ F := fun q hq hqF =>
    nd_dis hnd' (List.mem_append_left _ hqF) (List.mem_append_left _ hq)
  have hRO : ∀ q ∈ resPtrs μ rp rs.length, q ∉ optBuf cp rp := fun q hq hqO =>
    nd_dis (List.nodup_append.1 hnd').2.1 hq (List.mem_append_left _ (List.mem_append_left _ hqO))
  have hkRP : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ resPtrs μ rp rs.length → d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a := fun d hd hu h => hkeep d hd hu (hRF _ h) (hRO _ h)
  have eRP : resPtrs μ' rp' (rs.length + 1) = resPtrs μ rp rs.length ++ itemPtrs μ' (rp' + 144 * rs.length) := by
    rw [resPtrs_succ, resPtrs_move O0 hmv hkRP rs.length (Nat.le_refl _)]
  refine ⟨fun q hq => ?_, fun d hd hu h1 h2 h3 => ?_⟩
  · rw [hIF, show sp + 472 + 8 = sp + 480 by omega]; exact List.mem_append_right _ hq
  · obtain ⟨k1, k2⟩ := hkeep d hd hu h1 h2
    refine ⟨k1, k2, ?_, ?_⟩
    · rw [m456, eRP]; intro h
      rcases List.mem_append.1 h with h | h
      · exact h3 h
      · obtain ⟨e, he, hea⟩ := hown.2.1 _ h
        exact he.2.2.1 d hd hu h1 (by omega)
    · rw [m456]; intro h
      exact hd'n d hd hu h1 h2 (chunk_addr H' k1 hd'm (by rw [h, hd'a]))

end Services.Bootstrap.Acc.Handlers.InstrLoop
