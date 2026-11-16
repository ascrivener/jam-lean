import Services.Bootstrap.Acc.Handlers.InstrLoopInv

/-!
# R5, the instruction loop: the invariant after one instruction

Spec `onWorkItem`'s `for i in is do … results := results ++ [r]` (GP v0.8.0 Appendix B, Ω_W; bootstrap's
own loop). `LoopAt.step`: from `LoopAt` for i :: is and the results rs, the facts one body leaves (the
cursor advanced, the result r pushed into the results `Vec` at rp′ with cap cp′, every buffer still owned
kept, the new item owning chunks that are new or were the instruction's own) give `LoopAt` for is and
rs ++ [r]. The runs that produce these facts are composed in the body (`InstrLoopBody.lean`).
-/

namespace Services.Bootstrap.Acc.Handlers.InstrLoop

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Alloc Services.Bootstrap.Spec
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.Results
  Services.Bootstrap.Acc.Handlers.InstrRep Services.Bootstrap.Acc.Handlers.RowEleven
  Services.Bootstrap.Acc.Handlers.ResultsDrop

set_option maxHeartbeats 4000000

/-- Two allocated chunks with the same data address are equal. -/
theorem chunk_addr {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s)
    (h : c.addr + 32 = d.addr + 32) : c = d := by
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  exact Tiles.addr_inj ht c hc d hd (by omega)

theorem nd_dis {l₁ l₂ : List Nat} (h : (l₁ ++ l₂).Nodup) {x : Nat} (hx : x ∈ l₁) : x ∉ l₂ := fun hy =>
  (List.nodup_append.1 h).2.2 x hx x hy rfl

/-- The chunks the new item may own, against the head's state st (the instruction's buffers F): an
    allocated chunk of st′ whose data address is none of st's allocated chunks' outside F, and is not the
    results buffer rp′. -/
def NewC (st st' : State) (F : List Nat) (rp' : Nat) (d : Chunk) : Prop :=
  d ∈ chunks st' ∧ d.used = true ∧ (∀ d0 ∈ chunks st, d0.used = true → d0.addr + 32 ∉ F → d0.addr ≠ d.addr) ∧
    d.addr + 32 ≠ rp'

/-- **The loop's invariant after one instruction** (see the module doc). -/
theorem LoopAt.step {B : InstrRep} {code : ByteArray} {pb S0 S1 sp : Nat} {i : Spec.Instr}
    {is : List Spec.Instr} {rs : List Spec.Result} {r : Spec.Result} {zs zs' : Bool} {μ μ' : Memory}
    {st st' : State} {cp' rp' : Nat}
    (L : LoopAt B code pb S0 S1 sp (i :: is) rs zs μ st) (H' : HeapCtxC code pb S0 S1 μ' st')
    (hcur : rdN μ' (sp + 472 + 8) 8 = rdN μ (sp + 472 + 8) 8 + 232)
    (hend : rdN μ' (sp + 472 + 24) 8 = rdN μ (sp + 472 + 24) 8)
    (hbuf : rdN μ' (sp + 472) 8 = rdN μ (sp + 472) 8)
    (hcapI : rdN μ' (sp + 472 + 16) 8 = rdN μ (sp + 472 + 16) 8)
    (m448 : rdN μ' (sp + 448) 8 = cp') (m456 : rdN μ' (sp + 456) 8 = rp')
    (m464 : rdN μ' (sp + 464) 8 = rs.length + 1) (hlt : rs.length < cp')
    (m104 : rdN μ' (sp + 104) 8 = rdN μ (sp + 104) 8) (m128 : rdN μ' (sp + 128) 8 = rdN μ (sp + 128) 8)
    (m264 : rdN μ' (sp + 264) 8 = rdN μ (sp + 264) 8) (m272 : rdN μ' (sp + 272) 8 = rdN μ (sp + 272) 8)
    (hflag : rdN μ' (sp + 160) 8 = if zs' then 1 else 0)
    (c184 : rdN μ' (sp + 184) 8 = 9223372036854775808) (c216 : rdN μ' (sp + 216) 8 = 9223372036854775809)
    (c200 : rdN μ' (sp + 200) 8 = 678)
    (hkeep : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0) →
      d.addr + 32 ∉ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) →
      d ∈ chunks st' ∧ ∀ a, InData d a → μ'.read a = μ.read a)
    (hmv : ∀ k, k < 144 * rs.length → μ'.read (rp' + k) = μ.read (rdN μ (sp + 456) 8 + k))
    (hd' : ∃ d' ∈ chunks st', d'.used = true ∧ d'.addr + 32 = rp' ∧ rp' + 144 * cp' ≤ d'.addr + 32 * d'.size ∧
      ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∉ B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0) →
        d.addr + 32 ∉ optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) → d ≠ d')
    (hres : ResultAtP μ' (NewC st st' (B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0)) rp') (rp' + 144 * rs.length) r)
    (hown : ItemOwn μ' (NewC st st' (B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0)) rp') (rp' + 144 * rs.length)) :
    LoopAt B code pb S0 S1 sp is (rs ++ [r]) zs' μ' st' := by
  -- names
  have hT := L.T
  generalize hF : B.foot (slot μ (rdN μ (sp + 472 + 8) 8) 0) = F at hkeep hres hown hd'
  generalize hrp : rdN μ (sp + 456) 8 = rp at hkeep hmv hd'
  generalize hcp : rdN μ (sp + 448) 8 = cp at hkeep hd'
  have hn := L.hn
  have hcap := L.hcap
  rw [hcp] at hcap
  have hnd := L.hnd
  obtain ⟨d', hd'm, hd'u, hd'a, hd'e, hd'n⟩ := hd'
  -- the `IntoIter`
  have hnotRP : ∀ q ∈ iterFree B μ (sp + 472) (is.length + 1), q ∉ optBuf cp rp := fun q h1 h3 =>
    nd_dis hnd h1 (List.mem_append_right _ (by
      unfold tailBufs; rw [hcp, hrp]; simp only [List.mem_append]; exact .inl (.inl h3)))
  obtain ⟨I', hIF⟩ := InstrRep.IterOwn.step L.I hcur hend hbuf hcapI
    (fun d hd hu h1 h2 => hkeep d hd hu (hF ▸ h2) (hnotRP _ h1))
  rw [show (i :: is).length = is.length + 1 from rfl, hIF, hF] at hnd
  generalize hIF' : iterFree B μ' (sp + 472) is.length = IF at hnd I' ⊢
  -- the old lists
  have eTF : tailFree μ sp = resPtrs μ rp rs.length ++ (optBuf cp rp ++ optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) ++
      optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8)) := by
    unfold tailFree tailBufs; rw [hcp, hrp, hn]
  rw [eTF] at hnd
  generalize hB2 : optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) = B2 at hnd
  generalize hB3 : optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8) = B3 at hnd
  -- the pieces of the old list
  have ndL := (List.nodup_append.1 hnd).1
  have ndR := (List.nodup_append.1 hnd).2.1
  have ndRP := (List.nodup_append.1 ndR).1
  have ndT := (List.nodup_append.1 ndR).2.1
  have ndOB2 := (List.nodup_append.1 ndT).1
  have hcp0 : cp' ≠ 0 := by omega
  have ob' : optBuf cp' rp' = [rp'] := by unfold optBuf; simp [hcp0]
  have O0 : ResultsOwn μ st rp rs.length := by rw [← hrp, ← hn]; exact hT.O
  -- every buffer still owned: an allocated chunk of st, outside F and the results buffer
  have liveF : ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → q ∉ F := by
    intro q hq hqF
    rcases hq with hq | hq
    · exact nd_dis ndL hqF hq
    · exact nd_dis hnd (List.mem_append_left _ hqF) (by
        rcases hq with hq | hq | hq <;> simp [hq])
  have liveOB : ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → q ∉ optBuf cp rp := by
    intro q hq hqO
    rcases hq with hq | hq | hq | hq
    · exact nd_dis hnd (List.mem_append_right _ hq) (by simp [hqO])
    · exact nd_dis ndR hq (by simp [hqO])
    · exact nd_dis ndOB2 hqO hq
    · exact nd_dis ndT (List.mem_append_left _ hqO) hq
  have liveC : ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → ∃ e ∈ chunks st, e.used = true ∧ e.addr + 32 = q := by
    intro q hq
    rcases hq with hq | hq | hq | hq
    · exact L.I.owned q (by rw [show (i :: is).length = is.length + 1 from rfl, hIF, hF, hIF']; exact
        List.mem_append_right _ hq)
    · exact O0.2.1 q hq
    · rw [← hB2] at hq; unfold optBuf at hq
      split at hq
      · simp at hq
      · rename_i hc; simp at hq; subst hq; exact (hT.b2 hc).1
    · rw [← hB3] at hq; unfold optBuf at hq
      split at hq
      · simp at hq
      · rename_i hc; simp at hq; subst hq; exact (hT.b3 hc).1
  -- kept, and not the new buffer's address, nor a new item buffer's
  have liveK : ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → ∃ e ∈ chunks st, e.used = true ∧ e.addr + 32 = q ∧
      e ∈ chunks st' ∧ (∀ a, InData e a → μ'.read a = μ.read a) ∧ q ≠ rp' := by
    intro q hq
    obtain ⟨e, he, heu, heq⟩ := liveC q hq
    obtain ⟨he', hke⟩ := hkeep e he heu (heq ▸ liveF q hq) (heq ▸ liveOB q hq)
    refine ⟨e, he, heu, heq, he', hke, fun h => hd'n e he heu (heq ▸ liveF q hq) (heq ▸ liveOB q hq) ?_⟩
    exact chunk_addr H' he' hd'm (by rw [heq, h, hd'a])
  have liveN : ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → ∀ d, NewC st st' F rp' d → d.addr + 32 ≠ q := by
    intro q hq d hd h
    obtain ⟨e, he, heu, heq⟩ := liveC q hq
    exact hd.2.2.1 e he heu (heq ▸ liveF q hq) (by omega)
  have liveR : ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → q ≠ rp' := fun q hq => by
    obtain ⟨-, -, -, -, -, -, h⟩ := liveK q hq; exact h
  have NI_live : ∀ x ∈ itemPtrs μ' (rp' + 144 * rs.length), ∀ q, q ∈ IF ∨ q ∈ (resPtrs μ rp rs.length) ∨ q ∈ B2 ∨ q ∈ B3 → x ≠ q := by
    intro x hx q hq
    obtain ⟨d, hd, hdx⟩ := hown.2.1 x hx
    exact hdx ▸ liveN q hq d hd
  have NI_rp : ∀ x ∈ itemPtrs μ' (rp' + 144 * rs.length), x ≠ rp' := by
    intro x hx
    obtain ⟨d, hd, hdx⟩ := hown.2.1 x hx
    exact hdx ▸ hd.2.2.2
  -- the results' buffers after the push
  have hkRP : ∀ d ∈ chunks st, d.used = true → d.addr + 32 ∈ (resPtrs μ rp rs.length) → d ∈ chunks st' ∧
      ∀ a, InData d a → μ'.read a = μ.read a := fun d hd hu h =>
    hkeep d hd hu (liveF _ (.inr (.inl h))) (liveOB _ (.inr (.inl h)))
  have eRP : resPtrs μ' rp' (rs.length + 1) = (resPtrs μ rp rs.length) ++ itemPtrs μ' (rp' + 144 * rs.length) := by
    rw [resPtrs_succ, resPtrs_move O0 hmv hkRP rs.length (Nat.le_refl _)]
  have ndNew : ((resPtrs μ rp rs.length) ++ itemPtrs μ' (rp' + 144 * rs.length)).Nodup :=
    List.nodup_append.2 ⟨ndRP, hown.1, fun x hx y hy => (NI_live y hy x (.inr (.inl hx))).symm⟩
  have hd'N : d'.addr + 32 ∉ (resPtrs μ rp rs.length) ++ itemPtrs μ' (rp' + 144 * rs.length) := by
    rw [hd'a]; intro h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨-, -, -, -, -, -, hne⟩ := liveK rp' (.inr (.inl h)); exact hne rfl
    · exact NI_rp _ h rfl
  have hCn : ∀ d, NewC st st' F rp' d → d ∈ chunks st' ∧ d.used = true := fun d hd => ⟨hd.1, hd.2.1⟩
  have hinD' : ∀ k, k < 144 * (rs.length + 1) → InData d' (rp' + k) := fun k hk => by
    have : 144 * (rs.length + 1) ≤ 144 * cp' := Nat.mul_le_mul_left 144 hlt
    exact ⟨by omega, by omega⟩
  have O' : ResultsOwn μ' st' rp' (rs.length + 1) :=
    ResultsOwn.push O0 hmv hkRP hown hCn ndNew ⟨d', hd'm, hd'u, hinD', hd'N⟩
  -- the words
  have w448 : rdN μ' (sp + 448) 8 = cp' := m448
  have w456 : rdN μ' (sp + 456) 8 = rp' := m456
  have eB2 : optBuf (rdN μ' (sp + 128) 8) (rdN μ' (sp + 104) 8) = B2 := by rw [m128, m104, hB2]
  have eB3 : optBuf (rdN μ' (sp + 264) 8) (rdN μ' (sp + 272) 8) = B3 := by rw [m264, m272, hB3]
  have eTF' : tailFree μ' sp = ((resPtrs μ rp rs.length) ++ itemPtrs μ' (rp' + 144 * rs.length)) ++ ([rp'] ++ B2 ++ B3) := by
    unfold tailFree tailBufs; rw [w448, w456, m464, eRP, ob', eB2, eB3]
  -- the payloads
  have hC' : ∀ d, AvoidC st (F ++ IF ++ optBuf cp rp) d → AvoidC st' (IF ++ optBuf cp' rp') d ∧
      ∀ a, InData d a → μ'.read a = μ.read a := by
    intro d ⟨hd, hu, hn'⟩
    have h1 : d.addr + 32 ∉ F := fun h => hn' (by simp [h])
    have h2 : d.addr + 32 ∉ IF := fun h => hn' (by simp [h])
    have h3 : d.addr + 32 ∉ optBuf cp rp := fun h => hn' (by simp [h])
    obtain ⟨hd2, hk2⟩ := hkeep d hd hu h1 h3
    refine ⟨⟨hd2, hu, fun h => ?_⟩, hk2⟩
    rcases List.mem_append.1 h with h | h
    · exact h2 h
    · rw [ob'] at h; simp at h
      exact hd'n d hd hu h1 h3 (chunk_addr H' hd2 hd'm (by rw [h, hd'a]))
  have hr' : ResultAtP μ' (AvoidC st' (IF ++ optBuf cp' rp')) (rp' + 144 * rs.length) r :=
    ResultAtP.copy (μ' := μ') (fun d hd => ⟨⟨hd.1, hd.2.1, fun h => by
      rcases List.mem_append.1 h with h | h
      · exact liveN _ (.inl h) d hd rfl
      · rw [ob'] at h; simp at h; exact hd.2.2.2 h⟩, fun _ _ => rfl⟩) (fun _ _ => rfl) hres
  have hp0 : PayAvoid μ st rp rs (F ++ IF ++ optBuf cp rp) := by
    have := L.hpay
    rw [show (i :: is).length = is.length + 1 from rfl, hIF, hF, hIF', hcp, hrp] at this
    exact this
  have hpay' : PayAvoid μ' st' rp' (rs ++ [r]) (IF ++ optBuf cp' rp') := PayAvoid.push hp0 hmv hC' hr'
  have hrpIF : rp' ∉ IF := fun h => by
    obtain ⟨-, -, -, -, -, -, hne⟩ := liveK rp' (.inl h); exact hne rfl
  refine ⟨H', L.hsp, I', ⟨H', hT.hsp, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hflag, c184, c216, c200⟩
  · rw [w456, m464]; exact O'
  · rw [w456, m464, w448, eRP]
    intro _
    rw [hd'a] at hd'N
    exact ⟨⟨d', hd'm, hd'u, hd'a⟩, hd'N⟩
  · rw [w456, m464, w448, eRP, m128, m104, ob']
    intro hc
    obtain ⟨⟨e, he, heu, heq⟩, hnot⟩ := hT.b2 hc
    have hq : rdN μ (sp + 104) 8 ∈ B2 := by rw [← hB2]; simp [optBuf, hc]
    obtain ⟨-, -, -, -, he', -, hne⟩ := liveK _ (.inr (.inr (.inl hq)))
    have := liveK _ (.inr (.inr (.inl hq)))
    obtain ⟨e2, he2, heu2, heq2, he2', -, -⟩ := this
    refine ⟨⟨e2, he2', heu2, heq2⟩, fun h => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | h
    · exact nd_dis ndR h (by simp [hq])
    · exact NI_live _ h _ (.inr (.inr (.inl hq))) rfl
    · exact hne h
  · rw [w456, m464, w448, eRP, m128, m104, m264, m272, ob', hB2]
    intro hc
    have hq : rdN μ (sp + 272) 8 ∈ B3 := by rw [← hB3]; simp [optBuf, hc]
    obtain ⟨e2, he2, heu2, heq2, he2', -, hne⟩ := liveK _ (.inr (.inr (.inr hq)))
    refine ⟨⟨e2, he2', heu2, heq2⟩, fun h => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with ((h | h) | h) | h
    · exact nd_dis ndR h (by simp [hq])
    · exact NI_live _ h _ (.inr (.inr (.inr hq))) rfl
    · exact hne h
    · exact nd_dis ndT (List.mem_append_right _ h) hq
  · rw [m464, List.length_append, List.length_singleton]
  · rw [w448, List.length_append, List.length_singleton]; omega
  · rw [w456, hIF']
    refine PayAvoid.toAvoid (hpay'.mono fun q h => List.mem_append_left _ h) fun k hk => ⟨d', ⟨hd'm, hd'u, ?_⟩, ?_⟩
    · rw [hd'a]; exact hrpIF
    · rw [List.length_append, List.length_singleton] at hk; exact hinD' k hk
  · rw [hIF', eTF']
    refine List.nodup_append.2 ⟨(List.nodup_append.1 ndL).2.1, ?_, ?_⟩
    · refine List.nodup_append.2 ⟨ndNew, ?_, ?_⟩
      · refine List.nodup_append.2 ⟨List.nodup_append.2 ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
          (List.nodup_append.1 ndOB2).2.1, ?_⟩, (List.nodup_append.1 ndT).2.1, ?_⟩
        · intro x hx y hy; simp at hx; subst hx
          exact fun h => liveR y (.inr (.inr (.inl hy))) h.symm
        · intro x hx y hy
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · subst hx; exact fun h => liveR y (.inr (.inr (.inr hy))) h.symm
          · exact (List.nodup_append.1 ndT).2.2 x (List.mem_append_right _ hx) y hy
      · intro x hx y hy
        simp only [List.mem_append, List.mem_singleton] at hx hy
        rcases hx with hx | hx
        · rcases hy with (hy | hy) | hy
          · subst hy; exact liveR x (.inr (.inl hx))
          · exact (List.nodup_append.1 ndR).2.2 x hx y (by simp [hy])
          · exact (List.nodup_append.1 ndR).2.2 x hx y (by simp [hy])
        · rcases hy with (hy | hy) | hy
          · subst hy; exact NI_rp x hx
          · exact NI_live x hx y (.inr (.inr (.inl hy)))
          · exact NI_live x hx y (.inr (.inr (.inr hy)))
    · intro x hx y hy
      simp only [List.mem_append, List.mem_singleton] at hy
      rcases hy with (hy | hy) | ((hy | hy) | hy)
      · exact (List.nodup_append.1 hnd).2.2 x (List.mem_append_right _ hx) y (by simp [hy])
      · exact fun h => NI_live y hy x (.inl hx) h.symm
      · subst hy; exact fun h => hrpIF (h ▸ hx)
      · exact (List.nodup_append.1 hnd).2.2 x (List.mem_append_right _ hx) y (by simp [hy])
      · exact (List.nodup_append.1 hnd).2.2 x (List.mem_append_right _ hx) y (by simp [hy])
  · rw [w456, w448, hIF']; exact hpay'
  · rw [w448]; intro h; omega
  · rw [w448, w456]; exact fun _ => ⟨d', hd'm, hd'u, hd'a, hd'e⟩

end Services.Bootstrap.Acc.Handlers.InstrLoop
