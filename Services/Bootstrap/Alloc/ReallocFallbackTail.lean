import Services.Bootstrap.Alloc.ReallocFallback
import Services.Bootstrap.Alloc.AllocRefines
import Services.Bootstrap.Alloc.FreeRefines

/-!
# The binary's `realloc_impl`: the fallback, composed

43259 … 40805: `alloc_impl` gives a new block q (the model's `alloc` at one unit, without growing the
heap); `memcpy` copies the old usable size there; the free path frees the old chunk; `realloc_impl`
returns q. The memory holds the model's `free s₁ ptr`, s₁ the state after the allocation.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`alloc` at one unit keeps the allocated chunks**, and its new block q is a chunk of the result
    of r + 1 units, used, at q − 32. -/
theorem alloc_keeps {grow : Grow} {hb r q : Nat} {s s1 : State} (hwf : WF s)
    (h : alloc grow hb 1 r s = some (q, s1)) :
    (∀ c ∈ chunks s, c.used = true → c ∈ chunks s1 ∧
        (c.addr + 32 * c.size ≤ q - 32 ∨ q - 32 + 32 * (r + 1) ≤ c.addr)) ∧
      (⟨q - 32, r + 1, true⟩ : Chunk) ∈ chunks s1 ∧ 32 ≤ q ∧ s1.base = s.base := by
  rw [alloc_one hwf.1] at h
  obtain ⟨bin, a1, hbin, hmax, hS, -, -, hp, rfl⟩ := alloc1_eq h
  obtain ⟨pre, post, hcs, hcs1⟩ := allocPost_chunks (a1 := a1) hwf hmax hbin hS
  obtain ⟨-, -, -, -, -, hCb, hCal⟩ := bin_chunk hwf hmax hbin
  have htop : s.top = s.base + 32 * maxSize := rfl
  rw [htop] at hcs1
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  rw [hcs] at ht
  obtain ⟨hpa, -, hpp, -⟩ := Tiles.around ht
  refine ⟨fun c hc hu => ?_, ?_, by omega, by rw [allocPost_base]⟩
  · rw [hcs1]; rw [hcs] at hc
    rcases List.mem_append.mp hc with h | h
    · exact ⟨List.mem_append_left _ h, Or.inl (by have := hpa c h; omega)⟩
    · rcases List.mem_cons.mp h with h | h
      · subst h; simp at hu
      · exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ h)),
          Or.inr (by have := (hpp c h).1; omega)⟩
  · rw [hcs1, show q - 32 = s.heads bin by omega]
    exact List.mem_append_right _ List.mem_cons_self

/-- `Rep` reads the allocator's fields and the heap's headers, none of them in a chunk's data. -/
theorem Rep.congr_data {μ μ' : Memory} {s : State} (h : Rep μ s) (hwf : WF s) (hb0 : 206864 ≤ s.base)
    (hbT : s.base + 1073741824 < 2147483648) {c : Chunk} (hc : c ∈ chunks s) {lo hi : Nat}
    (hlo : c.addr + 32 ≤ lo) (hhi : hi ≤ c.addr + 32 * c.size)
    (wf : ∀ a, A0 ≤ a → a < 2147483648 → (a < lo ∨ hi ≤ a) → μ'.read a = μ.read a) : Rep μ' s := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  obtain ⟨C, S, u⟩ := c
  have ht' := ht
  rw [hcs] at ht'
  obtain ⟨hpa, -, hpp, -⟩ := Tiles.around ht'
  have hd : ∀ d ∈ chunks s, (d.addr + 16 ≤ lo ∨ hi ≤ d.addr) ∧ s.base ≤ d.addr ∧ d.addr + 16 < 2147483648 := by
    intro d hdm
    have hl := ht.mem_lt d hdm
    refine ⟨?_, by omega, by omega⟩
    rw [hcs] at hdm
    rcases List.mem_append.mp hdm with h1 | h1
    · have := hpa d h1; left; simp only at hlo; omega
    · rcases List.mem_cons.mp h1 with h2 | h2
      · subst h2; left; simp only at hlo ⊢; omega
      · have := (hpp d h2).1; right; simp only at hhi; omega
  have hCl := ht.mem_lt _ hc
  simp only at hCl hlo
  refine ⟨fun b hb => ?_, fun q hq => ?_, ?_, ?_, ?_, fun d hd' => ?_, fun d hd' => ?_, fun d hd' _ => ?_,
    fun d hd' _ => ?_⟩
  · rw [← h.heads b hb]; unfold A0; unfold binCount at hb
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.sec q hq]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.pri]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.base]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · rw [← h.alloc]; unfold A0; exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hd d hd'; rw [← h.prev d hd']
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hd d hd'; rw [← h.size d hd']
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hd d hd'; rw [← h.next d hd' ‹_›]
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)
  · have := hd d hd'; rw [← h.prevL d hd' ‹_›]
    exact rdN_frame fun j hj => wf _ (by unfold A0; omega) (by omega) (by omega)

/-- Reads off the headers keep their octets. -/
theorem HKeep.readN {μ μ' : Memory} {G : Nat → Prop} (h : HKeep μ μ' G) {a n : Nat}
    (ha : ∀ j, j < n → OffHdr G (a + j)) : μ'.readN a n = μ.readN a n :=
  readN_congr2 fun j hj => h _ (ha j hj)

theorem HKeepG.readN {μ μ' : Memory} {G : Nat → Prop} (h : HKeepG μ μ' G) {a n : Nat}
    (ha : ∀ j, j < n → OffHdr G (a + j)) : μ'.readN a n = μ.readN a n :=
  h.hkeep.readN ha

/-- **A chunk's data is off the headers**: in a well-formed heap below 2³¹, an octet of a chunk's
    data (from its address + 32 to its end) lies outside the allocator's fields, the stack and the
    first 16 octets of every chunk's header. -/
theorem off_hdr_data {t : State} (hwf : WF t) (hb0 : 206864 ≤ t.base)
    (hbT : t.base + 1073741824 < 2147483648) {c : Chunk} (hc : c ∈ chunks t) {a : Nat}
    (h1 : c.addr + 32 ≤ a) (h2 : a < c.addr + 32 * c.size) :
    OffHdr (fun h => ∃ d ∈ chunks t, d.addr = h) a := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : t.top = t.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hCl := ht.mem_lt _ hc
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  obtain ⟨C, S, u⟩ := c
  have ht' := ht
  rw [hcs] at ht'
  obtain ⟨hpa, -, hpp, -⟩ := Tiles.around ht'
  simp only at hCl h1 h2
  unfold OffHdr
  refine ⟨by omega, by omega, fun h ⟨d, hdm, hdh⟩ => ?_⟩
  subst hdh
  have hdl := ht.mem_lt d hdm
  rw [hcs] at hdm
  rcases List.mem_append.mp hdm with h3 | h3
  · have := hpa d h3; omega
  · rcases List.mem_cons.mp h3 with h4 | h4
    · subst h4; simp only; omega
    · have := (hpp d h4).1; omega

/-- **43259 … 40805, the fallback**: from memory holding a well-formed `s` (its first chunk's `prev`
    0), the frame at sp, ω₈ = ptr the data address of an allocated chunk with `u` (≥ 1) usable units
    (ω₆, u < req), and ω₁₀ = req, when the model's `alloc` at one unit gives q and s₁ without
    growing the heap: the binary copies the u·32 octets at ptr to q, frees ptr and returns q into
    `realloc` (40805), the memory holding `free s₁ ptr`, well-formed with its first chunk's `prev` 0. -/
theorem fallback_tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q u v5 v6 : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hfo : FirstOk s) (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hu : usable s ptr = u) (hu1 : 1 ≤ u) (hur : u < req)
    (h : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h6 : ω[6] = UInt64.ofNat u)
    (hrq : req < 33554432)
    (s0 : rdN μ (sp + 144) 8 = 1988) (s5 : rdN μ (sp + 136) 8 = v5) (s6 : rdN μ (sp + 128) 8 = v6)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp + 152 < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp + 152 ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 43259 ω μ x 40805 ω' μ' x (64 * u + 1000) ∧
      Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp + 152 ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat (sp + 152) ∧
      ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨hkeep, hnew, hq32, hb1⟩ := alloc_keeps hwf h
  obtain ⟨hc1, hdis⟩ := hkeep c hcm hcu
  have hwf1 : WF s1 := alloc_wf hwf h
  have hfo1 : FirstOk s1 := alloc_first hwf hfo h
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcl := ht.mem_lt c hcm
  have hca' := ht.aligned c hcm
  have ht1 := hwf1.2.2.2.1
  unfold TilesOk at ht1
  have htop1 : s1.top = s1.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hnl := ht1.mem_lt _ hnew
  have hna := ht1.aligned _ hnew
  simp only at hnl hna
  have hcsz : c.size = u + 1 := by
    have := chunks_hdr c hcm; rw [hcu] at this
    rw [← hu]; unfold usable; rw [← hca] at *; simp only [Nat.add_sub_cancel] at this ⊢
    rw [this, wordSize_sizeWord]; omega
  -- the old chunk lies in the allocated space; the new block too
  have hsp0 := hwf.2.2.2.2.2.2.2
  unfold SpaceOk at hsp0
  have hcT := (hsp0 c hcm).1 hcu
  have hsp1' := hwf1.2.2.2.2.2.2.2
  unfold SpaceOk at hsp1'
  have hnT := (hsp1' _ hnew).1 rfl
  simp only at hnT
  rw [hng, hb1] at hnT
  -- the call to `alloc_impl`
  obtain ⟨ω1, μ1, r1, a5, a8, a9, a10, a0, a104, fr1, ww1, g1⟩ := rf_call (p := p) (P := P) (R := R) x ω μ
    sp ptr 1 req h1 h7 h8 h9 h10 (by omega) (by decide) (by omega) (by omega) hsp1 ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  obtain ⟨ω2, μ2, r2, rep2, -, e7, e0, e5, e6, e1, ww2, stk2⟩ :=
    alloc_refines (p := p) (P := P) (R := R) x ω1 μ1 s s1 sp req q hwf rep1 h hng
      (by rw [fget g1 1 (by decide) (by decide)]; exact h1) (by rw [fget g1 7 (by decide) (by decide)]; exact h7)
      a8 a9 a10 hsp (by omega) hb0 hbT hA hfo hHTs ⟨by omega, by omega⟩ hHT (hw.of_eq ww1)
  have rj := al_ret_realloc (p := p) (P := P) (R := R) x ω2 μ2 (by rw [e0, a0])
  -- the copy
  obtain ⟨ω3, r3, c7, c8, c9, c6, c0, g3⟩ := rf_copy (p := p) (P := P) (R := R) x ω2 μ2 q u ptr e7
    (by rw [e6, fget g1 6 (by decide) (by decide)]; exact h6) (by rw [e5]; exact a5) (by omega) (by omega)
    (by omega) (by omega)
  have W2 := (hw.of_eq ww1).of_eq ww2
  obtain ⟨ω4, μ3, r4, d0, d1, d5, d6, -, dfr, -, dwr⟩ := memcpy_big_aligned (p := p) (P := P) (R := R)
    x ω3 μ2 2004 43295 sp q ptr (32 * u) c0
    (by rw [fget g3 1 (by decide) (by decide), e1, fget g1 1 (by decide) (by decide)]; exact h1) c7 c8 c9 (by decide)
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1001]) bs_43295 ⟨by omega, by omega, hsp8⟩ (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (W2 a (Or.inl ⟨by omega, by omega⟩)))
    (fun a h1 h2 => W2 a (Or.inl ⟨by omega, by omega⟩))
    (fun a h1 h2 => W2 a (Or.inr ⟨by omega, by omega⟩))
  have rep3 : Rep μ3 s1 := Rep.congr_data rep2 hwf1 (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hnew
    (lo := q) (hi := q + 32 * u) (by simp only; omega) (by simp only; omega)
    (fun a ha1 ha2 ha3 => dfr a (by omega) ha3 (Or.inl (by omega)))
  have stk3 : ∀ a, a < 4294967296 → sp ≤ a → μ3.read a = μ1.read a := fun a h1 h2 =>
    (dfr a h1 (Or.inr (by omega)) (Or.inr h2)).trans (stk2 a h1 h2)
  -- the free of the old chunk
  obtain ⟨ω5, r5, f7, f8, f0, g5⟩ := rf_free_call (p := p) (P := P) (R := R) x ω4 μ3 sp ptr d1
    (by rw [d5, fget g3 5 (by decide) (by decide), e5]; exact a5)
    (by rw [← a104]; exact rdN_frame fun j hj => stk3 _ (by omega) (by omega)) (by omega) (by omega) hsp1
    ⟨by omega, by omega⟩ ((W2.of_eq dwr).rd)
  obtain ⟨ω6, μ4, r6, rep4, wf4, fo4, ww4, stk4, b0, b1, b5, b6⟩ := free_refines (p := p) (P := P) (R := R)
    x ω5 μ3 s1 sp ptr hwf1 rep3 ⟨c, hc1, hca, hcu⟩ (by rw [fget g5 1 (by decide) (by decide)]; exact d1) f8 f7
    (by omega) (by omega) (by rw [hb1]; exact hb0) (by rw [hb1]; exact hbT) hfo1
    (by rw [hb1, hng]; exact hHT) ⟨by omega, by omega⟩ (W2.of_eq dwr)
  have rj2 := free_ret_fallback (p := p) (P := P) (R := R) x ω6 μ4 (by rw [b0, f0])
  have stk : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 104 ∨ sp + 112 ≤ a) → μ4.read a = μ.read a :=
    fun a h1 h2 h3 => ((stk4 a h1 h2).trans (stk3 a h1 h2)).trans (fr1 a h1 h3)
  have rd : ∀ a v, rdN μ a 8 = v → sp + 112 ≤ a → a + 8 ≤ sp + 152 → rdN μ4 a 8 = v := fun a v h h1 h2 => by
    rw [← h]; exact rdN_frame fun j hj => stk _ (by omega) (by omega) (Or.inr (by omega))
  have W4 := (W2.of_eq dwr).of_eq ww4
  obtain ⟨ω7, r7, k7, k0, k1, k5, k6⟩ := rf_ret (p := p) (P := P) (R := R) x ω6 μ4 sp q v5 v6 b1
    (by rw [b6, fget g5 6 (by decide) (by decide), d6, c6]) (by omega) (by omega) hsp1
    (rd _ _ s0 (by omega) (by omega)) (rd _ _ s5 (by omega) (by omega)) (rd _ _ s6 (by omega) (by omega))
    ⟨by omega, by omega⟩ W4.rd
  refine ⟨ω7, μ4, ((((((((r1.trans r2).trans rj).trans r3).trans r4).trans r5).trans r6).trans rj2).trans
      r7).mono (by omega), rep4, wf4, fo4, fun a => (ww4 a).trans ((dwr a).trans ((ww2 a).trans (ww1 a))),
    fun a h1 h2 => stk a h1 (by omega) (Or.inr (by omega)), k7, k0, k1, k5, k6⟩

end Services.Bootstrap.Alloc
