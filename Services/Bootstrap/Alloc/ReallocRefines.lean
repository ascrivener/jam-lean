import Services.Bootstrap.Alloc.ReallocImpl

/-!
# The binary's shrink on a well-formed heap

The facts `realloc_impl_shrink` takes about the heap, from the invariant; and the memory it leaves,
read back as `Rep` of the model's `shrink`.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The binary's `realloc_impl` refines the model's `shrink`**: from memory holding a well-formed
    `s`, the data address `ptr` of an allocated chunk and a request `req` of 1 … `usable s ptr − 1`
    units (Gray Paper v0.8.0, Appendix B: the refine invocation's `realloc` of the SDK heap),
    `realloc_impl` (42980) returns into `realloc` (40805) with ω₇ = ptr and memory holding the
    model's `shrink s ptr req`, itself well-formed with its first chunk's `prev` 0, the caller's
    ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem shrink_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr0 : req ≠ 0) (hr : req < usable s ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 180 ∧ Rep μ' (shrink s ptr req) ∧
      WF (shrink s ptr req) ∧ FirstOk (shrink s ptr req) ∧
      (∀ a, μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = cur at hcs
  have hXmem : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s := by
    rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
  have hcur : wordSize (s.hdr (ptr - 32)).size = cur := by
    have := chunks_hdr _ hXmem
    simp only at this; rw [this, wordSize_sizeWord]
  have hr' : req + 1 < cur := by unfold usable at hr; rw [hcur] at hr; omega
  have hfirst := shrink_first (newReq := req) hfo (by
    have ht := hwf.2.2.2.1; unfold TilesOk at ht
    exact (ht.mem_lt _ hXmem).1)
  obtain ⟨Rs, post0s, rest, hposts, -, hchS, hwfS⟩ := shrink_ok (newReq := req) hwf hcs (by omega)
  have hwf' := hwf
  obtain ⟨-, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold ListsOk' at hlists
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles hcoal hlists henc
  rw [htop] at htiles
  -- the header addresses
  generalize hH : HA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have mkF : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.used = false → F c.addr :=
    fun c hc hu => hF ▸ ⟨c, hc, rfl, hu⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := fun a h => by
    rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ : ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := by
      rcases h with h | h
      · exact unH a h
      · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hcs' : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post := hcs
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs' ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs' ▸ hc) hu⟩
  have hXm : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post :=
    List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  have hXa := htiles.aligned _ hXm
  simp only at hXl hXa
  have hXs : (s.hdr (ptr - 32)).size = sizeWord cur true := henc _ hXm
  have hsub : ∀ c, c ∈ pre ∨ c ∈ post → c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post := by
    rintro c (h | h)
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hAlc : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, Al s.base c.addr :=
    fun c hc => hHF _ (Or.inl (mkH c hc))
  have hbinlt : ∀ y, binDown y < binCount := fun y => toBin_lt false (Nat.min_le_right _ _)
  obtain ⟨hpa, hph, hpp, -⟩ := Tiles.around htiles
  -- the state after the new size is written
  have hF0 : FreeLists s (Fof (pre ++ ⟨ptr - 32, cur, true⟩ :: post)) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  have hF1 : FreeLists (shrinkHdr s ptr req) (Fof (pre ++ post)) :=
    (FreeLists.congr (t := shrinkHdr s ptr req) hF0 rfl (fun z => setHdr_next (f := fun h => { h with size := sizeWord (req + 1) true }) (fun _ => rfl) z)
      (fun z => setHdr_prevL (f := fun h => { h with size := sizeWord (req + 1) true }) (fun _ => rfl) z)).iff
      (fun b a _ => Fof_skip rfl b a)
  have hb1 : BitsOk (shrinkHdr s ptr req).secondary (shrinkHdr s ptr req).primary (shrinkHdr s ptr req).heads :=
    hbits
  have h0x : ∀ z, z ≠ ptr - 32 → (shrinkHdr s ptr req).hdr z = s.hdr z := fun z hz => setHdr_other hz
  have henc' : ∀ c ∈ post, ((shrinkHdr s ptr req).hdr c.addr).size = sizeWord c.size c.used := fun c hc => by
    have := (hpp c hc).1
    rw [h0x _ (by omega)]
    exact henc c (hsub c (Or.inr hc))
  have hcX : Coalesced (⟨ptr - 32, cur, true⟩ :: post) := (Coalesced.append.mp hcoal).2.1
  have hcp : Coalesced post := ((Coalesced.append (xs := [⟨ptr - 32, cur, true⟩]) (ys := post)).mp hcX).2.1
  rcases hnx : mergeNext (shrinkHdr s ptr req) (ptr - 32) cur (s.base + 1073741824) with ⟨s2, total⟩
  obtain ⟨R', post0, hpost0, -, htl2, -, hF2, -, -, -, -, hge⟩ :=
    mergeNext_ok htiles henc' hcp hF1 hb1 hnx
  have hsub0 : ∀ c ∈ pre ++ post0, c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hsub c (Or.inl h)
    · exact hsub c (Or.inr (by rw [hpost0]; exact List.mem_append_right _ h))
  have hsubP : ∀ c ∈ pre ++ post, c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hsub c (Or.inl h)
    · exact hsub c (Or.inr h)
  have hM2 := htl2.mem_lt ⟨ptr - 32, total, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hM2
  obtain ⟨hpa2, -, hpp2, -⟩ := Tiles.around htl2
  -- the chunk after X
  have hnc' : ptr - 32 + 32 * cur < s.base + 1073741824 → H (ptr - 32 + 32 * cur) := by
    intro hlt
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      rw [show ptr - 32 + 32 * cur = e.addr from (hph e (by rw [hp]; rfl)).symm]
      exact mkH e (hsub e (Or.inr (by rw [hp]; simp)))
  have hnf' : ptr - 32 + 32 * cur < s.base + 1073741824 →
      ((shrinkHdr s ptr req).hdr (ptr - 32 + 32 * cur)).size % 2 = 0 →
      NxFree (shrinkHdr s ptr req) F s.base (ptr - 32 + 32 * cur) cur := by
    intro hlt hev
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      have hem : e ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post := hsub e (Or.inr (by rw [hp]; simp))
      have hncE : ptr - 32 + 32 * cur = e.addr := (hph e (by rw [hp]; rfl)).symm
      unfold NxFree
      rw [hncE] at hev ⊢
      have hes : ((shrinkHdr s ptr req).hdr e.addr).size = sizeWord e.size e.used := henc' e (by rw [hp]; simp)
      rw [hes] at hev ⊢
      have heu : e.used = false := by
        cases hu : e.used
        · rfl
        · exfalso; rw [hu] at hev; simp [sizeWord] at hev; try omega
      rw [heu, show sizeWord e.size false / 2 = e.size by simp [sizeWord]]
      have hel := htiles.mem_lt e hem
      have hFe : Fof (pre ++ post) (binDown e.size) e.addr :=
        ⟨e, List.mem_append_right _ (by rw [hp]; simp), rfl, heu, rfl⟩
      obtain ⟨m1, m2⟩ := member_facts hF1 (hbinlt _) hFe
      refine ⟨mkF e hem heu, by simp [sizeWord]; omega, by simp [sizeWord]; omega, by omega, ?_,
        fun h => ?_, fun h => ?_⟩
      · rcases heads_ok hF1 (hbinlt e.size) with h | ⟨c, hc, h1, -⟩
        · exact Or.inl h
        · exact Or.inr (h1 ▸ hAlc c (hsubP c hc))
      · obtain ⟨c, hc, h1, h2⟩ := m1 h; exact h1 ▸ mkF c (hsubP c hc) h2
      · obtain ⟨⟨c, hc, h1, h2⟩, h3⟩ := m2 h; exact ⟨h1 ▸ mkF c (hsubP c hc) h2, h3⟩
  -- the free tail
  have hold' : s2.heads (binDown (total - (req + 1))) ≠ ptr - 32 + 32 * (req + 1) := by
    rcases heads_ok hF2 (hbinlt (total - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · rw [h]; omega
    · rw [← h1]
      rcases List.mem_append.mp hc with h | h
      · have := hpa2 c h; have := htl2.mem_lt c (List.mem_append_left _ h); omega
      · have := (hpp2 c h).1; omega
  have hold1' : s2.heads (binDown (total - (req + 1))) ≠ 0 →
      Al s.base (s2.heads (binDown (total - (req + 1)))) := by
    intro h0
    rcases heads_ok hF2 (hbinlt (total - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · exact absurd h h0
    · rw [← h1]; exact hAlc c (hsub0 c hc)
  have hnext' : ptr - 32 + 32 * total < s.base + 1073741824 → H (ptr - 32 + 32 * total) := by
    intro hlt
    cases hp : post0 with
    | nil =>
      rw [hp] at htl2
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htl2
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      have := (Tiles.around htl2).2.1 e (by rw [hp]; rfl)
      exact this ▸ mkH e (hsub0 e (by rw [hp]; simp))
  obtain ⟨ω', μ', run, rep', ww, stk, e7, e0, e1, e5, e6⟩ := realloc_impl_shrink (p := p) (P := P) (R := R)
    x ω μ s H F sp ptr req cur hrep' h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT (hHF _ (Or.inl (mkH _ hXm)))
    (by omega) (mkH _ hXm) hHF (by rw [hXs]; rfl) hr0 (by omega) (by omega) (by omega) hnc' hnf'
    (by rw [hnx]; simp only; omega) (by rw [hnx]; simp only; omega)
    (by rw [hnx]; exact hold') (by rw [hnx]; exact hold1') (by rw [hnx]; exact hnext') hw
  refine ⟨ω', μ', run, ?_, hwfS, hfirst, ww, stk, e7, e0, e1, e5, e6⟩
  -- the model's result, read from memory
  subst hposts
  have cls : ∀ c ∈ chunks (shrink s ptr req), H c.addr ∨ c = ⟨ptr - 32 + 32 * (req + 1), rest, false⟩ := by
    intro c hc
    rw [hchS] at hc
    rcases List.mem_append.mp hc with h | h
    · exact Or.inl (mkH c (List.mem_append_left _ h))
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (by rw [h]; show H (ptr - 32); exact mkH _ hXm)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr h
        · exact Or.inl (mkH c (hsub c (Or.inr (List.mem_append_right _ h))))
  have clsF : ∀ c ∈ chunks (shrink s ptr req), c.used = false →
      F c.addr ∨ c.addr = ptr - 32 + 32 * (req + 1) := by
    intro c hc hu
    rw [hchS] at hc
    rcases List.mem_append.mp hc with h | h
    · exact Or.inl (mkF c (List.mem_append_left _ h) hu)
    · rcases List.mem_cons.mp h with h | h
      · rw [h] at hu; simp at hu
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (by rw [h])
        · exact Or.inl (mkF c (hsub c (Or.inr (List.mem_append_right _ h))) hu)
  refine ⟨rep'.heads, rep'.sec, rep'.pri, rep'.base, rep'.alloc, fun c hc => ?_, fun c hc => ?_,
    fun c hc hu => ?_, fun c hc hu => ?_⟩
  · rcases cls c hc with h | rfl
    · exact rep'.prev _ (Or.inl h)
    · exact rep'.prev _ (Or.inr rfl)
  · rcases cls c hc with h | rfl
    · exact rep'.size _ (Or.inl h)
    · exact rep'.size _ (Or.inr rfl)
  · rcases clsF c hc hu with h | h
    · exact rep'.next _ (Or.inl h)
    · exact rep'.next _ (Or.inr h)
  · rcases clsF c hc hu with h | h
    · exact rep'.prevL _ (Or.inl h)
    · exact rep'.prevL _ (Or.inr h)

end Services.Bootstrap.Alloc
