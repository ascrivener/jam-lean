import Services.Bootstrap.Alloc.ReallocGrowHeapImpl
import Services.Bootstrap.Alloc.AllocGrowRefines
import Services.Bootstrap.Alloc.ReallocWrap

/-!
# The binary's `realloc_impl` refines the model's `realloc`: growing in place, the heap grown

As `grow_refines`, when the model's `growInplace` grows the allocated space: under
`refineContract`, with the model's `grow` the host's (`growTo pb`, pb the heap's bound in pages).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code JAM

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `unregister` reads only the lists and the headers, not the allocated space. -/
theorem unregister_heads_alloc {s : State} {E x bin : Nat} :
    (unregister { s with allocated := E } x bin).heads = (unregister s x bin).heads := by
  unfold unregister unregisterFirst unsetBit; dsimp only; split
  · split <;> rfl
  · split <;> rfl

/-- **What `growInplace` needs, when it grows the allocated space**: the next chunk below the
    heap's end, free and large enough; the new end E past the allocated space, which `grow` allows;
    and the result, with E allocated. -/
theorem growInplace_grown {grow : Grow} {s s' : State} {ptr req cur : Nat}
    (hsz : wordSize (s.hdr (ptr - 32)).size = cur) (hlt : cur < req + 1)
    (h : growInplace grow s ptr req = some s') (hg : s'.allocated ≠ s.allocated) :
    ptr - 32 + 32 * cur < s.base + 1073741824 ∧ wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = false ∧
      req + 1 ≤ cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size ∧
      s.allocated < (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
        (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1) ∧
      grow s.base ((ptr - 32 + 32 * (req + 1) - s.base) / 32 +
        (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1)) = true ∧
      s' = freeFinal (growHdr (unregister { s with allocated := (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
          (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1) }
          (ptr - 32 + 32 * cur) (binDown (wordSize (s.hdr (ptr - 32 + 32 * cur)).size))) (ptr - 32) (req + 1))
        (ptr - 32 + 32 * (req + 1)) (req + 1) (cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1))
        (s.base + 1073741824) := by
  unfold growInplace at h
  simp only [hsz, maxSize_val, Nat.reduceMul] at h
  rw [if_neg (by omega)] at h
  by_cases h1 : ptr - 32 + 32 * cur ≥ s.base + 1073741824
  · rw [if_pos h1] at h; simp at h
  rw [if_neg h1] at h
  generalize hw : (s.hdr (ptr - 32 + 32 * cur)).size = w at h ⊢
  by_cases h2 : wordUsed w = true
  · rw [if_pos h2] at h; simp at h
  rw [if_neg h2] at h
  by_cases h3 : cur + wordSize w < req + 1
  · rw [if_pos h3] at h; simp at h
  rw [if_neg h3] at h
  generalize hE : (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
    (if cur + wordSize w - (req + 1) = 0 then 0 else 1) = E at h ⊢
  by_cases h4 : s.allocated < E
  · rw [if_pos h4] at h
    by_cases hgr : grow s.base E = true
    · rw [if_pos hgr] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Option.pure_def] at h
      subst h
      exact ⟨by omega, by simpa using h2, by omega, h4, hgr, rfl⟩
    · rw [if_neg hgr] at h; simp at h
  · rw [if_neg h4] at h
    simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Option.pure_def] at h
    subst h
    exact absurd (by rw [freeFinal_allocated, setHdr_allocated, unregister_allocated]) hg

/-- **The binary's `realloc_impl` refines the model's `realloc`, growing in place with the heap
    grown**: as `grow_refines`, when `growInplace` grows the allocated space; the heap's writable
    pages grow to cover it.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem grow_heap_refinesK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : cap < 18446744073709551616) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s s' : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr req = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 42980 ω μ x 40805 ω' μ' x 300 ∧ Rep μ' s' ∧ WF s' ∧
      FirstOk s' ∧ (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
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
  have hlt : cur < req + 1 := by unfold usable at hr; rw [hcur] at hr; omega
  have hfirst := growInplace_first hfo (by
    have ht := hwf.2.2.2.1; unfold TilesOk at ht
    exact (ht.mem_lt _ hXmem).1) h
  obtain ⟨hwfS, hchS⟩ := growInplace_ok hwf hcs h
  obtain ⟨honc, hused, havail, hgr, hgE, hs'0⟩ := growInplace_grown hcur hlt h hgrown
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
  -- every header lies in the allocated space, so in the writable heap
  have hspT : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr + 32 ≤ 4096 * ph := fun c hc => by
    unfold SpaceOk at hspace; have := (hspace c (hcs' ▸ hc)).2; omega
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ 4096 * ph := by
    intro a h
    rcases h with h | h
    · obtain ⟨c, hc, rfl⟩ := unH a h; exact hspT c hc
    · obtain ⟨c, hc, rfl, -⟩ := unF a h; exact hspT c hc
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
  have hF0 : FreeLists s (Fof (pre ++ ⟨ptr - 32, cur, true⟩ :: post)) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  -- the next chunk
  obtain ⟨e, post', rfl⟩ : ∃ e post', post = e :: post' := by
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e post' => exact ⟨e, post', rfl⟩
  have hea : e.addr = ptr - 32 + 32 * cur := hph e rfl
  have hem : e ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: e :: post' := hsub e (Or.inr List.mem_cons_self)
  have hes : (s.hdr e.addr).size = sizeWord e.size e.used := henc e hem
  have heu : e.used = false := by
    rw [hea] at hes; rw [hes] at hused
    cases hu : e.used
    · rfl
    · rw [hu] at hused; simp [wordUsed, sizeWord] at hused
  rw [heu] at hes
  have hw2 : (s.hdr (ptr - 32 + 32 * cur)).size = 2 * e.size := by rw [← hea, hes]; simp [sizeWord]
  have hws : wordSize (s.hdr (ptr - 32 + 32 * cur)).size = e.size := by rw [hw2]; unfold wordSize; omega
  rw [hws] at havail hgr hgE hs'0
  generalize hEd : (ptr - 32 + 32 * (req + 1) - s.base) / 32 + (if cur + e.size - (req + 1) = 0 then 0 else 1) = E
    at hgr hgE hs'0
  have hR : pagesOf (s.base + 32 * E) ≤ pb := of_decide_eq_true hgE
  have hal' : s'.allocated = E := by rw [hs'0, freeFinal_allocated]; simp [growHdr]
  have hcost' : 275 + 121 * (growTop (pagesOf (s.base + 32 * E)) ph pb - ph) ≤ cap := by
    rw [hal'] at hcost; unfold growTop; split <;> omega
  have hel := htiles.mem_lt e hem
  have hFe : Fof (pre ++ ⟨ptr - 32, cur, true⟩ :: e :: post') (binDown e.size) e.addr := ⟨e, hem, rfl, heu, rfl⟩
  obtain ⟨m1, m2⟩ := member_facts hF0 (hbinlt _) hFe
  have hnf : NxFree s F s.base (ptr - 32 + 32 * cur) 0 := by
    unfold NxFree
    rw [← hea, hes, show sizeWord e.size false / 2 = e.size by simp [sizeWord]]
    refine ⟨mkF e hem heu, by simp [sizeWord]; omega, by simp [sizeWord]; omega, by omega, ?_,
      fun h => ?_, fun h => ?_⟩
    · rcases heads_ok hF0 (hbinlt e.size) with h | ⟨c, hc, h1, -⟩
      · exact Or.inl h
      · exact Or.inr (h1 ▸ hAlc c hc)
    · obtain ⟨c, hc, h1, h2⟩ := m1 h; exact h1 ▸ mkF c hc h2
    · obtain ⟨⟨c, hc, h1, h2⟩, h3⟩ := m2 h; exact ⟨h1 ▸ mkF c hc h2, h3⟩
  -- the state after the unlink, through `mergeNext`
  have hF0' : FreeLists s (Fof (pre ++ e :: post')) := hF0.iff (fun b a _ => Fof_skip rfl b a)
  have henc' : ∀ c ∈ e :: post', (s.hdr c.addr).size = sizeWord c.size c.used :=
    fun c hc => henc c (hsub c (Or.inr hc))
  have hcX : Coalesced (⟨ptr - 32, cur, true⟩ :: e :: post') := (Coalesced.append.mp hcoal).2.1
  have hcp : Coalesced (e :: post') :=
    ((Coalesced.append (xs := [⟨ptr - 32, cur, true⟩]) (ys := e :: post')).mp hcX).2.1
  have hnx := mergeNext_free (s := s) (c := ptr - 32) (sz := cur) (sz' := e.size) (T := s.base + 1073741824)
    honc hw2
  obtain ⟨R', post0, hpost0, -, htl2, -, hF2, -, -, -, -, -⟩ :=
    mergeNext_ok htiles henc' hcp hF0' hbits hnx
  have hsub0 : ∀ c ∈ pre ++ post0, c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: e :: post' := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hsub c (Or.inl h)
    · exact hsub c (Or.inr (by rw [hpost0]; exact List.mem_append_right _ h))
  obtain ⟨hpa2, -, hpp2, -⟩ := Tiles.around htl2
  have hold' : cur + e.size - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) ≠ ptr - 32 + 32 * (req + 1) := by
    intro _
    show (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)).heads _ ≠ _
    rw [unregister_heads_alloc]
    rcases heads_ok hF2 (hbinlt (cur + e.size - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · rw [h]; omega
    · rw [← h1]
      rcases List.mem_append.mp hc with h | h
      · have := hpa2 c h; have := htl2.mem_lt c (List.mem_append_left _ h); omega
      · have := (hpp2 c h).1; omega
  have hold1' : cur + e.size - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) ≠ 0 →
      Al s.base ((growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1)))) := by
    intro _ h0
    show Al s.base ((unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)).heads _)
    rw [unregister_heads_alloc]
    change (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)).heads _ ≠ 0 at h0
    rw [unregister_heads_alloc] at h0
    rcases heads_ok hF2 (hbinlt (cur + e.size - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · exact absurd h h0
    · rw [← h1]; exact hAlc c (hsub0 c hc)
  have hold1T : cur + e.size - (req + 1) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) ≠ 0 →
      (growHdr (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) + 32 ≤ 4096 * ph := by
    intro _ h0
    show (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)).heads _ + 32 ≤ 4096 * ph
    rw [unregister_heads_alloc]
    change (unregister { s with allocated := E } (ptr - 32 + 32 * cur) (binDown e.size)).heads _ ≠ 0 at h0
    rw [unregister_heads_alloc] at h0
    rcases heads_ok hF2 (hbinlt (cur + e.size - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · exact absurd h h0
    · rw [← h1]; exact hspT c (hsub0 c hc)
  have hnext' : ptr - 32 + 32 * (cur + e.size) < s.base + 1073741824 → H (ptr - 32 + 32 * (cur + e.size)) := by
    intro hlt
    cases hp : post0 with
    | nil =>
      rw [hp] at htl2
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htl2
      simp only [Tiles] at hm1 hm3; omega
    | cons d ds =>
      have := (Tiles.around htl2).2.1 d (by rw [hp]; rfl)
      exact this ▸ mkH d (hsub0 d (by rw [hp]; simp))
  obtain ⟨ω', μ', run, rep', hpH, hstH, stk, e7, e0, e1, e5, e6⟩ := realloc_impl_grow_heapK (p := p) (P := P) env cap hcap x ω μ s H F sp ptr req cur e.size hrep' h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT hA (hHF _ (Or.inl (mkH _ hXm)))
    (by omega) (mkH _ hXm) hHF (by rw [hXs]; rfl) hlt (by omega) (by omega) honc (by rw [← hea]; exact mkH e hem)
    hw2 hnf havail (by omega) E hEd hgr pb ph hbd h48 hhb hbs hR hcost' hold' hold1' hnext' hHFT hold1T hS hSb hp hst
  have hs' := hs'0
  obtain ⟨g1, g2, g3⟩ := growTop_ge (h := ph) hR
  have hpE := pagesOf_ge (s.base + 32 * E)
  have hbs' : s'.base = s.base := by rw [hs', freeFinal_base]; simp [growHdr]
  refine ⟨ω', μ', run, ?_, hwfS, hfirst, ⟨_, hpH, by rw [hbs', hal']; omega, g2, by omega⟩, hstH, stk,
    e7, e0, e1, e5, e6⟩
  rw [← hs'] at rep'
  -- the model's result, read from memory
  have hwfS' := hwfS
  obtain ⟨-, -, -, htS, hcoS, -, -, -⟩ := hwfS'
  unfold TilesOk at htS
  unfold CoalOk at hcoS
  have htop' : s'.top = s.base + 1073741824 := by
    unfold State.top; rw [maxSize_val, hs', freeFinal_base]; simp [growHdr]
  rw [htop'] at htS
  have hb' : s'.base = s.base := by rw [hs', freeFinal_base]; simp [growHdr]
  rw [hb'] at htS
  rcases hchS with rfl | ⟨e', post'', rest, hpe, -, hrestf, hchS⟩
  · exact ⟨rep'.heads, rep'.sec, rep'.pri, rep'.base, rep'.alloc,
      fun c hc => rep'.prev _ (Or.inl (mkH c (hcs' ▸ hc))),
      fun c hc => rep'.size _ (Or.inl (mkH c (hcs' ▸ hc))),
      fun c hc hu => rep'.next _ (Or.inl (mkF c (hcs' ▸ hc) hu)),
      fun c hc hu => rep'.prevL _ (Or.inl (mkF c (hcs' ▸ hc) hu))⟩
  · obtain ⟨rfl, rfl⟩ := List.cons.inj hpe
    rw [hchS] at htS hcoS
    have hend : Tiles (ptr - 32 + 32 * (cur + e.size)) (s.base + 1073741824) post' := by
      obtain ⟨m, -, hm⟩ := Tiles.append.mp htiles
      obtain ⟨hmX, -, -, -, hm⟩ := hm
      simp only at hmX hm
      rw [show ptr - 32 + 32 * (cur + e.size) = m + 32 * cur + 32 * e.size by omega]
      exact hm
    have hrp := tail_pos htS hrestf hcoS hend
    have cls : ∀ c ∈ chunks s', (c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: e :: post' ∧ (c.used = false →
        c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: e :: post')) ∨ c.addr = ptr - 32 ∨
        (cur + e.size - (req + 1) ≠ 0 ∧ c.addr = ptr - 32 + 32 * (req + 1)) := by
      intro c hc
      rw [hchS] at hc
      rcases List.mem_append.mp hc with h | h
      · exact Or.inl ⟨List.mem_append_left _ h, fun _ => List.mem_append_left _ h⟩
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inr (Or.inl (by rw [h]))
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨a1, a2, a3⟩ := hrp c h
            exact Or.inr (Or.inr ⟨by omega, a1⟩)
          · have : c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: e :: post' :=
              hsub c (Or.inr (List.mem_cons_of_mem _ h))
            exact Or.inl ⟨this, fun _ => this⟩
    have hXu : ∀ c ∈ chunks s', c.addr = ptr - 32 → c.used = true := by
      intro c hc ha
      rw [hchS] at hc
      rcases List.mem_append.mp hc with h | h
      · have := hpa c h; have := (htiles.mem_lt c (List.mem_append_left _ h)).2.2
        exfalso; omega
      · rcases List.mem_cons.mp h with h | h
        · rw [h]
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨a1, -, a3⟩ := hrp c h; exfalso; omega
          · have := (hpp c (List.mem_cons_of_mem _ h)).1; exfalso; omega
    refine ⟨rep'.heads, rep'.sec, rep'.pri, rep'.base, rep'.alloc, fun c hc => ?_, fun c hc => ?_,
      fun c hc hu => ?_, fun c hc hu => ?_⟩
    · rcases cls c hc with ⟨h, -⟩ | h | h
      · exact rep'.prev _ (Or.inl (mkH c h))
      · exact rep'.prev _ (Or.inl (by rw [h]; exact mkH _ hXm))
      · exact rep'.prev _ (Or.inr h)
    · rcases cls c hc with ⟨h, -⟩ | h | h
      · exact rep'.size _ (Or.inl (mkH c h))
      · exact rep'.size _ (Or.inl (by rw [h]; exact mkH _ hXm))
      · exact rep'.size _ (Or.inr h)
    · rcases cls c hc with ⟨-, h⟩ | h | h
      · exact rep'.next _ (Or.inl (mkF c (h hu) hu))
      · exact absurd (hXu c hc h) (by rw [hu]; simp)
      · exact rep'.next _ (Or.inr h)
    · rcases cls c hc with ⟨-, h⟩ | h | h
      · exact rep'.prevL _ (Or.inl (mkF c (h hu) hu))
      · exact absurd (hXu c hc h) (by rw [hu]; simp)
      · exact rep'.prevL _ (Or.inr h)

/-- `grow_heap_refinesK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem grow_heap_refines {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) (s s' : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr req = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 42980 ω μ x 40805 ω' μ' x 300 ∧ Rep μ' s' ∧ WF s' ∧
      FirstOk s' ∧ (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  grow_heap_refinesK (p := p) (P := P) (S0 := S0) (S1 := S1) env hostCostMax (by decide) x ω μ s s'
    sp ptr req hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs h hgrown h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT
    hA hfo (by unfold hostCostMax; omega) hHT hS hSb hp hst

/-- **The binary's `realloc` refines the model's `realloc`, growing in place with the heap grown**:
    from memory holding a well-formed `s` (its first chunk's `prev` 0), the lock byte clear, ω₇ the
    data address of an allocated chunk, ω₉ = `al` and ω₁₀ = `size` octets, with `⌈size/32⌉` units
    above the usable size (below 2²⁵ − 1), when the model's `growInplace` (with the host's
    `growTo pb`) grows the allocated space: the model's `realloc` keeps the address, and `realloc`
    (40701) reaches its return (the `jumpInd` at 40821) with ω₇ = ptr, memory holding the model's
    result, the heap grown to cover it, the lock byte clear again, the caller's ω₀, ω₁, ω₅, ω₆
    restored and the stack from sp up untouched.
    Under `refineContractK cap`: the `grow_heap` call may cost up to `cap`. -/
theorem realloc_wrap_grow_heapK {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : 275 + 121 * (pagesOf (s.base + 32 * s'.allocated) - ph) ≤ cap) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', FreeStepsH p (refineContractK cap env) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  refine ⟨realloc_grow hr h, ?_⟩
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have hcl := ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hwr := HeapPages.wrAt hp hhb hst
  obtain ⟨ω1, μ1, r1, a1, a8, a7, -, a10, a0, a5, -, st8, st16, fr1, ww1, g1⟩ :=
    rw_lock (p := p) (P := P) (R := refineContractK cap env) x ω μ sp ptr al size h1 h7 h9 h10 (by omega) (by omega)
      hal (by omega) (by omega) hsp1 hl (by omega) ⟨by omega, by omega⟩ hwr
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  have hp1 := HeapPages.of_eq hp ww1
  have hst1 : ∀ a, S0 ≤ a → a < S1 → μ1.writable a = true := fun a h1 h2 => by rw [ww1]; exact hst a h1 h2
  obtain ⟨ω2, μ2, r2, rep2, wf2, fo2, ⟨h', hpH, hE', hph, hpb⟩, hst2, stk2, e7, e0, e1, e5, e6⟩ :=
    grow_heap_refinesK (p := p) (P := P) env cap hcap x ω1 μ1 s s' (sp - 16) ptr ((size + 31) / 32) hwf rep1 hc hr hr1
      pb ph hbd h48 hhb hbs h hgrown a1 a8 a7 a10 a0 (by omega) (by omega) hb0 hbT hA hfo hcost hHT
      ⟨by omega, by omega⟩ hSb hp1 hst1
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    rw_unlock (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 (sp - 16) e1 (by rw [e5, a5]) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (HeapPages.wrAt hpH hpb hst2)
  have hb' : s'.base = s.base := growInplace_base h
  refine ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2,
    by rw [fget g3 7 (by decide) (by decide)]; exact e7, cl,
    ⟨h', HeapPages.of_eq hpH ww3, hE', hph, hpb⟩, fun a h1 h2 => by rw [ww3]; exact hst2 a h1 h2,
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))), ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), e6, fget g1 6 (by decide) (by decide)]

/-- `realloc_wrap_grow_heapK` at `hostCostMax`, the cap of `refineContract`: at most 14 pages a
    `grow_heap` call. -/
theorem realloc_wrap_grow_heap {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp ptr al size : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < (size + 31) / 32)
    (hr1 : (size + 31) / 32 < 33554431)
    (pb ph : Nat) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (h : growInplace (growTo pb) s ptr ((size + 31) / 32) = some s') (hgrown : s'.allocated ≠ s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal : al + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hcost : pagesOf (s.base + 32 * s'.allocated) ≤ ph + 14) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (ptr, s', false) ∧
      ∃ ω' μ', FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x 345 ∧ Rep μ' s' ∧ WF s' ∧
        FirstOk s' ∧ ω'[7] = UInt64.ofNat ptr ∧ rdN μ' 206848 1 = 0 ∧
        (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
        (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
        (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  realloc_wrap_grow_heapK (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1)
    env hostCostMax (by decide) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs
    h hgrown h1 h7 h9 h10 hal hsp hsp1 hb0 hbT hA hfo (by unfold hostCostMax; omega) hl hHT hS hSb
    hp hst

end Services.Bootstrap.Alloc
