import Services.Bootstrap.Alloc.ReallocGrowImpl
import Services.Bootstrap.Alloc.ReallocRefines

/-!
# The binary's grow in place on a well-formed heap

The facts `realloc_impl_grow` takes about the heap, from the invariant; and the memory it leaves,
read back as `Rep` of the model's `growInplace`.
-/

namespace Picoalloc

theorem freeFinal_allocated {s : State} {c p n T : Nat} : (freeFinal s c p n T).allocated = s.allocated := by
  unfold freeFinal; split <;> simp

/-- **What `growInplace` needs, when it keeps the allocated space**: the next chunk below the
    heap's end, free, large enough, and the new end within the allocated space. -/
theorem growInplace_facts {grow : Grow} {s s' : State} {ptr req cur : Nat}
    (hsz : wordSize (s.hdr (ptr - 32)).size = cur) (hlt : cur < req + 1)
    (h : growInplace grow s ptr req = some s') (hng : s'.allocated = s.allocated) :
    ptr - 32 + 32 * cur < s.base + 1073741824 ∧ wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = false ∧
      req + 1 ≤ cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size ∧
      (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
        (if cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size - (req + 1) = 0 then 0 else 1) ≤ s.allocated := by
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
  refine ⟨by omega, by simpa using h2, by omega, ?_⟩
  by_cases h4 : s.allocated < (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
      (if cur + wordSize w - (req + 1) = 0 then 0 else 1)
  · exfalso
    rw [if_pos h4] at h
    generalize hE : (ptr - 32 + 32 * (req + 1) - s.base) / 32 +
      (if cur + wordSize w - (req + 1) = 0 then 0 else 1) = E at h h4
    by_cases hg : grow s.base E = true
    · rw [if_pos hg] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, Option.pure_def] at h
      subst h
      rw [freeFinal_allocated, setHdr_allocated, unregister_allocated] at hng
      exact absurd hng (by show ¬ E = s.allocated; omega)
    · rw [if_neg hg] at h; simp at h
  · omega

/-- A tiling's start is determined by its chunks and its end. -/
theorem Tiles.start_eq {a b T : Nat} {l : List Chunk} (ha : Tiles a T l) (hb : Tiles b T l) : a = b := by
  cases l with
  | nil => exact ha.trans hb.symm
  | cons c cs => exact ha.1.symm.trans hb.1

/-- The free chunks between an allocation of n units at X and chunks tiling from X + 32·m: one
    chunk, of m − n units, at X + 32·n. -/
theorem tail_pos {a T X n m : Nat} {pre rest post : List Chunk}
    (h : Tiles a T (pre ++ ⟨X, n, true⟩ :: (rest ++ post))) (hrest : ∀ c ∈ rest, c.used = false)
    (hco : Coalesced (pre ++ ⟨X, n, true⟩ :: (rest ++ post))) (hend : Tiles (X + 32 * m) T post) :
    ∀ c ∈ rest, c.addr = X + 32 * n ∧ c.size = m - n ∧ n < m := by
  intro c hc
  obtain ⟨k, -, hk⟩ := Tiles.append.mp h
  obtain ⟨hkX, -, hk⟩ := hk
  simp only at hkX hk
  have hco' := (Coalesced.append.mp hco).2.1
  cases rest with
  | nil => simp at hc
  | cons c0 rest' =>
    obtain ⟨h0a, h0s, h0r⟩ := hk
    cases rest' with
    | nil =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      have := Tiles.start_eq h0r hend
      omega
    | cons c1 rest'' =>
      exfalso
      have hc0 := hrest c0 List.mem_cons_self
      have hc1 := hrest c1 (List.mem_cons_of_mem _ List.mem_cons_self)
      have := hco'.2.1
      simp [hc0, hc1] at this

end Picoalloc

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The free tail's header lies in the allocated space. -/
theorem tail_le {X b A HT n : Nat} (hX : (X - b) % 32 = 0) (hb : b ≤ X)
    (hE : (X + 32 * n - b) / 32 + 1 ≤ A) (hHT : b + 32 * A ≤ HT) : X + 32 * n + 32 ≤ HT := by
  omega

/-- `mergeNext` with a free next chunk below the end: it leaves its bin and is merged in. -/
theorem mergeNext_free {s : State} {c sz sz' T : Nat} (hlt : c + 32 * sz < T)
    (hw : (s.hdr (c + 32 * sz)).size = 2 * sz') :
    mergeNext s c sz T = (unregister s (c + 32 * sz) (binDown sz'), sz + sz') := by
  have h1 : wordUsed (s.hdr (c + 32 * sz)).size = false := by rw [hw]; unfold wordUsed; simp
  have h2 : wordSize (s.hdr (c + 32 * sz)).size = sz' := by rw [hw]; unfold wordSize; omega
  unfold mergeNext; rw [if_pos hlt, h1, h2]; rfl

/-- **The binary's `realloc_impl` refines the model's `growInplace`**, when the heap does not
    grow: from memory holding a well-formed `s`, the data address `ptr` of an allocated chunk and
    a request `req` above `usable s ptr` (below 2²⁵ − 1 units), when the model grows the allocation
    in place without changing the allocated space, `realloc_impl` (42980) returns into `realloc`
    (40805) with ω₇ = ptr and memory holding the model's result, itself well-formed with its first
    chunk's `prev` 0, the caller's ω₀, ω₁, ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem grow_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} (s s' : State) (sp ptr req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (h : growInplace grow s ptr req = some s') (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 250 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
      (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
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
  obtain ⟨honc, hused, havail, hE⟩ := growInplace_facts hcur hlt h hng
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
  have hspT : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr + 32 ≤ HT := fun c hc => by
    unfold SpaceOk at hspace; have := (hspace c (hcs' ▸ hc)).2; omega
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT := by
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
  rw [hws] at havail hE
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
      (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) ≠ ptr - 32 + 32 * (req + 1) := by
    intro _
    show (unregister s (ptr - 32 + 32 * cur) (binDown e.size)).heads _ ≠ _
    rcases heads_ok hF2 (hbinlt (cur + e.size - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · rw [h]; omega
    · rw [← h1]
      rcases List.mem_append.mp hc with h | h
      · have := hpa2 c h; have := htl2.mem_lt c (List.mem_append_left _ h); omega
      · have := (hpp2 c h).1; omega
  have hold1' : cur + e.size - (req + 1) ≠ 0 →
      (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) ≠ 0 →
      Al s.base ((growHdr (unregister s (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1)))) := by
    intro _ h0
    show Al s.base ((unregister s (ptr - 32 + 32 * cur) (binDown e.size)).heads _)
    rcases heads_ok hF2 (hbinlt (cur + e.size - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · exact absurd h h0
    · rw [← h1]; exact hAlc c (hsub0 c hc)
  have hold1T : cur + e.size - (req + 1) ≠ 0 →
      (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) ≠ 0 →
      (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1)).heads
        (binDown (cur + e.size - (req + 1))) + 32 ≤ HT := by
    intro _ h0
    show (unregister s (ptr - 32 + 32 * cur) (binDown e.size)).heads _ + 32 ≤ HT
    rcases heads_ok hF2 (hbinlt (cur + e.size - (req + 1))) with h | ⟨c, hc, h1, -⟩
    · exact absurd h h0
    · rw [← h1]; exact hspT c (hsub0 c hc)
  have hNT : cur + e.size - (req + 1) ≠ 0 → ptr - 32 + 32 * (req + 1) + 32 ≤ HT := by
    intro hr0
    have h' := hE; rw [if_neg hr0] at h'
    exact tail_le hXa.2 hXa.1 h' hHT
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
  obtain ⟨ω', μ', run, rep', ww, stk, e7, e0, e1, e5, e6⟩ := realloc_impl_grow (p := p) (P := P) (R := R)
    x ω μ s H F sp ptr req cur e.size hrep' h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT hA (hHF _ (Or.inl (mkH _ hXm)))
    (by omega) (mkH _ hXm) hHF (by rw [hXs]; rfl) hlt (by omega) (by omega) honc (by rw [← hea]; exact mkH e hem)
    hw2 hnf havail (by omega) hE hold' hold1' hnext' hHFT hNT hold1T hS hw
  have hs' : s' = freeFinal (growHdr (unregister s (ptr - 32 + 32 * cur) (binDown e.size)) (ptr - 32) (req + 1))
      (ptr - 32 + 32 * (req + 1)) (req + 1) (cur + e.size - (req + 1)) (s.base + 1073741824) := by
    have := growInplace_eq (grow := grow) (by rw [hXs]; rfl) hlt honc hw2 havail hE
    rw [h] at this; exact Option.some.inj this
  refine ⟨ω', μ', run, ?_, hwfS, hfirst, ww, stk, e7, e0, e1, e5, e6⟩
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

/-- The model's `realloc` above the usable size, when `growInplace` succeeds: the address kept, no
    copy. -/
theorem realloc_grow {grow : Grow} {hb : Nat} {s s' : State} {ptr align req : Nat} (hr : usable s ptr < req)
    (h : growInplace grow s ptr req = some s') :
    realloc grow hb s ptr align req = some (ptr, s', false) := by
  unfold realloc
  have e1 : req ≠ usable s ptr := by omega
  have e2 : req ≠ 0 := by omega
  have e3 : ¬ req < usable s ptr := by omega
  simp [e1, e2, e3, h]

/-- **The binary's `realloc_impl` refines the model's `realloc`, growing in place**: from memory
    holding a well-formed `s` (its first chunk's `prev` 0), the data address `ptr` of an allocated
    chunk and a request `req` above `usable s ptr` (below 2²⁵ − 1 units), when the model's
    `growInplace` succeeds without changing the allocated space, the model's `realloc` gives
    `(ptr, s', false)` and `realloc_impl` (42980) returns into `realloc` (40805) with ω₇ = ptr and
    memory holding `s'`, itself well-formed with its first chunk's `prev` 0, the caller's ω₀, ω₁,
    ω₅, ω₆ restored and the stack from sp up untouched. -/
theorem realloc_grow_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s' : State) (sp ptr align req : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hr : usable s ptr < req) (hr1 : req < 33554431)
    (h : growInplace grow s ptr req = some s') (hng : s'.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483800 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 152 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr align req = some (ptr, s', false) ∧
      ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x 250 ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  ⟨realloc_grow hr h, grow_refines (p := p) (P := P) (R := R) x ω μ s s' sp ptr req hwf hrep hc hr hr1 h hng
    h1 h8 h7 h10 h0 hsp hsp1 hb0 hbT hA hfo hHT hS hw⟩

end Services.Bootstrap.Alloc
