import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.ReallocCases
import Services.Bootstrap.Decode.VecU8Small

/-!
# `realloc` keeps the heap bound

`realloc_wrap_cases_hdata` is `Alloc.realloc_wrap_cases_data` with one more conclusion for each
block the model's `realloc` (GP Appendix B, Ω_♊'s heap as the host's `growTo pb`) returns: the new
state keeps the heap base, and its allocated space ends within the heap's pages h'
(`s'.base + 32 · s'.allocated ≤ 4096 · h'`). That bound is a hypothesis of every allocator theorem,
so with it a caller can run `alloc` or `realloc` again after a `realloc`, as `read_vec`'s chunk
loop (3473) does. The model lemmas: `free`, `shrink` and `free`'s merges keep the allocated space,
and `realloc_chunk`: the block `realloc` returns is an allocated chunk of exactly the request plus
one unit.
-/
namespace Picoalloc

/-- `growInplace_ok` when the chunk does grow (its `cur` units below `newReq + 1`): it takes in its
    free successor, the rest of which, if any, stays free. -/
theorem growInplace_grows {grow : Grow} {s s' : State} {ptr newReq cur : Nat} {pre post : List Chunk}
    (hwf : WF s) (hcs : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post) (hlt : cur < newReq + 1)
    (h : growInplace grow s ptr newReq = some s') :
    ∃ e post' rest, post = e :: post' ∧ e.used = false ∧ (∀ c ∈ rest, c.used = false) ∧
      chunks s' = pre ++ ⟨ptr - 32, newReq + 1, true⟩ :: (rest ++ post') := by
  have hwf' := hwf
  obtain ⟨hb0, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold PrevsOk at hprev
  unfold ListsOk' at hlists
  unfold SpaceOk at hspace
  have henc := @chunks_hdr s
  rw [hcs] at htiles hcoal hprev hlists hspace henc
  generalize hX : ptr - 32 = X at *
  generalize hk : newReq + 1 = k at *
  have hcur : wordSize (s.hdr X).size = cur := by
    rw [henc ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self), wordSize_sizeWord]
  unfold growInplace at h
  simp only [hX, hk, hcur] at h
  split at h
  · rename_i hck; exfalso; omega
  rename_i hck
  split at h
  · simp at h
  rename_i hT
  split at h
  · simp at h
  rename_i hu
  split at h
  · simp at h
  rename_i hav
  have hT' : s.base + 32 * maxSize = s.top := rfl
  rw [hT'] at hT h
  obtain ⟨m, -, hXm, -, hrest⟩ := Tiles.append.mp htiles
  simp only at hXm hrest
  subst hXm
  have hXal := htiles.aligned ⟨X, cur, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hXal
  cases post with
  | nil =>
    have : X + 32 * cur = s.top := hrest
    omega
  | cons e post' =>
  obtain ⟨he1, he2, -⟩ := hrest
  have hee := henc e (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [← he1, hee, wordUsed_sizeWord] at hu
  rw [← he1, hee, wordSize_sizeWord] at hav h
  have heu : e.used = false := by simpa using hu
  generalize hE : (X + 32 * k - s.base) / 32 + (if cur + e.size - k = 0 then 0 else 1) = E at h
  obtain ⟨sa, sah, saheads, sasec, sapri, sabase, saA1, saA2, rfl⟩ : ∃ sa : State, sa.hdr = s.hdr ∧
      sa.heads = s.heads ∧ sa.secondary = s.secondary ∧ sa.primary = s.primary ∧ sa.base = s.base ∧
      s.allocated ≤ sa.allocated ∧ E ≤ sa.allocated ∧
      s' = freeFinal (setHdr (unregister sa e.addr (binDown e.size)) X
        (fun h => { h with size := sizeWord k true })) (X + 32 * k) k (cur + e.size - k) s.top := by
    by_cases hlt : s.allocated < E
    · by_cases hg : grow s.base E = true
      · simp only [hlt, hg, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        exact ⟨{ s with allocated := E }, rfl, rfl, rfl, rfl, rfl, Nat.le_of_lt hlt, Nat.le_refl _, h.symm⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨s, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, by omega, h.symm⟩
  -- the lists
  have hF0 : FreeLists s (Fof (pre ++ ⟨X, cur, true⟩ :: e :: post')) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  have hFa : FreeLists sa (Fof (pre ++ ⟨X, cur, true⟩ :: e :: post')) :=
    hF0.congr saheads (fun x => by rw [sah]) (fun x => by rw [sah])
  have hba : BitsOk sa.secondary sa.primary sa.heads := by rw [sasec, sapri, saheads]; exact hbits
  obtain ⟨r1, r2⟩ := remove_ok (bin := binDown e.size) (x := e.addr) hFa (Fof_disj htiles (fun _ h => h)) hba
    (toBin_lt false (Nat.min_le_right _ _))
    ⟨e, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl, heu, rfl⟩
  generalize hs1 : unregister sa e.addr (binDown e.size) = s1 at r1 r2 ⊢
  have hl : pre ++ ⟨X, cur, true⟩ :: e :: post' = (pre ++ [⟨X, cur, true⟩]) ++ e :: post' := by simp
  have htiles' := htiles
  rw [hl] at htiles'
  have hF2 : FreeLists (setHdr s1 X (fun h => { h with size := sizeWord k true })) (Fof (pre ++ post')) :=
    ((FreeLists.congr (t := setHdr s1 X (fun h => { h with size := sizeWord k true })) r1 rfl (setHdr_next (f := fun h => { h with size := sizeWord k true }) (fun _ => rfl))
      (setHdr_prevL (f := fun h => { h with size := sizeWord k true }) (fun _ => rfl)))).iff (fun b a _ => by
        rw [hl, Fof_remove htiles'.others, show (pre ++ [⟨X, cur, true⟩]) ++ post' = pre ++ ⟨X, cur, true⟩ :: post'
          by simp, Fof_skip rfl])
  have hsz2 : ∀ x, ((setHdr s1 X (fun h => { h with size := sizeWord k true })).hdr x).size =
      if x = X then sizeWord k true else (s.hdr x).size := by
    intro x
    by_cases hx : x = X
    · subst hx; rw [setHdr_self, if_pos rfl]
    · rw [setHdr_other hx, if_neg hx, ← hs1, unregister_hdr.2, sah]
  have hpv2 : ∀ x, ((setHdr s1 X (fun h => { h with size := sizeWord k true })).hdr x).prev = (s.hdr x).prev := by
    intro x
    by_cases hx : x = X
    · subst hx; rw [setHdr_self]; show (s1.hdr x).prev = _; rw [← hs1, unregister_hdr.1, sah]
    · rw [setHdr_other hx, ← hs1, unregister_hdr.1, sah]
  have hbase2 : (setHdr s1 X (fun h => { h with size := sizeWord k true })).base = s.base := by
    rw [setHdr_base, ← hs1, unregister_base, sabase]
  have halloc2 : (setHdr s1 X (fun h => { h with size := sizeWord k true })).allocated = sa.allocated := by
    rw [setHdr_allocated, ← hs1, unregister_allocated]
  have htlm : Tiles s.base s.top (pre ++ ⟨X, cur + e.size, true⟩ :: post') := htiles.merge
  -- the neighbours
  obtain ⟨c1, c2, -⟩ := Coalesced.append.mp hcoal
  have c2' : Coalesced (e :: post') := ((Coalesced.append (xs := [⟨X, cur, true⟩])).mp c2).2.1
  have c3 : Coalesced post' := ((Coalesced.append (xs := [e])).mp c2').2.1
  have hhead := (Coalesced.around (pre := []) heu c2').1
  obtain ⟨p1, p2, plink⟩ := PrevOk.append.mp hprev
  have p3 : PrevOk s post' := ((PrevOk.append (xs := [⟨X, cur, true⟩, e])).mp p2).2.1
  have memBoth : ∀ c ∈ pre ++ post', c ∈ pre ++ ⟨X, cur, true⟩ :: e :: post' := fun c hc => by
    rcases List.mem_append.mp hc with hc | hc
    · exact List.mem_append_left _ hc
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc))
  have hsp : ∀ c ∈ pre ++ post', (c.used = true → c.addr + 32 * c.size ≤ s.base + 32 * sa.allocated) ∧
      c.addr + 32 ≤ s.base + 32 * sa.allocated := fun c hc => by
    obtain ⟨h1, h2⟩ := hspace c (memBoth c hc)
    exact ⟨fun hu => by have := h1 hu; omega, by omega⟩
  by_cases hr : cur + e.size - k = 0
  · rw [hr, freeFinal_zero]
    rw [hr] at hE
    have hkt : cur + e.size = k := by omega
    rw [hkt] at htlm
    obtain ⟨hch, hw⟩ := exactTail_ok hb0 hbal hfit htlm hF2 r2 hsz2 hpv2 hbase2 halloc2
      (fun c hc => henc c (memBoth c hc)) c1 c3 p1 p3 (fun x hx => plink x hx _ rfl) hsp (by omega)
    exact ⟨e, post', [], rfl, heu, by simp, hch⟩
  · rw [if_neg hr] at hE
    obtain ⟨hch, hw⟩ := splitTail_ok hb0 hbal hfit htlm (by omega) (by omega) hF2 r2 hsz2 hpv2 hbase2 halloc2
      (fun c hc => henc c (memBoth c hc)) c1 c3 hhead p1 p3 (fun x hx => plink x hx _ rfl) hsp (by omega)
    exact ⟨e, post', [⟨X + 32 * k, cur + e.size - k, false⟩], rfl, heu, by simp, hch⟩



/-- **The block `realloc` returns** (alignment one unit, a nonzero request, the data address of an
    allocated chunk): its chunk is an allocated chunk of exactly `newReq + 1` units of the new state,
    so its usable size is `newReq`. -/
theorem realloc_chunk {grow : Grow} {hb : Nat} {s s' : State} {ptr newReq p : Nat} {cp : Bool} (hwf : WF s)
    (hbT : s.base + 1073741824 < 2147483648)
    (hptr : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (h0 : newReq ≠ 0)
    (h : realloc grow hb s ptr 1 newReq = some (p, s', cp)) :
    ∃ c ∈ chunks s', c.addr + 32 = p ∧ c.used = true ∧ c.size = newReq + 1 := by
  obtain ⟨c, hc, h1, h2⟩ := hptr
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  have hc' : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at h1 h2 ⊢; subst h2; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hc'] at hcs
  have hcur : wordSize (s.hdr (ptr - 32)).size = c.size := by
    have := chunks_hdr c hc
    rw [show c.addr = ptr - 32 by omega, h2] at this
    rw [this, wordSize_sizeWord]
  unfold realloc usable at h
  rw [hcur] at h
  by_cases e1 : newReq = c.size - 1
  · simp only [e1, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨c, hc, h1, h2, by omega⟩
  by_cases e3 : newReq < c.size - 1
  · simp only [e1, h0, e3, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨_, _, _, -, -, hch, -⟩ := shrink_ok (cur := c.size) (newReq := newReq) hwf hcs (by omega)
    exact ⟨⟨ptr - 32, newReq + 1, true⟩, by rw [hch]; simp, by simp only; omega, rfl, rfl⟩
  simp only [e1, h0, e3, ↓reduceIte] at h
  cases hg : growInplace grow s ptr newReq with
  | some s2 =>
    simp only [hg, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    obtain ⟨_, _, _, -, -, -, hch⟩ := growInplace_grows hwf hcs (by omega) hg
    exact ⟨⟨ptr - 32, newReq + 1, true⟩, by rw [hch]; simp, by simp only; omega, rfl, rfl⟩
  | none =>
    simp only [hg] at h
    cases ha : alloc grow hb 1 newReq s with
    | none => simp [ha] at h
    | some r =>
      obtain ⟨p1, s1⟩ := r
      simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      have hw1 := alloc_wf hwf ha
      obtain ⟨-, hm1, hq1, -, -⟩ := Services.Bootstrap.Decode.VecU8.alloc_block hwf hbT ha
      obtain ⟨pre', post', S, h1', -, h2'⟩ := alloc_chunks hwf ha
      have hm : (⟨ptr - 32, c.size, true⟩ : Chunk) ∈ pre' ++ ⟨p1 - 32, S, false⟩ :: post' := by
        rw [← h1', hcs]; exact List.mem_append_right _ List.mem_cons_self
      have hold : (⟨ptr - 32, c.size, true⟩ : Chunk) ∈ chunks s1 := by
        rw [h2']
        rcases List.mem_append.mp hm with hm | hm
        · exact List.mem_append_left _ hm
        · rcases List.mem_cons.mp hm with hm | hm
          · simp at hm
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
      obtain ⟨pr1, po1, hcs1⟩ := List.append_of_mem hold
      obtain ⟨pre0, L, R, post0, M, total, rfl, rfl, hLR, hchF, -, -⟩ := free_ok hw1 hcs1
      refine ⟨⟨p1 - 32, newReq + 1, true⟩, ?_, by simp only; omega, rfl, rfl⟩
      rw [hchF]
      rw [hcs1] at hm1
      simp only [List.mem_append, List.mem_cons] at hm1 ⊢
      rcases hm1 with (hm1 | hm1) | hm1 | hm1 | hm1
      · exact Or.inl hm1
      · have := hLR _ (List.mem_append_left _ hm1); simp at this
      · exfalso; simp only [Chunk.mk.injEq] at hm1; omega
      · have := hLR _ (List.mem_append_right _ hm1); simp at this
      · exact Or.inr (Or.inr hm1)

end Picoalloc

namespace Services.Bootstrap.Decode.ReallocOk

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM

/-- `free`'s merge with the previous chunk keeps the allocated space. -/
theorem mergePrev_allocated {s : State} {c z pv : Nat} : (mergePrev s c z pv).1.allocated = s.allocated := by
  unfold mergePrev; split
  · dsimp only; split <;> simp
  · rfl

/-- `free`'s merge with the next chunk keeps the allocated space. -/
theorem mergeNext_allocated {s : State} {c z T : Nat} : (mergeNext s c z T).1.allocated = s.allocated := by
  unfold mergeNext; split
  · split <;> simp
  · rfl

/-- `free` keeps the allocated space. -/
theorem free_allocated {s : State} {ptr : Nat} : (free s ptr).allocated = s.allocated := by
  unfold free; exact freeFinal_allocated.trans (mergeNext_allocated.trans mergePrev_allocated)

/-- `shrink` keeps the allocated space. -/
theorem shrink_allocated {s : State} {ptr r : Nat} : (shrink s ptr r).allocated = s.allocated := by
  unfold shrink; dsimp only
  split
  · rfl
  · exact freeFinal_allocated.trans (mergeNext_allocated.trans setHdr_allocated)

/-- `realloc` to a nonzero size at most the usable size (in place, maybe shrunk) keeps the base
    and the allocated space. -/
theorem realloc_inplace_state {grow : Grow} {hb : Nat} {s s' : State} {ptr al req r : Nat} {b : Bool}
    (hle : req ≤ usable s ptr) (h0 : req ≠ 0) (h : realloc grow hb s ptr al req = some (r, s', b)) :
    s'.base = s.base ∧ s'.allocated = s.allocated := by
  have hu : realloc grow hb s ptr al req = some (ptr, if req = usable s ptr then s else shrink s ptr req, false) := by
    unfold realloc
    by_cases he : req = usable s ptr
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he, if_neg h0, if_pos (by omega)]; rfl
  rw [hu] at h; cases h
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨shrink_base, shrink_allocated⟩

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open Services.Bootstrap.Decode.VecU8 in
/-- **`realloc_wrap_cases_dataG` with the heap bound**: as `Alloc.realloc_wrap_cases_dataG`, and for
    each block `(r, s', _)` the model's `realloc` returns, `s'.base = s.base` and the h' whose pages
    the heap then has also bounds the allocated space: `s'.base + 32 · s'.allocated ≤ 4096 · h'`
    (h' = ph when nothing grew; the grown page count when `grow_heap` ran, in place or in the
    fallback's `alloc`). -/
theorem realloc_wrap_cases_hdataG {X : Type} {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ 0 → μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
          μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32))) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (env.rel hostCostMax) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ s'.base = s.base ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) := by
  have hwr := HeapPages.wrAt hp hhb hst
  have hal : al + 31 < 68719476736 := by omega
  by_cases hin : (size + 31) / 32 ≤ usable s ptr ∧ size ≠ 0
  · -- in place (the same usable size, or shrunk)
    obtain ⟨s', e, ω', μ', dat, run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
      realloc_wrap_inplace_data (p := p) (P := P) (R := env.rel hostCostMax) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al size hwf hrep hc
        hin.2 hin.1 h1 h7 h9 h10 hal (by omega) (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_right hin.1]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [e] at hrr; cases hrr; obtain ⟨eb, ea⟩ := realloc_inplace_state hin.1 (by omega) e; exact ⟨e7, rep, wf, fo, eb, ph, HeapPages.of_eq hp ww, by rw [eb, ea]; exact hHT, Nat.le_refl _, hhb⟩,
      fun hrr => by rw [e] at hrr; cases hrr⟩
  by_cases hs0 : size = 0
  · -- to size 0: freed, null
    subst hs0
    obtain ⟨e, ω', μ', run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
      realloc_wrap_zero (p := p) (P := P) (R := env.rel hostCostMax) (grow := growTo pb) (hb := hb) x ω μ s sp ptr al hwf hrep hc
        (hz rfl) h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hfo hl hHT ⟨by omega, by omega⟩ hwr
    exact ⟨ω', μ',
      fun r s'' b hrr hn => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn,
      fun r s'' b hrr _ hn2 => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr; exact absurd rfl hn2,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
      fun r s'' b hrr => by
        rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr
        exact ⟨e7, rep, wf, fo, free_base', ph, HeapPages.of_eq hp ww, by rw [free_base', free_allocated]; exact hHT, Nat.le_refl _, hhb⟩,
      fun hrr => by rw [show (0 + 31) / 32 = 0 from rfl, e] at hrr; cases hrr⟩
  have hr : usable s ptr < (size + 31) / 32 := by omega
  cases hg : growInplace (growTo pb) s ptr ((size + 31) / 32) with
  | some s' =>
    by_cases hng : s'.allocated = s.allocated
    · -- grown in place
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
        realloc_wrap_grow_data (p := p) (P := P) (R := env.rel hostCostMax) (hb := hb) x ω μ s s' sp ptr al size hwf hrep hc hr hr1 hg hng
          h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo hl hHT ⟨by omega, by omega⟩ hwr
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6,
        fun r s'' b hrr => by
          rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, growInplace_base hg, ph, HeapPages.of_eq hp ww, by rw [growInplace_base hg, hng]; exact hHT, Nat.le_refl _, hhb⟩,
        fun hrr => by rw [e] at hrr; cases hrr⟩
    · -- grown in place, the heap grown
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, hB, hph, hpb⟩, hst', stk, e0, e1, e5, e6⟩ :=
        realloc_wrap_grow_heap_dataG (p := p) (P := P) (hb := hb) env x ω μ s s' sp ptr al size hwf hrep hc hr hr1 pb ph hbd h48 hhb hbs hg
          hng h1 h7 h9 h10 hal (by omega) hsp1 hb0 hbT hA hfo
          (Nat.le_trans (growInplace_pages hr hg hng) hcost) hl hHT ⟨by omega, by omega⟩ hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr hn1 _ => by rw [e] at hrr; cases hrr; exact absurd rfl hn1,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, growInplace_base hg, h', hpH, hB, hph, hpb⟩,
        fun hrr => by rw [e] at hrr; cases hrr⟩
  | none =>
    cases ha : alloc (growTo pb) hb 1 ((size + 31) / 32) s with
    | some qs =>
      obtain ⟨q, s1⟩ := qs
      have hc1 : pagesOf (s.base + 32 * s1.allocated) ≤ ph + 14 := by
        by_cases hng : s1.allocated = s.allocated
        · rw [hng]; exact Nat.le_trans (pagesOf_le hHT) (by omega)
        · exact Nat.le_trans (alloc_pages hwf ha hng) hcost
      obtain ⟨e, ω', μ', dat, run, rep, wf, fo, e7, cl, ⟨h', hpH, hB, hph, hpb⟩, hst', stk, e0, e1, e5, e6⟩ :=
        realloc_wrap_fallback_dataG (p := p) (P := P) (hb := hb) env x ω μ s s1 sp ptr al size q pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha hc1 h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr _ => by rw [e] at hrr; cases hrr; rw [Nat.min_eq_left (Nat.le_of_lt hr)]; exact dat,
      fun r s'' b hrr _ _ => by rw [e] at hrr; cases hrr; exact dat,
      run.mono (by omega), cl, hst', stk, e0, e1, e5, e6,
        fun r s'' b hrr => by rw [e] at hrr; cases hrr; exact ⟨e7, rep, wf, fo, by rw [free_base', (alloc_block hwf hbT ha).1], h', hpH, by rw [free_base', free_allocated]; exact hB, hph, hpb⟩,
        fun hrr => by rw [e] at hrr; cases hrr⟩
    | none =>
      obtain ⟨e, ω', μ', run, rep, e7, cl, hp', hst', fr, -, e0, e1, e5, e6⟩ :=
        realloc_wrap_fallback_failG (p := p) (P := P) (hb := hb) env x ω μ s sp ptr al size pb ph hwf hrep hc hr hr1 hbd h48 hhb hbs hg
          ha h1 h7 h9 h10 hal1 hal2 hsp hsp1 hb0 hbT hA hl hHTs hHT hS hSb hp hst
      exact ⟨ω', μ',
      fun r s'' b hrr => (by rw [e] at hrr; cases hrr),
      fun r s'' b hrr => (by rw [e] at hrr; cases hrr),
      run.mono (by omega), cl, hst',
        fun a h1 h2 => fr a h1 (Or.inr h2) (Or.inr (by omega)) (Or.inr (by omega)), e0, e1, e5, e6,
        fun r s'' b hrr => (by rw [e] at hrr; cases hrr), fun _ => ⟨e7, rep, hp'⟩⟩

/-- `realloc_wrap_cases_hdataG` for the refine contract (`refineHeap env`). -/
theorem realloc_wrap_cases_hdata {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env)
    (x : RefineCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp ptr al size pb ph : Nat)
    (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (hr1 : (size + 31) / 32 < 33554431) (hz : size = 0 → usable s ptr ≠ 0)
    (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb) (hbs : pb < 4294967296)
    (hcost : pb ≤ ph + 14)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr) (h9 : ω[9] = UInt64.ofNat al)
    (h10 : ω[10] = UInt64.ofNat size) (hal1 : 1 ≤ al) (hal2 : al ≤ 32)
    (hsp : 2147483968 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hHT : s.base + 32 * s.allocated ≤ 4096 * ph)
    (hS : S0 + 320 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0) (hp : HeapPages μ 48 pb ph)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true) :
    ∃ ω' μ', (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ 0 → μ'.readN r (32 * min (usable s ptr) ((size + 31) / 32)) =
          μ.readN ptr (32 * min (usable s ptr) ((size + 31) / 32))) ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        r ≠ ptr → r ≠ 0 → μ'.readN r (32 * usable s ptr) = μ.readN ptr (32 * usable s ptr)) ∧
      FreeStepsH p (refineContract env) 40701 ω μ x 40821 ω' μ' x (64 * usable s ptr + 1300) ∧
      rdN μ' 206848 1 = 0 ∧ (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ r s' b, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = some (r, s', b) →
        ω'[7] = UInt64.ofNat r ∧ Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ s'.base = s.base ∧
        ∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none →
        ω'[7] = UInt64.ofNat 0 ∧ Rep μ' s ∧ HeapPages μ' 48 pb ph) :=
  realloc_wrap_cases_hdataG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s sp ptr al size pb ph hwf hrep hc hr1 hz hbd h48 hhb hbs hcost h1 h7 h9 h10 hal1 hal2 hsp hsp1 hsp8 hba hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hHT hS hSb hp hst


end Services.Bootstrap.Decode.ReallocOk
