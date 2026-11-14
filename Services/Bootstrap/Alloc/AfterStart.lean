import Services.Bootstrap.Alloc.AllocInit
import Services.Picoalloc.First

/-!
# The allocator after the SDK's start-up

Refine's argument parse runs the SDK start-up (44241), whose `fetch_vec` allocates once and later
frees that block. The first allocation runs picoalloc's `initialize` (`AllocInit.lean`), which
makes one free chunk spanning the address space at the heap base 206880; the allocation grows the
allocated space to 6 units, and the free merges the heap back into that one chunk. So when refine
starts decoding, the allocator is `init`'s state with `allocated := 6`: `sStart`.

Here: `sStart`, its invariant and chunk list, `Rep μ sStart` from the memory words, the first
allocation from it (a used chunk at the base, then the free rest: `OneUsed`), and `realloc`'s
in-place growth of that chunk, which keeps `OneUsed`.
-/

namespace Services.Bootstrap.Alloc.AfterStart

open PVM Picoalloc Services.Bootstrap.Alloc

/-! ## The state -/

/-- The allocator's zeroed static state. -/
def zeroState : State := ⟨0, 0, 0, fun _ => 0, fun _ => 0, fun _ => ⟨0, 0, 0, 0⟩⟩

/-- `init`'s state at heap base 206880: one free chunk of `maxSize` = 2²⁵ units, first in bin
    2431 (word 37, bit 63 of the bitmap). -/
def sInit : State where
  allocated := 1
  base := 206880
  primary := 2 ^ 37
  secondary := upd (fun _ => 0) 37 (2 ^ 63)
  heads := upd (fun _ => 0) 2431 206880
  hdr := upd (fun _ => ⟨0, 0, 0, 0⟩) 206880 ⟨0, sizeWord maxSize false, 0, 0⟩

/-- **The allocator when refine starts decoding**: `init`'s state, 6 units allocated. -/
def sStart : State := { sInit with allocated := 6 }

theorem init_zero {grow : Grow} (hg : grow 206880 1 = true) : init grow 206880 zeroState = some sInit := by
  unfold init
  simp only [zeroState, ne_eq, not_true_eq_false, ↓reduceIte, hg, Bool.not_true, Bool.false_eq_true,
    binDown_max, Option.some.injEq]
  unfold sInit setHdr setBit
  simp only [show 2431 / 64 = 37 from rfl, show 2431 % 64 = 63 from rfl, Nat.zero_or]

theorem sStart_base : sStart.base = 206880 := rfl
theorem sStart_allocated : sStart.allocated = 6 := rfl
theorem sStart_primary : sStart.primary = 2 ^ 37 := rfl
theorem sStart_secondary (p : Nat) : sStart.secondary p = if p = 37 then 2 ^ 63 else 0 := rfl
theorem sStart_heads (b : Nat) : sStart.heads b = if b = 2431 then 206880 else 0 := rfl
theorem sStart_hdr : sStart.hdr 206880 = ⟨0, 2 ^ 26, 0, 0⟩ := by
  show (⟨0, sizeWord maxSize false, 0, 0⟩ : Hdr) = _
  rw [maxSize_val]; rfl

/-! ## `allocated` only matters to `SpaceOk` -/

theorem walk_hdr {s t : State} (h : t.hdr = s.hdr) (a l f : Nat) : walk t a l f = walk s a l f := by
  induction f generalizing a with
  | zero => rfl
  | succ f ih => simp only [walk, h, ih]

theorem chunks_allocated (s : State) (a : Nat) : chunks { s with allocated := a } = chunks s := by
  unfold chunks; exact walk_hdr (t := { s with allocated := a }) (s := s) rfl s.base s.top walkFuel

/-- **A larger allocated space keeps the invariant.** -/
theorem wf_allocated {s : State} {a : Nat} (hwf : WF s) (ha : s.allocated ≤ a) :
    WF { s with allocated := a } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwf
  refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_, ?_⟩
  · unfold TilesOk at h4 ⊢; rw [chunks_allocated]; exact h4
  · unfold CoalOk at h5 ⊢; rw [chunks_allocated]; exact h5
  · unfold PrevsOk at h6 ⊢; rw [chunks_allocated]; exact h6.congr (fun _ _ => rfl)
  · unfold ListsOk' at h7 ⊢; rw [chunks_allocated]
    obtain ⟨l1, l2, l3, l4, l5⟩ := h7
    refine ⟨fun b hb => ?_, l2, l3, l4, l5⟩
    obtain ⟨l, e1, e2, e3, e4⟩ := l1 b hb
    exact ⟨l, e1.congr (fun _ _ => rfl), e2.congr (fun _ _ => rfl), e3, e4⟩
  · unfold SpaceOk at h8 ⊢; rw [chunks_allocated]
    intro c hc
    obtain ⟨u1, u2⟩ := h8 c hc
    dsimp only
    exact ⟨fun hu => by have := u1 hu; omega, by omega⟩

theorem sInit_facts : chunks sInit = [⟨206880, maxSize, false⟩] ∧ WF sInit := by
  have hfit : 206880 + 32 * maxSize < 2 ^ 32 := by rw [maxSize_val]; decide
  exact init_wf (grow := fun _ _ => true) (s := zeroState) (by decide) (by decide) hfit rfl
    (fun _ => rfl) (fun _ => rfl) rfl (init_zero rfl)

theorem sStart_chunks : chunks sStart = [⟨206880, maxSize, false⟩] := by
  unfold sStart; rw [chunks_allocated]; exact sInit_facts.1

theorem sStart_chunks' : chunks sStart = [⟨206880, 2 ^ 25, false⟩] := by
  rw [sStart_chunks, maxSize_val]

theorem sStart_wf : WF sStart := wf_allocated sInit_facts.2 (by decide)

theorem sStart_first : FirstOk sStart := rfl

/-! ## `Rep μ sStart` from the memory words -/

/-- **Memory holding the start-up's words holds `sStart`**: the bins' heads (206880 at bin 2431,
    at 206516), the bitmap (2⁶³ in word 37, at 206824; primary 2³⁷ at 206832), the base (206520),
    the allocated space (206840), and the one header at 206880. -/
theorem rep_sStart {μ : Memory}
    (hheads : ∀ b, b < binCount → rdN μ (A0 + 4 * b) 4 = if b = 2431 then 206880 else 0)
    (hsec : ∀ p, p < 38 → rdN μ (A0 + 9736 + 8 * p) 8 = if p = 37 then 2 ^ 63 else 0)
    (hpri : rdN μ 206832 8 = 2 ^ 37) (hbase : rdN μ 206520 8 = 206880) (halloc : rdN μ 206840 4 = 6)
    (h0 : rdN μ 206880 4 = 0) (h1 : rdN μ 206884 4 = 2 ^ 26) (h2 : rdN μ 206888 4 = 0)
    (h3 : rdN μ 206892 4 = 0) : Rep μ sStart := by
  refine ⟨fun b hb => hheads b hb, fun p hp => hsec p hp, hpri, hbase, halloc, ?_, ?_, ?_, ?_⟩ <;>
  · intro c hc
    rw [sStart_chunks, List.mem_singleton] at hc
    subst hc
    simp only [sStart_hdr]
    first | exact h0 | exact h1 | exact fun _ => h2 | exact fun _ => h3

/-! ## One used chunk at the base, then the free rest -/

/-- **The heap is one used chunk of k units at the base, then one free chunk to the end.** -/
def OneUsed (s : State) (k : Nat) : Prop :=
  WF s ∧ FirstOk s ∧ 0 < k ∧ k < maxSize ∧
    chunks s = [⟨s.base, k, true⟩, ⟨s.base + 32 * k, maxSize - k, false⟩]

/-- The chunks after a used first chunk of k < maxSize units, all free, on a well-formed heap: the
    one free chunk to the end. -/
theorem one_of_rest {s : State} {k : Nat} {rest : List Chunk} (hwf : WF s) (hk : k < maxSize)
    (hr : ∀ c ∈ rest, c.used = false) (hcs : chunks s = ⟨s.base, k, true⟩ :: rest) :
    chunks s = [⟨s.base, k, true⟩, ⟨s.base + 32 * k, maxSize - k, false⟩] := by
  have ht := hwf.2.2.2.1
  have hc := hwf.2.2.2.2.1
  unfold TilesOk at ht
  unfold CoalOk at hc
  rw [hcs] at ht hc
  obtain ⟨-, -, ht⟩ := ht
  unfold State.top at ht
  simp only at ht
  match rest, hr, ht, hc with
  | [], _, ht, _ =>
    simp only [Tiles] at ht; omega
  | [c], hr, ht, _ =>
    obtain ⟨e1, -, e3⟩ := ht
    simp only [Tiles] at e3
    have hu := hr c List.mem_cons_self
    rw [hcs]
    cases c; simp only at e1 e3 hu ⊢
    subst e1 hu
    simp only [List.cons.injEq, Chunk.mk.injEq, true_and, and_true]
    omega
  | c :: d :: _, hr, _, hc =>
    obtain ⟨-, hcd, -⟩ := hc
    rw [hr c (by simp), hr d (by simp)] at hcd
    simp at hcd

/-! ## The first allocation -/

/-- **The first allocation from `sStart`** (alignment one unit, r units): the block at 206912, the
    chunk at the base now used with r + 1 units, followed by the free rest if any. -/
theorem alloc_sStart {grow : Grow} {hb r p : Nat} {s' : State}
    (h : alloc grow hb 1 r sStart = some (p, s')) :
    p = 206912 ∧ r + 1 ≤ maxSize ∧
      chunks s' = ⟨206880, r + 1, true⟩ :: remChunk 206880 r maxSize ∧
      WF s' ∧ FirstOk s' ∧ s'.base = 206880 := by
  obtain ⟨pre, post, S, h1, hS, h2⟩ := alloc_chunks sStart_wf h
  rw [sStart_chunks] at h1
  obtain ⟨rfl, hc, rfl⟩ : pre = [] ∧ (⟨p - 32, S, false⟩ : Chunk) = ⟨206880, maxSize, false⟩ ∧ post = [] := by
    cases pre with
    | nil => simp only [List.nil_append, List.cons.injEq] at h1; exact ⟨rfl, h1.1.symm, h1.2.symm⟩
    | cons a l => cases l <;> simp at h1
  simp only [Chunk.mk.injEq, and_true] at hc
  obtain ⟨hp, rfl⟩ := hc
  have hw := alloc_wf sStart_wf h
  have hp' : p = 206912 := by
    have : 206880 ≤ p - 32 := by omega
    omega
  have hbase : s'.base = 206880 := by
    have ht := hw.2.2.2.1
    unfold TilesOk at ht
    rw [h2] at ht
    exact ht.1.symm.trans (by rw [hp])
  refine ⟨hp', hS, ?_, hw, alloc_first sStart_wf sStart_first h, hbase⟩
  rw [h2, hp, List.nil_append, List.append_nil]

/-- The first allocation of r units, r + 1 < maxSize: `OneUsed` with r + 1 units at 206880. -/
theorem alloc_sStart_one {grow : Grow} {hb r p : Nat} {s' : State} (hr : r + 1 < maxSize)
    (h : alloc grow hb 1 r sStart = some (p, s')) :
    p = 206912 ∧ s'.base = 206880 ∧ OneUsed s' (r + 1) ∧
      chunks s' = [⟨206880, r + 1, true⟩, ⟨206880 + 32 * (r + 1), maxSize - (r + 1), false⟩] := by
  obtain ⟨hp, -, hc, hw, hf, hb'⟩ := alloc_sStart h
  have hc' : chunks s' = [⟨206880, r + 1, true⟩, ⟨206880 + 32 * (r + 1), maxSize - (r + 1), false⟩] := by
    rw [hc]; unfold remChunk
    rw [if_neg (by omega)]
    simp only [List.cons.injEq, Chunk.mk.injEq, true_and, and_true]
    omega
  refine ⟨hp, hb', ⟨hw, hf, by omega, hr, by rw [hb']; exact hc'⟩, hc'⟩

/-! ## In-place growth -/

/-- The environment's growth is monotone in the end: covering more also covers less. -/
def GrowMono (grow : Grow) : Prop := ∀ b e e', e ≤ e' → grow b e' = true → grow b e = true

theorem growTo_mono (pb : Nat) : GrowMono (growTo pb) := by
  intro b e e' he h
  unfold growTo at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  have : pagesOf (b + 32 * e) ≤ pagesOf (b + 32 * e') := by
    unfold pagesOf; split <;> split <;> omega
  omega

theorem freeFinal_size_other {s : State} {z M pv total T : Nat} (hM : z < M) :
    ((freeFinal s M pv total T).hdr z).size = (s.hdr z).size := by
  unfold freeFinal
  split
  · rw [setHdr_prev_size]; exact (register_hdr_other (by omega)).2.1
  · exact (register_hdr_other (by omega)).2.1

/-- A `growInplace` that grows sets the chunk's size word. -/
theorem growInplace_hdr {grow : Grow} {s s' : State} {ptr newReq : Nat}
    (hlt : wordSize (s.hdr (ptr - 32)).size < newReq + 1) (h : growInplace grow s ptr newReq = some s') :
    (s'.hdr (ptr - 32)).size = sizeWord (newReq + 1) true := by
  unfold growInplace at h
  generalize ptr - 32 = X at *
  simp only at h
  split at h
  · rename_i hge; exact absurd hge (by omega)
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  generalize hE : (X + 32 * (newReq + 1) - s.base) / 32 + _ = E at h
  obtain ⟨sa, rfl⟩ : ∃ sa : State,
      s' = freeFinal (setHdr (unregister sa (X + 32 * wordSize (s.hdr X).size)
        (binDown (wordSize (s.hdr (X + 32 * wordSize (s.hdr X).size)).size))) X
        (fun h => { h with size := sizeWord (newReq + 1) true })) (X + 32 * (newReq + 1)) (newReq + 1)
        (wordSize (s.hdr X).size + wordSize (s.hdr (X + 32 * wordSize (s.hdr X).size)).size - (newReq + 1))
        (s.base + 32 * maxSize) := by
    by_cases hlt : s.allocated < E
    · by_cases hg : grow s.base E = true
      · simp only [hlt, hg, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        exact ⟨{ s with allocated := E }, h.symm⟩
      · simp [hlt, hg] at h
    · simp only [hlt, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      exact ⟨s, h.symm⟩
  rw [freeFinal_size_other (by omega), setHdr_self]

/-- `alloc1` grows the space when it must: its bin, and `grow` holding at its end if that is
    beyond the allocated space. -/
theorem alloc1_grow {grow : Grow} {r p : Nat} {s s' : State} (h : alloc1 grow r s = some (p, s')) :
    ∃ bin, ((findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1)))) = some bin ∧
      r + 1 ≤ maxSize ∧
      (s.allocated < (s.heads bin - s.base) / 32 + 1 + r +
          (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) →
        grow s.base ((s.heads bin - s.base) / 32 + 1 + r +
          (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1)) = true) := by
  unfold alloc1 at h
  split at h
  · simp at h
  rename_i hmax
  simp only [Option.orElse_eq_or] at h
  cases hfb : (findFirst s (binUp (r + 1))).or (findFirst s (binDown (r + 1))) with
  | none => simp [hfb] at h
  | some bin =>
    simp only [hfb, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · simp at h
    refine ⟨bin, rfl, by omega, fun hlt => ?_⟩
    generalize hE : (s.heads bin - s.base) / 32 + 1 + r +
      (if wordSize (s.hdr (s.heads bin)).size - r - 1 = 0 then 0 else 1) = E at h hlt ⊢
    by_cases hg : grow s.base E = true
    · exact hg
    · simp [hlt, hg] at h

/-- The size words of a `OneUsed` heap's two chunks. -/
theorem OneUsed.hdrs {s : State} {k : Nat} (hs : OneUsed s k) :
    (s.hdr s.base).size = sizeWord k true ∧
      (s.hdr (s.base + 32 * k)).size = sizeWord (maxSize - k) false := by
  have hc := hs.2.2.2.2
  exact ⟨chunks_hdr ⟨s.base, k, true⟩ (by rw [hc]; simp), chunks_hdr ⟨s.base + 32 * k, maxSize - k, false⟩ (by rw [hc]; simp)⟩

/-- **`growInplace` succeeds on a `OneUsed` heap** for a larger request below `maxSize`, when the
    environment can cover newReq + 2 units (the grown chunk and the rest's header). -/
theorem growInplace_one_some {grow : Grow} {s : State} {k newReq : Nat} (hs : OneUsed s k)
    (hk : k ≤ newReq) (hn : newReq + 1 < maxSize)
    (hg : s.allocated < newReq + 2 → grow s.base (newReq + 2) = true) :
    ∃ s', growInplace grow s (s.base + 32) newReq = some s' := by
  obtain ⟨h1, h2⟩ := hs.hdrs
  have hk' := hs.2.2.2.1
  unfold growInplace
  simp only [show s.base + 32 - 32 = s.base by omega, h1, h2, wordSize_sizeWord, wordUsed_sizeWord]
  have e1 : ¬ (k ≥ newReq + 1) := by omega
  have e2 : ¬ (s.base + 32 * k ≥ s.base + 32 * maxSize) := by omega
  have e3 : ¬ (k + (maxSize - k) < newReq + 1) := by omega
  have e4 : (s.base + 32 * (newReq + 1) - s.base) / 32 +
      (if k + (maxSize - k) - (newReq + 1) = 0 then 0 else 1) = newReq + 2 := by
    rw [if_neg (by omega)]; omega
  simp only [e1, e2, e3, e4, ↓reduceIte, Bool.false_eq_true]
  by_cases hlt : s.allocated < newReq + 2
  · simp [hlt, hg hlt]
  · simp [hlt]

/-- **In-place growth keeps `OneUsed`**: on a heap of one used chunk of k units at the base and
    the free rest, `realloc` of its block to newReq ≥ k − 1 units (newReq + 1 < maxSize, alignment
    one unit, the environment's growth monotone) returns the same block, copies nothing, and
    leaves one used chunk of newReq + 1 units at the base and the free rest. -/
theorem realloc_one {grow : Grow} {hb : Nat} {s s' : State} {k newReq p : Nat} {cp : Bool}
    (hs : OneUsed s k) (hk : k ≤ newReq + 1) (hn : newReq + 1 < maxSize) (hmono : GrowMono grow)
    (h : realloc grow hb s (s.base + 32) 1 newReq = some (p, s', cp)) :
    p = s.base + 32 ∧ cp = false ∧ s'.base = s.base ∧ OneUsed s' (newReq + 1) ∧
      chunks s' = [⟨s.base, newReq + 1, true⟩,
        ⟨s.base + 32 * (newReq + 1), maxSize - (newReq + 1), false⟩] := by
  obtain ⟨hwf, hfo, hk0, hkm, hcs⟩ := hs
  have hs : OneUsed s k := ⟨hwf, hfo, hk0, hkm, hcs⟩
  obtain ⟨h1, -⟩ := hs.hdrs
  have hX : s.base + 32 - 32 = s.base := by omega
  unfold realloc usable at h
  rw [hX, h1, wordSize_sizeWord] at h
  by_cases e1 : newReq = k - 1
  · simp only [e1, ↓reduceIte, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hk1 : newReq + 1 = k := by omega
    rw [hk1]
    exact ⟨rfl, rfl, rfl, hs, hcs⟩
  have e2 : newReq ≠ 0 := by omega
  have e3 : ¬ newReq < k - 1 := by omega
  simp only [e1, e2, e3, ↓reduceIte] at h
  have hkn : k ≤ newReq := by omega
  cases hg : growInplace grow s (s.base + 32) newReq with
  | some s2 =>
    simp only [hg, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hcs' : chunks s = [] ++ ⟨s.base + 32 - 32, k, true⟩ ::
        [⟨s.base + 32 * k, maxSize - k, false⟩] := by rw [hX, hcs]; rfl
    obtain ⟨hw2, hor⟩ := growInplace_ok hwf hcs' hg
    have hf2 := growInplace_first hfo (by omega) hg
    rcases hor with rfl | ⟨e, post', rest, hpost, -, hrest, hch⟩
    · have := growInplace_hdr (by rw [hX, h1, wordSize_sizeWord]; omega) hg
      rw [hX, h1] at this
      have := congrArg wordSize this
      rw [wordSize_sizeWord, wordSize_sizeWord] at this
      omega
    · simp only [List.cons.injEq] at hpost
      obtain ⟨-, rfl⟩ := hpost
      rw [hX, List.nil_append, List.append_nil] at hch
      have hb2 : s2.base = s.base := by
        have ht := hw2.2.2.2.1
        unfold TilesOk at ht
        rw [hch] at ht
        exact ht.1.symm
      rw [← hb2] at hch
      have hone := one_of_rest hw2 hn hrest hch
      rw [hb2] at hone
      refine ⟨rfl, rfl, hb2, ⟨hw2, hf2, by omega, hn, ?_⟩, hone⟩
      rw [hb2]; exact hone
  | none =>
    exfalso
    simp only [hg] at h
    cases ha : alloc grow hb 1 newReq s with
    | none => simp [ha] at h
    | some r =>
      obtain ⟨p1, s1⟩ := r
      rw [alloc_one hwf.1] at ha
      obtain ⟨bin, hbin, hmax, hgE⟩ := alloc1_grow ha
      obtain ⟨-, -, -, -, ⟨pre, post, hcb⟩, -, -⟩ := bin_chunk hwf hmax hbin
      rw [hcs] at hcb
      have hC : s.heads bin = s.base + 32 * k := by
        match pre, hcb with
        | [], hcb => simp at hcb
        | [x], hcb =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq, Chunk.mk.injEq] at hcb
          exact hcb.2.1.1.symm
        | x :: y :: z, hcb => simp at hcb
      obtain ⟨s2, hs2⟩ := growInplace_one_some hs hkn hn (fun hlt => by
        rw [hC] at hgE
        refine hmono _ _ _ ?_ (hgE ?_) <;>
        · have : (s.base + 32 * k - s.base) / 32 = k := by omega
          rw [this]; split <;> omega)
      rw [hs2] at hg
      simp at hg

/-- **`realloc` grows a `OneUsed` block in place** when the environment can cover newReq + 2
    units: it returns the same block, with nothing to copy (and then `realloc_one` gives the
    state's shape). -/
theorem realloc_one_some {grow : Grow} {hb : Nat} {s : State} {k newReq : Nat} (hs : OneUsed s k)
    (hk : k ≤ newReq) (hn : newReq + 1 < maxSize)
    (hg : s.allocated < newReq + 2 → grow s.base (newReq + 2) = true) :
    ∃ s', realloc grow hb s (s.base + 32) 1 newReq = some (s.base + 32, s', false) := by
  obtain ⟨s2, hs2⟩ := growInplace_one_some hs hk hn hg
  obtain ⟨h1, -⟩ := hs.hdrs
  refine ⟨s2, ?_⟩
  unfold realloc usable
  have hk0 := hs.2.2.1
  rw [show s.base + 32 - 32 = s.base by omega, h1, wordSize_sizeWord]
  have e1 : ¬ newReq = k - 1 := by omega
  have e2 : ¬ newReq = 0 := by omega
  have e3 : ¬ newReq < k - 1 := by omega
  simp only [e1, e2, e3, ↓reduceIte, hs2, Option.pure_def]

end Services.Bootstrap.Alloc.AfterStart
