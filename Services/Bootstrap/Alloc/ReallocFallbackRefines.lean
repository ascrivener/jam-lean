import Services.Bootstrap.Alloc.ReallocFallbackPre
import Services.Bootstrap.Alloc.ReallocFallbackTail
import Services.Bootstrap.Alloc.ReallocGrowRefines

/-!
# The binary's `realloc_impl` refines the model's `realloc`: the fallback

When the chunk cannot grow in place (its next chunk past the heap's end, used, or too small), the
model's `realloc` allocates a new block, and the old chunk is freed (`copy` true); the binary does
the same (`fallback_pre`, `fallback_tail`).
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- `growInplace` fails when the next chunk lies past the heap's end, is used, or with it the chunk
    is still too small. -/
theorem growInplace_none_of {grow : Grow} {s : State} {ptr req cur : Nat}
    (hsz : wordSize (s.hdr (ptr - 32)).size = cur) (hlt : cur < req + 1)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨ wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = true ∨
      cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size < req + 1) :
    growInplace grow s ptr req = none := by
  unfold growInplace
  simp only [hsz, maxSize_val, Nat.reduceMul]
  rw [if_neg (by omega)]
  by_cases h1 : ptr - 32 + 32 * cur ≥ s.base + 1073741824
  · rw [if_pos h1]; rfl
  rw [if_neg h1]
  by_cases h2 : wordUsed (s.hdr (ptr - 32 + 32 * cur)).size = true
  · rw [if_pos h2]; rfl
  rw [if_neg h2]
  have h3 : cur + wordSize (s.hdr (ptr - 32 + 32 * cur)).size < req + 1 := by
    rcases hcase with h | h | h
    · omega
    · exact absurd h h2
    · exact h
  rw [if_pos h3]; rfl

/-- The model's `realloc` above the usable size, when `growInplace` fails and `alloc` gives q. -/
theorem realloc_fallback {grow : Grow} {hb : Nat} {s s1 : State} {ptr align req q : Nat}
    (hr : usable s ptr < req) (h : growInplace grow s ptr req = none)
    (ha : alloc grow hb align req s = some (q, s1)) :
    realloc grow hb s ptr align req = some (q, free s1 ptr, true) := by
  unfold realloc
  have e1 : req ≠ usable s ptr := by omega
  have e2 : req ≠ 0 := by omega
  have e3 : ¬ req < usable s ptr := by omega
  simp [e1, e2, e3, h, ha]

/-- **The binary's `realloc_impl` refines the model's `realloc`, through the fallback**: from memory
    holding a well-formed `s` (its first chunk's `prev` 0), ω₈ = ptr the data address of an allocated
    chunk with u ≥ 1 usable units, ω₉ = 1 (the alignment, one unit) and ω₁₀ = req > u, when the
    chunk's next chunk lies past the heap's end, is used, or with it the chunk is still too small,
    and the model's `alloc` at one unit gives q and s₁ without growing the heap: the model's
    `realloc` gives `(q, free s₁ ptr, true)`, and `realloc_impl` (42980) allocates q, copies the old
    usable size there, frees ptr and returns q into `realloc` (40805), with memory holding
    `free s₁ ptr` (well-formed, its first chunk's `prev` 0), the caller's ω₀, ω₁, ω₅, ω₆ restored and
    the stack from sp up untouched. -/
theorem fallback_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    {grow : Grow} {hb : Nat} (s s1 : State) (sp ptr req q : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true) (hu1 : 1 ≤ usable s ptr)
    (hr : usable s ptr < req) (hr1 : req < 33554431)
    (hcase : s.base + 1073741824 ≤ ptr - 32 + 32 * (usable s ptr + 1) ∨
      wordUsed (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size = true ∨
      usable s ptr + 1 + wordSize (s.hdr (ptr - 32 + 32 * (usable s ptr + 1))).size < req + 1)
    (ha : alloc grow hb 1 req s = some (q, s1)) (hng : s1.allocated = s.allocated)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h9 : ω[9] = UInt64.ofNat 1) (h10 : ω[10] = UInt64.ofNat req) (h0 : ω[0] = UInt64.ofNat 1988)
    (hsp : 2147483952 ≤ sp) (hsp1 : sp < 4294967296) (hsp8 : sp % 8 = 0) (hba : s.base % 8 = 0)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) {HT S0 S1 : Nat} (hHTs : 208896 ≤ HT) (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 304 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    realloc grow hb s ptr 1 req = some (q, free s1 ptr, true) ∧
      ∃ ω' μ', FreeStepsH p R 42980 ω μ x 40805 ω' μ' x (64 * usable s ptr + 1070) ∧
        Rep μ' (free s1 ptr) ∧ WF (free s1 ptr) ∧ FirstOk (free s1 ptr) ∧
        (∀ a, μ'.writable a = μ.writable a) ∧ (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
        ω'[7] = UInt64.ofNat q ∧ ω'[0] = UInt64.ofNat 1988 ∧ ω'[1] = UInt64.ofNat sp ∧
        ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, hcu⟩ := hc'
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = cur at hcs
  have hXmem : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ chunks s := by
    rw [hcs]; exact List.mem_append_right _ List.mem_cons_self
  have hXs : (s.hdr (ptr - 32)).size = sizeWord cur true := by
    have := chunks_hdr _ hXmem; simp only at this; exact this
  have hcur : wordSize (s.hdr (ptr - 32)).size = cur := by rw [hXs, wordSize_sizeWord]
  have husable : usable s ptr = cur - 1 := by unfold usable; rw [hcur]
  have hc1 : 1 ≤ cur := by omega
  rw [husable, show cur - 1 + 1 = cur by omega] at hcase
  have hlt : cur < req + 1 := by omega
  refine ⟨realloc_fallback hr (growInplace_none_of hcur hlt hcase) ha, ?_⟩
  have hwf' := hwf
  obtain ⟨-, -, -, htiles, -, -, -, hspace⟩ := hwf'
  unfold TilesOk at htiles
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles henc
  rw [htop] at htiles
  -- the header addresses
  generalize hH : HA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨ptr - 32, cur, true⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := fun a h => by
    rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have unHF : ∀ a, H a ∨ F a → ∃ c ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post, c.addr = a := by
    rintro a (h | h)
    · exact unH a h
    · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ := unHF a h
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hcs' : chunks s = pre ++ ⟨ptr - 32, cur, true⟩ :: post := hcs
  have hHFT : ∀ a, H a ∨ F a → a + 32 ≤ HT := by
    intro a ha
    obtain ⟨c, hc, rfl⟩ := unHF a ha
    unfold SpaceOk at hspace; have := (hspace c (hcs' ▸ hc)).2; omega
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs' ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs' ▸ hc) hu⟩
  have hXm : (⟨ptr - 32, cur, true⟩ : Chunk) ∈ pre ++ ⟨ptr - 32, cur, true⟩ :: post :=
    List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  simp only at hXl
  obtain ⟨-, hph, -, -⟩ := Tiles.around htiles
  -- the next chunk, when below the heap's end, is a chunk
  have hnc : ptr - 32 + 32 * cur < s.base + 1073741824 → H (ptr - 32 + 32 * cur) := by
    intro hlt'
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      rw [show ptr - 32 + 32 * cur = e.addr from (hph e (by rw [hp]; rfl)).symm]
      exact mkH e (List.mem_append_right _ (List.mem_cons_of_mem _ (by rw [hp]; simp)))
  have hcase' : s.base + 1073741824 ≤ ptr - 32 + 32 * cur ∨
      (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
        (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1) ∨
      (ptr - 32 + 32 * cur < s.base + 1073741824 ∧ H (ptr - 32 + 32 * cur) ∧
        (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 0 ∧ cur + (s.hdr (ptr - 32 + 32 * cur)).size / 2 < req + 1) := by
    by_cases hin : s.base + 1073741824 ≤ ptr - 32 + 32 * cur
    · exact Or.inl hin
    · have hH' := hnc (by omega)
      by_cases hodd : (s.hdr (ptr - 32 + 32 * cur)).size % 2 = 1
      · exact Or.inr (Or.inl ⟨by omega, hH', hodd⟩)
      · refine Or.inr (Or.inr ⟨by omega, hH', by omega, ?_⟩)
        rcases hcase with h | h | h
        · omega
        · exfalso; unfold wordUsed at h; simp at h; omega
        · unfold wordSize at h; exact h
  obtain ⟨ω1, μ1, r1, -, ww1, fr1, st0, st5, st6, a1, a6, a7, a8, a9, a10⟩ := fallback_pre (p := p) (P := P)
    (R := R) x ω μ s H F sp ptr req cur hrep' h1 h8 h7 h10 (by omega) hsp1 hb0 hbT (hHF _ (Or.inl (mkH _ hXm)))
    (by omega) (mkH _ hXm) hHF (by rw [hXs]; unfold sizeWord; simp) hlt (by omega) hc1 (by omega) hcase'
    hHFT ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => fr1 a (by omega) (Or.inl (by omega))
  have rd : ∀ a v, μ1.readN a 8 = Num.encodeLE 8 v → v < 18446744073709551616 → rdN μ1 a 8 = v :=
    fun a v h hv => rd_enc h hv
  obtain ⟨ω2, μ2, r2, rep2, wf2, fo2, ww2, stk2, e7, e0, e1, e5, e6⟩ := fallback_tail (p := p) (P := P) (R := R)
    x ω1 μ1 (grow := grow) (hb := hb) s s1 (sp - 152) ptr req q (cur - 1) ω[5].toNat ω[6].toNat hwf rep1 hfo hc
    husable (by omega) (by omega) ha hng a1 a7 a8 (by rw [a9]; exact h9) a10 a6 (by omega)
    (by rw [show sp - 152 + 144 = sp - 8 by omega]; exact (rd _ _ st0 (UInt64.toNat_lt _)).trans (by rw [h0]; rfl))
    (by rw [show sp - 152 + 136 = sp - 16 by omega]; exact rd _ _ st5 (UInt64.toNat_lt _))
    (by rw [show sp - 152 + 128 = sp - 24 by omega]; exact rd _ _ st6 (UInt64.toNat_lt _))
    (by omega) (by omega) (by omega) hba hb0 hbT hA hHTs hHT ⟨by omega, by omega⟩ (hw.of_eq ww1)
  refine ⟨ω2, μ2, (r1.trans r2).mono (by rw [husable]; omega), rep2, wf2, fo2,
    fun a => (ww2 a).trans (ww1 a), fun a h1 h2 => (stk2 a h1 (by omega)).trans (fr1 a h1 (Or.inr h2)), e7, e0,
    by rw [e1]; congr 1; omega, by rw [e5, UInt64.ofNat_toNat], by rw [e6, UInt64.ofNat_toNat]⟩

end Services.Bootstrap.Alloc
