import Services.Bootstrap.Fmt.Sink
import Services.Bootstrap.Alloc.Dealloc
import Services.Bootstrap.Alloc.ReallocFallbackTail
import Services.Bootstrap.Decode.ReallocOk

/-!
# `dealloc` (40613) from the allocator's context, frame-only

`dealloc_ctx`: from `HeapCtx` with ω₇ the data address of an allocated chunk c, `dealloc` reaches its
return (40697) with the context kept for `free s ptr` (same base), every other allocated chunk of s
still allocated with its data, `Outside` (the stack from sp up, the globals, the pages and the
read-only octets), and ω₀, ω₁, ω₅, ω₆ restored. It makes no host call, so it holds under any host
relation: the run is built under the empty relation (`keep_nohost` then gives the pages and the
read-only octets) and widened (`FreeStepsH.weaken`).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.ReallocOk

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The empty host relation: a run under it makes no host call. -/
def NoHost (X : Type) : HostRel X := fun _ _ _ _ _ _ _ _ => False

/-- **A run with no host call keeps the pages and every octet that is not writable.** -/
theorem keep_nohost {X : Type} {p : ByteArray} {i i' n : Nat} {ω ω' : Regs} {μ μ' : Memory} {x x' : X}
    (run : FreeStepsH p (NoHost X) i ω μ x i' ω' μ' x' n) :
    μ'.pages = μ.pages ∧ ∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b := by
  induction run with
  | refl => exact ⟨rfl, fun _ _ _ => rfl⟩
  | pad _ ih => exact ih
  | next hn _ _ ih =>
    obtain ⟨P, -, hs⟩ := hn
    obtain ⟨hp, hk⟩ := P.freeStep_keep hs
    refine ⟨by rw [ih.1, hp], fun b hb hw => ?_⟩
    have hw2 : _ := hw
    unfold Memory.writable at hw2
    rw [ih.2 b hb (by unfold Memory.writable; rw [hp]; exact hw2), hk b hb hw]
  | host _ _ _ hR _ _ => exact absurd hR id

/-- `dealloc_refines` with the heap frame: the octets off the headers of s, and the globals, kept. -/
theorem dealloc_refines_hdr {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P]
    (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (hsp : 2147483716 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hHT : s.base + 32 * s.allocated ≤ HT)
    (hS : S0 + 40 ≤ sp ∧ sp ≤ S1) (hw : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x 40697 ω' μ' x 248 ∧ Rep μ' (free s ptr) ∧ WF (free s ptr) ∧
      FirstOk (free s ptr) ∧ rdN μ' 206848 1 = 0 ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      HKeepG μ μ' (fun a => ∃ c ∈ chunks s, c.addr = a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hc' := hc
  obtain ⟨c, hcm, hca, -⟩ := hc'
  have hcl : s.base ≤ c.addr ∧ c.addr + 32 * c.size ≤ s.top ∧ 0 < c.size := by
    have ht := hwf.2.2.2.1
    unfold TilesOk at ht
    exact ht.mem_lt c hcm
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  obtain ⟨ω1, μ1, r1, a1, a8, a7, a0, a5, a4, st8, st16, fr1, ww1, g1⟩ :=
    dl_lock (p := p) (P := P) (R := R) x ω μ sp ptr h1 h7 (by omega) (by omega) hsp hsp1 hl (by omega)
      ⟨by omega, by omega⟩ hw
  have rep1 : Rep μ1 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inr (by unfold A0 at ha1; omega)) ha3
  obtain ⟨ω2, μ2, r2, rep2, wf2, fo2, ww2, stk2, b0, b1, b5, b6, hk2⟩ :=
    free_refines_hdr (p := p) (P := P) (R := R) x ω1 μ1 s (sp - 16) ptr hwf rep1 hc a1 a8 a7 (by omega)
      (by omega) hb0 hbT hfo hHT ⟨by omega, by omega⟩ (hw.of_eq ww1)
  have rj := free_ret_dealloc (p := p) (P := P) (R := R) x ω2 μ2 (by rw [b0, a0])
  obtain ⟨ω3, μ3, r3, c0, c5, c1, cl, fr3, ww3, g3⟩ :=
    dl_unlock (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) b1 (by rw [b5, a5]) (by omega) (by omega) (by omega)
      ⟨by omega, by omega⟩ ((hw.of_eq ww1).of_eq ww2)
  have hb' : (free s ptr).base = s.base := free_base'
  have hk1 : HKeepG μ μ1 (fun a => ∃ c ∈ chunks s, c.addr = a) := fun a ha => by
    obtain ⟨ha1, ha2, -⟩ := ha
    unfold Glob at ha1
    exact fr1 a (by omega) (Or.inl (by omega)) (by omega) (by omega)
  have hk3 : HKeepG μ2 μ3 (fun a => ∃ c ∈ chunks s, c.addr = a) := fun a ha => by
    obtain ⟨ha1, ha2, -⟩ := ha
    unfold Glob at ha1
    exact fr3 a (by omega) (by omega)
  refine ⟨ω3, μ3, (((r1.trans r2).trans rj).trans r3).mono (by omega),
    rep2.congr_lock wf2 (by rw [hb']; exact hb0) (by rw [hb']; exact hbT)
      (fun a ha1 ha2 ha3 => fr3 a (by omega) (by omega)), wf2, fo2, cl,
    fun a => (ww3 a).trans ((ww2 a).trans (ww1 a)),
    fun a ha1 ha2 => ((fr3 a ha1 (by omega)).trans (stk2 a ha1 (by omega))).trans
      (fr1 a ha1 (Or.inr ha2) (Or.inr (by omega)) (Or.inr (by omega))),
    (hk1.trans hk2).trans hk3, ?_, ?_, ?_, ?_⟩
  · rw [c0, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega), show sp - 16 + 8 = sp - 8 by omega]
    unfold rdN; rw [st8, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [c1, h1]; congr 1; omega
  · rw [c5, rdN_frame (μ := μ1) fun j hj => stk2 _ (by omega) (by omega)]
    unfold rdN; rw [st16, Num.decodeLE_encodeLE]
    rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat]
  · rw [fget g3 6 (by decide) (by decide), b6, fget g1 6 (by decide) (by decide)]

/-- Every allocated chunk of s other than the freed one c is a chunk of `free s ptr`. -/
theorem free_keeps_used {s : State} {c d : Chunk} {ptr : Nat} (hwf : WF s) (hc : c ∈ chunks s)
    (hca : c.addr + 32 = ptr) (hcu : c.used = true) (hd : d ∈ chunks s) (hdu : d.used = true) (hdc : d ≠ c) :
    d ∈ chunks (free s ptr) := by
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hc
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  obtain ⟨pre0, L, R, post0, M, total, hpre, hpost, hfree, hch, -, -⟩ := free_ok hwf hcs
  rw [hch]
  rw [hcs, hpre, hpost] at hd
  simp only [List.mem_append, List.mem_cons] at hd ⊢
  rcases hd with (h | h) | h | h | h
  · exact Or.inl h
  · exact absurd hdu (by rw [hfree d (List.mem_append_left _ h)]; decide)
  · exact absurd (h.trans hceq.symm) hdc
  · exact absurd hdu (by rw [hfree d (List.mem_append_right _ h)]; decide)
  · exact Or.inr (Or.inr h)

/-- **`dealloc` from the allocator's context, frame-only** (40613 … its return at 40697), under any
    host relation: the context kept for `free s ptr`, the same base, `Outside` from sp up, every
    other allocated chunk of s still allocated with its data, ω₀, ω₁, ω₅, ω₆ restored. -/
theorem dealloc_ctx {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P]
    (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr : Nat)
    (c : Chunk) (H : HeapCtx env pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true)
    (hca : c.addr + 32 = ptr) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat ptr)
    (hsp : 2147483716 ≤ sp) (hS : S0 + 40 ≤ sp ∧ sp ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x 40697 ω' μ' x 248 ∧ HeapCtx env pb S0 S1 μ' (free s ptr) ∧
      (free s ptr).base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks (free s ptr) ∧
        ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp1 : sp < 4294967296 := by have := H.hS1; omega
  obtain ⟨ω', μ', run, rep', wf', fo', lk, ww, stk, hk, e0, e1, e5, e6⟩ :=
    dealloc_refines_hdr (R := NoHost X) (p := p) (P := P) (HT := 4096 * ph) (S0 := S0) (S1 := S1) x ω μ s sp ptr
      H.wf H.rep ⟨c, hc, hca, hcu⟩ h1 h7 hsp hsp1 H.hb0 H.hbT H.fo H.lock hHT hS (HeapPages.wrAt hp hhb H.st)
  obtain ⟨hpg, hro⟩ := keep_nohost run
  have hb' : (free s ptr).base = s.base := free_base'
  have hal : (free s ptr).allocated = s.allocated := free_allocated
  have hG : ∀ b, (fun a => ∃ c ∈ chunks s, c.addr = a) b → b + 16 ≤ 196616 ∨ 196792 ≤ b := by
    rintro b ⟨d, hd, rfl⟩
    have := chunk_bounds H.wf hd
    have := H.hb0
    right; omega
  refine ⟨ω', μ', run.weaken (fun _ _ _ _ _ _ _ h => absurd h id),
    ⟨wf', rep', fo', lk, by rw [hb']; exact H.hb0, by rw [hb']; exact H.hbT, by rw [hal]; exact H.hA, H.bd,
      ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', hal]; exact hHT⟩, H.hSb, H.hS1,
      fun a h1 h2 => by rw [ww]; exact H.st a h1 h2, fun a ha => by rw [ww]; exact H.ro a ha⟩,
    hb', ⟨fun b _ => ⟨by unfold Memory.readable; rw [hpg], by unfold Memory.writable; rw [hpg]⟩,
      fun b hb _ hw => hro b hb hw, fun a ha hb _ => stk a hb ha, HKeepG.glob hk hG⟩,
    fun d hd hdu hdc => ⟨free_keeps_used H.wf hc hca hcu hd hdu hdc, fun a ha => ?_⟩, e0, e1, e5, e6⟩
  unfold InData at ha
  exact hk.hkeep a (off_hdr_data H.wf H.hb0 H.hbT hd ha.1 ha.2)

end Services.Bootstrap.Fmt
