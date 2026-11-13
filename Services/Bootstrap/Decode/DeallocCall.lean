import Services.Bootstrap.Alloc.Dealloc
import Services.Bootstrap.Alloc.ReallocFallbackTail
import Services.Bootstrap.Decode.HeapCtx
import Services.Bootstrap.Decode.ReallocOk
import Services.Bootstrap.Decode.LoopA

/-!
# One call of `dealloc` (40613), from the allocator's context

`dealloc_callG`: from `HeapCtxC` with ω₇ the data address of an allocated chunk c and a return address
ω₀ that `djump` resolves to t, `dealloc` (GP Appendix B's heap, picoalloc's `free`) returns to t
with:
- the context kept for `free s ptr`, with the same base;
- the pages, every octet that is not writable, the stack from sp up and the globals below the
  allocator kept;
- every other allocated chunk of s still allocated, with its data;
- ω₀, ω₁, ω₅, ω₆ restored.

`dealloc` makes no host call, so this holds under **any** host relation: the run is built under the
empty relation `NoHost` (`keep_nohost` then gives the pages and the octets that are not writable)
and widened with `FreeStepsH.weaken`. `dealloc_call` is the refine form (`HeapCtx env`).
-/

namespace Services.Bootstrap.Decode.DeallocCall

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

/-- `dealloc`'s return (40697) to t, the address ω₀ resolves to. -/
theorem dl_ret {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) : FreeStepsH p R 40697 ω μ x t ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0, hret, hjt, hbt]

/-- **One call of `dealloc` (40613) from the allocator's context, under any host relation**: with
    ω₇ = ptr the data address of an allocated chunk c of s and a return address ω₀ that `djump`
    resolves to t, the call returns to t with the context kept for `free s ptr` (same base), the
    pages, the octets that are not writable, the stack from sp up and the globals kept, every other
    allocated chunk of s still allocated with its data, and ω₀, ω₁, ω₅, ω₆ restored. -/
theorem dealloc_callG {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr ret t : Nat)
    (c : Chunk) (H : HeapCtxC code pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true)
    (hca : c.addr + 32 = ptr) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat ptr)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : 2147483716 ≤ sp) (hS : S0 + 40 ≤ sp ∧ sp ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 249 ∧ HeapCtxC code pb S0 S1 μ' (free s ptr) ∧
      (free s ptr).base = s.base ∧ μ'.pages = μ.pages ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧ (∀ a, Glob a → μ'.read a = μ.read a) ∧
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
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hG : ∀ b, (fun a => ∃ c ∈ chunks s, c.addr = a) b → b + 16 ≤ 196616 ∨ 196792 ≤ b := by
    rintro b ⟨d, hd, rfl⟩
    have := ht.mem_lt d hd
    have := H.hb0
    right; omega
  refine ⟨ω', μ', (run.weaken (fun _ _ _ _ _ _ _ h => absurd h id)).trans
      (dl_ret (R := R) (p := p) (P := P) x ω' μ' ret t (e0.trans h0) hret hjt hbt),
    ⟨wf', rep', fo', lk, by rw [hb']; exact H.hb0, by rw [hb']; exact H.hbT, by rw [hal]; exact H.hA, H.bd,
      ⟨ph, h48, hhb, HeapPages.of_eq hp ww, hHTs, by rw [hb', hal]; exact hHT⟩, H.hSb, H.hS1,
      fun a h1 h2 => by rw [ww]; exact H.st a h1 h2, fun a ha => by rw [ww]; exact H.ro a ha⟩,
    hb', hpg, hro, fun a ha hb => stk a ha hb, HKeepG.glob hk hG,
    fun d hd hdu hdc => ⟨free_keeps_used H.wf hc hca hcu hd hdu hdc, fun a ha => ?_⟩, e0, e1, e5, e6⟩
  unfold InData at ha
  exact hk.hkeep a (off_hdr_data H.wf H.hb0 H.hbT hd ha.1 ha.2)

/-- `dealloc_callG` for the refine host's context (`HeapCtx env`). -/
theorem dealloc_call {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P]
    (env : RefineHost.Env) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr ret t : Nat)
    (c : Chunk) (H : HeapCtx env pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true)
    (hca : c.addr + 32 = ptr) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat ptr)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : 2147483716 ≤ sp) (hS : S0 + 40 ≤ sp ∧ sp ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 249 ∧ HeapCtx env pb S0 S1 μ' (free s ptr) ∧
      (free s ptr).base = s.base ∧ μ'.pages = μ.pages ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧ (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks (free s ptr) ∧
        ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  dealloc_callG (R := R) (p := p) (P := P) env.code pb S0 S1 x ω μ s sp ptr ret t c H hc hcu hca h0 h1 h7
    hret hjt hbt hsp hS

/-! ## The free path (42327) with the lock held -/

/-- **The allocator's context with the lock held**: μ is a memory holding the context (`HeapCtxC`)
    but for the wrapper's lock word at 196608 … 196616 and the lock at 206848 … 206852, with the same
    access everywhere. This is what the wrappers' lock steps (`al_lock`'s frame) leave. -/
def HeapCtxL (code : ByteArray) (pb S0 S1 : Nat) (μ : Memory) (s : State) : Prop :=
  ∃ μ₀, HeapCtxC code pb S0 S1 μ₀ s ∧
    (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ.read a = μ₀.read a) ∧
    (∀ a, μ.writable a = μ₀.writable a)

/-- The context, held (unlocked) by μ itself, is the context with the lock held. -/
theorem HeapCtxC.held {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) : HeapCtxL code pb S0 S1 μ s :=
  ⟨μ, H, fun _ _ _ _ => rfl, fun _ => rfl⟩

/-- The free path's return (42978) to t, the address ω₀ resolves to. -/
theorem fr_ret {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs)
    (μ : Memory) (ret t : Nat) (h0 : ω[0] = UInt64.ofNat ret)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) : FreeStepsH p R 42978 ω μ x t ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0, hret, hjt, hbt]

/-- **One call of the free path (42327) with the lock held, under any host relation**: with
    ω₇ = 196792 (the allocator), ω₈ = ptr the data address of an allocated chunk c of s, and a return
    address ω₀ that `djump` resolves to t, the call returns to t with the context, lock still held,
    kept for `free s ptr` (same base), the pages, the octets that are not writable, the stack from sp
    up and the globals kept, every other allocated chunk of s still allocated with its data, and
    ω₀, ω₁, ω₅, ω₆ restored. -/
theorem free_callG {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P]
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr ret t : Nat)
    (c : Chunk) (H : HeapCtxL code pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true)
    (hca : c.addr + 32 = ptr) (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat 196792) (h8 : ω[8] = UInt64.ofNat ptr)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : 2147483700 ≤ sp) (hS : S0 + 24 ≤ sp ∧ sp ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 42327 ω μ x t ω' μ' x 221 ∧ HeapCtxL code pb S0 S1 μ' (free s ptr) ∧
      (free s ptr).base = s.base ∧ μ'.pages = μ.pages ∧
      (∀ b, b < two32 → μ.writable b = false → μ'.read b = μ.read b) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧ (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks (free s ptr) ∧
        ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H₀.pages
  have hsp1 : sp < 4294967296 := by have := H₀.hS1; omega
  have rep : Rep μ s := H₀.rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a ha1 ha2 ha3 => hag a (by omega) (Or.inr (by
    unfold A0 at ha1; omega)) ha3
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := fun a h1 h2 => by rw [hwa]; exact H₀.st a h1 h2
  obtain ⟨ω', μ', run, rep', wf', fo', ww, stk, e0, e1, e5, e6, hk⟩ :=
    free_refines_hdr (R := NoHost X) (p := p) (P := P) (HT := 4096 * ph) (S0 := S0) (S1 := S1) x ω μ s sp ptr
      H₀.wf rep ⟨c, hc, hca, hcu⟩ h1 h8 h7 hsp hsp1 H₀.hb0 H₀.hbT H₀.fo hHT hS
      (HeapPages.wrAt (HeapPages.of_eq hp hwa) hhb hst)
  obtain ⟨hpg, hro⟩ := keep_nohost run
  have hb' : (free s ptr).base = s.base := free_base'
  have hal : (free s ptr).allocated = s.allocated := free_allocated
  have ht := H₀.wf.2.2.2.1
  unfold TilesOk at ht
  have hG : ∀ b, (fun a => ∃ c ∈ chunks s, c.addr = a) b → b + 16 ≤ 196616 ∨ 196792 ≤ b := by
    rintro b ⟨d, hd, rfl⟩
    have := ht.mem_lt d hd
    have := H₀.hb0
    right; omega
  -- the twin of μ' with μ₀'s lock words
  let μ₀' := (μ'.writeN 196608 (μ₀.readN 196608 8)).writeN 206848 (μ₀.readN 206848 4)
  have ag' : ∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
      μ'.read a = μ₀'.read a := fun a ha h1 h2 => by
    simp only [μ₀']
    rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Memory.length_readN]; omega)
        (by simp only [Memory.length_readN, two32]; omega) (by simp only [two32]; omega),
      Memory.read_writeN_disjoint _ _ _ _ (by simp only [Memory.length_readN]; omega)
        (by simp only [Memory.length_readN, two32]; omega) (by simp only [two32]; omega)]
  have wa' : ∀ a, μ₀'.writable a = μ'.writable a := fun a => by
    simp only [μ₀', Memory.writable_writeN]
  have wa0 : ∀ a, μ₀'.writable a = μ₀.writable a := fun a => by rw [wa', ww, hwa]
  have hlk : rdN μ₀' 206848 1 = 0 := by
    rw [← H₀.lock]
    apply rdN_frame
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [μ₀']
    rw [show (206848 + 0 : Nat) = 206848 + 0 from rfl,
      Memory.read_writeN_at _ _ _ (by simp only [Memory.length_readN, two32]; omega) 0
        (by simp only [Memory.length_readN]; omega)]
    simp [Memory.readN]
  refine ⟨ω', μ', (run.weaken (fun _ _ _ _ _ _ _ h => absurd h id)).trans
      (fr_ret (R := R) (p := p) (P := P) x ω' μ' ret t (e0.trans h0) hret hjt hbt),
    ⟨μ₀', ⟨wf', rep'.congr_lock wf' (by rw [hb']; exact H₀.hb0) (by rw [hb']; exact H₀.hbT)
        (fun a ha1 ha2 ha3 => (ag' a (by omega) (Or.inr (by unfold A0 at ha1; omega)) ha3).symm),
      fo', hlk, by rw [hb']; exact H₀.hb0, by rw [hb']; exact H₀.hbT, by rw [hal]; exact H₀.hA, H₀.bd,
      ⟨ph, h48, hhb, HeapPages.of_eq hp wa0, hHTs, by rw [hb', hal]; exact hHT⟩, H₀.hSb, H₀.hS1,
      fun a h1 h2 => by rw [wa0]; exact H₀.st a h1 h2, fun a ha => by rw [wa0]; exact H₀.ro a ha⟩,
      ag', fun a => (wa' a).symm⟩,
    hb', hpg, hro, fun a ha hb => stk a ha hb, HKeepG.glob hk hG,
    fun d hd hdu hdc => ⟨free_keeps_used H₀.wf hc hca hcu hd hdu hdc, fun a ha => ?_⟩, e0,
    by rw [e1, h1], e5, e6⟩
  unfold InData at ha
  exact hk.hkeep a (off_hdr_data H₀.wf H₀.hb0 H₀.hbT hd ha.1 ha.2)

end Services.Bootstrap.Decode.DeallocCall
