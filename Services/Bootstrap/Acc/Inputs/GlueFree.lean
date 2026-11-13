import Services.Bootstrap.Acc.Inputs.GlueLock
import Services.Bootstrap.Decode.DeallocCall

/-!
# The inputs' glue: the fetched buffer freed (44591 … 44641)

The lock taken inline (`g_lock`), the free path 42327 from the allocator's context with the lock held
(`free_callG`, GP Appendix B's heap: picoalloc's `free`), the lock released (`g_unlock`): the context
`HeapCtxC` again, for the state `free s ptr`.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The lock released: from the lock-held context, a memory that agrees off the lock byte 206848, with
    that byte 0 and the same pages, is the allocator's context again. -/
theorem heapL_release {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxL code pb S0 S1 μ s) (hl : rdN μ' 206848 1 = 0)
    (hr : ∀ a, a < 4294967296 → a ≠ 206848 → μ'.read a = μ.read a)
    (hw : ∀ a, μ'.writable a = μ.writable a) : HeapCtxC code pb S0 S1 μ' s := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  have hw' : ∀ a, μ'.writable a = μ₀.writable a := fun a => (hw a).trans (hwa a)
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H₀.pages
  refine ⟨H₀.wf, ?_, H₀.fo, hl, H₀.hb0, H₀.hbT, H₀.hA, H₀.bd,
    ⟨ph, h48, hhb, HeapPages.of_eq hp hw', hHTs, hHT⟩, H₀.hSb, H₀.hS1,
    fun a h1 h2 => by rw [hw']; exact H₀.st a h1 h2, fun a ha => by rw [hw']; exact H₀.ro a ha⟩
  exact H₀.rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a ha1 ha2 ha3 => by
    unfold A0 at ha1
    rw [hr a (by omega) (by omega), hag a (by omega) (Or.inr (by omega)) ha3]

/-- **44591 … 44641**: the fetched buffer `ptr` (saved at sp, the data of the allocated chunk c) freed
    under the lock taken and released inline; the context for `free s ptr`, the stack from sp, the
    other allocated chunks' data and ω₁, ω₅, ω₆ kept. -/
theorem g_free {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (code : ByteArray)
    (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State) (sp ptr : Nat) (c : Chunk)
    (H : HeapCtxC code pb S0 S1 μ s) (hc : c ∈ chunks s) (hcu : c.used = true) (hca : c.addr + 32 = ptr)
    (h1 : ω[1] = UInt64.ofNat sp) (h6 : ω[6] = UInt64.ofNat 196792)
    (h7 : ω[7] = UInt64.ofNat 206848) (h8 : ω[8] = UInt64.ofNat 1) (hptr : rdN μ sp 8 = ptr)
    (hsp : 2147483700 ≤ sp) (hS : S0 + 24 ≤ sp ∧ sp + 8 ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 44591 ω μ x 44641 ω' μ' x 237 ∧ HeapCtxC code pb S0 S1 μ' (free s ptr) ∧
      (free s ptr).base = s.base ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks (free s ptr) ∧
        ∀ a, d.addr + 32 ≤ a → a < d.addr + 32 * d.size → μ'.read a = μ.read a) ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  obtain ⟨ω1, μ1, r1, a0, a1, a7, a8, a5, a6, fr1, wr1, -⟩ :=
    g_lock (p := p) (P := P) (R := R) x ω μ sp h1 h6 h7 h8 H.lock (HT := 4096 * ph) (by omega)
      ⟨by omega, hS.2⟩ ⟨by omega, by omega⟩ (HeapPages.wrAt hp hhb H.st)
  have HL : HeapCtxL code pb S0 S1 μ1 s := ⟨μ, H, fr1, wr1⟩
  obtain ⟨ω2, μ2, r2, H2, hb2, pg2, ro2, stk2, _, kd2, b0, b1, b5, b6⟩ :=
    free_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω1 μ1 s sp ptr 2028 44632 c HL hc hcu hca a0
      a1 a7 (by rw [a8, hptr]) (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1013]) bs_44632
      hsp ⟨hS.1, by omega⟩
  have wr2 : ∀ a, μ2.writable a = μ1.writable a := fun a => by unfold Memory.writable; rw [pg2]
  have h62 : ω2[6] = UInt64.ofNat 196792 := by rw [b6, a6, h6]
  have hwl : μ2.writable 206848 = true := by
    rw [wr2, wr1]; exact HeapPages.wrAt hp hhb H.st 206848 (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨ω3, μ3, r3, l3, fr3, rd3, wr3, -, c1, c5, c6, -⟩ := g_unlock (p := p) (P := P) (R := R) x ω2 μ2 h62 hwl
  refine ⟨ω3, μ3, (r1.trans r2).trans r3, heapL_release H2 l3 fr3 wr3, hb2,
    fun a => by rw [wr3, wr2, wr1], fun a ha hsa => ?_, fun d hd hdu hdc => ⟨(kd2 d hd hdu hdc).1, fun a ha ha' => ?_⟩,
    ?_, ?_, ?_⟩
  · rw [fr3 a ha (by omega), stk2 a ha hsa, fr1 a ha (Or.inr (by omega)) (Or.inr (by omega))]
  · have ht := H.wf.2.2.2.1
    unfold TilesOk at ht
    have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    have := ht.mem_lt d hd
    have := H.hb0
    have := H.hbT
    rw [fr3 a (by omega) (by omega), (kd2 d hd hdu hdc).2 a ⟨ha, ha'⟩, fr1 a (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
  · rw [c1, b1, a1]
  · rw [c5, b5, a5]
  · rw [c6, b6, a6]

end Services.Bootstrap.Acc
