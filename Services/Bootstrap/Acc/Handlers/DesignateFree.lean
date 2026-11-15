import Services.Bootstrap.Acc.Handlers.DesignateAlloc
import Services.Bootstrap.Acc.Handlers.HeapLock
import Services.Bootstrap.Acc.Handlers.DesignateLoop

/-!
# `Designate`'s free of the keys' buffer (49910 … 10070)

The buffer ptr (the word at S + 32, the data address of an allocated chunk c) is freed: the lock is
taken (`freeLock`), `free_impl` runs (`free_callG`, with the lock held), the lock is cleared and the
callee returns to the handler at 10070 (`unlockRet`). The allocator's context is kept, for
`free s ptr`.
-/

namespace Services.Bootstrap.Acc.Handlers.DesignateFree

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Acc.Handlers.HeapLock
  Services.Bootstrap.Acc.Handlers.DesignateAlloc

/-- **49910 … 10070**: from the allocator's context with the buffer ptr = c's data address at S + 32,
    the result's index b in ω₅ and the caller's frame (return address 354 at S + 64, ω₅ and ω₆ saved
    at S + 56, S + 48): ptr freed, the context kept for `free s ptr`, the return to 10070 with ω₇ = b,
    ω₁ = S + 72 and ω₅, ω₆ restored. Memory from S up and every other allocated chunk's data are
    kept. No host call, so any `R`. -/
theorem free_seg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {X : Type} {R : HostRel X}
    (code : ByteArray) (pb S0 S1 : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (S ptr b r5 r6 : Nat) (c : Chunk) (H : HeapCtxC code pb S0 S1 μ s) (hc : c ∈ chunks s)
    (hcu : c.used = true) (hca : c.addr + 32 = ptr)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat b) (hb : b < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 ptr)
    (m64 : μ.readN (S + 64) 8 = Num.encodeLE 8 354) (m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 r5)
    (m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 r6)
    (hsp : 2147483700 ≤ S) (hS : S0 + 24 ≤ S ∧ S + 80 ≤ S1) :
    ∃ ω' μ', FreeStepsH p R 49910 ω μ x 10070 ω' μ' x 253 ∧ HeapCtxC code pb S0 S1 μ' (free s ptr) ∧
      ω'[7] = UInt64.ofNat b ∧ ω'[1] = UInt64.ofNat (S + 72) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ (∀ a, a < 4294967296 → S ≤ a → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks (free s ptr) ∧
        ∀ a, InData d a → μ'.read a = μ.read a) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hS1 := H.hS1
  have hSb := H.hSb
  have hph : 4096 * ph ≤ 4096 * pb := Nat.mul_le_mul_left _ hhb
  have hwr := HeapPages.wrAt hp hhb H.st
  -- the lock taken
  obtain ⟨ω1, μ1, run1, a7, a8, a0, a6, a5, a1, afr, awr⟩ := freeLock (p := p) (P := P) (R := R) x ω μ S ptr
    h1 hptr m32 H.lock (by omega) hwr ⟨by omega, by omega, by omega, by omega⟩
  have HL : HeapCtxL code pb S0 S1 μ1 s := HeapCtxC.toL H afr awr
  -- the free path, with the lock held
  obtain ⟨ω2, μ2, run2, HL2, -, pg2, -, stk2, -, keep2, b0, b1, b5, b6⟩ := free_callG (R := R) (p := p) (P := P)
    code pb S0 S1 x ω1 μ1 s S ptr 2214 49968 c HL hc hcu hca a0 (a1.trans h1) a7 a8
    ⟨by decide, by decide, by decide⟩ jte_1106 bs_49968 hsp ⟨hS.1, by omega⟩
  -- the frame survives both
  have k12 : ∀ a, a < 4294967296 → S ≤ a → μ2.read a = μ.read a := fun a h0 h1' => by
    rw [stk2 a h0 h1', afr a h0 (Or.inr (by omega)) (Or.inr (by omega))]
  have rk : ∀ o, o + 8 ≤ 80 → μ2.readN (S + o) 8 = μ.readN (S + o) 8 := fun o ho =>
    Services.Bootstrap.Acc.Handlers.DesignateLoop.readN_keep fun a h1' h2 => k12 a (by omega) (by omega)
  have wr2 : ∀ a, μ2.writable a = μ.writable a := fun a => by
    rw [← awr a]; unfold Memory.writable; rw [pg2]
  have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.readable a = true := fun a h1' h2 =>
    Memory.readable_of_writable (by rw [wr2]; exact H.st a h1' h2)
  -- the lock cleared and the return
  obtain ⟨ω3, run3, c7, c1, c5, c6⟩ := unlockRet (p := p) (P := P) (R := R) x ω2 μ2 S b r5 r6
    (b1.trans (a1.trans h1)) (b5.trans (a5.trans h5)) (b6.trans a6) hb hr5 hr6
    (by rw [rk 64 (by omega)]; exact m64) (by rw [rk 56 (by omega)]; exact m56)
    (by rw [rk 48 (by omega)]; exact m48) ⟨by omega, by omega⟩
    (fun a h1' h2 => hst2 a (by omega) (by omega))
    (by rw [wr2]; exact hwr 206848 (Or.inl ⟨by decide, by omega⟩))
  let μ3 := μ2.writeN 206848 [UInt8.ofNat 0]
  have k3 : ∀ a, a < 4294967296 → a ≠ 206848 → μ3.read a = μ2.read a := fun a h0 hne =>
    Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]) (by simp [two32]; omega)
  have HC : HeapCtxC code pb S0 S1 μ3 (free s ptr) :=
    HeapCtxL.unlock HL2 (fun a h0 h1' h2 => k3 a h0 (by omega)) (fun a => Memory.writable_writeN ..)
      (by
        show Num.decodeLE _ = _
        rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32])]
        rfl)
  refine ⟨ω3, μ3, ((run1.trans run2).trans run3).mono (by omega), HC, c7, c1, c5, c6,
    fun a h0 h1' => by rw [k3 a h0 (by omega), k12 a h0 h1'], fun d hd hdu hdc => ?_⟩
  obtain ⟨hd', hk⟩ := keep2 d hd hdu hdc
  refine ⟨hd', fun a ha => ?_⟩
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hlt := ht.mem_lt d hd
  have hb0 := H.hb0
  have hbT := H.hbT
  unfold InData at ha
  rw [k3 a (by omega) (by omega), hk a ha, afr a (by omega) (Or.inr (by omega)) (Or.inr (by omega))]

end Services.Bootstrap.Acc.Handlers.DesignateFree
