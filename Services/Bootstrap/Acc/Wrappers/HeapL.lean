import Services.Bootstrap.Acc.Inputs.GlueFree
import Services.Bootstrap.Acc.Inputs.OperandCall

/-!
# The allocator's context with the lock held, kept by writes above the heap

`HeapCtxL` (the context while the allocator's lock is held) survives a run that writes only at or
above 2³¹, the stack: the SDK wrappers save words in their frames between taking the lock and
calling `alloc_impl`.
-/
namespace Services.Bootstrap.Acc
open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall

/-- **The context with the lock held, from the free one**: μ′ reads as μ₀ (where the context
    holds) below 2³¹ off the allocator's scratch word (196608 … 196616) and lock word (206848 …
    206852), and keeps writability. -/
theorem HeapCtxL.of_lo {code : ByteArray} {pb S0 S1 : Nat} {μ₀ μ' : Memory} {s : State}
    (H₀ : HeapCtxC code pb S0 S1 μ₀ s)
    (fr : ∀ a, a < 2147483648 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ₀.read a)
    (wr : ∀ a, μ'.writable a = μ₀.writable a) : HeapCtxL code pb S0 S1 μ' s := by
  -- μ' with μ₀'s scratch and lock words put back
  let μs := μ'.writeN 196608 (μ₀.readN 196608 8)
  let μm := μs.writeN 206848 (μ₀.readN 206848 4)
  have inl : ∀ k, k < 4 → μm.read (206848 + k) = μ₀.read (206848 + k) := fun k hk => by
    have := PVM.Memory.read_writeN_at μs 206848 (μ₀.readN 206848 4) (by simp [Memory.readN, two32]) k
      (by simp [Memory.readN]; omega)
    rw [this]; simp [Memory.readN]
  have outl : ∀ a, a < 4294967296 → (a < 206848 ∨ 206852 ≤ a) → μm.read a = μs.read a := fun a ha h =>
    PVM.Memory.read_writeN_of_not_mem μs 206848 _ a fun k hk => by
      simp [Memory.readN] at hk; simp only [two32]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt ha]; omega
  have ins : ∀ k, k < 8 → μs.read (196608 + k) = μ₀.read (196608 + k) := fun k hk => by
    have := PVM.Memory.read_writeN_at μ' 196608 (μ₀.readN 196608 8) (by simp [Memory.readN, two32]) k
      (by simp [Memory.readN]; omega)
    rw [this]; simp [Memory.readN]
  have outs : ∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → μs.read a = μ'.read a := fun a ha h =>
    PVM.Memory.read_writeN_of_not_mem μ' 196608 _ a fun k hk => by
      simp [Memory.readN] at hk; simp only [two32]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt ha]; omega
  have wm : ∀ a, μm.writable a = μ₀.writable a := fun a => by
    simp only [μm, μs, Memory.writable_writeN]; rw [wr]
  have Hm : HeapCtxC code pb S0 S1 μm s := Services.Bootstrap.Acc.HeapCtxC.keep_hi H₀ (fun a ha => by
    by_cases hl : 206848 ≤ a ∧ a < 206852
    · have := inl (a - 206848) (by omega); rwa [show 206848 + (a - 206848) = a by omega] at this
    · rw [outl a (by omega) (by omega)]
      by_cases hs : 196608 ≤ a ∧ a < 196616
      · have := ins (a - 196608) (by omega); rwa [show 196608 + (a - 196608) = a by omega] at this
      · rw [outs a (by omega) (by omega), fr a ha (by omega) (by omega)]) wm
  refine ⟨μm, Hm, fun a ha h1 h2 => ?_, fun a => (wr a).trans (wm a).symm⟩
  rw [outl a ha h2, outs a ha h1]

/-- **The context with the lock held survives writes above the heap**: μ′ reads as μ below 2³¹
    (the stack is above) and keeps writability. -/
theorem HeapCtxL.keep_hi {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxL code pb S0 S1 μ s) (fr : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (wr : ∀ a, μ'.writable a = μ.writable a) : HeapCtxL code pb S0 S1 μ' s := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  exact HeapCtxL.of_lo H₀ (fun a ha h1 h2 => by rw [fr a ha, hag a (by omega) h1 h2])
    (fun a => (wr a).trans (hwa a))

end Services.Bootstrap.Acc
