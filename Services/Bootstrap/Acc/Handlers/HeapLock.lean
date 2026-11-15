import Services.Bootstrap.Decode.DeallocCall

/-!
# Taking and clearing the allocator's lock inline

`Designate` and `Assign` call `alloc_impl` (41177) and `free_impl` (42327) directly, with their own
copies of the allocator wrapper's lock steps. The calls are stated on `HeapCtxL` (the context with
the lock held: memory as a `HeapCtxC` memory but for the scratch word at 196608 … 196616 and the
lock word at 206848 … 206852). These two lemmas cross between the two:
* `HeapCtxC.toL`: memory that agrees with a `HeapCtxC` memory outside those words, with the same
  access, holds the context with the lock held;
* `HeapCtxL.unlock`: from the context with the lock held, a memory that agrees outside those words,
  with the same access and the lock octet 0, holds the context.
-/

namespace Services.Bootstrap.Acc.Handlers.HeapLock

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.DeallocCall

theorem HeapCtxC.toL {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s)
    (hrd : ∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
      μ'.read a = μ.read a)
    (hw : ∀ a, μ'.writable a = μ.writable a) : HeapCtxL code pb S0 S1 μ' s :=
  ⟨μ, H, hrd, hw⟩

theorem HeapCtxL.unlock {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxL code pb S0 S1 μ s)
    (hrd : ∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
      μ'.read a = μ.read a)
    (hw : ∀ a, μ'.writable a = μ.writable a) (hl : rdN μ' 206848 1 = 0) :
    HeapCtxC code pb S0 S1 μ' s := by
  obtain ⟨μ₀, H₀, hag, hwa⟩ := H
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H₀.pages
  have hw0 : ∀ a, μ'.writable a = μ₀.writable a := fun a => by rw [hw, hwa]
  refine ⟨H₀.wf, H₀.rep.congr_lock H₀.wf H₀.hb0 H₀.hbT fun a h1 h2 h3 => ?_, H₀.fo, hl, H₀.hb0, H₀.hbT,
    H₀.hA, H₀.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp hw0, hHTs, hHT⟩, H₀.hSb, H₀.hS1,
    fun a h1 h2 => by rw [hw0]; exact H₀.st a h1 h2, fun a ha => by rw [hw0]; exact H₀.ro a ha⟩
  unfold A0 at h1
  rw [hrd a (by omega) (Or.inr (by omega)) h3, hag a (by omega) (Or.inr (by omega)) h3]

end Services.Bootstrap.Acc.Handlers.HeapLock
