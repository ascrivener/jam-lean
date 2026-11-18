import Services.Bootstrap.Acc.Transfer.Glob
import Services.Bootstrap.Alloc.AllocZeroedImpl

/-!
# The statics kept by the inputs decode: helpers

The inputs decode (6630 … 6674, `inputs_decode`) keeps the read-write statics 196616 … 196791
(`Alloc.Glob`): its stack writes are above 2³¹, its heap writes are into chunk data (at or above the
allocator's base, 206864) and its allocator steps keep them (`glob_of_hkeepC`). These helpers give the
bounds the frame facts need.
-/

namespace Services.Bootstrap.Acc

open Services.Bootstrap.Alloc

/-- A static lies below 2³¹. -/
theorem Glob.lt {a : Nat} (h : Glob a) : a < 2147483648 := by unfold Glob at h; omega

/-- A static lies below the allocator's base (206864 ≤ base). -/
theorem Glob.lt_base {a b : Nat} (h : Glob a) (hb : 206864 ≤ b) : a < b := by unfold Glob at h; omega

/-- A zeroing allocator frame (`HKeepGD`, the zeroed block D … E in the heap) whose headers are chunk
    addresses of `s` keeps the statics. -/
theorem glob_of_hkeepGD {s : Picoalloc.State} (hwf : Picoalloc.WF s) (hb0 : 206864 ≤ s.base) {μ μ' : PVM.Memory}
    {D E : Nat} (hk : HKeepGD μ μ' (fun a => ∃ d ∈ Picoalloc.chunks s, d.addr = a) D E) (hD : 206864 ≤ D) :
    ∀ a, Glob a → μ'.read a = μ.read a := fun a ha => by
  have ⟨g1, g2⟩ : 196616 ≤ a ∧ a < 196792 := ha
  refine hk a ⟨Or.inl ha, by omega, fun b ⟨d, hd, e⟩ => ?_⟩ (Or.inl (by omega))
  have ht := hwf.2.2.2.1; unfold Picoalloc.TilesOk at ht
  have := (ht.mem_lt d hd).1; omega

end Services.Bootstrap.Acc
