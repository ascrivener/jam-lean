import Services.Bootstrap.Decode.HeapCtx

/-!
# The read-write statics kept

The accumulate prologue stores the chain parameters in the read-write statics 196616 … 196791
(`Alloc.Glob`; `Acc/Statics.lean`), and later code must keep them (Handlers A's row 8 reads 𝖢 and 𝖨).
The allocator's frames keep them: `glob_of_hkeepC`.
-/

namespace Services.Bootstrap.Acc

open Services.Bootstrap.Alloc PVM

/-- An allocator frame whose headers are chunk addresses of `s` keeps the statics (`Glob`), since
    every chunk lies at or above `s.base` ≥ 206864. -/
theorem glob_of_hkeepC {s : Picoalloc.State} (hwf : Picoalloc.WF s) (hb0 : 206864 ≤ s.base) {μ μ' : Memory}
    (hk : HKeepG μ μ' (fun a => ∃ d ∈ Picoalloc.chunks s, d.addr = a)) :
    ∀ a, Glob a → μ'.read a = μ.read a :=
  hk.glob fun b ⟨d, hd, e⟩ => by
    have ht := hwf.2.2.2.1; unfold Picoalloc.TilesOk at ht
    have := (ht.mem_lt d hd).1; omega

end Services.Bootstrap.Acc
