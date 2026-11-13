import Services.Bootstrap.Acc.Inputs.LoopItemOp
import Services.Bootstrap.Decode.LoopAPass

/-!
# `Vec<AccumulateItem>::decode` (44916): the induction over the items

See the Acc README for the invariant.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The allocator's context survives a write inside an allocated chunk's data** (`heap_of_data`, for
    any host). -/
theorem HeapCtxC.keep_data {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s)
    (hr : ∀ a, a < 2147483648 → (a < c.addr + 32 ∨ c.addr + 32 * c.size ≤ a) → μ'.read a = μ.read a)
    (hw : ∀ a, μ'.writable a = μ.writable a) : HeapCtxC code pb S0 S1 μ' s := by
  have := H.hb0
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  exact ⟨H.wf, Services.Bootstrap.Decode.HeapFrame.Rep.congr_data H.rep H.wf H.hb0 H.hbT hc
      (fun a h1 h2 => hr a h1 (by omega)), H.fo,
    by rw [rdN_frame fun j hj => hr _ (by omega) (by omega)]; exact H.lock, H.hb0, H.hbT, H.hA, H.bd,
    ⟨ph, h48, hhb, HeapPages.of_eq hpg hw, hHTs, hHT⟩, H.hSb, H.hS1, fun a h1 h2 => by rw [hw]; exact H.st a h1 h2,
    fun a ha => by rw [hw]; exact H.ro a ha⟩

end Services.Bootstrap.Acc
