import Services.Bootstrap.Decode.HeapCtx
import Services.Bootstrap.Decode.VecU8Pass

/-!
# The allocator's context under stack and block writes

Three facts about `HeapCtxC` (the allocator's context, GP v0.8.0 Appendix A's memory with the
service's heap) that the handlers' compositions need: it survives writes off the heap
(`keepHi`) and writes inside an allocated chunk's data (`keepData`), and an allocated chunk's data
is writable (`writableData`). These restate `Acc.HeapCtxC.keep_hi`, `Acc.heapC_writable_data` and
T2-inputs' `HeapCtxC.keep_data` without importing the items loop's modules.
-/

namespace Services.Bootstrap.Acc.Handlers.HeapKeep

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

/-- A chunk's data: the addresses past its 32-octet header. -/
def InData (c : Chunk) (a : Nat) : Prop := c.addr + 32 ≤ a ∧ a < c.addr + 32 * c.size

/-- **The context survives stack-only changes**: memory kept below 2³¹ and the same page access. -/
theorem keepHi {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) (fr : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (wr : ∀ a, μ'.writable a = μ.writable a) : HeapCtxC code pb S0 S1 μ' s := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  exact ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT fun a _ ha2 _ => fr a ha2, H.fo,
    by rw [rdN_frame fun j hj => fr _ (by omega)]; exact H.lock, H.hb0, H.hbT, H.hA,
    H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp wr, hHTs, hHT⟩, H.hSb, H.hS1,
    fun a h1 h2 => by rw [wr]; exact H.st a h1 h2, fun a ha => by rw [wr]; exact H.ro a ha⟩

/-- **The context survives a write inside an allocated chunk's data.** -/
theorem keepData {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
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

/-- **An allocated chunk's data is writable.** -/
theorem writableData {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
    (ha : InData c a) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp := H.wf.2.2.2.2.2.2.2
  unfold SpaceOk at hsp
  have h1 := (hsp c hc).1 hu
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  have := H.hb0
  unfold InData at ha
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega

end Services.Bootstrap.Acc.Handlers.HeapKeep
