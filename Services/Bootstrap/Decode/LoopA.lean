import Services.Bootstrap.Decode.Loop
import Services.Bootstrap.Decode.HeapCtx

/-!
# Element decoders that allocate

`ElemOkA`: `ElemOk` for a decoder that may call picoalloc's `alloc`. It runs under the refine
host contract `refineContractK cap env`, with the allocator's context (`HeapCtx`) and the payload
inside an allocated chunk, and either
* returns to the loop as `ElemOk` says, in at most N steps, with a new allocator state s' that keeps
  every allocated chunk of s and its data, the context kept, and a value whose property may also
  depend on the heap, through chunks allocated during the element only (so later steps that keep
  those chunks' data keep it); or
* reaches the `alloc` wrapper's return (40611) with null, the model's `alloc` having failed: the
  start of heap exhaustion (bootstrap decision 4).

`ElemOkA.of_elemOk`: every `ElemOk` is an `ElemOkA` that leaves the allocator alone.
-/

namespace Services.Bootstrap.Decode.LoopA

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.HeapCtx

/-- The stack's extent: the blob's 8192 octets below 4278059008. -/
abbrev S0 : Nat := 4278050816
abbrev S1 : Nat := 4278059008

/-- A chunk's data: from 32 past its start to its end. -/
def InData (c : Chunk) (a : Nat) : Prop := c.addr + 32 ≤ a ∧ a < c.addr + 32 * c.size

/-- **An allocated chunk's data is writable**: it lies in the heap's writable pages. -/
theorem heap_writable_data {env : RefineHost.Env} {pb : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
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

/-- **One element decodes, possibly allocating** (see the module doc). -/
def ElemOkA (env : RefineHost.Env) (cap pb : Nat) (p : ByteArray) (P : Program) (N : Nat)
    (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat) (s : State),
    ω[1] = UInt64.ofNat 4278057632 → ω[5] = UInt64.ofNat 4278057752 → ω[6] = UInt64.ofNat 4278058648 →
    ω[7] = UInt64.ofNat 0 → μ.read 4278057632 = enc.headD 0 →
    μ.readN 4278058648 8 = Num.encodeLE 8 ptr → μ.readN 4278058656 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN 4278057680 8 = Num.encodeLE 8 18 → μ.readN 4278057672 8 = Num.encodeLE 8 v5 →
    μ.readN 4278057664 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < 4278058216 → μ.writable a = true) →
    (∀ a, 4278058648 ≤ a → a < 4278058664 → μ.writable a = true) →
    HeapCtx env pb S0 S1 μ s →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + (enc.length - 1) ≤ c.addr + 32 * c.size) →
    (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 20626 ω μ x 723 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat 4278057688 ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN 4278058648 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN 4278058656 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN 4278057752 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          Rep (μ'.readN 4278057752 232) μ'') ∧
      (∀ a, 4278057664 ≤ a → a < 4294967296 →
        (a < 4278058648 ∨ 4278058664 ≤ a) → (a < 4278057752 ∨ 4278057984 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.readable a = μ.readable a) ∧
      (∀ a, 4278050816 ≤ a → μ'.writable a = μ.writable a)) ∨
    (∃ (ω' : Regs) (μ' : Memory) (s'' : State) (hb r : Nat), FreeStepsH p (refineContractK cap env) 20626 ω μ x 40611 ω' μ' x N ∧
      ω'[7] = UInt64.ofNat 0 ∧ alloc (growTo pb) hb 1 r s'' = none)

/-- **Every `ElemOk` is an `ElemOkA`** that keeps the allocator's state: its writes, to the stack,
    the reader and the slot, are all above 2^31. -/
theorem ElemOkA.of_elemOk {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program}
    {enc : List UInt8} {Rep : List UInt8 → Prop} (h : ElemOk p P enc Rep) :
    ElemOkA env cap pb p P 4000 enc (fun bs _ => Rep bs) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _
  obtain ⟨ω', μ', run, e1, e5, e6, eR0, eR8, eW, eRep, efr, erd, ewr⟩ :=
    h RefineCtx (refineContractK cap env) x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay
      s0 s5 s6 hv5 hv6 tab rt ws wr
  have low : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha =>
    efr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  refine Or.inl ⟨ω', μ', s, run, e1, e5, e6, eR0, eR8, eW,
    ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT (fun a _ ha2 _ => low a ha2), H.fo,
      by rw [rdN_frame fun j hj => low _ (by omega)]; exact H.lock, H.hb0, H.hbT, H.hA, H.bd,
      ⟨ph, h48, hhb, HeapPages.of_eq hpg ewr, hHTs, hHT⟩, H.hSb, H.hS1,
      fun a h1 h2 => by rw [ewr]; exact H.st a h1 h2, fun a ha => by rw [ewr]; exact H.ro a ha⟩,
    fun c hc _ => hc, fun c hc _ a ha => low a ?_, ⟨[], by simp, fun _ _ => eRep⟩,
    fun a h h0 h2 h3 => efr a h0 (Or.inr h) h2 h3, fun a ha => low a (by omega), fun a _ => erd a, fun a _ => ewr a⟩
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  have := H.hbT
  unfold InData at ha
  omega

end Services.Bootstrap.Decode.LoopA
