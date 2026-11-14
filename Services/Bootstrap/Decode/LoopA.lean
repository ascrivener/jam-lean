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
* reaches a failed allocator call (`Exhausts`): an allocator wrapper returned null and the model's
  call fails (`AllocFail`: `alloc` at 40611, or `realloc` in `read_vec` at 33055), the start of heap
  exhaustion (bootstrap decision 4).

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

/-- **An allocated chunk's data is writable**: it lies in the heap's writable pages (for any code). -/
theorem heap_writable_dataG {code : ByteArray} {pb : Nat} {μ : Memory} {s : State}
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

/-- `heap_writable_dataG` for the refine host's code. -/
theorem heap_writable_data {env : RefineHost.Env} {pb : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
    (ha : InData c a) : μ.writable a = true :=
  heap_writable_dataG H hc hu ha

/-- **A failed allocator call**, at the point `j` where the run sees it: the `alloc` wrapper's
    return (40611), the model's `alloc` failing; or `read_vec`'s return from the `realloc` wrapper
    (33055, in `finish_grow`'s growth of a `Vec`), the model's `realloc` failing. At either the wrapper
    has returned null (ω₇ = 0): the start of heap exhaustion (bootstrap decision 4). -/
def AllocFail (pb j : Nat) : Prop :=
  (j = 40611 ∧ ∃ (s : State) (hb r : Nat), alloc (growTo pb) hb 1 r s = none) ∨
  (j = 33055 ∧ ∃ (s : State) (hb ptr al r : Nat), realloc (growTo pb) hb s ptr al r = none)

/-- The run reaches a failed allocator call (`AllocFail`), the wrapper having returned null. -/
def Exhausts (env : RefineHost.Env) (cap pb : Nat) (p : ByteArray) (P : Program) (i : Nat) (ω : Regs)
    (μ : Memory) (x : RefineCtx) (n : Nat) : Prop :=
  ∃ (ω' : Regs) (μ' : Memory) (j : Nat),
    FreeStepsH p (refineContractK cap env) i ω μ x j ω' μ' x n ∧ ω'[7] = UInt64.ofNat 0 ∧ AllocFail pb j

/-- The run reaches a failed allocator call (`AllocFail`), the wrapper having returned null, under
    any host fit for the allocator (`Exhausts`'s host-generic form). -/
def ExhaustsG {X : Type} (env : HeapHost X) (cap pb : Nat) (p : ByteArray) (P : Program) (i : Nat) (ω : Regs)
    (μ : Memory) (x : X) (n : Nat) : Prop :=
  ∃ (ω' : Regs) (μ' : Memory) (j : Nat),
    FreeStepsH p (env.rel cap) i ω μ x j ω' μ' x n ∧ ω'[7] = UInt64.ofNat 0 ∧ AllocFail pb j

/-- A failed `alloc`, reaching the wrapper's return with null, is a failed allocator call. -/
theorem ExhaustsG.of_alloc {X : Type} {env : HeapHost X} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω ω' : Regs} {μ μ' : Memory} {x : X} {n : Nat} {s : State} {hb r : Nat}
    (run : FreeStepsH p (env.rel cap) i ω μ x 40611 ω' μ' x n) (e7 : ω'[7] = UInt64.ofNat 0)
    (ha : alloc (growTo pb) hb 1 r s = none) : ExhaustsG env cap pb p P i ω μ x n :=
  ⟨ω', μ', 40611, run, e7, Or.inl ⟨rfl, s, hb, r, ha⟩⟩

/-- A failed `realloc` in `read_vec`, returning null to 33055, is a failed allocator call. -/
theorem ExhaustsG.of_realloc {X : Type} {env : HeapHost X} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω ω' : Regs} {μ μ' : Memory} {x : X} {n : Nat} {s : State} {hb ptr al r : Nat}
    (run : FreeStepsH p (env.rel cap) i ω μ x 33055 ω' μ' x n) (e7 : ω'[7] = UInt64.ofNat 0)
    (ha : realloc (growTo pb) hb s ptr al r = none) : ExhaustsG env cap pb p P i ω μ x n :=
  ⟨ω', μ', 33055, run, e7, Or.inr ⟨rfl, s, hb, ptr, al, r, ha⟩⟩

/-- A run before a failed allocator call is still one. -/
theorem ExhaustsG.pre {X : Type} {env : HeapHost X} {cap pb : Nat} {p : ByteArray} {P : Program} {i j : Nat}
    {ω ω1 : Regs} {μ μ1 : Memory} {x : X} {n m : Nat}
    (run : FreeStepsH p (env.rel cap) i ω μ x j ω1 μ1 x n) (h : ExhaustsG env cap pb p P j ω1 μ1 x m) :
    ExhaustsG env cap pb p P i ω μ x (n + m) := by
  obtain ⟨ω', μ', k, run', e7, ha⟩ := h
  exact ⟨ω', μ', k, run.trans run', e7, ha⟩

theorem ExhaustsG.mono {X : Type} {env : HeapHost X} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω : Regs} {μ : Memory} {x : X} {n m : Nat} (h : ExhaustsG env cap pb p P i ω μ x n) (hnm : n ≤ m) :
    ExhaustsG env cap pb p P i ω μ x m := by
  obtain ⟨ω', μ', k, run', e7, ha⟩ := h
  exact ⟨ω', μ', k, run'.mono hnm, e7, ha⟩

/-- `Exhausts` is `ExhaustsG` for the refine contract (`refineHeap env`). -/
theorem Exhausts_iff {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω : Regs} {μ : Memory} {x : RefineCtx} {n : Nat} :
    Exhausts env cap pb p P i ω μ x n ↔ ExhaustsG (refineHeap env) cap pb p P i ω μ x n := Iff.rfl

theorem Exhausts.of_alloc {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω ω' : Regs} {μ μ' : Memory} {x : RefineCtx} {n : Nat} {s : State} {hb r : Nat}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x 40611 ω' μ' x n) (e7 : ω'[7] = UInt64.ofNat 0)
    (ha : alloc (growTo pb) hb 1 r s = none) : Exhausts env cap pb p P i ω μ x n :=
  ExhaustsG.of_alloc (env := refineHeap env) (P := P) run e7 ha

theorem Exhausts.of_realloc {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω ω' : Regs} {μ μ' : Memory} {x : RefineCtx} {n : Nat} {s : State} {hb ptr al r : Nat}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x 33055 ω' μ' x n) (e7 : ω'[7] = UInt64.ofNat 0)
    (ha : realloc (growTo pb) hb s ptr al r = none) : Exhausts env cap pb p P i ω μ x n :=
  ExhaustsG.of_realloc (env := refineHeap env) (P := P) run e7 ha

theorem Exhausts.pre {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i j : Nat}
    {ω ω1 : Regs} {μ μ1 : Memory} {x : RefineCtx} {n m : Nat}
    (run : FreeStepsH p (refineContractK cap env) i ω μ x j ω1 μ1 x n) (h : Exhausts env cap pb p P j ω1 μ1 x m) :
    Exhausts env cap pb p P i ω μ x (n + m) :=
  ExhaustsG.pre (env := refineHeap env) (P := P) run h

theorem Exhausts.mono {env : RefineHost.Env} {cap pb : Nat} {p : ByteArray} {P : Program} {i : Nat}
    {ω : Regs} {μ : Memory} {x : RefineCtx} {n m : Nat} (h : Exhausts env cap pb p P i ω μ x n) (hnm : n ≤ m) :
    Exhausts env cap pb p P i ω μ x m :=
  ExhaustsG.mono (env := refineHeap env) (P := P) h hnm

/-- **One element decodes, possibly allocating** (see the module doc). -/
def ElemOkAF (env : RefineHost.Env) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program) (F RD N : Nat)
    (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat) (s : State),
    ω[1] = UInt64.ofNat F → ω[5] = UInt64.ofNat (F + 120) → ω[6] = UInt64.ofNat RD →
    ω[7] = UInt64.ofNat 0 → μ.read F = enc.headD 0 →
    μ.readN RD 8 = Num.encodeLE 8 ptr → μ.readN (RD + 8) 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN (F + 48) 8 = Num.encodeLE 8 18 → μ.readN (F + 40) 8 = Num.encodeLE 8 v5 →
    μ.readN (F + 32) 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < (F + 584) → μ.writable a = true) →
    (∀ a, RD ≤ a → a < (RD + 16) → μ.writable a = true) →
    HeapCtx env pb S0 S1 μ s → (∀ a, Glob a → μ.read a = gl a) →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + (enc.length - 1) ≤ c.addr + 32 * c.size) →
    (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 20626 ω μ x 723 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN RD 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN (RD + 8) 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN (F + 120) 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          Rep (μ'.readN (F + 120) 232) μ'') ∧
      (∀ a, (F + 32) ≤ a → a < 4294967296 →
        (a < RD ∨ (RD + 16) ≤ a) → (a < (F + 120) ∨ (F + 352) ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, 4278050816 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 20626 ω μ x N

/-- **One element decodes, possibly allocating** (see the module doc), under any host fit for the
    allocator (`ElemOkAF`'s host-generic form). -/
def ElemOkAFG {X : Type} (env : HeapHost X) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program) (F RD N : Nat)
    (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ∀ (x : X) (ω : Regs) (μ : Memory) (ptr len v5 v6 : Nat) (s : State),
    ω[1] = UInt64.ofNat F → ω[5] = UInt64.ofNat (F + 120) → ω[6] = UInt64.ofNat RD →
    ω[7] = UInt64.ofNat 0 → μ.read F = enc.headD 0 →
    μ.readN RD 8 = Num.encodeLE 8 ptr → μ.readN (RD + 8) 8 = Num.encodeLE 8 len →
    enc.length - 1 ≤ len → len < 4294967296 → 65536 ≤ ptr → ptr + enc.length + 72 ≤ 4278050816 →
    μ.readN ptr (enc.length - 1) = enc.tail →
    (∀ a, ptr ≤ a → a < ptr + (enc.length - 1) → μ.readable a = true) →
    μ.readN (F + 48) 8 = Num.encodeLE 8 18 → μ.readN (F + 40) 8 = Num.encodeLE 8 v5 →
    μ.readN (F + 32) 8 = Num.encodeLE 8 v6 → v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    μ.readN 67476 100 = Tag.table → (∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true) →
    (∀ a, 4278050816 ≤ a → a < (F + 584) → μ.writable a = true) →
    (∀ a, RD ≤ a → a < (RD + 16) → μ.writable a = true) →
    HeapCtxC env.code pb S0 S1 μ s → (∀ a, Glob a → μ.read a = gl a) →
    (∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + (enc.length - 1) ≤ c.addr + 32 * c.size) →
    (∃ ω' μ' s', FreeStepsH p (env.rel cap) 20626 ω μ x 723 ω' μ' x N ∧
      ω'[1] = UInt64.ofNat (F + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN RD 8 = Num.encodeLE 8 (ptr + (enc.length - 1)) ∧
      μ'.readN (RD + 8) 8 = Num.encodeLE 8 (len - (enc.length - 1)) ∧
      (∃ W, W < 18446744073709551616 ∧ μ'.readN (F + 120) 8 = Num.encodeLE 8 W ∧
        W ≠ 18446744073709551614) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s' ∧ c.used = true ∧ ∀ d ∈ chunks s, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ'.read a) →
          Rep (μ'.readN (F + 120) 232) μ'') ∧
      (∀ a, (F + 32) ≤ a → a < 4294967296 →
        (a < RD ∨ (RD + 16) ≤ a) → (a < (F + 120) ∨ (F + 352) ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a) ∧ (∀ a, a < 196608 → μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧
      (∀ a, 4278050816 ≤ a → μ'.writable a = μ.writable a)) ∨
    ExhaustsG env cap pb p P 20626 ω μ x N

/-- `ElemOkAF` is `ElemOkAFG` for the refine contract (`refineHeap env`). -/
theorem ElemOkAF_iff {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {F RD N : Nat} {enc : List UInt8} {Rep : List UInt8 → Memory → Prop} :
    ElemOkAF env cap pb gl p P F RD N enc Rep ↔ ElemOkAFG (refineHeap env) cap pb gl p P F RD N enc Rep :=
  Iff.rfl

/-- **Every `ElemOkF` is an `ElemOkAFG`** that keeps the allocator's state: its writes, to the stack,
    the reader and the slot, are all above 2^31. -/
theorem ElemOkAFG.of_elemOkF {X : Type} {env : HeapHost X} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {enc : List UInt8} {Rep : List UInt8 → Prop} {F RD : Nat}
    (hL : Lay F RD) (h : ElemOkF p P F RD enc Rep) :
    ElemOkAFG env cap pb gl p P F RD 4000 enc (fun bs _ => Rep bs) := by
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H _ _
  obtain ⟨l1, l2, l3, l4⟩ := hL
  obtain ⟨ω', μ', run, e1, e5, e6, eR0, eR8, eW, eRep, efr, erd, ewr⟩ :=
    h X (env.rel cap) x ω μ ptr len v5 v6 h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay
      s0 s5 s6 hv5 hv6 tab rt ws wr
  have low : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha =>
    efr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  refine Or.inl ⟨ω', μ', s, run, e1, e5, e6, eR0, eR8, eW,
    { wf := H.wf, rep := H.rep.congr_lock H.wf H.hb0 H.hbT (fun a _ ha2 _ => low a ha2), fo := H.fo,
      lock := by rw [rdN_frame fun j hj => low _ (by omega)]; exact H.lock, hb0 := H.hb0, hbT := H.hbT,
      hA := H.hA, bd := H.bd, pages := ⟨ph, h48, hhb, HeapPages.of_eq hpg ewr, hHTs, hHT⟩, hSb := H.hSb,
      hS1 := H.hS1, st := fun a h1 h2 => by rw [ewr]; exact H.st a h1 h2,
      ro := fun a ha => by rw [ewr]; exact H.ro a ha },
    fun c hc _ => hc, fun c hc _ a ha => low a ?_, ⟨[], by simp, fun _ _ => eRep⟩,
    fun a h h0 h2 h3 => efr a h0 (Or.inr h) h2 h3, fun a ha => low a (by omega), fun a _ => erd a,
    fun a ha => low a (by unfold Glob at ha; omega), fun a _ => ewr a⟩
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  have := H.hbT
  unfold InData at ha
  omega


/-- **Every `ElemOkF` is an `ElemOkAF`** that keeps the allocator's state: its writes, to the stack,
    the reader and the slot, are all above 2^31. -/
theorem ElemOkAF.of_elemOkF {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {enc : List UInt8} {Rep : List UInt8 → Prop} {F RD : Nat}
    (hL : Lay F RD) (h : ElemOkF p P F RD enc Rep) :
    ElemOkAF env cap pb gl p P F RD 4000 enc (fun bs _ => Rep bs) :=
  ElemOkAFG.of_elemOkF (env := refineHeap env) hL h

/-! ## In refine's frame -/

/-- **One element decodes, possibly allocating**, in refine's frame: `ElemOkAF` at
    F = 4278057632, RD = 4278058648. -/
abbrev ElemOkA (env : RefineHost.Env) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program) (N : Nat)
    (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ElemOkAF env cap pb gl p P 4278057632 4278058648 N enc Rep

/-- **Every `ElemOk` is an `ElemOkA`**, in refine's frame. -/
theorem ElemOkA.of_elemOk {env : RefineHost.Env} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray} {P : Program}
    {enc : List UInt8} {Rep : List UInt8 → Prop} (h : ElemOk p P enc Rep) :
    ElemOkA env cap pb gl p P 4000 enc (fun bs _ => Rep bs) :=
  ElemOkAF.of_elemOkF lay_refine h

/-- `ElemOkA`'s host-generic form: `ElemOkAFG` at F = 4278057632, RD = 4278058648. -/
abbrev ElemOkAG {X : Type} (env : HeapHost X) (cap pb : Nat) (gl : Nat → UInt8) (p : ByteArray) (P : Program)
    (N : Nat) (enc : List UInt8) (Rep : List UInt8 → Memory → Prop) : Prop :=
  ElemOkAFG env cap pb gl p P 4278057632 4278058648 N enc Rep

theorem ElemOkAG.of_elemOk {X : Type} {env : HeapHost X} {cap pb : Nat} {gl : Nat → UInt8} {p : ByteArray}
    {P : Program} {enc : List UInt8} {Rep : List UInt8 → Prop} (h : ElemOk p P enc Rep) :
    ElemOkAG env cap pb gl p P 4000 enc (fun bs _ => Rep bs) :=
  ElemOkAFG.of_elemOkF lay_refine h

end Services.Bootstrap.Decode.LoopA
