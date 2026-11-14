import Services.Bootstrap.Encode.WriterGrow
import Services.Bootstrap.Encode.VecCore

/-!
# The writer with growth: the state between appends, and one append

The encoder's output `Vec<u8>` `{cap, ptr, len}` at v may grow on any append
(`WriterGrow.extend_any`). This file gives the pieces the arms are built from, for growth:

* `capBound`, `growGas`, `stepGas`, `encGas`: the capacity bound kept on the writer and the gas
  bounds (one growth costs at most `growGas` on top of an append without growth). They are named so that
  they can be swapped (e.g. for an amortised bound) in one place.
* `BufH … pre cap ptr s μ`: since the entry memory μ0 (writer state ptr0, len, allocator state s0), the
  octets `pre` were appended: the vector is `{cap, ptr, len + |pre|}`, its buffer an allocated chunk of
  the allocator state s holding the old len octets then `pre`, the context `HeapCtx` held for s, every
  other allocated chunk of s0 kept with its data, low memory, the allocator's globals and the access
  outside the heap kept, and memory at or above the bound B kept but for the vector.
* `SafeR`: a stretch kept by any append: on the stack at or above B, or in another allocated chunk.
* `extendH`: one call of `Vec<u8>::extend_from_slice` (58508) at any sp, for any n (no growth for n = 0),
  as a step of `BufH`, or a failed `realloc` (`ExhaustsW`).
* `StH` / `StDH`: `Fixed.St` / `VecCore.StD` with `BufH` (B = F) for the writer; `ext_stepH`,
  `ext_stepDH`, `scratchDH`, `heapDH` their appends; `StH.scratch`, `StDH.scratch` the scratch writes;
  `StH.slot` the value's octets.
-/

namespace Services.Bootstrap.Encode.GrowH

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX
  Services.Bootstrap.CodeA Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.VecU8 Services.Bootstrap.Decode.GrowOne
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-! ## Bounds -/

/-- The bound kept on the writer's capacity (2²⁸): with twice the output below it, a growth's request
    stays below `realloc_call`'s 2²⁵ units (`extend_any`'s `hbig`). -/
def capBound : Nat := 268435456

/-- The extra steps an append may take for a growth: `realloc` on a chunk of at most 2²⁵ units
    (64 · 2²⁵) and the grow path's own steps. -/
def growGas : Nat := 2147485088

/-- The gas of one append of n octets: as without growth (7·n + 360), and `growGas` when n > 0. -/
def stepGas (n : Nat) : Nat := 7 * n + 360 + growGas * min n 1

/-- The gas of one element's encoding `enc`: `EncOkMD`'s 2000·|enc| + 4000, and one growth per
    octet appended. -/
def encGas (enc : List UInt8) : Nat := 2000 * enc.length + 4000 + growGas * enc.length

/-! ## The writer's state -/

/-- **The writer since μ0**, the octets `pre` appended (see the module doc). B: memory at or above it is
    kept but for the vector v … v + 24. -/
structure BufH (env : RefineHost.Env) (pb S0 S1 B v len ptr0 : Nat) (s0 : State) (μ0 : Memory)
    (pre : List UInt8) (cap ptr : Nat) (s : State) (μ : Memory) : Prop where
  vS : v + 24 ≤ S1
  vc : μ.readN v 8 = Num.encodeLE 8 cap
  vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr
  vl : μ.readN (v + 16) 8 = Num.encodeLE 8 (len + pre.length)
  out : μ.readN ptr (len + pre.length) = μ0.readN ptr0 len ++ pre
  room : len + pre.length ≤ cap
  cpos : 0 < cap
  cb : cap ≤ capBound
  H : HeapCtx env pb S0 S1 μ s
  chunk : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 = ptr ∧ cap ≤ 32 * (c.size - 1)
  others : ∀ e ∈ chunks s0, e.used = true → e.addr + 32 ≠ ptr0 →
    e ∈ chunks s ∧ e.addr + 32 ≠ ptr ∧ ∀ a, InData e a → μ.read a = μ0.read a
  acc : ∀ a, (a < 196608 ∨ 4096 * pb ≤ a) → μ.readable a = μ0.readable a ∧ μ.writable a = μ0.writable a
  low : ∀ a, a < 196608 → μ.read a = μ0.read a
  glob : ∀ a, Glob a → μ.read a = μ0.read a
  hi : ∀ a, a < 4294967296 → B ≤ a → (a < v ∨ v + 24 ≤ a) → μ.read a = μ0.read a

/-- A stretch q … q + m that any append keeps: on the stack at or above B (and below S1), apart from the
    vector v, or in the data of an allocated chunk of s other than the buffer's (ptr). -/
def SafeR (s : State) (ptr B S1 v q m : Nat) : Prop :=
  (B ≤ q ∧ q + m ≤ S1 ∧ (q + m ≤ v ∨ v + 24 ≤ q)) ∨ HeapSrc s ptr q m

section
variable {env : RefineHost.Env} {pb S0 S1 B v len ptr0 : Nat} {s0 : State} {μ0 : Memory}
  {pre : List UInt8} {cap ptr : Nat} {s : State} {μ : Memory}

/-- The buffer lies in the heap, below 2³¹. -/
theorem BufH.buf_lt (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) :
    206896 ≤ ptr ∧ ptr + cap < 2147483648 := by
  obtain ⟨c, hc, hcu, hcp, hcc⟩ := W.chunk
  have := chunk_in W.H.wf hc hcu
  have := W.H.hb0; have := W.H.hbT; have := W.cpos
  omega

/-- **Writes in a stack stretch [lo, hi) below B and apart from the vector keep `BufH`.** -/
theorem BufH.frame (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) {μ' : Memory} (lo hi : Nat)
    (hlo : 2147483648 ≤ lo) (hhi : hi ≤ B) (hv : hi ≤ v ∨ v + 24 ≤ lo)
    (hk : ∀ a, a < 4294967296 → (a < lo ∨ hi ≤ a) → μ'.read a = μ.read a)
    (hrd : ∀ a, μ'.readable a = μ.readable a) (hwr : ∀ a, μ'.writable a = μ.writable a) :
    BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ' := by
  have hS1 := W.H.hS1
  have vS := W.vS
  obtain ⟨hp0, hp1⟩ := W.buf_lt
  have room := W.room
  have kl : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha => hk a (by omega) (Or.inl (by omega))
  refine ⟨vS, ?_, ?_, ?_, ?_, room, W.cpos, W.cb, ctx_high W.H kl hwr, W.chunk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact W.vc
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact W.vp
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact W.vl
  · rw [Memory.readN_congr (fun j hj => kl _ (by omega))]; exact W.out
  · intro e he heu hne
    obtain ⟨h1, h2, h3⟩ := W.others e he heu hne
    refine ⟨h1, h2, fun a ha => ?_⟩
    have := (chunk_in W.H.wf h1 heu).2.2
    have := W.H.hbT
    unfold InData at ha
    rw [kl a (by omega)]; exact h3 a ha
  · intro a ha; rw [hrd, hwr]; exact W.acc a ha
  · intro a ha; rw [kl a (by omega)]; exact W.low a ha
  · intro a ha; have hg := ha; unfold Glob at hg; rw [kl a (by omega)]; exact W.glob a ha
  · intro a h0 h1 h2; rw [hk a h0 (Or.inr (by omega))]; exact W.hi a h0 h1 h2

/-- A larger bound keeps less. -/
theorem BufH.mono (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) {B' : Nat} (h : B ≤ B') :
    BufH env pb S0 S1 B' v len ptr0 s0 μ0 pre cap ptr s μ :=
  { W with hi := fun a h0 h1 h2 => W.hi a h0 (by omega) h2 }

/-- The same octets, written differently. -/
theorem BufH.cast (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) {pre' : List UInt8}
    (h : pre = pre') : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre' cap ptr s μ := h ▸ W

/-- **A kept stretch reads as at μ0.** -/
theorem BufH.readN_safe (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) {q m : Nat}
    (h : SafeR s0 ptr0 B S1 v q m) : μ.readN q m = μ0.readN q m := by
  have hS1 := W.H.hS1
  rcases h with ⟨h1, h2, h3⟩ | ⟨e, he, heu, hne, h1, h2⟩
  · exact Memory.readN_congr (fun j hj => W.hi _ (by omega) (by omega) (by omega))
  · exact Memory.readN_congr (fun j hj => (W.others e he heu hne).2.2 _ ⟨by omega, by omega⟩)

/-- **A kept stretch is still kept** after the appends: `SafeR` for the current buffer and state. -/
theorem BufH.safe (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) {q m : Nat}
    (h : SafeR s0 ptr0 B S1 v q m) : SafeR s ptr B S1 v q m := by
  rcases h with h | ⟨e, he, heu, hne, h1, h2⟩
  · exact Or.inl h
  · obtain ⟨h1', h2', -⟩ := W.others e he heu hne
    exact Or.inr ⟨e, h1', heu, h2', h1, h2⟩

/-- A kept stretch is readable. -/
theorem BufH.safe_readable (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ) {q m : Nat}
    (hB : S0 ≤ B) (h : SafeR s ptr B S1 v q m) : ∀ a, q ≤ a → a < q + m → μ.readable a = true := by
  intro a h1 h2
  rcases h with ⟨b1, b2, -⟩ | ⟨e, he, heu, -, e1, e2⟩
  · exact Memory.readable_of_writable (W.H.st a (by omega) (by omega))
  · exact Memory.readable_of_writable (heap_writable W.H he heu ⟨by omega, by omega⟩)

/-- **Composing two stretches of appends**: `BufH` from μ0 to μ1 (`pre1`), then from μ1 to μ (`pre2`,
    with the writer as left at μ1), is `BufH` from μ0 for `pre1 ++ pre2`. -/
theorem BufH.trans (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ)
    {pre2 : List UInt8} {cap2 ptr2 : Nat} {s2 : State} {μ2 : Memory}
    (W2 : BufH env pb S0 S1 B v (len + pre.length) ptr s μ pre2 cap2 ptr2 s2 μ2) :
    BufH env pb S0 S1 B v len ptr0 s0 μ0 (pre ++ pre2) cap2 ptr2 s2 μ2 := by
  have hl : len + (pre ++ pre2).length = len + pre.length + pre2.length := by simp; omega
  refine ⟨W.vS, W2.vc, W2.vp, by rw [hl]; exact W2.vl, by rw [hl, W2.out, W.out, List.append_assoc],
    by rw [hl]; exact W2.room, W2.cpos, W2.cb, W2.H, W2.chunk, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he heu hne
    obtain ⟨h1, h2, h3⟩ := W.others e he heu hne
    obtain ⟨g1, g2, g3⟩ := W2.others e h1 heu h2
    exact ⟨g1, g2, fun a ha => (g3 a ha).trans (h3 a ha)⟩
  · intro a ha
    obtain ⟨a1, a2⟩ := W2.acc a ha
    obtain ⟨b1, b2⟩ := W.acc a ha
    exact ⟨a1.trans b1, a2.trans b2⟩
  · intro a ha; exact (W2.low a ha).trans (W.low a ha)
  · intro a ha; exact (W2.glob a ha).trans (W.glob a ha)
  · intro a h0 h1 h2; exact (W2.hi a h0 h1 h2).trans (W.hi a h0 h1 h2)

end

/-- **The writer at entry**: no octets appended yet. -/
theorem BufH.init {env : RefineHost.Env} {pb S0 S1 B v len cap ptr : Nat} {s : State} {μ : Memory}
    (vS : v + 24 ≤ S1) (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len) (hlc : len ≤ cap) (cpos : 0 < cap)
    (cb : cap ≤ capBound) (H : HeapCtx env pb S0 S1 μ s)
    (chunk : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 = ptr ∧ cap ≤ 32 * (c.size - 1)) :
    BufH env pb S0 S1 B v len ptr s μ [] cap ptr s μ :=
  ⟨vS, vc, vp, by simpa using vl, by simp, by simpa using hlc, cpos, cb, H, chunk,
    fun e he _ hne => ⟨he, hne, fun _ _ => rfl⟩, fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ _ _ => rfl⟩

/-! ## One append -/

/-- **One call of `Vec<u8>::extend_from_slice`** (58508) at stack pointer sp, returning to t, for the n
    octets at src: n = 0, or the octets on the stack at or above sp (apart from the vector), or in the data
    of an allocated chunk of s0 other than the entry buffer's (`HeapSrc`). Either the octets are appended
    (`BufH (pre ++ μ.readN src n)`), ω₀, ω₁, ω₅, ω₆ kept and memory at or above sp kept but for the
    vector; or the run reaches a failed `realloc` (`ExhaustsW`). The capacity stays within `capBound`
    while twice the output does. Gas `stepGas n`. -/
theorem extendH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 B v len ptr0 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8} {cap ptr : Nat} {s : State}
    (W : BufH env pb S0 S1 B v len ptr0 s0 μ0 pre cap ptr s μ)
    (sp src n ret t : Nat) (hsp : S0 + 424 ≤ sp ∧ 2147484072 ≤ sp ∧ sp % 8 = 0) (hB : sp ≤ B)
    (hv : sp ≤ v) (hS1 : S1 + 16 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hlen : 2 * (len + pre.length + n) ≤ capBound)
    (hsrc : n = 0 ∨ (sp ≤ src ∧ src + n ≤ S1 ∧ (src + n ≤ v ∨ v + 24 ≤ src)) ∨ HeapSrc s0 ptr0 src n) :
    (∃ cap' ptr' s' ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x t ω' μ' x (stepGas n) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      BufH env pb S0 S1 B v len ptr0 s0 μ0 (pre ++ μ.readN src n) cap' ptr' s' μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < v ∨ v + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (stepGas n) := by
  have vS := W.vS
  have hS0 := W.H.hSb
  have hst := W.H.st
  have room := W.room
  have cb := W.cb
  obtain ⟨hp0, hp1⟩ := W.buf_lt
  obtain ⟨c, hc, hcu, hcp, hcc⟩ := W.chunk
  have hcs : c.size ≤ 33554432 := by
    have := chunk_in W.H.wf hc hcu
    have := W.H.hb0
    omega
  unfold capBound at cb hlen
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- nothing to copy
    obtain ⟨ω', μ', run, e0, e1, e5, e6, el, efr, erd, ewr⟩ := Services.Bootstrap.Encode.Enc.extend_zero
      (p := p) (P := P) (R := refineContractK K env) x ω μ sp v cap (len + pre.length) ret t
      ⟨by omega, by omega, hsp.2.2⟩ h0 h1 h7 h9 room (by omega) W.vc W.vl (by omega) (Or.inr hv) hret hjt hbt
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega))
    have kv : ∀ a, v + 16 ≤ a → a < v + 24 → μ'.read a = μ.read a := fun a h1 h2 => by
      have e1 := Memory.read_of_readN el (a - (v + 16)) (by omega)
      have e2 := Memory.read_of_readN W.vl (a - (v + 16)) (by omega)
      rw [show v + 16 + (a - (v + 16)) = a by omega] at e1 e2
      rw [e1, e2]
    have hk : ∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → μ'.read a = μ.read a := fun a h0 h1 => by
      by_cases ha : v + 16 ≤ a ∧ a < v + 24
      · exact kv a ha.1 ha.2
      · exact efr a h0 h1 (by omega)
    have W' := W.frame (μ' := μ') (sp - 80) sp (by omega) hB (Or.inl hv) hk erd ewr
    refine Or.inl ⟨cap, ptr, s, ω', μ', run.mono (by unfold stepGas; omega), e0, e1, e5, e6,
      W'.cast (by simp [Memory.readN]), fun a h0 h1 _ => hk a h0 (Or.inr h1)⟩
  · have hsrc' : StackSrc sp v src n μ ∨ HeapSrc s ptr src n := by
      rcases hsrc with h | ⟨h1, h2, h3⟩ | ⟨e, he, heu, hne, h1, h2⟩
      · omega
      · exact Or.inl ⟨h1, by omega, h3, fun a b1 b2 =>
          Memory.readable_of_writable (hst a (by omega) (by omega))⟩
      · obtain ⟨g1, g2, -⟩ := W.others e he heu hne
        exact Or.inr ⟨e, g1, heu, g2, h1, h2⟩
    rcases extend_any env K hK1 hK x ω μ s c sp v src n cap ptr (len + pre.length) ret t pb S0 S1 W.H hc hcu hcp
        hcc W.cpos room ⟨by omega, by omega⟩ ⟨by omega, by omega, hsp.2.1, hsp.2.2⟩ ⟨hv, vS⟩ h0 h1 h7 h8 h9
        W.vc W.vp W.vl hret hjt hbt hsrc' with
      ⟨cap', r, s', ω', μ', run, e0, e1, e5, e6, ev, ev8, el, hroom', hcap', eo, ed, H', hd, oth, fresh, po,
        stk, low, gl, -⟩ | hx
    · have hlen' : (pre ++ μ.readN src n).length = pre.length + n := by simp [Memory.readN]
      refine Or.inl ⟨cap', r, s', ω', μ', run.mono (by unfold stepGas growGas; rw [Nat.min_eq_right hn]; omega),
        e0, e1, e5, e6, ⟨vS, ev, ev8, ?_, ?_, by rw [hlen']; omega, by omega, ?_, H', hd, ?_, ?_, ?_, ?_, ?_⟩,
        stk⟩
      · rw [hlen', ← Nat.add_assoc]; exact el
      · rw [hlen', ← Nat.add_assoc, Services.Bootstrap.Encode.Enc.readN_add', eo, ed, W.out, List.append_assoc]
      · rcases hcap' with h | ⟨h1, h2⟩
        · unfold capBound; omega
        · rw [h2]; unfold capBound; exact newCap_le _ _ _ _ (by omega) (by omega) (by omega)
      · intro e he heu hne
        obtain ⟨h1, h2, h3⟩ := W.others e he heu hne
        obtain ⟨g1, g3⟩ := oth e h1 heu h2
        refine ⟨g1, ?_, fun a ha => (g3 a ha).trans (h3 a ha)⟩
        rcases fresh with hr | hr
        · rw [hr]; exact h2
        · exact hr e h1 heu
      · intro a ha
        have e := po (a / pageSize) (by unfold pageSize; omega)
        obtain ⟨b1, b2⟩ := W.acc a ha
        refine ⟨?_, ?_⟩
        · unfold Memory.readable at b1 ⊢; rw [e]; exact b1
        · unfold Memory.writable at b2 ⊢; rw [e]; exact b2
      · intro a ha; rw [(low a ha).1]; exact W.low a ha
      · intro a ha; rw [gl a ha]; exact W.glob a ha
      · intro a h0 h1 h2; rw [stk a h0 (by omega) h2]; exact W.hi a h0 h1 h2
    · exact Or.inr (hx.mono (by unfold stepGas growGas; rw [Nat.min_eq_right hn]; omega))

/-! ## The state between appends in `Instruction::encode_to` -/

/-- The stack the arms of `Instruction::encode_to` (frame base F, callees down to F − D) need, under
    `HeapCtx`'s stack S0 … S1: room for a growth below the deepest call, and the vector v above F. -/
structure FrH (S0 S1 D F v : Nat) : Prop where
  hF8 : F % 8 = 0
  hFS0 : S0 + D + 424 ≤ F
  hF2 : 2147484072 + D ≤ F
  hFv : F ≤ v
  hvS1 : v + 24 ≤ S1
  hS1 : S1 + 16 < 4294967296

/-- **The state between appends, with growth**: `Fixed.St` with the writer given by `BufH` (bound F):
    ω₁ = F − 56, the caller's ω₀, ω₅, ω₆ saved at F − 8, F − 16, F − 24, and the octets `pre` appended
    since the entry memory μ0. -/
structure StH (env : RefineHost.Env) (pb S0 S1 F v len ptr0 ret r5 r6 : Nat) (s0 : State) (μ0 : Memory)
    (pre : List UInt8) (ω : Regs) (μ : Memory) : Prop where
  h1 : ω[1] = UInt64.ofNat (F - 56)
  w0 : μ.readN (F - 8) 8 = Num.encodeLE 8 ret
  w5 : μ.readN (F - 16) 8 = Num.encodeLE 8 r5
  w6 : μ.readN (F - 24) 8 = Num.encodeLE 8 r6
  buf : ∃ cap ptr s, BufH env pb S0 S1 F v len ptr0 s0 μ0 pre cap ptr s μ

/-- `StH` with the writer v saved at F − 40 (`VecCore.StD`). -/
structure StDH (env : RefineHost.Env) (pb S0 S1 F v len ptr0 ret r5 r6 : Nat) (s0 : State) (μ0 : Memory)
    (pre : List UInt8) (ω : Regs) (μ : Memory) : Prop extends
    StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ where
  sv : μ.readN (F - 40) 8 = Num.encodeLE 8 v

section
variable {env : RefineHost.Env} {pb S0 S1 F v len ptr0 ret r5 r6 D : Nat} {s0 : State} {μ0 : Memory}
  {pre : List UInt8} {ω : Regs} {μ : Memory}

theorem StH.cast (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) {pre' : List UInt8}
    (h : pre = pre') : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre' ω μ := h ▸ st

theorem StDH.cast (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) {pre' : List UInt8}
    (h : pre = pre') : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre' ω μ := h ▸ st

/-- **The value's octets are as at entry**, for a kept value slot. -/
theorem StH.slot (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) {S i m : Nat}
    (hS : SafeR s0 ptr0 F S1 v S 232) (him : i + m ≤ 232) : μ.readN (S + i) m = μ0.readN (S + i) m := by
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  refine W.readN_safe ?_
  rcases hS with ⟨h1, h2, h3⟩ | ⟨e, he, heu, hne, h1, h2⟩
  · exact Or.inl ⟨by omega, by omega, by omega⟩
  · exact Or.inr ⟨e, he, heu, hne, by omega, by omega⟩

/-- **Writes to the scratch [F − 56, F − 24)** (with ω₁ = F − 56) keep `StH`. -/
theorem StH.scratch (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (Fr : FrH S0 S1 D F v)
    {ω' : Regs} {μ' : Memory} (h1 : ω'[1] = UInt64.ofNat (F - 56))
    (hk : ∀ a, a < 4294967296 → (a < F - 56 ∨ F - 24 ≤ a) → μ'.read a = μ.read a)
    (hrd : ∀ a, μ'.readable a = μ.readable a) (hwr : ∀ a, μ'.writable a = μ.writable a) :
    StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω' μ' := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  refine ⟨h1, ?_, ?_, ?_, ⟨cap, ptr, s, W.frame (F - 56) (F - 24) (by omega) (by omega) (Or.inl (by omega)) hk
    hrd hwr⟩⟩
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.w0
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.w5
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.w6

/-- **Writes to the scratch [F − 56, F − 40) and [F − 32, F − 24)** keep `StDH`. -/
theorem StDH.scratch (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ) (Fr : FrH S0 S1 D F v)
    {ω' : Regs} {μ' : Memory} (h1 : ω'[1] = UInt64.ofNat (F - 56))
    (hk : ∀ a, a < 4294967296 → (a < F - 56 ∨ (F - 40 ≤ a ∧ a < F - 32) ∨ F - 24 ≤ a) → μ'.read a = μ.read a)
    (hrd : ∀ a, μ'.readable a = μ.readable a) (hwr : ∀ a, μ'.writable a = μ.writable a) :
    StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω' μ' := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1
  have hk' : ∀ a, a < 4294967296 → (a < F - 56 ∨ F - 24 ≤ a) → μ'.read a = μ.read a :=
    fun a h0 h1 => hk a h0 (by omega)
  exact ⟨st.toStH.scratch Fr h1 hk' hrd hwr,
    by rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.sv⟩

end

/-- **One append in an arm** (58508, returning to e) for the n octets at src: n = 0, or the octets in the
    arm's frame or above (from F − 56, below S1, apart from the vector), or in the data of an allocated
    chunk of s0 other than the entry buffer's. `StH pre` becomes `StH (pre ++ μ.readN src n)`, the frame
    [F − 56, F) and ω₅, ω₆ kept; or a failed `realloc` (`ExhaustsW`). The callee frames reach F − 136. -/
theorem ext_stepH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (st : StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (src n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hlen : 2 * (len + pre.length + n) ≤ capBound)
    (hsrc : n = 0 ∨ (F - 56 ≤ src ∧ src + n ≤ S1 ∧ (src + n ≤ v ∨ v + 24 ≤ src)) ∨ HeapSrc s0 ptr0 src n) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x e ω' μ' x (stepGas n) ∧
      StH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ.readN src n) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (stepGas n) := by
  have := Fr.hF8; have := Fr.hFS0; have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1
  obtain ⟨cap, ptr, s, W⟩ := st.buf
  rcases extendH env K hK1 hK x ω μ W (F - 56) src n r e ⟨by omega, by omega, by omega⟩ (by omega) (by omega)
      Fr.hS1 h0 st.h1 h7 h8 h9 hr hje hbe hlen hsrc with
    ⟨cap', ptr', s', ω', μ', run, e0, e1, e5, e6, W', kF⟩ | hx
  · have kF' : ∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a := fun a h1 h2 =>
      kF a (by omega) h1 (Or.inl (by omega))
    refine Or.inl ⟨ω', μ', run, ⟨e1, ?_, ?_, ?_, ⟨cap', ptr', s', W'⟩⟩, e5, e6, kF'⟩
    · rw [Memory.readN_congr (fun j hj => kF' _ (by omega) (by omega))]; exact st.w0
    · rw [Memory.readN_congr (fun j hj => kF' _ (by omega) (by omega))]; exact st.w5
    · rw [Memory.readN_congr (fun j hj => kF' _ (by omega) (by omega))]; exact st.w6
  · exact Or.inr hx

/-- `ext_stepH` for `StDH`: the writer saved at F − 40 is kept. -/
theorem ext_stepDH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (src n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hlen : 2 * (len + pre.length + n) ≤ capBound)
    (hsrc : n = 0 ∨ (F - 56 ≤ src ∧ src + n ≤ S1 ∧ (src + n ≤ v ∨ v + 24 ≤ src)) ∨ HeapSrc s0 ptr0 src n) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x e ω' μ' x (stepGas n) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ μ.readN src n) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (stepGas n) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1
  rcases ext_stepH env K hK1 hK x ω μ Fr hD st.toStH src n r e h0 h7 h8 h9 hr hje hbe hlen hsrc with
    ⟨ω', μ', run, st', e5, e6, kF⟩ | hx
  · exact Or.inl ⟨ω', μ', run, ⟨st', by rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.sv⟩,
      e5, e6, kF⟩
  · exact Or.inr hx

/-- **An append from the scratch word** F − 32 (`VariantsVec.scratchD` with growth): k ≤ 8 octets `bs`. -/
theorem scratchDH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (bs : List UInt8) (k r e : Nat) (hk : bs.length = k) (hk8 : k ≤ 8)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat (F - 56 + 24))
    (h9 : ω[9] = UInt64.ofNat k) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hlen : 2 * (len + pre.length + k) ≤ capBound)
    (hbs : μ.readN (F - 56 + 24) k = bs) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x e ω' μ' x (stepGas k) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ bs) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (stepGas k) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1
  rcases ext_stepDH env K hK1 hK x ω μ Fr hD st (F - 56 + 24) k r e h0 h7 h8 h9 hr hje hbe hlen
      (Or.inr (Or.inl ⟨by omega, by omega, Or.inl (by omega)⟩)) with
    ⟨ω', μ', run, st', e5, e6, kF⟩ | hx
  · rw [hbs] at st'; exact Or.inl ⟨ω', μ', run, st', e5, e6, kF⟩
  · exact Or.inr hx

/-- **The heap octets of a `Vec<u8>` field** (`VecCore.heapD` with growth): the n octets at q, kept by the
    appends (`SafeR` at entry, e.g. in another allocated chunk), as at entry: `StDH (pre ++ bytes)`. -/
theorem heapDH {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : RefineHost.Env) (K : Nat) (hK1 : 134217728 ≤ K) (hK : K < 18446744073709551616)
    (x : RefineCtx) (ω : Regs) (μ : Memory)
    {pb S0 S1 D F v len ptr0 ret r5 r6 : Nat} {s0 : State} {μ0 : Memory} {pre bytes : List UInt8}
    (Fr : FrH S0 S1 D F v) (hD : 136 ≤ D) (st : StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 pre ω μ)
    (q n r e : Nat) (hbn : bytes.length = n) (hb : μ0.readN q n = bytes)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat q)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hlen : 2 * (len + pre.length + n) ≤ capBound)
    (hsrc : n = 0 ∨ SafeR s0 ptr0 F S1 v q n) :
    (∃ ω' μ', FreeStepsH p (refineContractK K env) 58508 ω μ x e ω' μ' x (stepGas n) ∧
      StDH env pb S0 S1 F v len ptr0 ret r5 r6 s0 μ0 (pre ++ bytes) ω' μ' ∧ ω'[5] = ω[5] ∧
      ω'[6] = ω[6] ∧ (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a)) ∨
    ExhaustsW env K pb p P 58508 ω μ x (stepGas n) := by
  have := Fr.hF2; have := Fr.hFv; have := Fr.hvS1; have := Fr.hS1
  have hq : μ.readN q n = bytes := by
    rcases hsrc with rfl | h
    · rw [← hb]; simp [Memory.readN]
    · obtain ⟨cap, ptr, s, W⟩ := st.buf
      rw [W.readN_safe h, hb]
  rcases ext_stepDH env K hK1 hK x ω μ Fr hD st q n r e h0 h7 h8 h9 hr hje hbe hlen
      (hsrc.elim Or.inl (fun h => Or.inr (h.elim (fun h => Or.inl ⟨by omega, h.2⟩) Or.inr))) with
    ⟨ω', μ', run, st', e5, e6, kF⟩ | hx
  · rw [hq] at st'; exact Or.inl ⟨ω', μ', run, st', e5, e6, kF⟩
  · exact Or.inr hx

end Services.Bootstrap.Encode.GrowH
