import Services.Bootstrap.Decode.LoopA

/-!
# One pass of the decode loop, for elements that may allocate

`InvA`: the loop's invariant `Inv` with the allocator's context (`HeapCtx`), the payload and the
buffer inside allocated chunks `cp` and `cb`, and each decoded value's property holding for every
memory that keeps the data of some allocated chunks other than `cb`. `passA`: from `InvA` after k
elements, element k decodes through its `ElemOkA`, and the loop reaches its next pass (or its exit)
with `InvA` after k + 1, or the run reaches a failed allocation.
-/

namespace Services.Bootstrap.Decode.LoopA

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.Loop Services.Bootstrap.Decode.HeapCtx
open Services.Bootstrap.DecodeLoop (rdN_of)

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Writes above 2^31 keep the allocator's context. -/
theorem heap_of_high {env : RefineHost.Env} {pb : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) (hr : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (hw : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  exact ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT (fun a _ ha2 _ => hr a ha2), H.fo,
    by rw [rdN_frame fun j hj => hr _ (by omega)]; exact H.lock, H.hb0, H.hbT, H.hA, H.bd,
    ⟨ph, h48, hhb, HeapPages.of_eq hpg hw, hHTs, hHT⟩, H.hSb, H.hS1, fun a h1 h2 => by rw [hw]; exact H.st a h1 h2,
    fun a ha => by rw [hw]; exact H.ro a ha⟩

/-- Writes inside an allocated chunk's data, or above 2^31, keep the allocator's context. -/
theorem heap_of_data {env : RefineHost.Env} {pb : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s)
    (hr : ∀ a, a < 2147483648 → (a < c.addr + 32 ∨ c.addr + 32 * c.size ≤ a) → μ'.read a = μ.read a)
    (hw : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  have := H.hb0
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  obtain ⟨ph, h48, hhb, hpg, hHTs, hHT⟩ := H.pages
  exact ⟨H.wf, HeapFrame.Rep.congr_data H.rep H.wf H.hb0 H.hbT hc (fun a h1 h2 => hr a h1 (by omega)), H.fo,
    by rw [rdN_frame fun j hj => hr _ (by omega) (by omega)]; exact H.lock, H.hb0, H.hbT, H.hA, H.bd,
    ⟨ph, h48, hhb, HeapPages.of_eq hpg hw, hHTs, hHT⟩, H.hSb, H.hS1, fun a h1 h2 => by rw [hw]; exact H.st a h1 h2,
    fun a ha => by rw [hw]; exact H.ro a ha⟩

/-- Distinct chunks' data are apart. -/
theorem InData.apart {s : State} (hwf : WF s) {c d : Chunk} (hc : c ∈ chunks s) (hd : d ∈ chunks s)
    (hne : d ≠ c) {a : Nat} (ha : InData c a) : ¬ InData d a := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  intro hb
  unfold InData at ha hb
  rcases HeapFrame.Tiles.disjoint ht c hc d hd (Ne.symm hne) with h | h <;> omega

/-- **The loop's invariant, with the allocator** (see the module doc). -/
structure InvAF (env : RefineHost.Env) (pb : Nat) (F RD P0 Lt : Nat) (es : List (List UInt8))
    (reps : Nat → List UInt8 → Memory → Prop) (k B : Nat) (cp cb : Chunk) (ω : Regs) (μ : Memory)
    (s : State) : Prop where
  r1 : ω[1] = UInt64.ofNat (F + 56)
  r5 : ω[5] = UInt64.ofNat (es.length - k)
  m24 : μ.readN (F + 80) 8 = Num.encodeLE 8 RD
  m40 : μ.readN (F + 96) 8 = Num.encodeLE 8 es.length
  m48 : μ.readN (F + 104) 8 = Num.encodeLE 8 B
  m56 : μ.readN (F + 112) 8 = Num.encodeLE 8 k
  rP : μ.readN RD 8 = Num.encodeLE 8 (P0 + off es k)
  rL : μ.readN (RD + 8) 8 = Num.encodeLE 8 (Lt - off es k)
  pay : μ.readN P0 es.flatten.length = es.flatten
  tab : μ.readN 67476 100 = Tag.table
  el : ∀ j, j < k → ∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks s ∧ c.used = true ∧ c ≠ cb) ∧
    ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InData c a → μ''.read a = μ.read a) →
      reps j (μ.readN (B + 232 * j) 232) μ''
  ws : ∀ a, 4278050816 ≤ a → a < (F + 584) → μ.writable a = true
  wr : ∀ a, RD ≤ a → a < (RD + 16) → μ.writable a = true
  rt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true
  heap : HeapCtx env pb S0 S1 μ s
  cpm : cp ∈ chunks s ∧ cp.used = true
  cpd : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → InData cp a
  cbm : cb ∈ chunks s ∧ cb.used = true
  cbd : ∀ a, B ≤ a → a < B + 232 * es.length → InData cb a

/-- What a pass may change: above the loop's frame ((F + 584)), only the reader; among the allocated
    chunks' data, only the buffer's octets; nothing below 196608; and the access of nothing from the
    stack's bottom up. The globals between the allocator's lock and the allocator (`Glob`) keep their
    values. -/
def FrameAF (F RD : Nat) (n B : Nat) (s : State) (μ : Memory) (s' : State) (μ' : Memory) : Prop :=
  (∀ a, (F + 584) ≤ a → a < 4294967296 →
    (a < RD ∨ (RD + 16) ≤ a) → μ'.read a = μ.read a) ∧
  (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
  (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → (a < B ∨ B + 232 * n ≤ a) → μ'.read a = μ.read a) ∧
  (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
  (∀ a, Glob a → μ'.read a = μ.read a) ∧
  (∀ a, 4278050816 ≤ a → μ'.writable a = μ.writable a)

/-- **One pass, with the allocator** (see the module doc). -/
theorem passAF {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb N : Nat) (gl : Nat → UInt8)
    (F RD P0 Lt : Nat)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    (es : List (List UInt8)) (reps : Nat → List UInt8 → Memory → Prop) (k B : Nat) (cp cb : Chunk)
    (hk : k < es.length) (ok : OkF F RD P0 Lt es B)
    (hel : ElemOkAF env cap pb gl p P F RD N es[k] (reps k))
    (h : InvAF env pb F RD P0 Lt es reps k B cp cb ω μ s) (hg : ∀ a, Glob a → μ.read a = gl a) :
    (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 680 ω μ x (if k + 1 < es.length then 680 else 562)
      ω' μ' x (N + 1700) ∧ InvAF env pb F RD P0 Lt es reps (k + 1) B cp cb ω' μ' s' ∧ FrameAF F RD es.length B s μ s' μ') ∨
    Exhausts env cap pb p P 680 ω μ x (N + 1700) := by
  obtain ⟨hn, hB1, hB2, hB3, hne, hP0, hLt, hLt', hF1, hF8, hRD1, hRD2⟩ := ok
  obtain ⟨r1, r5, m24, m40, m48, m56, rP, rL, pay, tab, el, ws, wr, rt, heap, ⟨hcp, hcpu⟩, cpd, ⟨hcb, hcbu⟩,
    cbd⟩ := h
  have wb : ∀ a, B ≤ a → a < B + 232 * es.length → μ.writable a = true := fun a h1 h2 =>
    heap_writable_data heap hcb hcbu (cbd a h1 h2)
  have rp : ∀ a, P0 ≤ a → a < P0 + es.flatten.length → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (heap_writable_data heap hcp hcpu (cpd a h1 h2))
  have hL := hne k hk
  have hoff := off_lt es k hk
  have offk1 := off_succ es k hk
  have offle := off_le es (k + 1)
  -- element k in the payload
  have ek : μ.readN (P0 + off es k) es[k].length = es[k] := by
    rw [readN_sub μ P0 _ _ _ _ pay hoff, flatten_at es k hk]
  have ek0 : μ.read (P0 + off es k) = es[k].headD 0 := read_head μ _ _ _ ek (by omega)
  have ekt : μ.readN (P0 + off es k + 1) (es[k].length - 1) = es[k].tail := by
    rw [readN_sub μ _ _ 1 _ _ ek (by omega), List.drop_one, List.take_of_length_le (by simp)]
  -- S1
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, as0, as5, as6, afr, ard, awr⟩ :=
    LoopF.s1F (p := p) (P := P) (R := refineContractK cap env) x ω μ F RD ⟨by omega, by omega⟩ (by omega) r1 m24
      (fun a h1 h2 => ws a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (ws a (by omega) (by omega)))
  have afr' : ∀ a, (decide (a < 4294967296) && !(decide (F ≤ a ∧ a < (F + 56)))) = true → μ1.read a = μ.read a :=
    fun a ha => afr a (by fr_conv) (by fr_conv)
  clear afr
  -- the tag
  obtain ⟨ω2, μ2, run2, ok2⟩ := read_ok (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 930 20626
    F RD F (P0 + off es k) (Lt - off es k) 1 a0 a1 a7 a8 a9
    (by omega) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_464]) bs_20626 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wr a h1 h2)
    (fun a h1 h2 => by rw [awr]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [ard]; exact rp a (by omega) (by omega))
    (by rw [Memory.readN_congr (fun j hj => afr' _ (by fr_conv))]; exact rP)
    (by rw [Memory.readN_congr (fun j hj => afr' _ (by fr_conv))]; exact rL)
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b12, b7, bR0, bR8, bbuf, bfr, brd, bwr⟩ := ok2
  have bfr' : ∀ a, (decide (a < 4294967296) && !(decide ((F - 88) ≤ a ∧ a < F)) && !(decide (RD ≤ a ∧ a < (RD + 16))) && !(decide (F ≤ a ∧ a < (F + 1)))) = true →
      μ2.read a = μ1.read a := fun a ha => bfr a (by fr_conv) (by fr_conv) (by fr_conv) (by fr_conv)
  clear bfr
  have tag2 : μ2.read F = es[k].headD 0 := by
    have := congrArg List.head? bbuf
    simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.head?_cons, Option.some.injEq, Nat.add_zero] at this
    rw [this, afr' _ (by fr_conv)]
    exact ek0
  have low2 : ∀ a, a < 2147483648 → μ2.read a = μ.read a := fun a ha =>
    (bfr' a (by fr_conv)).trans (afr' a (by fr_conv))
  have heap2 : HeapCtx env pb S0 S1 μ2 s := heap_of_high heap low2 (fun a => by rw [bwr, awr])
  -- the element
  have v5 : (ω[5]).toNat = es.length - k := by rw [r5]; simp; omega
  have cplo := cpd (P0 + off es k) (by omega) (by omega)
  have cphi := cpd (P0 + off es k + es[k].length - 1) (by omega) (by omega)
  unfold InData at cplo cphi
  rcases hel x ω2 μ2 (P0 + off es k + 1) (Lt - off es k - 1) (es.length - k)
      (ω[6]).toNat s (b1.trans a1) (b5.trans a5) (b6.trans a6) b7 tag2 bR0 bR8 (by omega) (by omega) (by omega)
      (by omega)
      (by rw [Memory.readN_congr (fun j hj => low2 _ (by omega))]; exact ekt)
      (fun a h1 h2 => by rw [brd, ard]; exact rp a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv))]; exact as0)
      (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv)), as5, v5])
      (by rw [Memory.readN_congr (fun j hj => bfr' _ (by fr_conv))]; exact as6)
      (by omega) (UInt64.toNat_lt _)
      (by rw [Memory.readN_congr (fun j hj => low2 _ (by omega))]; exact tab)
      (fun a h1 h2 => by rw [brd, ard]; exact rt a h1 h2)
      (fun a h1 h2 => by rw [bwr, awr]; exact ws a h1 h2)
      (fun a h1 h2 => by rw [bwr, awr]; exact wr a h1 h2)
      heap2 (fun a ha => by have hg' := ha; unfold Glob at hg'; rw [low2 a (by omega)]; exact hg a ha)
      ⟨cp, hcp, hcpu, by omega, by omega⟩ with hs | hx
  rotate_left
  · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))
  obtain ⟨ω3, μ3, s', run3, c1, c5, c6, cR0, cR8, ⟨W, hW, cW, cne⟩, heap3, keepU, keepD, ⟨cs, hcs, crep⟩,
    cfr, clow, clowr, cglob, cwr⟩ := hs
  have cfr' : ∀ a, (F + 32) ≤ a → (decide (a < 4294967296) && !(decide (RD ≤ a ∧ a < (RD + 16))) && !(decide ((F + 120) ≤ a ∧ a < (F + 352)))) = true →
      μ3.read a = μ2.read a := fun a h0 ha => cfr a h0 (by fr_conv) (by fr_conv) (by fr_conv)
  clear cfr
  have wr3 : ∀ a, 4278050816 ≤ a → μ3.writable a = μ.writable a := fun a h => by rw [cwr a h, bwr, awr]
  have hcb' := keepU cb hcb hcbu
  have hcp' := keepU cp hcp hcpu
  -- S3 and the first move
  obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9⟩ := LoopF.g3F (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3
    F W ⟨by omega, by omega⟩ c1 cW hW cne
    (fun a h1 h2 => Memory.readable_of_writable (by rw [wr3 a (by omega)]; exact ws a (by omega) (by omega)))
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, ecp, efr, erd, ewr⟩ := memcpy_big_aligned (p := p) (P := P)
    (R := refineContractK cap env)
    x ω4 μ3 20 749 (F + 56) (F + 352) (F + 120) 232 d0 d1 d7 d8 d9 (by omega)
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_9]) bs_749 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (by rw [wr3 a (by omega)]; exact ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr3 a (by omega)]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr3 a (by omega)]; exact ws a (by omega) (by omega))
  have efr' : ∀ a, (decide (a < 4294967296) && !(decide ((F + 352) ≤ a ∧ a < (F + 584))) && !(decide ((F + 8) ≤ a ∧ a < (F + 56)))) = true → μ5.read a = μ3.read a :=
    fun a ha => efr a (by fr_conv) (by fr_conv) (by fr_conv)
  clear efr
  -- S4 and the second move
  have keep : ∀ a, (F + 80) ≤ a → a < (F + 120) → μ5.read a = μ.read a := fun a h1 h2 =>
    (efr' a (by fr_conv)).trans ((cfr' a (by omega) (by fr_conv)).trans ((bfr' a (by fr_conv)).trans
      (afr' a (by fr_conv))))
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, f8, f9, ffr, frd, fwr⟩ := LoopF.s4F (p := p) (P := P)
    (R := refineContractK cap env)
    x ω5 μ5 F k es.length B ⟨by omega, by omega⟩ hk (by omega) (by omega) e1
    (by rw [Memory.readN_congr (fun j hj => keep _ (by omega) (by omega))]; exact m40)
    (by rw [Memory.readN_congr (fun j hj => keep _ (by omega) (by omega))]; exact m48)
    (by rw [Memory.readN_congr (fun j hj => keep _ (by omega) (by omega))]; exact m56)
    (fun a h1 h2 => by rw [ewr, wr3 a (by omega)]; exact ws a (by omega) (by omega))
    (fun a h1 h2 => Memory.readable_of_writable (by rw [ewr, wr3 a (by omega)]; exact ws a (by omega) (by omega)))
  have ffr' : ∀ a, (decide (a < 4294967296) && !(decide ((F + 88) ≤ a ∧ a < (F + 96)))) = true → μ6.read a = μ5.read a :=
    fun a ha => ffr a (by fr_conv) (by fr_conv)
  clear ffr
  obtain ⟨ω7, μ7, run7, g0, g1, g5, g6, gcp, gfr, grd, gwr⟩ := memcpy_big_aligned (p := p) (P := P)
    (R := refineContractK cap env)
    x ω6 μ6 16 668 (F + 56) (B + 232 * k) (F + 352) 232 f0 f1 f7 f8 f9 (by omega)
    (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_7]) bs_668 (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (by rw [fwr, ewr, wr3 a (by omega)]; exact ws a (by omega) (by omega)))
    (fun a h1 h2 => by rw [fwr, ewr]; exact heap_writable_data heap3 hcb' hcbu (cbd a (by omega) (by omega)))
    (fun a h1 h2 => by rw [fwr, ewr, wr3 a (by omega)]; exact ws a (by omega) (by omega))
  have gfr' : ∀ a, (decide (a < 4294967296) && !(decide (B + 232 * k ≤ a ∧ a < B + 232 * k + 232)) &&
      !(decide ((F + 8) ≤ a ∧ a < (F + 56)))) = true → μ7.read a = μ6.read a :=
    fun a ha => gfr a (by fr_conv) (by fr_conv) (by fr_conv)
  clear gfr
  -- the slot holds the element's value
  have slot : μ7.readN (B + 232 * k) 232 = μ3.readN (F + 120) 232 := by
    rw [gcp, Memory.readN_congr (fun j hj => ffr' _ (by fr_conv)), ecp]
  -- the slot lies in cb's data
  have slotlo := cbd (B + 232 * k) (by omega) (by omega)
  have slothi := cbd (B + 232 * k + 231) (by omega) (by omega)
  unfold InData at slotlo slothi
  -- after the element, below 2^31 only the slot changed
  have low37 : ∀ a, a < 2147483648 → (a < B + 232 * k ∨ B + 232 * k + 232 ≤ a) → μ7.read a = μ3.read a :=
    fun a h0 h1 => (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans (efr' a (by fr_conv)))
  -- everything above 2^31 outside the stack and the reader is as at the start
  have backH : ∀ a, (F + 584) ≤ a → a < 4294967296 →
      (a < RD ∨ (RD + 16) ≤ a) → μ7.read a = μ.read a := fun a h h0 h2 =>
    (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans ((efr' a (by fr_conv)).trans
      ((cfr' a (by omega) (by fr_conv)).trans ((bfr' a (by fr_conv)).trans (afr' a (by fr_conv))))))
  -- an allocated chunk's data, off the slot, is as at the start
  have backD : ∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → (a < B + 232 * k ∨ B + 232 * k + 232 ≤ a) →
      μ7.read a = μ.read a := fun c hc hu a ha hs => by
    have hm := heap.wf.2.2.2.1
    unfold TilesOk at hm
    have := hm.mem_lt c hc
    have := heap.hbT
    have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
    unfold InData at ha
    rw [low37 a (by omega) hs, keepD c hc hu a ⟨ha.1, ha.2⟩]
    exact low2 a (by omega)
  have backL : ∀ a, a < 196608 → μ7.read a = μ.read a := fun a ha => by
    rw [low37 a (by omega) (by omega), clow a ha]; exact low2 a (by omega)
  have backG : ∀ a, Glob a → μ7.read a = μ.read a := fun a ha => by
    have hg := ha; unfold Glob at hg
    rw [low37 a (by omega) (by omega), cglob a ha]; exact low2 a (by omega)
  have q6 : ω7[6] = UInt64.ofNat k := g6.trans f6
  have q5 : ω7[5] = UInt64.ofNat (es.length - k) := g5.trans (f5.trans (e5.trans (d5.trans c5)))
  have q1 : ω7[1] = UInt64.ofNat (F + 56) := g1
  have hrdL : ∀ a, a < 196608 → μ7.readable a = μ.readable a := fun a ha => by
    rw [grd, frd, erd, clowr a ha, brd, ard]
  have hwrq : ∀ a, 4278050816 ≤ a → μ7.writable a = μ.writable a := fun a ha => by
    rw [gwr, fwr, ewr, wr3 a ha]
  have hwr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [gwr, fwr, ewr]
  -- the reader, after the element
  have rd7 : ∀ a, RD ≤ a → a < (RD + 16) → μ7.read a = μ3.read a := fun a h1 h2 =>
    (gfr' a (by fr_conv)).trans ((ffr' a (by fr_conv)).trans (efr' a (by fr_conv)))
  -- the allocator's context after the moves
  have heap7 : HeapCtx env pb S0 S1 μ7 s' := heap_of_data heap3 hcb'
    (fun a h0 h1 => low37 a h0 (by omega)) hwr73
  -- S5: count it, and loop or leave
  have post : ∀ (t : Nat) (ω8 : Regs), FreeStepsH p (refineContractK cap env) 668 ω7 μ7 x t ω8
      (μ7.writeN (F + 112) (Num.encodeLE 8 (k + 1))) x 4 →
      ω8[1] = UInt64.ofNat (F + 56) → ω8[5] = UInt64.ofNat (es.length - (k + 1)) →
      (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 680 ω μ x t ω' μ' x (N + 1700) ∧
        InvAF env pb F RD P0 Lt es reps (k + 1) B cp cb ω' μ' s' ∧ FrameAF F RD es.length B s μ s' μ') := by
    intro t ω8 run8 h1' h5'
    have wlow : ∀ a, a < 2147483648 → (μ7.writeN (F + 112) (Num.encodeLE 8 (k + 1))).read a = μ7.read a :=
      fun a ha => Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)
    refine ⟨ω8, _, s', (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans (run7.trans
      run8))))))).mono (by omega),
      ⟨h1', h5', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hcp', hcpu⟩, cpd, ⟨hcb', hcbu⟩, cbd⟩,
      ⟨?_, keepU, ?_, ?_, ?_, ?_⟩⟩
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega),
        Memory.readN_congr (fun j hj => (gfr' _ (by fr_conv)).trans ((ffr' _ (by fr_conv)).trans (keep _ (by omega) (by omega))))]; exact m24
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega),
        Memory.readN_congr (fun j hj => (gfr' _ (by fr_conv)).trans ((ffr' _ (by fr_conv)).trans (keep _ (by omega) (by omega))))]; exact m40
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega),
        Memory.readN_congr (fun j hj => (gfr' _ (by fr_conv)).trans ((ffr' _ (by fr_conv)).trans (keep _ (by omega) (by omega))))]; exact m48
    · exact Memory.readN_writeN_same _ _ _ _ (Num.length_encodeLE _ _) (by simp [two32] <;> omega)
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega),
        Memory.readN_congr (fun j hj => rd7 _ (by omega) (by omega)), cR0, offk1]
      congr 1; omega
    · rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega),
        Memory.readN_congr (fun j hj => rd7 _ (by omega) (by omega)), cR8, offk1]
      congr 1; omega
    · rw [Memory.readN_congr (fun j hj => (wlow _ (by omega)).trans
        (backD cp hcp hcpu _ (cpd _ (by omega) (by omega)) (by omega)))]; exact pay
    · rw [Memory.readN_congr (fun j hj => (wlow _ (by omega)).trans (backL _ (by omega)))]; exact tab
    · intro j hj
      rcases Nat.lt_or_ge j k with hj' | hj'
      · obtain ⟨cs', hcs', hrep'⟩ := el j hj'
        refine ⟨cs', fun c hc => ⟨keepU c (hcs' c hc).1 (hcs' c hc).2.1, (hcs' c hc).2.1, (hcs' c hc).2.2⟩,
          fun μ'' hag => ?_⟩
        have e1 : (μ7.writeN (F + 112) (Num.encodeLE 8 (k + 1))).readN (B + 232 * j) 232 =
            μ.readN (B + 232 * j) 232 := by
          rw [Memory.readN_congr (fun i hi => (wlow _ (by omega)).trans
            (backD cb hcb hcbu _ (cbd _ (by omega) (by omega)) (by omega)))]
        rw [e1]
        refine hrep' μ'' (fun c hc a ha => (hag c hc a ha).trans ?_)
        have hcm := hcs' c hc
        have hna := InData.apart heap.wf hcm.1 hcb hcm.2.2.symm ha
        have hd := ha
        unfold InData at hna hd
        have hm := heap.wf.2.2.2.1
        unfold TilesOk at hm
        have := hm.mem_lt c hcm.1
        have := heap.hbT
        have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
        exact (wlow a (by omega)).trans (backD c hcm.1 hcm.2.1 a ha (by omega))
      · have hjk : j = k := by omega
        subst hjk
        refine ⟨cs, fun c hc => ⟨(hcs c hc).1, (hcs c hc).2.1, fun e => (hcs c hc).2.2 cb hcb hcbu e.symm⟩,
          fun μ'' hag => ?_⟩
        have e1 : (μ7.writeN (F + 112) (Num.encodeLE 8 (j + 1))).readN (B + 232 * j) 232 =
            μ3.readN (F + 120) 232 := by
          rw [Memory.readN_congr (fun i hi => wlow _ (by omega)), slot]
        rw [e1]
        refine crep μ'' (fun c hc a ha => (hag c hc a ha).trans ?_)
        have hcm := hcs c hc
        have hne' : cb ≠ c := (hcm.2.2 cb hcb hcbu)
        have hna := InData.apart heap3.wf hcm.1 hcb' hne' ha
        unfold InData at hna
        have hd := ha
        unfold InData at hd
        have hm := heap3.wf.2.2.2.1
        unfold TilesOk at hm
        have := hm.mem_lt c hcm.1
        have := heap3.hbT
        have htop : s'.top = s'.base + 1073741824 := by unfold State.top; rw [maxSize_val]
        exact (wlow a (by omega)).trans (low37 a (by omega) (by omega))
    · intro a h1 h2; rw [Memory.writable_writeN, hwrq a (by omega)]; exact ws a h1 h2
    · intro a h1 h2; rw [Memory.writable_writeN, hwrq a (by omega)]; exact wr a h1 h2
    · intro a h1 h2; rw [Memory.readable_writeN, hrdL a (by omega)]; exact rt a h1 h2
    · exact heap_of_high heap7 wlow (fun a => Memory.writable_writeN _ _ _ _)
    · intro a h h0 h2
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp <;> omega) (by simp [two32] <;> omega) (by simp [two32] <;> omega)]
      exact backH a h h0 h2
    · intro c hc hu a ha hb
      have hd := ha
      unfold InData at hd
      have hm := heap.wf.2.2.2.1
      unfold TilesOk at hm
      have := hm.mem_lt c hc
      have := heap.hbT
      have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
      rw [wlow a (by omega)]; exact backD c hc hu a ha (by omega)
    · intro a ha
      exact ⟨by rw [wlow a (by omega)]; exact backL a ha, by rw [Memory.readable_writeN]; exact hrdL a ha⟩
    · intro a ha
      have hg := ha; unfold Glob at hg
      rw [wlow a (by omega)]; exact backG a ha
    · intro a ha; rw [Memory.writable_writeN]; exact hwrq a ha
  by_cases hmore : k + 1 < es.length
  · rw [if_pos hmore]
    obtain ⟨ω8, run8, i1, i5⟩ := LoopF.s5_moreF (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 F k
      (es.length - k) ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) q1 q5 q6
      (fun a h1 h2 => by rw [hwrq a (by omega)]; exact ws a (by omega) (by omega))
    exact Or.inl (post 680 ω8 run8 i1 (i5.trans (by rw [show es.length - k - 1 = es.length - (k + 1) by omega])))
  · rw [if_neg hmore]
    obtain ⟨ω8, run8, i1, i5⟩ := LoopF.s5_lastF (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 F k ⟨by omega, by omega⟩
      (by omega) q1 (q5.trans (by rw [show es.length - k = 1 by omega])) q6
      (fun a h1 h2 => by rw [hwrq a (by omega)]; exact ws a (by omega) (by omega))
    exact Or.inl (post 562 ω8 run8 i1 (i5.trans (by rw [show es.length - (k + 1) = 0 by omega])))

theorem FrameAF.trans {F RD n B : Nat} {s s1 s2 : State} {μ μ1 μ2 : Memory} (f1 : FrameAF F RD n B s μ s1 μ1)
    (f2 : FrameAF F RD n B s1 μ1 s2 μ2) : FrameAF F RD n B s μ s2 μ2 :=
  ⟨fun a h h0 h2 => (f2.1 a h h0 h2).trans (f1.1 a h h0 h2),
   fun c hc hu => f2.2.1 c (f1.2.1 c hc hu) hu,
   fun c hc hu a ha hb => (f2.2.2.1 c (f1.2.1 c hc hu) hu a ha hb).trans (f1.2.2.1 c hc hu a ha hb),
   fun a ha => ⟨(f2.2.2.2.1 a ha).1.trans (f1.2.2.2.1 a ha).1, (f2.2.2.2.1 a ha).2.trans (f1.2.2.2.1 a ha).2⟩,
   fun a ha => (f2.2.2.2.2.1 a ha).trans (f1.2.2.2.2.1 a ha),
   fun a ha => (f2.2.2.2.2.2 a ha).trans (f1.2.2.2.2.2 a ha)⟩

/-- The loop's step bound from element k, r elements to go: each element's own bound and 1700 for
    the loop's own steps. -/
def bound (Ns : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | k, r + 1 => Ns k + 1700 + bound Ns (k + 1) r

/-- **The decode loop, for elements that may allocate**: from `InvA` after k < n elements, the loop
    decodes the rest, element j through its `ElemOkA` with bound `Ns j`, and leaves for 562 with `InvA`
    after all n, within the sum of the elements' bounds and 1700 an element (`bound`), changing only
    what `FrameA` allows; or the run reaches a failed allocation. -/
theorem loopAF {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat) (gl : Nat → UInt8)
    (F RD P0 Lt : Nat)
    (Ns : Nat → Nat) (x : RefineCtx) (es : List (List UInt8)) (reps : Nat → List UInt8 → Memory → Prop)
    (B : Nat) (cp cb : Chunk) (ok : OkF F RD P0 Lt es B)
    (hel : ∀ j (hj : j < es.length), ElemOkAF env cap pb gl p P F RD (Ns j) es[j] (reps j)) :
    ∀ r k (ω : Regs) (μ : Memory) (s : State), es.length - k = r → k < es.length →
      InvAF env pb F RD P0 Lt es reps k B cp cb ω μ s → (∀ a, Glob a → μ.read a = gl a) →
      (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 680 ω μ x 562 ω' μ' x (bound Ns k r) ∧
        InvAF env pb F RD P0 Lt es reps es.length B cp cb ω' μ' s' ∧ FrameAF F RD es.length B s μ s' μ') ∨
      Exhausts env cap pb p P 680 ω μ x (bound Ns k r) := by
  intro r
  induction r with
  | zero => intro k ω μ s hr hk; omega
  | succ r ih =>
    intro k ω μ s hr hk h hg
    rcases passAF (p := p) (P := P) env cap pb (Ns k) gl F RD P0 Lt x ω μ s es reps k B cp cb hk ok (hel k hk) h hg with ⟨ω1, μ1, s1, run1, h1, f1⟩ | hx
    · by_cases hmore : k + 1 < es.length
      · rw [if_pos hmore] at run1
        rcases ih (k + 1) ω1 μ1 s1 (by omega) hmore h1 (fun a ha => (f1.2.2.2.2.1 a ha).trans (hg a ha)) with ⟨ω2, μ2, s2, run2, h2, f2⟩ | hx
        · exact Or.inl ⟨ω2, μ2, s2, (run1.trans run2).mono (by simp only [bound]; omega), h2, f1.trans f2⟩
        · exact Or.inr ((Exhausts.pre run1 hx).mono (by simp only [bound]; omega))
      · rw [if_neg hmore] at run1
        rw [show k + 1 = es.length by omega] at h1
        exact Or.inl ⟨ω1, μ1, s1, run1.mono (by simp only [bound]; omega), h1, f1⟩
    · exact Or.inr (hx.mono (by simp only [bound]; omega))


/-! ## In refine's frame -/

/-- The loop's invariant, with the allocator, in refine's frame (`InvAF`). -/
abbrev InvA (env : RefineHost.Env) (pb : Nat) (es : List (List UInt8))
    (reps : Nat → List UInt8 → Memory → Prop) (k B : Nat) (cp cb : Chunk) (ω : Regs) (μ : Memory)
    (s : State) : Prop :=
  InvAF env pb 4278057632 4278058648 206913 (es.flatten.length + 32) es reps k B cp cb ω μ s

/-- What a pass may change, in refine's frame (`FrameAF`). -/
abbrev FrameA (n B : Nat) (s : State) (μ : Memory) (s' : State) (μ' : Memory) : Prop :=
  FrameAF 4278057632 4278058648 n B s μ s' μ'

theorem FrameA.trans {n B : Nat} {s s1 s2 : State} {μ μ1 μ2 : Memory} (f1 : FrameA n B s μ s1 μ1)
    (f2 : FrameA n B s1 μ1 s2 μ2) : FrameA n B s μ s2 μ2 := FrameAF.trans f1 f2

/-- **One pass, with the allocator**, in refine's frame: `passAF`. -/
theorem passA {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb N : Nat) (gl : Nat → UInt8)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    (es : List (List UInt8)) (reps : Nat → List UInt8 → Memory → Prop) (k B : Nat) (cp cb : Chunk)
    (hk : k < es.length) (ok : Ok es B)
    (hel : ElemOkA env cap pb gl p P N es[k] (reps k))
    (h : InvA env pb es reps k B cp cb ω μ s) (hg : ∀ a, Glob a → μ.read a = gl a) :
    (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 680 ω μ x (if k + 1 < es.length then 680 else 562)
      ω' μ' x (N + 1700) ∧ InvA env pb es reps (k + 1) B cp cb ω' μ' s' ∧ FrameA es.length B s μ s' μ') ∨
    Exhausts env cap pb p P 680 ω μ x (N + 1700) :=
  passAF env cap pb N gl _ _ _ _ x ω μ s es reps k B cp cb hk ok.okF hel h hg

/-- **The decode loop, for elements that may allocate**, in refine's frame: `loopAF`. -/
theorem loopA {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat) (gl : Nat → UInt8)
    (Ns : Nat → Nat) (x : RefineCtx) (es : List (List UInt8)) (reps : Nat → List UInt8 → Memory → Prop)
    (B : Nat) (cp cb : Chunk) (ok : Ok es B)
    (hel : ∀ j (hj : j < es.length), ElemOkA env cap pb gl p P (Ns j) es[j] (reps j)) :
    ∀ r k (ω : Regs) (μ : Memory) (s : State), es.length - k = r → k < es.length →
      InvA env pb es reps k B cp cb ω μ s → (∀ a, Glob a → μ.read a = gl a) →
      (∃ ω' μ' s', FreeStepsH p (refineContractK cap env) 680 ω μ x 562 ω' μ' x (bound Ns k r) ∧
        InvA env pb es reps es.length B cp cb ω' μ' s' ∧ FrameA es.length B s μ s' μ') ∨
      Exhausts env cap pb p P 680 ω μ x (bound Ns k r) :=
  loopAF env cap pb gl _ _ _ _ Ns x es reps B cp cb ok.okF hel

end Services.Bootstrap.Decode.LoopA
