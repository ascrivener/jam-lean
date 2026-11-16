import Services.Bootstrap.Acc.Handlers.InstrRep
import Services.Bootstrap.Acc.Handlers.RowElevenTail

/-!
# Row 11 (R7): the final results write and the work item's drops

`onWorkItem`'s end (GP v0.8.0 Appendix B, Ω_W; quirk Q4): `unless (is.any zombify) (store key
(encodeResults results))`, then the frame's drops.

`r11_tail` (15133 → 6766): the results' items dropped (`drop_results`), then the results buffer, the
buffer at sp + 104 and the buffer at sp + 272 freed when their caps are not 0. `KF` is what holds along
the way: the allocator's context with the listed buffers freed, every other allocated chunk kept with
its data (`Kept`), and the memory from sp up kept (`Frm`).
-/

namespace Services.Bootstrap.Acc.Handlers.RowEleven

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.DeallocCall Services.Bootstrap.Acc.Handlers.ResultsDrop
  Services.Bootstrap.Acc.Handlers.InstrRep

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The allocator's context with the buffers FR freed from (μ₀, s₀), the other allocated chunks kept
    with their data, and the memory from sp up, the globals and the octets that are not writable kept. -/
structure KF (code : ByteArray) (pb S0 S1 : Nat) (s0 : State) (μ0 : Memory) (sp : Nat) (FR : List Nat)
    (μ : Memory) (s : State) : Prop where
  H : HeapCtxC code pb S0 S1 μ s
  K : Kept s0 μ0 FR μ s
  Fm : Frm μ0 sp μ
  hs : s = FR.foldl free s0

/-- **A call of `dealloc` for a buffer w that is not yet freed** keeps `KF` (with w freed). -/
theorem KF.dk {p : ByteArray} {P : Program} [HasCode p P] {code : ByteArray} {pb S0 S1 : Nat}
    {s0 : State} {μ0 : Memory} {sp : Nat} {FR : List Nat} (x : X) {ω : Regs} {μ : Memory} {s : State}
    (C : KF code pb S0 S1 s0 μ0 sp FR μ s) (hsp : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp ≤ S1)
    (w r t : Nat) (hc : ∃ c ∈ chunks s0, c.used = true ∧ c.addr + 32 = w) (hw : w ∉ FR)
    (h0 : ω[0] = UInt64.ofNat r) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat w)
    (hret : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hjt : P.jumpTable.getD (r / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∃ ω' μ', FreeStepsH p R 40613 ω μ x t ω' μ' x 249 ∧
      KF code pb S0 S1 s0 μ0 sp (FR ++ [w]) μ' (free s w) ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨H, K, ⟨f1, f2, f3, f4, f5⟩, hs⟩ := C
  obtain ⟨c, hc0, hcu, hca⟩ := hc
  have hcs := (K c hc0 hcu (by rw [hca]; exact hw)).1
  obtain ⟨ω', μ', run, H', -, pg, ro, stk, gl, keep, e0, e1, e5, e6⟩ :=
    dealloc_callG (R := R) (p := p) (P := P) code pb S0 S1 x ω μ s sp w r t c H hcs hcu hca h0 h1 h7
      hret hjt hbt hsp.1 ⟨hsp.2.1, hsp.2.2⟩
  have rdeq : ∀ a, μ'.readable a = μ.readable a := fun a => by unfold Memory.readable; rw [pg]
  have wreq : ∀ a, μ'.writable a = μ.writable a := fun a => by unfold Memory.writable; rw [pg]
  refine ⟨ω', μ', run, ⟨H', fun d hd hu hn => ?_,
    ⟨fun a h1 h2 => (stk a h1 h2).trans (f1 a h1 h2), fun a ha => (gl a ha).trans (f2 a ha),
     fun b hb hw' => (ro b hb (by rw [f5]; exact hw')).trans (f3 b hb hw'), fun a => (rdeq a).trans (f4 a),
     fun a => (wreq a).trans (f5 a)⟩,
    by rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hs]⟩, e1, e5, e6⟩
  have hn' : d.addr + 32 ∉ FR := fun h => hn (List.mem_append_left _ h)
  have hdc : d ≠ c := by
    rintro rfl; exact hn (List.mem_append_right _ (by rw [hca]; exact List.mem_singleton_self _))
  obtain ⟨h1, h2⟩ := K d hd hu hn'
  obtain ⟨h3, h4⟩ := keep d h1 hu hdc
  exact ⟨h3, fun a ha => (h4 a ha).trans (h2 a ha)⟩

/-- A buffer that the drops free: if its cap c is not 0, its pointer q is the data address of an
    allocated chunk of s₀ that is not among FR. -/
def BufOK (s0 : State) (FR : List Nat) (c q : Nat) : Prop :=
  c ≠ 0 → (∃ d ∈ chunks s0, d.used = true ∧ d.addr + 32 = q) ∧ q ∉ FR

/-- **One optional dealloc** (a cap word c, a buffer q): from `KF FR` to `KF (FR ++ optBuf c q)`. -/
theorem KF.opt {p : ByteArray} {P : Program} [HasCode p P] {code : ByteArray} {pb S0 S1 : Nat}
    {s0 : State} {μ0 : Memory} {sp : Nat} {FR : List Nat} (x : X) {i0 t : Nat} {ω : Regs} {μ : Memory}
    {s : State} (C : KF code pb S0 S1 s0 μ0 sp FR μ s) (hsp : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp ≤ S1)
    (c q r : Nat) (hB : BufOK s0 FR c q) (h1 : ω[1] = UInt64.ofNat sp)
    (hret : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hjt : P.jumpTable.getD (r / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (seg0 : c = 0 → ∃ ω', FreeStepsH p R i0 ω μ x t ω' μ x 3 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6])
    (seg1 : c ≠ 0 → ∃ ω', FreeStepsH p R i0 ω μ x 40613 ω' μ x 9 ∧ ω'[0] = UInt64.ofNat r ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q) :
    ∃ ω' μ' s' N, FreeStepsH p R i0 ω μ x t ω' μ' x N ∧
      KF code pb S0 S1 s0 μ0 sp (FR ++ optBuf c q) μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  by_cases hc : c = 0
  · obtain ⟨ω1, run1, a1, a5, a6⟩ := seg0 hc
    refine ⟨ω1, μ, s, _, run1, ?_, a1, a5, a6⟩
    unfold optBuf; rw [if_pos hc, List.append_nil]; exact C
  · obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := seg1 hc
    obtain ⟨hch, hn⟩ := hB hc
    obtain ⟨ω2, μ2, run2, C2, b1, b5, b6⟩ :=
      C.dk (R := R) (P := P) x hsp q r t hch hn a0 (a1.trans h1) a7 hret hjt hbt
    refine ⟨ω2, μ2, free s q, _, run1.trans run2, ?_, b1.trans a1, b5.trans a5, b6.trans a6⟩
    unfold optBuf; rw [if_neg hc]; exact C2

/-- The buffers row 11 frees after the results' items, in order: the results buffer (cap at sp + 448,
    ptr at sp + 456), the buffer at sp + 104 (cap at sp + 128), the buffer at sp + 272 (cap at sp + 264). -/
def tailBufs (μ : Memory) (sp : Nat) : List Nat :=
  optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) ++ optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) ++
    optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8)

/-- Everything row 11's tail frees: the results' buffers (`resPtrs`), then `tailBufs`. -/
def tailFree (μ : Memory) (sp : Nat) : List Nat :=
  resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) ++ tailBufs μ sp

/-- **What row 11's tail needs at 15133**: the allocator's context; sp's bounds; the results `Vec` at
    sp + 448 (ptr rp at sp + 456, len n at sp + 464) owned as `ResultsOwn`; each of the three buffers
    (`tailBufs`), if its cap is not 0, the data of an allocated chunk not freed before it. -/
structure TailHyp (code : ByteArray) (pb S0 S1 : Nat) (μ : Memory) (s : State) (sp : Nat) : Prop where
  H : HeapCtxC code pb S0 S1 μ s
  hsp : 2147483772 ≤ sp ∧ S0 + 96 ≤ sp ∧ sp + 472 ≤ S1
  O : ResultsOwn μ s (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8)
  b1 : BufOK s (resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8)) (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8)
  b2 : BufOK s (resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) ++
    optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8)) (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8)
  b3 : BufOK s (resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8) ++
    optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) ++ optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8))
    (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8)

/-- **Row 11's tail (15133 → 6766)**: the results' items dropped, then the results buffer, the buffer at
    sp + 104 and the buffer at sp + 272 freed when their caps are not 0: `KF` with `tailFree` freed,
    ω₁ = sp, ω₅, ω₆ kept. -/
theorem r11_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {code : ByteArray}
    {pb S0 S1 : Nat} (x : X) (ω : Regs) (μ : Memory) (s : State) (sp : Nat)
    (T : TailHyp code pb S0 S1 μ s sp) (h1 : ω[1] = UInt64.ofNat sp) :
    ∃ ω' μ' s' N, FreeStepsH p R 15133 ω μ x 6766 ω' μ' x N ∧
      KF code pb S0 S1 s μ sp (tailFree μ sp) μ' s' ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  obtain ⟨H, ⟨hs1, hs2, hs3⟩, O, B1, B2, B3⟩ := T
  have hT := H.hS1
  have hsp' : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp ≤ S1 := ⟨by omega, by omega, by omega⟩
  have rd0 : ∀ a, sp ≤ a → a < sp + 472 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (H.st a (by omega) (by omega))
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7⟩ := r11_dr (R := R) (P := P) x ω μ sp h1 (by omega)
  obtain ⟨ω2, μ2, N2, run2, H2, K2, F2, b1, b5, b6⟩ :=
    drop_results (R := R) (P := P) x ω1 μ s sp (sp + 448) _ _ 564 15143 H O ⟨by omega, by omega, by omega⟩
      a0 (a1.trans h1) a7 (by omega) (.inr (by omega)) rfl rfl (fun a h1 h2 => rd0 a (by omega) (by omega))
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_281]) bs_15143
  have C2 : KF code pb S0 S1 s μ sp (resPtrs μ (rdN μ (sp + 456) 8) (rdN μ (sp + 464) 8)) μ2 _ :=
    ⟨H2, K2, F2, rfl⟩
  -- reads of the frame (from sp up) are μ's, readable, through every KF
  have rdK : ∀ {FR μ' s'}, KF code pb S0 S1 s μ sp FR μ' s' → ∀ b, sp ≤ b → b + 8 ≤ sp + 472 →
      rdN μ' b 8 = rdN μ b 8 ∧ ∀ a, b ≤ a → a < b + 8 → μ'.readable a = true := by
    intro FR μ' s' C b h1 h2
    exact ⟨rdN_frame fun j hj => C.Fm.1 _ (by omega) (by omega),
      fun a ha1 ha2 => by rw [C.Fm.2.2.2.1]; exact rd0 a (by omega) (by omega)⟩
  -- the results buffer (15143 → 15172)
  obtain ⟨r48, q48⟩ := rdK C2 (sp + 448) (by omega) (by omega)
  obtain ⟨r56, q56⟩ := rdK C2 (sp + 456) (by omega) (by omega)
  obtain ⟨ω3, μ3, s3, N3, run3, C3, c1, c5, c6⟩ :=
    C2.opt (R := R) (P := P) x (i0 := 15143) (t := 15172) hsp' _ _ 566 B1 (b1)
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_282]) bs_15172
      (fun hc => by
        obtain ⟨ω', r, e⟩ := r11_b0 (R := R) (P := P) x ω2 μ2 sp b1 (by omega) (by rw [r48, hc]) q48
        exact ⟨ω', r.mono (by omega), e⟩)
      (fun hc => by
        obtain ⟨ω', r, e⟩ := r11_b1 (R := R) (P := P) x ω2 μ2 sp _ _ b1 (by omega) r48 hc r56
          (fun a h1 h2 => if h : a < sp + 456 then q48 a h1 h else q56 a (by omega) h2)
        exact ⟨ω', r, e⟩)
  -- the buffer at sp + 104 (15172 → 15191)
  obtain ⟨r28, q28⟩ := rdK C3 (sp + 128) (by omega) (by omega)
  obtain ⟨r04, q04⟩ := rdK C3 (sp + 104) (by omega) (by omega)
  obtain ⟨ω4, μ4, s4, N4, run4, C4, d1, d5, d6⟩ :=
    C3.opt (R := R) (P := P) x (i0 := 15172) (t := 15191) hsp' _ _ 568 B2 (c1.trans b1)
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_283]) bs_15191
      (fun hc => by
        obtain ⟨ω', r, e⟩ := r11_c0 (R := R) (P := P) x ω3 μ3 sp (c1.trans b1) (by omega) (by rw [r28, hc]) q28
        exact ⟨ω', r.mono (by omega), e⟩)
      (fun hc => by
        obtain ⟨ω', r, e⟩ := r11_c1 (R := R) (P := P) x ω3 μ3 sp _ _ (c1.trans b1) (by omega) r28 hc r04
          (fun a h1 h2 => by
            rw [C3.Fm.2.2.2.1]; exact rd0 a (by omega) (by omega))
        exact ⟨ω', r.mono (by omega), e⟩)
  -- the buffer at sp + 272 (15191 → 6766)
  obtain ⟨r64, q64⟩ := rdK C4 (sp + 264) (by omega) (by omega)
  obtain ⟨r72, q72⟩ := rdK C4 (sp + 272) (by omega) (by omega)
  obtain ⟨ω5, μ5, s5, N5, run5, C5, e1, e5, e6⟩ :=
    C4.opt (R := R) (P := P) x (i0 := 15191) (t := 6766) hsp' _ _ 228 B3 (d1.trans (c1.trans b1))
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_113]) bs_6766
      (fun hc => by
        obtain ⟨ω', r, e⟩ := r11_e0 (R := R) (P := P) x ω4 μ4 sp (d1.trans (c1.trans b1)) (by omega)
          (by rw [r64, hc]) q64
        exact ⟨ω', r, e⟩)
      (fun hc => by
        obtain ⟨ω', r, e⟩ := r11_e1 (R := R) (P := P) x ω4 μ4 sp _ _ (d1.trans (c1.trans b1)) (by omega) r64 hc
          r72 (fun a h1 h2 => if h : a < sp + 272 then q64 a h1 h else q72 a (by omega) h2)
        exact ⟨ω', r.mono (by omega), e⟩)
  refine ⟨ω5, μ5, s5, _, (((run1.trans run2).trans run3).trans run4).trans run5, ?_,
    e1.trans (d1.trans (c1.trans b1)), e5.trans (d5.trans (c5.trans (b5.trans (a5)))),
    e6.trans (d6.trans (c6.trans (b6.trans a6)))⟩
  unfold tailFree tailBufs
  simpa only [List.append_assoc] using C5

end Services.Bootstrap.Acc.Handlers.RowEleven
