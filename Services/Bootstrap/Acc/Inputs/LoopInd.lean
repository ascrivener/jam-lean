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

/-- **One item of the loop, 45126 → 45103** (n ≤ 89 items, the buffer at q in the allocated chunk C,
    L < n slots filled): the item decode (`ItemOk`) into the stack slot s + 88, the check, its copy to
    s + 272 and then into the buffer's slot q + 184·L. Either the slot holds octets satisfying `Rep`
    (for memory agreeing on the item's fresh chunks), the context holds for the new state keeping every
    allocated chunk, and their data outside the new slot is kept; or the allocator is exhausted. -/
theorem lp_body {X : Type} (env : HeapHost X) (cap pb N : Nat) {p : ByteArray} {P : Program} [HasCode p P]
    [HasCodeA p P] {enc : List UInt8} {Rep : List UInt8 → Memory → Prop} (item : ItemOk env cap pb p P N enc Rep)
    (x : X) (ω : Regs) (μ : Memory) (hb : Nat) (st : State) (s rd ip rlen S0 S1 n q L c : Nat) (C : Chunk)
    (H : HeapCtxC env.code pb S0 S1 μ st)
    (h0 : ω[0] = UInt64.ofNat 2044) (h1 : ω[1] = UInt64.ofNat s) (h5 : ω[5] = UInt64.ofNat c)
    (h7 : ω[7] = UInt64.ofNat (s + 88)) (h8 : ω[8] = UInt64.ofNat rd)
    (hs : 2147483960 + 424 ≤ s ∧ s % 8 = 0) (hSTk : S0 + 864 ≤ s) (hrds : s + 480 ≤ rd) (hrdS : rd + 16 ≤ S1)
    (m64 : rdN μ (s + 64) 8 = n) (m72 : rdN μ (s + 72) 8 = q) (m80 : rdN μ (s + 80) 8 = L) (hL : L < n)
    (hC : C ∈ chunks st) (hCu : C.used = true) (hCq : C.addr + 32 ≤ q) (hCe : q + 184 * n ≤ C.addr + 32 * C.size)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : enc.length ≤ rlen) (hrl32 : rlen < 4294967296) (henc : μ.readN ip enc.length = enc)
    (hsrc : ∃ c ∈ chunks st, c.used = true ∧ c.addr + 32 ≤ ip ∧ ip + enc.length + 32 ≤ c.addr + 32 * c.size) :
    (∃ st' ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45103 ω' μ' x (N + 2000) ∧
      ω'[1] = UInt64.ofNat s ∧ ω'[5] = UInt64.ofNat c ∧ ω'[6] = UInt64.ofNat L ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧ (∀ c ∈ chunks st, c.used = true → c ∈ chunks st') ∧
      (∀ c ∈ chunks st, c.used = true → ∀ a, InDataA c a → (a < q + 184 * L ∨ q + 184 * L + 184 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∃ cs : List Chunk, (∀ c ∈ cs, c ∈ chunks st' ∧ c.used = true ∧ ∀ d ∈ chunks st, d.used = true → d ≠ c) ∧
        ∀ μ'' : Memory, (∀ c ∈ cs, ∀ a, InDataA c a → μ''.read a = μ'.read a) →
          Rep (μ'.readN (q + 184 * L) 184) μ'') ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + enc.length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - enc.length) ∧
      rdN μ' (s + 56) 8 = q ∧
      (∀ a, a < 4294967296 → s ≤ a → (a < s + 56 ∨ s + 64 ≤ a) → (a < s + 88 ∨ s + 456 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45975 ω' μ' x (N + 2000)) := by
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  obtain ⟨Cb1, Cb2, Cb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hC hCu
  rcases item x ω μ hb st s rd ip rlen S0 S1 H h0 h1 h7 h8 hs.1 hs.2 hSTk hrds hrdS hR0 hR8 hrl hrl32 henc hsrc with
    ⟨st', ω1, μ1, r1, e0, e1, e5, e6, ne2, H1, keep, keepd, ⟨cs, fresh, rep⟩, R0, R8, fr1⟩ | ⟨ω1, μ1, r1⟩
  · have hst := H1.st
    obtain ⟨ω2, r2, c0, c1, c5, c6, c7, c8, c9⟩ :=
      lp_chk (p := p) (P := P) (R := env.rel cap) x ω1 μ1 s e1 ne2 ⟨by omega, by omega⟩
        (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    obtain ⟨ω3, μ3, r3, d0, d1, d5, d6, cp1, fr3, rd3, wr3⟩ :=
      memcpy_big_aligned (p := p) (P := P) (R := env.rel cap) x ω2 μ1 2046 45192 s (s + 272) (s + 88) 184 c0 c1 c7 c8 c9
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1022]) bs_45192
        ⟨by omega, by omega, hs.2⟩ (by decide) (by omega) (by omega) (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
    have k31 : ∀ o, s ≤ o → o + 8 ≤ s + 88 → rdN μ3 o 8 = rdN μ o 8 := fun o h1 h2 => by
      rw [rdN_frame fun j hj => fr3 _ (by omega) (Or.inl (by omega)) (Or.inr (by omega)),
        rdN_frame fun j hj => fr1 _ (by omega) (by omega) (Or.inl (by omega)) (by omega)]
    have hq : q + 184 * n < 4294967296 := by omega
    obtain ⟨ω4, μ4, r4, f0, f1, f5, f6, f7, f8, f9, s56, fr4, rd4, wr4⟩ :=
      lp_step (p := p) (P := P) (R := env.rel cap) x ω3 μ3 s n q L d1
        (by rw [k31 _ (by omega) (by omega)]; exact m64) (by rw [k31 _ (by omega) (by omega)]; exact m72)
        (by rw [k31 _ (by omega) (by omega)]; exact m80) hL hq ⟨by omega, by omega⟩
        (fun a h1 h2 => by rw [wr3]; exact hst a (by omega) (by omega))
    have hCw : ∀ a, q + 184 * L ≤ a → a < q + 184 * L + 184 → μ4.writable a = true := fun a h1 h2 => by
      rw [wr4, wr3]; exact heapC_writable_data H1 (keep C hC hCu) hCu ⟨by omega, by omega⟩
    obtain ⟨ω5, μ5, r5, g0, g1, g5, g6, cp2, fr5, rd5, wr5⟩ :=
      memcpy_big (p := p) (P := P) (R := env.rel cap) x ω4 μ4 2042 45103 s (q + 184 * L) (s + 272) 184 f0 f1 f7 f8 f9
        (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1020]) bs_45103
        ⟨by omega, by omega, hs.2⟩ (by decide) (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))
        (Or.inl (by omega))
        (fun a h1 h2 => by rw [rd4, rd3]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
        hCw (fun a h1 h2 => by rw [wr4, wr3]; exact hst a (by omega) (by omega))
    -- memory below 2^31: only the new slot changed after the item
    have lo : ∀ a, a < 2147483648 → (a < q + 184 * L ∨ q + 184 * L + 184 ≤ a) → μ5.read a = μ1.read a :=
      fun a h1 h2 => by
        rw [fr5 a (by omega) h2 (Or.inl (by omega)), fr4 a (by omega) (Or.inl (by omega)),
          fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
    have lo1 : ∀ a, a < 2147483648 → μ4.read a = μ1.read a := fun a h1 => by
      rw [fr4 a (by omega) (Or.inl (by omega)), fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
    have H4 : HeapCtxC env.code pb S0 S1 μ4 st' := HeapCtxC.keep_hi H1 lo1 (fun a => by rw [wr4, wr3])
    have H5 : HeapCtxC env.code pb S0 S1 μ5 st' := HeapCtxC.keep_data H4 (keep C hC hCu)
      (fun a h1 h2 => fr5 a (by omega) (by omega) (Or.inl (by omega))) wr5
    -- the slot's octets
    have slot : μ5.readN (q + 184 * L) 184 = μ1.readN (s + 88) 184 := by
      rw [cp2, PVM.Memory.readN_congr (μ := μ3) (fun j hj => fr4 _ (by omega) (Or.inr (by omega))), cp1]
    refine Or.inl ⟨st', ω5, μ5, (((((r1.trans r2).trans r3).trans r4).trans r5)).mono (by omega),
      g1, by rw [g5, f5, d5, c5, e5, h5], by rw [g6, f6], H5, keep,
      fun c hc hu a ha hout => ?_, ⟨cs, fresh, fun μ'' hag => ?_⟩, ?_, ?_, ?_, fun a h0 hs h56 h88 hr => ?_⟩
    · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
      unfold InDataA at ha
      rw [lo a (by omega) hout, keepd c hc hu a ⟨ha.1, ha.2⟩]
    · rw [slot]
      refine rep μ'' fun c hc a ha => ?_
      rw [hag c hc a ha]
      obtain ⟨hcm, hcu, hcf⟩ := fresh c hc
      have hne : C ≠ c := hcf C hC hCu
      have hap := Services.Bootstrap.Decode.LoopA.InData.apart H1.wf hcm (keep C hC hCu) hne ha
      have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hcm hcu
      have := H1.hbT
      unfold Services.Bootstrap.Decode.LoopA.InData at hap
      unfold InDataA at ha
      exact lo a (by omega) (by omega)
    · rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => by
        rw [fr5 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)), fr4 _ (by omega) (Or.inr (by omega)),
          fr3 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]), R0]
    · rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => by
        rw [fr5 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)), fr4 _ (by omega) (Or.inr (by omega)),
          fr3 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]), R8]
    · rw [rdN_frame fun j hj => fr5 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]; exact s56
    · rw [fr5 a h0 (Or.inr (by omega)) (Or.inr hs), fr4 a h0 h56, fr3 a h0 (by omega) (Or.inr hs),
        fr1 a h0 hs (by omega) hr]
  · exact Or.inr ⟨ω1, μ1, r1.mono (by omega)⟩

end Services.Bootstrap.Acc
