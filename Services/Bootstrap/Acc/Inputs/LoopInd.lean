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

/-- An item list's encodings, concatenated. -/
def encs (rest : List (List UInt8 × (List UInt8 → Memory → Prop))) : List UInt8 := (rest.map Prod.fst).flatten

theorem encs_cons (e : List UInt8 × (List UInt8 → Memory → Prop)) (rest) : encs (e :: rest) = e.1 ++ encs rest := by
  simp [encs]

/-- **The loop over the remaining items, 45126 → 45613** (see the module doc): with L slots filled and the
    reader holding the rest's encodings, either every remaining item's slot q + 184·(L + j) satisfies its
    `Rep` in the final memory, `Vec { n, q, n }` is written at out and the frame popped; or the allocator
    is exhausted. -/
theorem lp_items {X : Type} (env : HeapHost X) (cap pb N : Nat) {p : ByteArray} {P : Program} [HasCode p P]
    [HasCodeA p P] (x : X) (hb S0 S1 s rd out n q : Nat) (C Rc : Chunk)
    (hs : 2147483960 + 424 ≤ s ∧ s % 8 = 0) (hSTk : S0 + 864 ≤ s) (hrds : s + 480 ≤ rd) (hrdS : rd + 16 ≤ S1)
    (hout : s + 480 ≤ out ∧ out + 24 ≤ S1) (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out) (hn : n ≤ 89)
    (hRC : Rc ≠ C) :
    ∀ (rest : List (List UInt8 × (List UInt8 → Memory → Prop))) (ω : Regs) (μ : Memory) (st : State)
      (L ip rlen : Nat),
    (∀ e ∈ rest, ItemOk env cap pb p P N e.1 e.2) → rest ≠ [] → HeapCtxC env.code pb S0 S1 μ st →
    ω[0] = UInt64.ofNat 2044 → ω[1] = UInt64.ofNat s → ω[5] = UInt64.ofNat rest.length →
    ω[7] = UInt64.ofNat (s + 88) → ω[8] = UInt64.ofNat rd →
    rdN μ s 8 = out → rdN μ (s + 32) 8 = n → rdN μ (s + 40) 8 = n → rdN μ (s + 48) 8 = rd →
    rdN μ (s + 56) 8 = q → rdN μ (s + 64) 8 = n → rdN μ (s + 72) 8 = q → rdN μ (s + 80) 8 = L →
    L + rest.length = n →
    C ∈ chunks st → C.used = true → C.addr + 32 ≤ q → q + 184 * n ≤ C.addr + 32 * C.size →
    Rc ∈ chunks st → Rc.used = true → Rc.addr + 32 ≤ ip → ip + (encs rest).length + 32 ≤ Rc.addr + 32 * Rc.size →
    μ.readN rd 8 = Num.encodeLE 8 ip → μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen →
    (encs rest).length ≤ rlen → rlen < 4294967296 → μ.readN ip (encs rest).length = encs rest →
    (∃ st' ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45613 ω' μ' x ((N + 2100) * rest.length) ∧
      ω'[0] = UInt64.ofNat (rdN μ (s + 472) 8) ∧ ω'[1] = UInt64.ofNat (s + 480) ∧
      ω'[5] = UInt64.ofNat (rdN μ (s + 464) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (s + 456) 8) ∧
      rdN μ' out 8 = n ∧ rdN μ' (out + 8) 8 = q ∧ rdN μ' (out + 16) 8 = n ∧
      HeapCtxC env.code pb S0 S1 μ' st' ∧ (∀ c ∈ chunks st, c.used = true → c ∈ chunks st') ∧
      (∀ c ∈ chunks st, c.used = true → ∀ a, InDataA c a → (a < q + 184 * L ∨ q + 184 * n ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ (j : Nat) (e : List UInt8 × (List UInt8 → Memory → Prop)), rest[j]? = some e →
        e.2 (μ'.readN (q + 184 * (L + j)) 184) μ') ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + (encs rest).length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (encs rest).length)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45975 ω' μ' x ((N + 2100) * rest.length)) := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _ _ _ _ hne; exact absurd rfl hne
  | cons e tail ih =>
  intro ω μ st L ip rlen hok _ H h0 h1 h5 h7 h8 m0 m32 m40 m48 m56 m64 m72 m80 hLn hC hCu hCq hCe hR hRu hRq hRe
    hR0 hR8 hrl hrl32 henc
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hLn' : L + 1 + tail.length = n := by simp at hLn; omega
  rw [encs_cons] at hrl henc hRe
  simp only [List.length_append] at hrl hRe
  obtain ⟨he, ht⟩ := readN_app μ ip e.1 (encs tail) (by rw [← List.length_append]; exact henc)
  rcases lp_body env cap pb N (hok e (by simp)) x ω μ hb st s rd ip rlen S0 S1 n q L (e :: tail).length C H
      h0 h1 h5 h7 h8 hs hSTk hrds hrdS m64 m72 m80 (by simp at hLn; omega) hC hCu hCq hCe hR0 hR8 (by omega) hrl32 he
      ⟨Rc, hR, hRu, hRq, by omega⟩ with
    ⟨st1, ω1, μ1, r1, a1, a5, a6, H1, keep1, keepd1, ⟨cs, fresh, rep⟩, R0, R8, s56, fr1⟩ | ⟨ω1, μ1, r1⟩
  · have hst := H1.st
    have kf : ∀ o, s ≤ o → o + 8 ≤ s + 56 → rdN μ1 o 8 = rdN μ o 8 := fun o h1 h2 =>
      rdN_frame fun j hj => fr1 _ (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have kg : ∀ o, s + 456 ≤ o → o + 8 ≤ s + 480 → rdN μ1 o 8 = rdN μ o 8 := fun o h1 h2 =>
      rdN_frame fun j hj => fr1 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
    have kh : ∀ o, s + 64 ≤ o → o + 8 ≤ s + 88 → rdN μ1 o 8 = rdN μ o 8 := fun o h1 h2 =>
      rdN_frame fun j hj => fr1 _ (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have hCu1 : C ∈ chunks st1 := keep1 C hC hCu
    have hR1 : Rc ∈ chunks st1 := keep1 Rc hR hRu
    -- the item's slot and its fresh chunks, kept by any later step that keeps st1's chunks' data
    have keepRep : ∀ μ' : Memory, (∀ c ∈ chunks st1, c.used = true → ∀ a, InDataA c a →
        (a < q + 184 * (L + 1) ∨ q + 184 * n ≤ a) → μ'.read a = μ1.read a) →
        e.2 (μ'.readN (q + 184 * (L + 0)) 184) μ' := fun μ' hk => by
      have slotk : μ'.readN (q + 184 * L) 184 = μ1.readN (q + 184 * L) 184 :=
        PVM.Memory.readN_congr fun j hj => hk C hCu1 hCu _ ⟨by omega, by omega⟩ (Or.inl (by omega))
      rw [Nat.add_zero, slotk]
      refine rep μ' fun c hc a ha => ?_
      obtain ⟨hcm, hcu, hcf⟩ := fresh c hc
      have hne : C ≠ c := hcf C hC hCu
      have hap := Services.Bootstrap.Decode.LoopA.InData.apart H1.wf hcm hCu1 hne ha
      unfold Services.Bootstrap.Decode.LoopA.InData at hap
      exact hk c hcm hcu a ha (by omega)
    by_cases htl : tail = []
    · subst htl
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at a5 hLn
      obtain ⟨ω2, μ2, r2, b0, b1, b5, b6, o0, o8, o16, fr2, rd2, wr2⟩ :=
        lp_last (p := p) (P := P) (R := env.rel cap) x ω1 μ1 s out n q L a1 a5 a6
          (by rw [kf _ (by omega) (by omega)]; exact m0) (by rw [kf _ (by omega) (by omega)]; exact m32)
          (by rw [kf _ (by omega) (by omega)]; exact m40) s56 (by rw [kh _ (by omega) (by omega)]; exact m64)
          (by rw [kh _ (by omega) (by omega)]; exact m72) (by omega) (by omega) ⟨by omega, by omega⟩
          ⟨by omega, by omega⟩ (Or.inr hout.1) (fun a h1 h2 => hst a (by omega) (by omega))
          (fun a h1 h2 => hst a (by omega) (by omega))
      have lo2 : ∀ a, a < 2147483648 → μ2.read a = μ1.read a := fun a ha =>
        fr2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      refine Or.inl ⟨st1, ω2, μ2, (r1.trans r2).mono (by simp; try omega),
        by rw [b0, kg _ (by omega) (by omega)], b1, by rw [b5, kg _ (by omega) (by omega)],
        by rw [b6, kg _ (by omega) (by omega)], o0, o8, by rw [o16]; try omega,
        HeapCtxC.keep_hi H1 lo2 wr2, keep1, fun c hc hu a ha hout' => ?_, fun j e' hj => ?_, ?_, ?_⟩
      · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
        unfold InDataA at ha
        rw [lo2 a (by omega), keepd1 c hc hu a ha (by omega)]
      · cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
          refine keepRep μ2 fun c hc hu a ha _ => ?_
          have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hc hu
          have := H1.hbT
          unfold InDataA at ha
          exact lo2 a (by omega)
        | succ j => simp at hj
      · rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega)), R0]
        simp [encs]
      · rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega)), R8]
        simp [encs]
    · have hlen : 1 < (e :: tail).length := by
        cases tail with
        | nil => exact absurd rfl htl
        | cons _ _ => simp
      obtain ⟨ω2, μ2, r2, b0, b1, b5, b7, b8, s80, fr2, rd2, wr2⟩ :=
        lp_next (p := p) (P := P) (R := env.rel cap) x ω1 μ1 s rd L (e :: tail).length a1 a5 a6
          (by rw [kf _ (by omega) (by omega)]; exact m48) ⟨hlen, by simp only [List.length_cons]; omega⟩ (by omega) ⟨by omega, by omega⟩
          (fun a h1 h2 => hst a (by omega) (by omega))
      have lo2 : ∀ a, a < 2147483648 → μ2.read a = μ1.read a := fun a ha => fr2 a (by omega) (Or.inl (by omega))
      have H2 : HeapCtxC env.code pb S0 S1 μ2 st1 := HeapCtxC.keep_hi H1 lo2 wr2
      have k2 : ∀ o, s ≤ o → o + 8 ≤ s + 80 → rdN μ2 o 8 = rdN μ1 o 8 := fun o h1 h2 =>
        rdN_frame fun j hj => fr2 _ (by omega) (Or.inl (by omega))
      have k2' : ∀ o, s + 88 ≤ o → o + 8 ≤ 4294967296 → rdN μ2 o 8 = rdN μ1 o 8 := fun o h1 h2 =>
        rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega))
      have tailOk : ∀ e' ∈ tail, ItemOk env cap pb p P N e'.1 e'.2 := fun e' h => hok e' (by simp [h])
      have hrd2 : μ2.readN rd 8 = Num.encodeLE 8 (ip + e.1.length) := by
        rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => fr2 _ (by omega) (Or.inr (by omega))), R0]
      have hrd8 : μ2.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - e.1.length) := by
        rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => fr2 _ (by omega) (Or.inr (by omega))), R8]
      obtain ⟨Rb1, Rb2, Rb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hR hRu
      have hencT : μ2.readN (ip + e.1.length) (encs tail).length = encs tail := by
        rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => lo2 _ (by omega))]
        rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => keepd1 Rc hR hRu _ ⟨by omega, by omega⟩ (by
          have := Services.Bootstrap.Decode.LoopA.InData.apart H.wf hR hC (Ne.symm hRC) (a := ip + e.1.length + j)
            ⟨by omega, by omega⟩
          unfold Services.Bootstrap.Decode.LoopA.InData at this; omega))]
        exact ht
      rcases ih ω2 μ2 st1 (L + 1) (ip + e.1.length) (rlen - e.1.length) tailOk htl H2 b0 b1
          (by rw [b5]; simp) b7 b8
          (by rw [k2 _ (by omega) (by omega), kf _ (by omega) (by omega)]; exact m0)
          (by rw [k2 _ (by omega) (by omega), kf _ (by omega) (by omega)]; exact m32)
          (by rw [k2 _ (by omega) (by omega), kf _ (by omega) (by omega)]; exact m40)
          (by rw [k2 _ (by omega) (by omega), kf _ (by omega) (by omega)]; exact m48)
          (by rw [k2 _ (by omega) (by omega)]; exact s56)
          (by rw [k2 _ (by omega) (by omega), kh _ (by omega) (by omega)]; exact m64)
          (by rw [k2 _ (by omega) (by omega), kh _ (by omega) (by omega)]; exact m72)
          s80 (by simp at hLn; omega) hCu1 hCu hCq hCe hR1 hRu (by omega) (by omega) hrd2 hrd8 (by omega)
          (by omega) hencT with
        ⟨st', ω', μ', r3, c0, c1, c5, c6, o0, o8, o16, H', keep', keepd', reps, R0', R8'⟩ | ⟨ω', μ', r3⟩
      · refine Or.inl ⟨st', ω', μ', ((r1.trans r2).trans r3).mono (by simp; rw [Nat.mul_succ]; omega),
          by rw [c0, k2' _ (by omega) (by omega), kg _ (by omega) (by omega)], c1,
          by rw [c5, k2' _ (by omega) (by omega), kg _ (by omega) (by omega)],
          by rw [c6, k2' _ (by omega) (by omega), kg _ (by omega) (by omega)], o0, o8, o16, H',
          fun c hc hu => keep' c (keep1 c hc hu) hu, fun c hc hu a ha hout' => ?_, fun j e' hj => ?_, ?_, ?_⟩
        · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
          unfold InDataA at ha
          rw [keepd' c (keep1 c hc hu) hu a ha (by omega), lo2 a (by omega), keepd1 c hc hu a ha (by omega)]
        · cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
            refine keepRep μ' fun c hc hu a ha hout' => ?_
            have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hc hu
            have := H1.hbT
            unfold InDataA at ha
            rw [keepd' c hc hu a ha hout', lo2 a (by omega)]
          | succ j =>
            simp only [List.getElem?_cons_succ] at hj
            have := reps j e' hj
            rwa [show L + 1 + j = L + (j + 1) by omega] at this
        · rw [R0', encs_cons, List.length_append, Nat.add_assoc]
        · rw [R8', encs_cons, List.length_append, Nat.sub_add_eq]
      · exact Or.inr ⟨ω', μ', ((r1.trans r2).trans r3).mono (by simp; rw [Nat.mul_succ]; omega)⟩
  · exact Or.inr ⟨ω1, μ1, r1.mono (by simp; rw [Nat.mul_succ]; omega)⟩

end Services.Bootstrap.Acc
