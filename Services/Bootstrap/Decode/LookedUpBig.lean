import Services.Bootstrap.Decode.LookedUp
import Services.Bootstrap.Decode.VecU8Pass

/-!
# `Instruction::decode` of `LookedUp { data: Some(bytes) }`, |bytes| > 16384

`looked_up_big` is `looked_up_small` with `VecU8.vec_u8_big` in place of `vec_u8_small`: the bytes are
read through `read_vec`'s chunk loop, the buffer grown by `realloc`.
-/

namespace Services.Bootstrap.Decode.LookedUp

open PVM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc JAM
  Services.Bootstrap.Decode.Tag Services.Bootstrap.Decode.VecU8 Services.Bootstrap.CodeX

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`LookedUp { data: Some(bytes) }`, 16384 < n = |bytes| < 2³⁰ − 64**: as `looked_up_small`, with the
    model's `alloc` returning q₀ for the first chunk's 512 units and `read_vec`'s loop growing the
    buffer by `realloc` (`vec_u8_big`). Either `Instruction::decode` returns `LookedUp { data:
    Some(bytes) }` in O (the `Vec` `{cap n, ptr q, len n}` at O + 8, the n octets at q, q an
    allocated chunk of ⌈n/32⌉ + 1 units of the model's state after the `realloc`s), or the run
    reaches `finish_grow`'s return point from a `realloc` that the model fails (33055, ω₇ = 0). -/
theorem looked_up_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s1 : State) (A O ret t v5 v6 rd ptr len n q0 pb ph : Nat)
    (F : Frame P A O ret t v5 v6 ω μ)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (tag : μ.read A = 18) (tab : μ.readN 67476 100 = table)
    (hrt : ∀ a, 67476 ≤ a → a < 67576 → μ.readable a = true)
    (hwf : WF s) (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 512 s = some (q0, s1))
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hS : S0 + 512 ≤ A ∧ A + 56 ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) (hS1 : S1 < 4294967296)
    (hA8 : 2147484160 ≤ A ∧ A % 8 = 0)
    (hn : 16384 < n ∧ n < 1073741760)
    (hlen : 1 + (Blob.encodeNat n).length + n ≤ len ∧ len < 4294967296)
    (hrd : A + 56 ≤ rd ∧ rd + 16 ≤ S1) (hO : A + 56 ≤ O ∧ O + 32 ≤ S1) (hOr : O + 32 ≤ rd ∨ rd + 16 ≤ O)
    (hptr : A + 56 ≤ ptr ∧ ptr + 1 + (Blob.encodeNat n).length + n + 32 < 4294967296)
    (hpr : ptr + 1 + (Blob.encodeNat n).length + n + 32 ≤ rd ∨ rd + 16 ≤ ptr)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hsome : μ.read ptr = 1) (henc : μ.readN (ptr + 1) (Blob.encodeNat n).length = Blob.encodeNat n)
    (hra : ∀ a, ptr ≤ a → a < ptr + 1 + (Blob.encodeNat n).length + n → μ.readable a = true) :
    (∃ ω' μ' s' q h', FreeStepsH p (refineContract env) 20626 ω μ x t ω' μ' x
        (35000 + loopSteps 16384 (n - 16384)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (A + 56) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775825 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 n ∧
      μ'.readN q n = μ.readN (ptr + 1 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1 - (Blob.encodeNat n).length - n) ∧
      Rep μ' s' ∧ WF s' ∧ FirstOk s' ∧ rdN μ' 206848 1 = 0 ∧
      (∃ c ∈ chunks s', c.addr + 32 = q ∧ c.used = true ∧ c.size = (n + 31) / 32 + 1) ∧ s'.base = s.base ∧
      HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧ PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 32 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ' s'' q'' n'', FreeStepsH p (refineContract env) 20626 ω μ x 33055 ω' μ' x
        (35000 + loopSteps 16384 (n - 16384)) ∧
      ω'[7] = UInt64.ofNat 0 ∧ realloc (growTo pb) hb s'' q'' 1 n'' = none ∧ Rep μ' s'' ∧ WF s'') := by
  have hA2 := F.hA
  have hO64 : O < 18446744073709551616 := by omega
  have hw1 : 1 ≤ (Blob.encodeNat n).length := by
    unfold Blob.encodeNat; split
    · simp
    · split <;> simp
  generalize hW : (Blob.encodeNat n).length = w at *
  have hws : ∀ a, A - 400 ≤ a → a < A + 56 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  have hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true := fun a h1 h2 => hst a (by omega) (by omega)
  obtain ⟨ω1, run1, e0, e1, e5, e6⟩ := dispatch (p := p) (P := P) (R := refineContract env) x ω μ A 18 (by decide)
    (by omega) F.h1 h7 tag tab (F.hr A (by omega) (by omega)) hrt
  obtain ⟨ω2, run2, f0, f1, f5, f6, f7, f8⟩ := k1 (p := p) (P := P) (R := refineContract env) x ω1 μ
  obtain ⟨ω3, μ3, run3, g0, g1, g5, g6, g7, g8, g9, gs0, gs5, gs6, gfr, grd, gwr⟩ :=
    o1 (p := p) (P := P) (R := refineContract env) x ω2 μ A A rd 1006 O rd ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega) (by omega) (by omega) (by rw [f0])
      (by rw [f1, e1, F.h1]) (by rw [f5, e5, F.h5]) (by rw [f6, e6, h6]) (by rw [f7, e1, F.h1])
      (by rw [f8, e6, h6]) (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨k0, k1', -, -, -, k5, k6, -, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := refineContract env) x ω3 μ3 1682 35970 (A - 56) rd (A - 25) ptr len 1 g0 g1
      g7 g8 g9 (by decide) jte_840 bs_35970 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) hlen.2 (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [gwr]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [grd]; exact hra a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => gfr _ (by omega) (by omega))]; exact hR8)
  have htag : μ4.read (A - 56 + 31) = 1 := by
    rw [show A - 56 + 31 = A - 25 by omega, read_of_readN1 kbuf, ← hsome]
    exact gfr ptr (by omega) (by omega)
  obtain ⟨ω5, run5, m0, m1, m5, m6, m7⟩ := o_some (p := p) (P := P) (R := refineContract env) x ω4 μ4 (A - 56)
    ⟨by omega, by omega⟩ (by rw [k1', g1]) k7 htag
    (by rw [krd, grd]; exact Memory.readable_of_writable (hws _ (by omega) (by omega)))
  have pay4 : ∀ a, ptr ≤ a → a < ptr + 1 + w + n → μ4.read a = μ.read a := fun a h1 h2 =>
    (kfr a (by omega) (by omega) (by omega) (by omega)).trans (gfr a (by omega) (by omega))
  obtain ⟨ω6, μ6, run6, ⟨d0, d1, -, -, -, d5, d6, -, d7, d8, dR0, dR8, dfr, drd, dwr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContract env) x ω5 μ4 1684 35994 (A - 56) rd (ptr + 1) (len - 1) m0
      (by rw [m1, k1', g1]) (by rw [m7, k6, g6]) (by decide) jte_841 bs_35994 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [kwr, gwr]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr]; exact hwr a h1 h2) kR0 kR8 n (by omega)
      (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd]; exact hra a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => pay4 _ (by omega) (by omega))]; exact henc)
  rw [hW] at dR0 dR8
  obtain ⟨ω7, run7, o0, o1', o5, o6, o7, o8, o9⟩ := o_len (p := p) (P := P) (R := refineContract env) x ω6 μ6
    (A - 56) n (by omega) (by omega) (by rw [d1, m1, k1', g1]) d7 d8
  -- the heap is as it was so far
  have b6 : ∀ a, a < 4294967296 → (a < A - 400 ∨ A ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ6.read a = μ.read a :=
    fun a h0 h1 h2 => (dfr a h0 (by omega) h2).trans ((kfr a h0 (by omega) h2 (by omega)).trans (gfr a h0 (by omega)))
  have wr6 : ∀ a, μ6.writable a = μ.writable a := fun a => by rw [dwr, kwr, gwr]
  have rd6 : ∀ a, μ6.readable a = μ.readable a := fun a => by rw [drd, krd, grd]
  have rep6 : Rep μ6 s := hrep.congr_lock hwf hb0 hbT fun a ha1 ha2 ha3 => b6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hl6 : rdN μ6 206848 1 = 0 := by
    rw [rdN_frame (fun j hj => b6 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))]; exact hl
  have hv6 : ω7[6] = UInt64.ofNat rd := by rw [o6, d6, m6, k6, g6]
  have hbig := vec_u8_big (p := p) (P := P) env x ω7 μ6 s s1 (A - 56) (A - 56) rd (ptr + 1 + w) (len - 1 - w) n 1686
      36016 A rd q0 pb ph hwf rep6 hbd h48 hhb hbs hcost h hb0 hbT hA hfo hl6 (S0 := S0) (S1 := S1) hHTs
      ⟨by omega, by omega⟩ hSb (HeapPages.of_eq hp wr6) (fun a h1 h2 => by rw [wr6]; exact hst a h1 h2) hHT hS1
      ⟨by omega, by omega, by omega⟩ o0 (by rw [o1', d1, m1, k1', g1]) (by rw [o5, d5, m5, k5, g5]) hv6 o7
      (by rw [o8, d6, m6, k6, g6]) o9 (by decide) jte_842 bs_36016 (by omega) (by omega) hn (by omega) (by omega)
      ⟨by omega, by omega⟩ ⟨Nat.le_refl _, by omega⟩ (by omega) ⟨by omega, by omega⟩ (by omega) dR0 dR8
      (fun a h1 h2 => by rw [rd6]; exact hra a (by omega) (by omega))
  have run07 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  rcases hbig with ⟨ω8, μ8, s', q, h', run8, v0, v1, v5', v6', vc, vp, vl, vdata, vR0, vR8, rep8, wf8, fo8, cl8, cm8,
      hbase', hp8', hHT8, hph, hpb, hst8, pg8, vfr⟩ | ⟨ω8, μ8, s'', q'', n'', run8, f7, fR, frep, fwf⟩
  rotate_left
  · exact Or.inr ⟨ω8, μ8, s'', q'', n'', (run07.trans run8).mono (by omega), f7, fR, frep, fwf⟩
  -- the copy to A and the variant
  have hfA : ∀ a, A - 32 ≤ a → a < A + 56 → a ≠ A - 25 → μ8.read a = μ3.read a := fun a h1 h2 h3 =>
    (vfr a (by omega) (by omega) (by omega) (by omega)).trans ((dfr a (by omega) (by omega) (by omega)).trans
      (kfr a (by omega) (by omega) (by omega) (by omega)))
  have hqT : q + n < 2147483648 := by
    obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := cm8
    have := chunk_in wf8 hcrm hcru; rw [hcrs] at this; omega
  obtain ⟨ω9, μ9, run9, c0, c1, c5, c6, cO, cO8, cO16, cfr, crd, cwr⟩ :=
    o_copy (p := p) (P := P) (R := refineContract env) x ω8 μ8 (A - 56) A n q n 1006 21817 O rd
      ⟨by omega, by omega⟩ (by omega) (by omega) v1 v5' (by omega) (by omega) (by omega) hO64 (by omega) vc vp vl
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 48 = A - 8 by omega]; exact gs0)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 40 = A - 16 by omega]; exact gs5)
      (by rw [Memory.readN_congr (fun j hj => hfA _ (by omega) (by omega) (by omega)), show A - 56 + 32 = A - 24 by omega]; exact gs6)
      (by decide) jte_502 bs_21817
      (fun a h1 h2 => Memory.readable_of_writable (hst8 a (by omega) (by omega)))
      (fun a h1 h2 => hst8 a (by omega) (by omega))
  have hfar : ∀ a, a < 4294967296 → A + 24 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ9.read a = μ.read a :=
    fun a h0 h1 h2 => (cfr a h0 (by omega)).trans ((vfr a h0 (by omega) h2 (by omega)).trans (b6 a h0 (by omega) h2))
  obtain ⟨ω10, μ10, run10, n0, n1, n5, n6, nO, nO8, nO16, nO24, nfr, nrd, nwr⟩ :=
    k2 (p := p) (P := P) (R := refineContract env) x ω9 μ9 A O n q n ret t v5 v6 ⟨by omega, by omega⟩ (by omega)
      (by omega) (by rw [c1]; congr 1; omega) c5 (by omega) (by omega) (by omega) (by omega) F.hv5 F.hv6 cO cO8 cO16
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s0)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s5)
      (by rw [Memory.readN_congr (fun j hj => hfar _ (by omega) (by omega) (by omega))]; exact F.s6)
      F.hret F.hjt F.hbt (fun a h1 h2 => Memory.readable_of_writable (by rw [cwr]; exact hst8 a (by omega) (by omega)))
      (fun a h1 h2 => by rw [cwr]; exact hst8 a (by omega) (by omega))
  -- the heap after the copies: only the stack changed
  have hlow : ∀ a, a < 2147483648 → μ10.read a = μ8.read a := fun a h0 =>
    (nfr a (by omega) (by omega)).trans (cfr a (by omega) (by omega))
  have hb0' : 206864 ≤ s'.base := by rw [hbase']; exact hb0
  have hbT' : s'.base + 1073741824 < 2147483648 := by rw [hbase']; exact hbT
  have run := run07.trans (run8.trans (run9.trans run10))
  have wr10 : ∀ a, μ10.writable a = μ8.writable a := fun a => by rw [nwr, cwr]
  refine Or.inl ⟨ω10, μ10, s', q, h', run.mono (by omega), n0, n1, n5, n6, nO, nO8, nO16, nO24, ?_, ?_, ?_,
    rep8.congr_lock wf8 hb0' hbT' (fun a ha1 ha2 ha3 => hlow a ha2), wf8, fo8,
    by rw [rdN_frame (fun j hj => hlow _ (by omega))]; exact cl8, cm8, hbase',
    HeapPages.of_eq hp8' wr10, hHT8, hph, hpb, fun a h1 h2 => by rw [wr10]; exact hst8 a h1 h2,
    FreeStepsH.pagesOut hbd run, ?_⟩
  · rw [Memory.readN_congr (fun j hj => hlow _ (by omega)), vdata]
    exact Memory.readN_congr (fun j hj => b6 _ (by omega) (by omega) (by omega))
  · have e : ∀ j, j < 8 → μ10.read (rd + j) = μ8.read (rd + j) := fun j hj =>
      (nfr _ (by omega) (by omega)).trans (cfr _ (by omega) (by omega))
    rw [Memory.readN_congr e, vR0]
  · have e : ∀ j, j < 8 → μ10.read (rd + 8 + j) = μ8.read (rd + 8 + j) := fun j hj =>
      (nfr _ (by omega) (by omega)).trans (cfr _ (by omega) (by omega))
    rw [Memory.readN_congr e, vR8]
  · intro a h0 h1 h2 h3
    rw [nfr a h0 h3]; exact hfar a h0 h1 h2

end Services.Bootstrap.Decode.LookedUp
