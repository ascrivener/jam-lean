import Services.Bootstrap.Acc.Inputs.OperandCall

/-!
# `AccumulateItem::decode` (45126), the operand arm (46300 → 47332)

`op_head`, then `op_mid_ok` or `op_mid_err`, then `op_end`, under the heap contract.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- Words copied twice. -/
theorem Words4.trans' {μ0 μ1 μ2 μ3 : Memory} {o i k : Nat} (h : Words4 μ3 o μ2 i)
    (e : ∀ j, j < 32 → μ2.read (i + j) = μ1.read (i + j)) (w : Words4 μ1 i μ0 k) : Words4 μ3 o μ0 k := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  obtain ⟨w0, w1, w2, w3⟩ := w
  have r : ∀ c, c + 8 ≤ 32 → rdN μ2 (i + c) 8 = rdN μ1 (i + c) 8 := fun c hc =>
    rdN_frame fun j hj => by rw [Nat.add_assoc]; exact e (c + j) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h0, show i = i + 0 by rfl, r 0 (by omega)]; exact w0
  · rw [h1, r 8 (by omega)]; exact w1
  · rw [h2, r 16 (by omega)]; exact w2
  · rw [h3, r 24 (by omega)]; exact w3

/-- **The operand arm with a work output, 46300 → 47332** (GP v0.8.0 §12, 𝕌, and Appendix C): the
    reader's octets at ip are ℰ(p, e, a, y) (128), ℰ(g), the work result's tag 0, ℰ(↕o) (n_o octets) and
    ℰ(↕t) (n_t octets), all inside one allocated chunk. Either the 184-octet operand slot at out holds
    n_t, the trace's pointer, n_t, n_o, the output's pointer, n_o, p, e, a, y and g, the two vectors are
    fresh blocks (`VAlloc`) holding o and t, and the reader is past the operand; or one of the two
    allocations fails and the run reaches 45975. n_o, n_t ≤ 16384 is the temporary bound. -/
theorem op_call_ok {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (b out rd ip rlen g no nt pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd) (h6 : ω[6] = UInt64.ofNat out)
    (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = 0)
    (hbs : 2147483960 ≤ b ∧ b % 8 = 0 ∧ b + 424 ≤ rd) (hSTk : S0 + 440 ≤ b) (hrd : rd + 16 ≤ S1)
    (hout : b + 424 ≤ out ∧ out + 184 ≤ S1) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hg : g < 18446744073709551616) (hno : no ≤ 16384) (hnt : nt ≤ 16384)
    (hrl : 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no +
      (Blob.encodeNat nt).length + nt ≤ rlen) (hrl32 : rlen < 4294967296)
    (heg : μ.readN (ip + 128) (Blob.encodeNat g).length = Blob.encodeNat g)
    (ht0 : μ.readN (ip + 128 + (Blob.encodeNat g).length) 1 = [0])
    (heo : μ.readN (ip + 128 + (Blob.encodeNat g).length + 1) (Blob.encodeNat no).length = Blob.encodeNat no)
    (het : μ.readN (ip + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no)
      (Blob.encodeNat nt).length = Blob.encodeNat nt)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no +
        (Blob.encodeNat nt).length + nt) ≤ c.addr + 32 * c.size) :
    (∃ po pt s1 s2 ω' μ', VAlloc pb hb no po s s1 ∧ VAlloc pb hb nt pt s1 s2 ∧
      FreeStepsH p (env.rel cap) 46300 ω μ x 47332 ω' μ' x (7 * no + 7 * nt + 7000) ∧
      HeapCtxC env.code pb S0 S1 μ' s2 ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s2) ∧
      (∀ c ∈ chunks s, c.used = true → c ∈ chunks s1) ∧ (∀ c ∈ chunks s1, c.used = true → c ∈ chunks s2) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      ω'[0] = UInt64.ofNat (rdN μ (b + 416) 8) ∧ ω'[1] = UInt64.ofNat (b + 424) ∧
      ω'[5] = UInt64.ofNat (rdN μ (b + 408) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (b + 400) 8) ∧
      rdN μ' out 8 = nt ∧ rdN μ' (out + 8) 8 = pt ∧ rdN μ' (out + 16) 8 = nt ∧
      rdN μ' (out + 24) 8 = no ∧ rdN μ' (out + 32) 8 = po ∧ rdN μ' (out + 40) 8 = no ∧
      Words4 μ' (out + 48) μ ip ∧ Words4 μ' (out + 80) μ (ip + 32) ∧ Words4 μ' (out + 112) μ (ip + 64) ∧
      Words4 μ' (out + 144) μ (ip + 96) ∧ rdN μ' (out + 176) 8 = g ∧
      μ'.readN po no = μ.readN (ip + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length) no ∧
      μ'.readN pt nt = μ.readN (ip + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no +
        (Blob.encodeNat nt).length) nt ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length +
        no + (Blob.encodeNat nt).length + nt)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (128 + (Blob.encodeNat g).length + 1 +
        (Blob.encodeNat no).length + no + (Blob.encodeNat nt).length + nt)) ∧
      (∀ a, a < 4294967296 → b + 304 ≤ a → (a < out ∨ out + 184 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 46300 ω μ x 45975 ω' μ' x (7 * no + 7 * nt + 7000)) := by
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hst := H.st
  have lg := encodeNat_length_le g
  have hra : ∀ a, ip ≤ a → a < ip + 128 + (Blob.encodeNat g).length → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩)
  -- the hashes and the gas
  obtain ⟨ω1, μ1, r1, a1, a6, a7, a8, s24, W1, W2, W3, W4, R0, R8, fr1, hi1, rd1, wr1⟩ :=
    op_head (p := p) (P := P) (R := env.rel cap) x ω μ b out rd ip rlen g h1 h5 h6 h7 mt
      ⟨by omega, by omega, hbs.2.1⟩ (by omega) ⟨hbs.2.2, by omega⟩ ⟨by omega, by omega⟩ hR0 hR8 (by omega)
      hrl32 hra hg heg (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s := HeapCtxC.keep_hi H lo1 wr1
  -- the work output
  rcases op_mid_ok (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s b rd
      (ip + 128 + (Blob.encodeNat g).length) (rlen - 128 - (Blob.encodeNat g).length) g no pb S0 S1 H1
      a1 a6 a7 a8 hg hbs hSTk hrd R0 R8 hno (by omega) (by omega)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => lo1 _ (by omega))]; exact ht0)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => lo1 _ (by omega))]; exact heo)
      ⟨c, hcm, hcu, by omega, by omega⟩ with
    ⟨po, s1, ω2, μ2, va1, r2, H2, keep1, keepd1, b0, b1, b5, b6, b7, b8, m0, m8, m16, od, R0', R8', fr2⟩ |
    ⟨-, -, ω2, μ2, r2⟩
  · have hc1 : c ∈ chunks s1 := keep1 c hcm hcu
    have k21 : ∀ a, ip ≤ a → a < ip + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no +
        (Blob.encodeNat nt).length + nt) → μ2.read a = μ.read a := fun a h1 h2 => by
      rw [keepd1 c hcm hcu a ⟨by omega, by omega⟩, lo1 a (by omega)]
    -- the trace and the slot
    rcases op_end (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s1 b out rd
        (ip + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no)
        (rlen - 128 - (Blob.encodeNat g).length - 1 - (Blob.encodeNat no).length - no) g nt pb S0 S1 H2
        b0 b1 b5 b7 b8 hg
        (by rw [rdN_frame fun j hj => fr2 _ (by omega) (by omega) (by omega) (by omega)]; exact s24)
        hbs hSTk hrd hout dor (by rw [R0']; all_goals (congr 1 <;> omega)) (by rw [R8']; all_goals (congr 1 <;> omega)) hnt (by omega) (by omega)
        (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => k21 _ (by omega) (by omega))]; exact het)
        ⟨c, hc1, hcu, by omega, by omega⟩ with
      ⟨pt, s2, ω3, μ3, va2, r3, H3, keep2, keepd2, e0, e1, e5, e6, x0, x8, x16, x24, x32, x40, X48, X80, X112,
        X144, x176, td, R0f, R8f, fr3⟩ | ⟨-, -, ω3, μ3, r3⟩
    · -- the frame at b, from μ2 back to μ
      have k2 : ∀ a, b + 24 ≤ a → a < b + 424 → (a < b + 272 ∨ b + 296 ≤ a) → μ2.read a = μ1.read a :=
        fun a h1 h2 h3 => fr2 a (by omega) h1 h3 (by omega)
      have kb : ∀ o, b + 304 ≤ o → o + 8 ≤ b + 424 → rdN μ2 o 8 = rdN μ o 8 := fun o h1 h2 => by
        rw [rdN_frame fun j hj => k2 _ (by omega) (by omega) (by omega),
          rdN_frame fun j hj => hi1 _ (by omega) (by omega) (by omega)]
      have kw : ∀ i, b + 32 ≤ i → i + 32 ≤ b + 272 → ∀ j, j < 32 → μ2.read (i + j) = μ1.read (i + j) :=
        fun i h1 h2 j hj => k2 _ (by omega) (by omega) (by omega)
      refine Or.inl ⟨po, pt, s1, s2, ω3, μ3, va1, va2,
        (((r1.trans r2).trans r3)).mono (by omega), H3, fun c hc hu => keep2 c (keep1 c hc hu) hu, keep1, keep2,
        fun c hc hu a ha => ?_, by rw [e0, kb _ (by omega) (by omega)], e1,
        by rw [e5, kb _ (by omega) (by omega)], by rw [e6, kb _ (by omega) (by omega)], x0, x8, x16,
        by rw [x24, m8], by rw [x32, m16], by rw [x40, m0],
        X48.trans' (kw _ (by omega) (by omega)) W1, X80.trans' (kw _ (by omega) (by omega)) W2,
        X112.trans' (kw _ (by omega) (by omega)) W3, X144.trans' (kw _ (by omega) (by omega)) W4, x176, ?_, ?_,
        by rw [R0f]; congr 1; omega, by rw [R8f]; congr 1; omega, fun a h0 h hout' hr => ?_⟩
      · rw [keepd2 c (keep1 c hc hu) hu a ha, keepd1 c hc hu a ha]
        have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
        unfold InDataA at ha
        exact lo1 a (by omega)
      · rcases va1 with ⟨rfl, -, -⟩ | ⟨-, -, hnew, -⟩
        · simp [PVM.Memory.readN]
        · have := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hnew rfl
          simp only at this
          have := H2.hb0
          have := H2.hbT
          rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => keepd2 _ hnew rfl _ ⟨by simp only; omega,
            by simp only; omega⟩), od,
            PVM.Memory.readN_congr (μ := μ) (fun j hj => lo1 _ (by omega))]
      · rw [td, PVM.Memory.readN_congr (μ := μ) (fun j hj => k21 _ (by omega) (by omega))]
      · rw [fr3 a h0 (by omega) (by omega) hout' hr, fr2 a h0 (by omega) (by omega) hr, hi1 a h0 h hr]
    · exact Or.inr ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega)⟩
  · exact Or.inr ⟨ω2, μ2, (r1.trans r2).mono (by omega)⟩

/-- **The operand arm with a work error, 46300 → 47332** (GP v0.8.0 §12, 𝕌, and Appendix C): the
    reader's octets at ip are ℰ(p, e, a, y) (128), ℰ(g), the work result's tag t ∈ 1 … 6 (∞, ☇, ⊚, ⊖,
    BAD, BIG) and ℰ(↕t) (n_t octets), all inside one allocated chunk. Either the operand slot at out
    holds n_t, the trace's pointer, n_t, −1 (no output), t, then p, e, a, y and g, the trace
    is a fresh block (`VAlloc`), and the reader is past the operand; or the trace's allocation fails and
    the run reaches 45975. n_t ≤ 16384 is the temporary bound. -/
theorem op_call_err {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (b out rd ip rlen g t nt pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd) (h6 : ω[6] = UInt64.ofNat out)
    (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = 0)
    (hbs : 2147483960 ≤ b ∧ b % 8 = 0 ∧ b + 424 ≤ rd) (hSTk : S0 + 440 ≤ b) (hrd : rd + 16 ≤ S1)
    (hout : b + 424 ≤ out ∧ out + 184 ≤ S1) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hg : g < 18446744073709551616) (ht6 : 1 ≤ t ∧ t ≤ 6) (hnt : nt ≤ 16384)
    (hrl : 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length + nt ≤ rlen) (hrl32 : rlen < 4294967296)
    (heg : μ.readN (ip + 128) (Blob.encodeNat g).length = Blob.encodeNat g)
    (htt : rdN μ (ip + 128 + (Blob.encodeNat g).length) 1 = t)
    (het : μ.readN (ip + 128 + (Blob.encodeNat g).length + 1) (Blob.encodeNat nt).length = Blob.encodeNat nt)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length + nt) ≤
        c.addr + 32 * c.size) :
    (∃ pt s2 ω' μ', VAlloc pb hb nt pt s s2 ∧
      FreeStepsH p (env.rel cap) 46300 ω μ x 47332 ω' μ' x (7 * nt + 7000) ∧
      HeapCtxC env.code pb S0 S1 μ' s2 ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s2) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      ω'[0] = UInt64.ofNat (rdN μ (b + 416) 8) ∧ ω'[1] = UInt64.ofNat (b + 424) ∧
      ω'[5] = UInt64.ofNat (rdN μ (b + 408) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (b + 400) 8) ∧
      rdN μ' out 8 = nt ∧ rdN μ' (out + 8) 8 = pt ∧ rdN μ' (out + 16) 8 = nt ∧
      rdN μ' (out + 24) 8 = 18446744073709551615 ∧ rdN μ' (out + 32) 8 = t ∧
      Words4 μ' (out + 48) μ ip ∧ Words4 μ' (out + 80) μ (ip + 32) ∧ Words4 μ' (out + 112) μ (ip + 64) ∧
      Words4 μ' (out + 144) μ (ip + 96) ∧ rdN μ' (out + 176) 8 = g ∧
      μ'.readN pt nt = μ.readN (ip + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length) nt ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length +
        nt)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (128 + (Blob.encodeNat g).length + 1 +
        (Blob.encodeNat nt).length + nt)) ∧
      (∀ a, a < 4294967296 → b + 304 ≤ a → (a < out ∨ out + 184 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 46300 ω μ x 45975 ω' μ' x (7 * nt + 7000)) := by
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hst := H.st
  have lg := encodeNat_length_le g
  have hra : ∀ a, ip ≤ a → a < ip + 128 + (Blob.encodeNat g).length → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩)
  -- the hashes and the gas
  obtain ⟨ω1, μ1, r1, a1, a6, a7, a8, s24, W1, W2, W3, W4, R0, R8, fr1, hi1, rd1, wr1⟩ :=
    op_head (p := p) (P := P) (R := env.rel cap) x ω μ b out rd ip rlen g h1 h5 h6 h7 mt
      ⟨by omega, by omega, hbs.2.1⟩ (by omega) ⟨hbs.2.2, by omega⟩ ⟨by omega, by omega⟩ hR0 hR8 (by omega)
      hrl32 hra hg heg (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s := HeapCtxC.keep_hi H lo1 wr1
  -- the work error
  obtain ⟨ω2, μ2, r2, b0, b1, b5, b6, b7, b8, m8, m16, R0', R8', frl, frh, rd2, wr2⟩ :=
    op_mid_err (p := p) (P := P) (R := env.rel cap) x ω1 μ1 b rd (ip + 128 + (Blob.encodeNat g).length)
      (rlen - 128 - (Blob.encodeNat g).length) g t a1 a6 a7 a8 hg ⟨by omega, hbs.2.1, hbs.2.2⟩ (by omega)
      ⟨by omega, by omega⟩ R0 R8 (by omega) (by omega)
      (by rw [rdN_frame fun j hj => lo1 _ (by omega)]; exact htt) ht6
      (by rw [rd1]; exact Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have lo2 : ∀ a, a < 2147483648 → μ2.read a = μ.read a := fun a ha => by
    rw [frl a (by omega) (Or.inl (by omega)) (Or.inl (by omega)), lo1 a ha]
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s := HeapCtxC.keep_hi H lo2 (fun a => by rw [wr2, wr1])
  rcases op_end (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s b out rd
      (ip + 128 + (Blob.encodeNat g).length + 1)
      (rlen - 128 - (Blob.encodeNat g).length - 1) g nt pb S0 S1 H2
      b0 b1 b5 b7 b8 hg
      (by rw [rdN_frame fun j hj => frh _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact s24)
      hbs hSTk hrd hout dor (by rw [R0']) (by rw [R8']) hnt (by omega) (by omega)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => lo2 _ (by omega))]; exact het)
      ⟨c, hcm, hcu, by omega, by omega⟩ with
    ⟨pt, s2, ω3, μ3, va2, r3, H3, keep2, keepd2, e0, e1, e5, e6, x0, x8, x16, x24, x32, x40, X48, X80, X112,
      X144, x176, td, R0f, R8f, fr3⟩ | ⟨-, -, ω3, μ3, r3⟩
  · have k2 : ∀ a, b + 24 ≤ a → a < b + 424 → (a < b + 135 ∨ b + 136 ≤ a) → (a < b + 271 ∨ b + 296 ≤ a) →
        μ2.read a = μ1.read a := fun a h1 h2 h3 h4 => frh a (by omega) h1 h3 h4 (by omega)
    have kb : ∀ o, b + 304 ≤ o → o + 8 ≤ b + 424 → rdN μ2 o 8 = rdN μ o 8 := fun o h1 h2 => by
      rw [rdN_frame fun j hj => k2 _ (by omega) (by omega) (by omega) (by omega),
        rdN_frame fun j hj => hi1 _ (by omega) (by omega) (by omega)]
    have kw : ∀ i, b + 32 ≤ i → i + 32 ≤ b + 135 ∨ (b + 136 ≤ i ∧ i + 32 ≤ b + 271) →
        ∀ j, j < 32 → μ2.read (i + j) = μ1.read (i + j) :=
      fun i h1 h2 j hj => k2 _ (by omega) (by omega) (by omega) (by omega)
    refine Or.inl ⟨pt, s2, ω3, μ3, va2,
      ((r1.trans r2).trans r3).mono (by omega), H3, fun c hc hu => keep2 c hc hu,
      fun c hc hu a ha => ?_, by rw [e0, kb _ (by omega) (by omega)], e1,
      by rw [e5, kb _ (by omega) (by omega)], by rw [e6, kb _ (by omega) (by omega)], x0, x8, x16,
      by rw [x24, m8], by rw [x32, m16],
      X48.trans' (kw _ (by omega) (by omega)) W1, X80.trans' (kw _ (by omega) (by omega)) W2,
      X112.trans' (kw _ (by omega) (by omega)) W3, X144.trans' (kw _ (by omega) (by omega)) W4, x176, ?_,
      by rw [R0f]; congr 1; omega, by rw [R8f]; congr 1; omega, fun a h0 h hout' hr => ?_⟩
    · rw [keepd2 c hc hu a ha]
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
      unfold InDataA at ha
      exact lo2 a (by omega)
    · rw [td, PVM.Memory.readN_congr (μ := μ) (fun j hj => lo2 _ (by omega))]
    · rw [fr3 a h0 (by omega) (by omega) hout' hr, frh a h0 (by omega) (by omega) (by omega) hr, hi1 a h0 h hr]
  · exact Or.inr ⟨ω3, μ3, ((r1.trans r2).trans r3).mono (by omega)⟩

end Services.Bootstrap.Acc
