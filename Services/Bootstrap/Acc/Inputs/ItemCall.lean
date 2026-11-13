import Services.Bootstrap.Acc.Inputs.OperandArm
import Services.Bootstrap.Acc.Inputs.Item

/-!
# `AccumulateItem::decode` (45126 → 47332): an operand

`it_pre` and the read of the tag octet 0, then `op_call_ok` / `op_call_err`; ω₀, ω₅, ω₆ restored.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **45126 → 46300 for the tag 0**: `it_pre` and the tag octet read into b + 272 (b = sp − 424). -/
theorem item_pre0 {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : X) (ω : Regs) (μ : Memory) (sp out rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat sp)
    (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 1 ≤ rlen) (hrl32 : rlen < 4294967296) (htag : rdN μ ip 1 = 0)
    (hip : 65536 ≤ ip ∧ ip + 16 < 2147483648) (hra : μ.readable ip = true)
    (hsp : 2147483648 + 512 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out < 18446744073709551616)
    (hrd : sp ≤ rd ∧ rd + 16 < 4294967296)
    (hwf : ∀ a, sp - 512 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 45126 ω μ x 46300 ω' μ' x 100 ∧
      ω'[1] = UInt64.ofNat (sp - 424) ∧ ω'[5] = UInt64.ofNat rd ∧ ω'[6] = UInt64.ofNat out ∧
      ω'[7] = UInt64.ofNat 0 ∧ rdN μ' (sp - 424 + 272) 1 = 0 ∧
      rdN μ' (sp - 424 + 416) 8 = ω[0].toNat ∧ rdN μ' (sp - 424 + 408) 8 = ω[5].toNat ∧
      rdN μ' (sp - 424 + 400) 8 = ω[6].toNat ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 1) ∧
      (∀ a, a < 4294967296 → (a < sp - 512 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, a10, s8, s16, s24, fr1, rd1, wr1⟩ :=
    it_pre (p := p) (P := P) (R := R) x ω μ sp out rd h1 h7 h8 ⟨by omega, hsp.2⟩ hout.2 hrd64
      (fun a h1 h2 => hwf a (by omega) h2)
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ip := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 rlen := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 2082 46300 (sp - 424) rd (sp - 152) ip rlen 1 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1040]) bs_46300
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide) hrl hrl32
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1, show a = ip by omega]; exact hra) hR0' hR8'
  have k : ∀ o, sp - 24 ≤ o → o + 8 ≤ sp → rdN μ2 o 8 = rdN μ1 o 8 := fun o h1 h2 =>
    rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
  refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), by rw [e1, a1], by rw [e5, a5], by rw [e6, a6], e7, ?_,
    by rw [show sp - 424 + 416 = sp - 8 by omega, k _ (by omega) (by omega), s8],
    by rw [show sp - 424 + 408 = sp - 16 by omega, k _ (by omega) (by omega), s16],
    by rw [show sp - 424 + 400 = sp - 24 by omega, k _ (by omega) (by omega), s24], q0, q8,
    fun a h0 hs hr => ?_, fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  · unfold rdN at htag ⊢
    rw [show sp - 424 + 272 = sp - 152 by omega, qb,
      PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (Or.inl (by omega)))]; exact htag
  · rw [fr2 a h0 (by omega) hr (by omega), fr1 a h0 (by omega)]

/-- **`AccumulateItem::decode` of an operand with a work output, 45126 → 47332** (GP v0.8.0 §12, 𝕌,
    and Appendix C: the tag 0, then ℰ(p, e, a, y, g, O(l), ↕t) with l's tag 0): `item_pre0` and
    `op_call_ok`, with ω₀, ω₁, ω₅, ω₆ as at the call. -/
theorem item_op_ok {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen g no nt pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hsp : 2147483960 + 424 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 864 ≤ sp)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hout : sp ≤ out ∧ out + 184 ≤ S1) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hg : g < 18446744073709551616) (hno : no ≤ 16384) (hnt : nt ≤ 16384)
    (hrl : 1 + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no +
      (Blob.encodeNat nt).length + nt) ≤ rlen) (hrl32 : rlen < 4294967296)
    (htag : μ.readN ip 1 = [0])
    (heg : μ.readN (ip + 1 + 128) (Blob.encodeNat g).length = Blob.encodeNat g)
    (ht0 : μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length) 1 = [0])
    (heo : μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length + 1) (Blob.encodeNat no).length = Blob.encodeNat no)
    (het : μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no)
      (Blob.encodeNat nt).length = Blob.encodeNat nt)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + 1 + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length + no +
        (Blob.encodeNat nt).length + nt) + 32 ≤ c.addr + 32 * c.size) :
    (∃ po pt s1 s2 ω' μ', VAlloc pb hb no po s s1 ∧ VAlloc pb hb nt pt s1 s2 ∧
      FreeStepsH p (env.rel cap) 45126 ω μ x 47332 ω' μ' x (7 * no + 7 * nt + 7100) ∧
      HeapCtxC env.code pb S0 S1 μ' s2 ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s2) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' out 8 = nt ∧ rdN μ' (out + 8) 8 = pt ∧ rdN μ' (out + 16) 8 = nt ∧
      rdN μ' (out + 24) 8 = no ∧ rdN μ' (out + 32) 8 = po ∧ rdN μ' (out + 40) 8 = no ∧
      Words4 μ' (out + 48) μ (ip + 1) ∧ Words4 μ' (out + 80) μ (ip + 1 + 32) ∧
      Words4 μ' (out + 112) μ (ip + 1 + 64) ∧ Words4 μ' (out + 144) μ (ip + 1 + 96) ∧
      rdN μ' (out + 176) 8 = g ∧
      μ'.readN po no = μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length) no ∧
      μ'.readN pt nt = μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat no).length +
        no + (Blob.encodeNat nt).length) nt ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 1 + (128 + (Blob.encodeNat g).length + 1 +
        (Blob.encodeNat no).length + no + (Blob.encodeNat nt).length + nt)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 1 - (128 + (Blob.encodeNat g).length + 1 +
        (Blob.encodeNat no).length + no + (Blob.encodeNat nt).length + nt)) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 184 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45975 ω' μ' x (7 * no + 7 * nt + 7100)) := by
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨ω1, μ1, r1, a1, a5, a6, a7, mt, s416, s408, s400, R0, R8, fr1, rd1, wr1⟩ :=
    item_pre0 (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd ip rlen h1 h7 h8 hR0 hR8 (by omega) (by omega)
      (by unfold rdN; rw [htag]; rfl) ⟨by omega, by omega⟩
      (Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
      ⟨by omega, by omega⟩ ⟨hout.1, by omega⟩ ⟨hrd.1, by omega⟩
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s := HeapCtxC.keep_hi H lo1 wr1
  have kk : ∀ o n, o + n ≤ 2147483648 → μ1.readN o n = μ.readN o n := fun o n h =>
    PVM.Memory.readN_congr fun j hj => lo1 _ (by omega)
  rcases op_call_ok (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s (sp - 424) out rd (ip + 1) (rlen - 1)
      g no nt pb S0 S1 H1 a1 a5 a6 a7 mt ⟨by omega, by omega, by omega⟩ (by omega) hrd.2
      ⟨by omega, hout.2⟩ dor R0 R8 hg hno hnt (by omega) (by omega)
      (by rw [kk _ _ (by omega)]; exact heg) (by rw [kk _ _ (by omega)]; exact ht0)
      (by rw [kk _ _ (by omega)]; exact heo) (by rw [kk _ _ (by omega)]; exact het)
      ⟨c, hcm, hcu, by omega, by omega⟩ with
    ⟨po, pt, s1, s2, ω2, μ2, va1, va2, r2, H2, keep, keepd, e0, e1, e5, e6, x0, x8, x16, x24, x32, x40, X48, X80,
      X112, X144, x176, od, td, R0f, R8f, fr2⟩ | ⟨ω2, μ2, r2⟩
  · have wk : ∀ i, i + 32 ≤ 2147483648 → ∀ j, j < 32 → μ1.read (i + j) = μ.read (i + j) :=
      fun i h j hj => lo1 _ (by omega)
    have wsame : ∀ {o i : Nat}, Words4 μ2 o μ1 i → i + 32 ≤ 2147483648 → Words4 μ2 o μ i :=
      fun w h => (w.trans' (μ1 := μ1) (fun j hj => rfl) (by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> exact rdN_frame fun j hj => lo1 _ (by omega)))
    refine Or.inl ⟨po, pt, s1, s2, ω2, μ2, va1, va2, (r1.trans r2).mono (by omega), H2, keep,
      fun c hc hu a ha => ?_, by rw [e0, s416, UInt64.ofNat_toNat], by rw [e1, show sp - 424 + 424 = sp by omega],
      by rw [e5, s408, UInt64.ofNat_toNat], by rw [e6, s400, UInt64.ofNat_toNat], x0, x8, x16, x24, x32, x40,
      wsame X48 (by omega), wsame X80 (by omega), wsame X112 (by omega), wsame X144 (by omega), x176,
      by rw [od, kk _ _ (by omega)], by rw [td, kk _ _ (by omega)], by rw [R0f]; all_goals (congr 1 <;> omega),
      by rw [R8f]; all_goals (congr 1 <;> omega), fun a h0 hs ho hr => by
        rw [fr2 a h0 (by omega) ho hr, fr1 a h0 (Or.inr hs) hr]⟩
    rw [keepd c hc hu a ha]
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
    unfold InDataA at ha
    exact lo1 a (by omega)
  · exact Or.inr ⟨ω2, μ2, (r1.trans r2).mono (by omega)⟩

/-- **`AccumulateItem::decode` of an operand with a work error, 45126 → 47332** (GP v0.8.0 §12, 𝕌,
    and Appendix C: the tag 0, then ℰ(p, e, a, y, g, O(l), ↕t) with l's tag t ∈ 1 … 6): `item_pre0` and
    `op_call_err`, with ω₀, ω₁, ω₅, ω₆ as at the call. -/
theorem item_op_err {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen g t nt pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hsp : 2147483960 + 424 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 864 ≤ sp)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hout : sp ≤ out ∧ out + 184 ≤ S1) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hg : g < 18446744073709551616) (ht6 : 1 ≤ t ∧ t ≤ 6) (hnt : nt ≤ 16384)
    (hrl : 1 + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length + nt) ≤ rlen) (hrl32 : rlen < 4294967296)
    (htag : μ.readN ip 1 = [0])
    (heg : μ.readN (ip + 1 + 128) (Blob.encodeNat g).length = Blob.encodeNat g)
    (htt : rdN μ (ip + 1 + 128 + (Blob.encodeNat g).length) 1 = t)
    (het : μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length + 1) (Blob.encodeNat nt).length = Blob.encodeNat nt)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + 1 + (128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length + nt) + 32 ≤
        c.addr + 32 * c.size) :
    (∃ pt s2 ω' μ', VAlloc pb hb nt pt s s2 ∧
      FreeStepsH p (env.rel cap) 45126 ω μ x 47332 ω' μ' x (7 * nt + 7100) ∧
      HeapCtxC env.code pb S0 S1 μ' s2 ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s2) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' out 8 = nt ∧ rdN μ' (out + 8) 8 = pt ∧ rdN μ' (out + 16) 8 = nt ∧
      rdN μ' (out + 24) 8 = 18446744073709551615 ∧ rdN μ' (out + 32) 8 = t ∧
      Words4 μ' (out + 48) μ (ip + 1) ∧ Words4 μ' (out + 80) μ (ip + 1 + 32) ∧
      Words4 μ' (out + 112) μ (ip + 1 + 64) ∧ Words4 μ' (out + 144) μ (ip + 1 + 96) ∧
      rdN μ' (out + 176) 8 = g ∧
      μ'.readN pt nt = μ.readN (ip + 1 + 128 + (Blob.encodeNat g).length + 1 + (Blob.encodeNat nt).length) nt ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 1 + (128 + (Blob.encodeNat g).length + 1 +
        (Blob.encodeNat nt).length + nt)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 1 - (128 + (Blob.encodeNat g).length + 1 +
        (Blob.encodeNat nt).length + nt)) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 184 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (env.rel cap) 45126 ω μ x 45975 ω' μ' x (7 * nt + 7100)) := by
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨ω1, μ1, r1, a1, a5, a6, a7, mt, s416, s408, s400, R0, R8, fr1, rd1, wr1⟩ :=
    item_pre0 (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd ip rlen h1 h7 h8 hR0 hR8 (by omega) (by omega)
      (by unfold rdN; rw [htag]; rfl) ⟨by omega, by omega⟩
      (Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
      ⟨by omega, by omega⟩ ⟨hout.1, by omega⟩ ⟨hrd.1, by omega⟩
      (fun a h1 h2 => hst a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha =>
    fr1 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s := HeapCtxC.keep_hi H lo1 wr1
  have kk : ∀ o n, o + n ≤ 2147483648 → μ1.readN o n = μ.readN o n := fun o n h =>
    PVM.Memory.readN_congr fun j hj => lo1 _ (by omega)
  rcases op_call_err (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω1 μ1 s (sp - 424) out rd (ip + 1) (rlen - 1)
      g t nt pb S0 S1 H1 a1 a5 a6 a7 mt ⟨by omega, by omega, by omega⟩ (by omega) hrd.2
      ⟨by omega, hout.2⟩ dor R0 R8 hg ht6 hnt (by omega) (by omega)
      (by rw [kk _ _ (by omega)]; exact heg) (by rw [rdN, kk _ _ (by omega)]; exact htt)
      (by rw [kk _ _ (by omega)]; exact het)
      ⟨c, hcm, hcu, by omega, by omega⟩ with
    ⟨pt, s2, ω2, μ2, va2, r2, H2, keep, keepd, e0, e1, e5, e6, x0, x8, x16, x24, x32, X48, X80,
      X112, X144, x176, td, R0f, R8f, fr2⟩ | ⟨ω2, μ2, r2⟩
  · have wk : ∀ i, i + 32 ≤ 2147483648 → ∀ j, j < 32 → μ1.read (i + j) = μ.read (i + j) :=
      fun i h j hj => lo1 _ (by omega)
    have wsame : ∀ {o i : Nat}, Words4 μ2 o μ1 i → i + 32 ≤ 2147483648 → Words4 μ2 o μ i :=
      fun w h => (w.trans' (μ1 := μ1) (fun j hj => rfl) (by
        refine ⟨?_, ?_, ?_, ?_⟩ <;> exact rdN_frame fun j hj => lo1 _ (by omega)))
    refine Or.inl ⟨pt, s2, ω2, μ2, va2, (r1.trans r2).mono (by omega), H2, keep,
      fun c hc hu a ha => ?_, by rw [e0, s416, UInt64.ofNat_toNat], by rw [e1, show sp - 424 + 424 = sp by omega],
      by rw [e5, s408, UInt64.ofNat_toNat], by rw [e6, s400, UInt64.ofNat_toNat], x0, x8, x16, x24, x32,
      wsame X48 (by omega), wsame X80 (by omega), wsame X112 (by omega), wsame X144 (by omega), x176,
      by rw [td, kk _ _ (by omega)], by rw [R0f]; all_goals (congr 1 <;> omega),
      by rw [R8f]; all_goals (congr 1 <;> omega), fun a h0 hs ho hr => by
        rw [fr2 a h0 (by omega) ho hr, fr1 a h0 (Or.inr hs) hr]⟩
    rw [keepd c hc hu a ha]
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
    unfold InDataA at ha
    exact lo1 a (by omega)
  · exact Or.inr ⟨ω2, μ2, (r1.trans r2).mono (by omega)⟩

end Services.Bootstrap.Acc
