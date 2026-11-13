import Services.Bootstrap.Acc.Inputs.ItemOperandFill
import Services.Bootstrap.Acc.Inputs.ItemOperandB
import Services.Bootstrap.Acc.Inputs.ItemOperandC
import Services.Bootstrap.Acc.Inputs.CompactU64Call
import Services.Bootstrap.Acc.Inputs.VecU8A
import Services.Bootstrap.Acc.Inputs.OperandHead
import Services.Bootstrap.Acc.Inputs.ReaderAdj

/-!
# `AccumulateItem::decode` (45126), the operand arm composed

The segments of `ItemOperand*.lean`, `cu_call` and two `vv_call`s, under the heap contract.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The allocator's context survives stack-only changes**: memory kept below 2^31 and the same
    page access. -/
theorem HeapCtxC.keep_hi {code : ByteArray} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) (fr : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (wr : ∀ a, μ'.writable a = μ.writable a) : HeapCtxC code pb S0 S1 μ' s := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  exact ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT fun a _ ha2 _ => fr a ha2, H.fo,
    by rw [rdN_frame fun j hj => fr _ (by omega)]; exact H.lock, H.hb0, H.hbT, H.hA,
    H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp wr, hHTs, hHT⟩, H.hSb, H.hS1,
    fun a h1 h2 => by rw [wr]; exact H.st a h1 h2, fun a ha => by rw [wr]; exact H.ro a ha⟩

/-- What a `Vec<u8>` decode of n octets allocates: nothing for n = 0 (the pointer 1, the dangling
    one), else a fresh block of ⌈n / 32⌉ units from the model's `alloc`, a new chunk distinct from
    every allocated one. -/
def VAlloc (pb hb n ptr : Nat) (s s' : State) : Prop :=
  (n = 0 ∧ ptr = 1 ∧ s' = s) ∨
  (0 < n ∧ alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (ptr, s') ∧
    (⟨ptr - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
    ∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (n + 31) / 32 + 1, true⟩)

/-- **The length-prefixed `Vec<u8>` decoder for 0 … 16384 octets** on `HeapCtxC` (39634 → 39708):
    `vv_empty` and `vv_call` together. Either the n octets are at ptr (`VAlloc`), with
    `Vec { cap: n, ptr, len: n }` at out, the context kept for the new state, every allocated chunk
    kept with its data, and the reader advanced past ℰ(n) and the octets; or n > 0 and the model's
    `alloc` fails, and the run reaches the trap at 45975. n ≤ 16384 is the temporary bound. -/
theorem vv_any {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen n pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hn : n ≤ 16384) (hrl : (Blob.encodeNat n).length + n ≤ rlen) (hrl32 : rlen < 4294967296)
    (henc : μ.readN ip (Blob.encodeNat n).length = Blob.encodeNat n)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hsp : 2147483960 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 440 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hrd : sp ≤ rd ∧ rd + 16 ≤ S1)
    (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out) :
    (∃ ptr s' ω' μ', VAlloc pb hb n ptr s s' ∧
      FreeStepsH p (env.rel cap) 39634 ω μ x 39708 ω' μ' x (7 * n + 1800) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      rdN μ' out 8 = n ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = n ∧
      μ'.readN ptr n = μ.readN (ip + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (Blob.encodeNat n).length - n) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (0 < n ∧ alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 39634 ω μ x 45975 ω' μ' x (7 * n + 1800)) := by
  by_cases hz : n = 0
  · subst hz
    have he : Blob.encodeNat 0 = [0] := by simp [Blob.encodeNat]
    rw [he] at henc hrl hsrc ⊢
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at henc hrl hsrc ⊢
    obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
    have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
    have hbT := H.hbT
    have hS1 := H.hS1
    have hb0 := H.hb0
    obtain ⟨ω', μ', r, o0, o8, o16, q0, q8, fr, rd', wr', e0, e1, e5, e6⟩ :=
      vv_empty (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd ip rlen h1 h7 h8 hR0 hR8 (by omega) hrl32
        henc ⟨by omega, by omega⟩
        (Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
        ⟨hsp.1, by omega⟩ ⟨hout.1, by omega⟩ ⟨hrd.1, by omega⟩ dor
        (fun a h1 h2 => H.st a (by omega) (by omega)) (fun a h1 h2 => H.st a (by omega) (by omega))
        (fun a h1 h2 => H.st a (by omega) (by omega))
    have lo : ∀ a, a < 2147483648 → μ'.read a = μ.read a := fun a ha =>
      fr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    refine Or.inl ⟨1, s, ω', μ', Or.inl ⟨rfl, rfl, rfl⟩, r.mono (by omega), HeapCtxC.keep_hi H lo wr',
      fun c hc _ => hc, fun c hc hu a ha => ?_, o0, o8, o16, by simp [PVM.Memory.readN],
      by simpa using q0, by simpa using q8, fun a h0 hs ho hr => fr a h0 (Or.inr hs) ho hr, e0, e1, e5, e6⟩
    have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
    unfold InDataA at ha
    exact lo a (by omega)
  · rcases vv_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s sp out rd ip rlen n pb S0 S1 H h1 h7 h8
        hR0 hR8 ⟨Nat.pos_of_ne_zero hz, hn⟩ hrl hrl32 henc hsrc hsp hSTk hout hrd dor with
      ⟨ptr, s', ω', μ', ha, r, H', keep, hnew, hfresh, keepd, o0, o8, o16, od, q0, q8, fr, e0, e1, e5, e6⟩ |
      ⟨ha, rest⟩
    · exact Or.inl ⟨ptr, s', ω', μ', Or.inr ⟨Nat.pos_of_ne_zero hz, ha, hnew, hfresh⟩, r, H', keep, keepd,
        o0, o8, o16, od, q0, q8, fr, e0, e1, e5, e6⟩
    · exact Or.inr ⟨Nat.pos_of_ne_zero hz, ha, rest⟩

/-- **The work output, 46889 → 39634** (GP v0.8.0 Appendix C, O(l) with tag 0): after the gas
    (ω₈ = g), the tag octet 0 and the output's `Vec<u8>` (n octets, `vv_any`) read from the reader;
    n saved at b, its capacity n at b + 8 and its pointer at b + 16, and the call of 39634 for the
    auth trace (return address 2116). Or n > 0 and the model's `alloc` fails (the run reaches 45975). -/
theorem op_mid_ok {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (b rd ip rlen g n pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (h8 : ω[8] = UInt64.ofNat g) (hg : g < 18446744073709551616)
    (hbs : 2147483960 ≤ b ∧ b % 8 = 0 ∧ b + 424 ≤ rd) (hSTk : S0 + 440 ≤ b) (hrd : rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hn : n ≤ 16384) (hrl : 1 + (Blob.encodeNat n).length + n ≤ rlen) (hrl32 : rlen < 4294967296)
    (ht : μ.readN ip 1 = [0])
    (henc : μ.readN (ip + 1) (Blob.encodeNat n).length = Blob.encodeNat n)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + 1 + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size) :
    (∃ po s1 ω' μ', VAlloc pb hb n po s s1 ∧
      FreeStepsH p (env.rel cap) 46889 ω μ x 39634 ω' μ' x (7 * n + 2000) ∧
      HeapCtxC env.code pb S0 S1 μ' s1 ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s1) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      ω'[0] = UInt64.ofNat 2116 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat g ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = UInt64.ofNat rd ∧
      rdN μ' b 8 = n ∧ rdN μ' (b + 8) 8 = n ∧ rdN μ' (b + 16) 8 = po ∧
      μ'.readN po n = μ.readN (ip + 1 + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 1 + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 1 - (Blob.encodeNat n).length - n) ∧
      (∀ a, a < 4294967296 → b + 24 ≤ a → (a < b + 272 ∨ b + 296 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a)) ∨
    (0 < n ∧ alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 46889 ω μ x 45975 ω' μ' x (7 * n + 2000)) := by
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  have hS1 := H.hS1
  have hl := encodeNat_length_le n
  have hst := H.st
  have hra : ∀ a, ip ≤ a → a < ip + 1 + (Blob.encodeNat n).length + n → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (heapC_writable_data H hcm hcu ⟨by omega, by omega⟩)
  -- the tag octet
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ :=
    op_res (p := p) (P := P) (R := env.rel cap) x ω μ b rd g h1 h6 h7 h8 ⟨by omega, by omega⟩ (by omega) hg
      (fun a h1 h2 => hst a (by omega) (by omega))
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ip := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 rlen := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := env.rel cap) x ω1 μ1 2108 46920 b rd (b + 272) ip rlen 1 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1053]) bs_46920
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by omega) hrl32 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a h1 (by omega)) hR0' hR8'
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (Or.inl (by omega))
  have lo2 : ∀ a, a < 2147483648 → μ2.read a = μ.read a := fun a ha => by
    rw [fr2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), lo1 a ha]
  have mt : rdN μ2 (b + 272) 1 = 0 := by
    unfold rdN; rw [qb, PVM.Memory.readN_congr (μ := μ) (fun j hj => lo1 _ (by omega)), ht]; rfl
  obtain ⟨ω3, r3, c0, c1, c5, c6, c7, c8⟩ :=
    op_t0 (p := p) (P := P) (R := env.rel cap) x ω2 μ2 b (by rw [e1, a1]) e7 mt ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
  have ww2 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s := HeapCtxC.keep_hi H lo2 ww2
  rcases vv_any (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω3 μ2 s b (b + 272) rd (ip + 1) (rlen - 1) n pb S0 S1 H2
      (by rw [c1]) c7 (by rw [c8, e6, a6]) q0 q8 hn (by omega) (by omega)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => lo2 _ (by omega))]; exact henc)
      ⟨c, hcm, hcu, by omega, by omega⟩ ⟨by omega, hbs.2.1⟩ hSTk ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (Or.inl (by omega)) with
    ⟨po, s1, ω4, μ4, va, r4, H4, keep, keepd, o0, o8, o16, od, z0, z8, fr4, f0, f1, f5, f6⟩ | ⟨hpos, ha, ω4, μ4, r4⟩
  · obtain ⟨ω5, μ5, r5, g0, g1, g5, g6, g7, g8, w0, w8, w16, fr5, rd5, wr5⟩ :=
      op_ok (p := p) (P := P) (R := env.rel cap) x ω4 μ4 b n po n (by rw [f1, c1]) o0 o8 o16 (by omega)
        ⟨by omega, by omega⟩ (fun a h1 h2 => by
          have := H4.st a (by omega) (by omega); exact this)
    have lo5 : ∀ a, a < 2147483648 → μ5.read a = μ4.read a := fun a ha => fr5 a (by omega) (Or.inl (by omega))
    refine Or.inl ⟨po, s1, ω5, μ5, va, ((((r1.trans r2).trans r3).trans r4).trans
      ((op_ret1 (p := p) (P := P) (R := env.rel cap) x ω4 μ4 (by rw [f0, c0])).trans r5)).mono (by omega),
      HeapCtxC.keep_hi H4 lo5 wr5, keep, fun c hc hu a ha => ?_, g0, g1, ?_, ?_, g7, ?_, w0, w8, w16, ?_,
      ?_, ?_, fun a h0 h1 h2 h3 => ?_⟩
    · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
      unfold InDataA at ha
      rw [lo5 a (by omega), keepd c hc hu a ha, lo2 a (by omega)]
    · rw [g5, f5, c5, e5, a5]
    · rw [g6, f6, c6, e6, a6]
    · rw [g8, f6, c6, e6, a6]
    · rcases va with ⟨rfl, -, -⟩ | ⟨-, -, hnew, -⟩
      · simp [PVM.Memory.readN]
      · have := Services.Bootstrap.Decode.VecU8.chunk_in H4.wf hnew rfl
        simp only at this
        have := H4.hb0
        have := H4.hbT
        rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => lo5 _ (by omega)), od,
          PVM.Memory.readN_congr (μ := μ) (fun j hj => lo2 _ (by omega))]
    · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (Or.inr (by omega))), z0]
    · rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (Or.inr (by omega))), z8]
    · rw [fr5 a h0 (Or.inr h1), fr4 a h0 (by omega) h2 h3, fr2 a h0 (by omega) h3 (by omega),
        fr1 a h0 (by omega)]
  · exact Or.inr ⟨hpos, ha, ω4, μ4, (((r1.trans r2).trans r3).trans r4).mono (by omega)⟩

/-- **A work error, 46889 → 39634** (GP v0.8.0 Appendix C, O(l) with tag t ∈ 1 … 6: ∞, ☇, ⊚, ⊖, BAD,
    BIG): after the gas (ω₈ = g), the tag octet t read, re-read from the one-octet reader {b + 135, 1}
    (`WorkError::decode`), −1 saved at b + 8 and t at b + 16, and the call of 39634 for the auth trace
    (return address 2116). Stack only. -/
theorem op_mid_err {X : Type} {R : HostRel X} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : X) (ω : Regs) (μ : Memory) (b rd ip rlen g t : Nat)
    (h1 : ω[1] = UInt64.ofNat b) (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (h8 : ω[8] = UInt64.ofNat g) (hg : g < 18446744073709551616)
    (hbs : 2147483648 + 88 ≤ b ∧ b % 8 = 0 ∧ b + 424 ≤ rd) (hrd : rd + 16 < 4294967296)
    (hip : 65536 ≤ ip ∧ ip + 16 < 2147483648)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 1 ≤ rlen) (hrl32 : rlen < 4294967296)
    (ht : rdN μ ip 1 = t) (ht6 : 1 ≤ t ∧ t ≤ 6) (hra : μ.readable ip = true)
    (hwf : ∀ a, b - 88 ≤ a → a < b + 424 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46889 ω μ x 39634 ω' μ' x 300 ∧
      ω'[0] = UInt64.ofNat 2116 ∧ ω'[1] = UInt64.ofNat b ∧ ω'[5] = UInt64.ofNat g ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat (b + 272) ∧ ω'[8] = UInt64.ofNat rd ∧
      rdN μ' (b + 8) 8 = 18446744073709551615 ∧ rdN μ' (b + 16) 8 = t ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 1) ∧
      (∀ a, a < 4294967296 → (a < b - 88 ∨ b + 424 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → b + 24 ≤ a → (a < b + 135 ∨ b + 136 ≤ a) → (a < b + 271 ∨ b + 296 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ :=
    op_res (p := p) (P := P) (R := R) x ω μ b rd g h1 h6 h7 h8 ⟨by omega, by omega⟩ (by omega) hg
      (fun a h1 h2 => hwf a (by omega) h2)
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ip := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 rlen := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 2108 46920 b rd (b + 272) ip rlen 1 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1053]) bs_46920
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      hrl hrl32 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1, show a = ip by omega]; exact hra) hR0' hR8'
  have mt : rdN μ2 (b + 272) 1 = t := by
    unfold rdN at ht ⊢
    rw [qb, PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact ht
  obtain ⟨ω3, μ3, r3, c0, c1, c5, c6, c7, c8, c9, m135, l0, l8, fr3, rd3, wr3⟩ :=
    op_te1 (p := p) (P := P) (R := R) x ω2 μ2 b t (by rw [e1, a1]) e7 mt (by omega) ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [wr2, wr1]; exact hwf a (by omega) h2)
  obtain ⟨ω4, μ4, r4, d0, d1, -, -, -, d5, d6, -, d7, -, -, db, fr4, rd4, wr4⟩ :=
    read_ok_adj (p := p) (P := P) (R := R) x ω3 μ3 2110 46974 b (b + 272) (b + 271) (b + 135) 1 1 c0 c1 c7 c8 c9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1054]) bs_46974
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by decide)
      (by decide) (by decide) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
      (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3, rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
      l0 l8
  have mt' : rdN μ4 (b + 271) 1 = t := by unfold rdN at m135 ⊢; rw [db]; exact m135
  obtain ⟨ω5, μ5, r5, f0, f1, f5, f6, f7, f8, w8, w16, fr5, rd5, wr5⟩ :=
    op_te2 (p := p) (P := P) (R := R) x ω4 μ4 b t (by rw [d1, c1]) d7 mt' ht6 ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [wr4, wr3, wr2, wr1]; exact hwf a (by omega) h2)
  have run : FreeStepsH p R 46889 ω μ x 39634 ω5 μ5 x 300 :=
    ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega)
  refine ⟨ω5, μ5, run, f0, f1, by rw [f5, d5, c5, e5, a5], by rw [f6, d6, c6, e6, a6], f7,
    by rw [f8, d6, c6, e6, a6], w8, w16, ?_, ?_, ?_, ?_, fun a => by rw [rd5, rd4, rd3, rd2, rd1],
    fun a => by rw [wr5, wr4, wr3, wr2, wr1]⟩
  · rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => by
      rw [fr5 _ (by omega) (by omega), fr4 _ (by omega) (by omega) (by omega) (by omega),
        fr3 _ (by omega) (by omega) (by omega)]), q0]
  · rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => by
      rw [fr5 _ (by omega) (by omega), fr4 _ (by omega) (by omega) (by omega) (by omega),
        fr3 _ (by omega) (by omega) (by omega)]), q8]
  · intro a h0 hs hr
    rw [fr5 a h0 (by omega), fr4 a h0 (by omega) (by omega) (by omega), fr3 a h0 (by omega) (by omega),
      fr2 a h0 (by omega) hr (by omega), fr1 a h0 (by omega)]
  · intro a h0 hs h135 h271 hr
    rw [fr5 a h0 (by omega), fr4 a h0 (by omega) (by omega) (by omega), fr3 a h0 h135 (by omega),
      fr2 a h0 (by omega) hr (by omega), fr1 a h0 (by omega)]

/-- **The auth trace and the operand slot, 39634 → 47332** (GP v0.8.0 §12, 𝕌's t): the trace's
    `Vec<u8>` (n octets, `vv_any`) read into b + 272, then the 184-octet slot at out (b + 24) filled:
    + 0 n, + 8 the trace's pointer, + 16 n, + 24 / + 32 / + 40 the work result (b + 8, b + 16, b),
    + 48 p, + 80 e, + 112 a, + 144 y (from b + 32, + 64, + 96, + 136) and + 176 g; ω₀, ω₅, ω₆ restored
    and the frame popped, at the return's `jumpInd`. Or n > 0 and the model's `alloc` fails. -/
theorem op_end {X : Type} {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (b out rd it rlen g n pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h0 : ω[0] = UInt64.ofNat 2116) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat g)
    (h7 : ω[7] = UInt64.ofNat (b + 272)) (h8 : ω[8] = UInt64.ofNat rd) (hg : g < 18446744073709551616)
    (m24 : rdN μ (b + 24) 8 = out)
    (hbs : 2147483960 ≤ b ∧ b % 8 = 0 ∧ b + 424 ≤ rd) (hSTk : S0 + 440 ≤ b) (hrd : rd + 16 ≤ S1)
    (hout : b + 424 ≤ out ∧ out + 184 ≤ S1) (dor : out + 184 ≤ rd ∨ rd + 16 ≤ out)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 it) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hn : n ≤ 16384) (hrl : (Blob.encodeNat n).length + n ≤ rlen) (hrl32 : rlen < 4294967296)
    (henc : μ.readN it (Blob.encodeNat n).length = Blob.encodeNat n)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ it ∧
      it + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size) :
    (∃ pt s2 ω' μ', VAlloc pb hb n pt s s2 ∧
      FreeStepsH p (env.rel cap) 39634 ω μ x 47332 ω' μ' x (7 * n + 2000) ∧
      HeapCtxC env.code pb S0 S1 μ' s2 ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s2) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      ω'[0] = UInt64.ofNat (rdN μ (b + 416) 8) ∧ ω'[1] = UInt64.ofNat (b + 424) ∧
      ω'[5] = UInt64.ofNat (rdN μ (b + 408) 8) ∧ ω'[6] = UInt64.ofNat (rdN μ (b + 400) 8) ∧
      rdN μ' out 8 = n ∧ rdN μ' (out + 8) 8 = pt ∧ rdN μ' (out + 16) 8 = n ∧
      rdN μ' (out + 24) 8 = rdN μ (b + 8) 8 ∧ rdN μ' (out + 32) 8 = rdN μ (b + 16) 8 ∧
      rdN μ' (out + 40) 8 = rdN μ b 8 ∧
      Words4 μ' (out + 48) μ (b + 32) ∧ Words4 μ' (out + 80) μ (b + 64) ∧ Words4 μ' (out + 112) μ (b + 96) ∧
      Words4 μ' (out + 144) μ (b + 136) ∧ rdN μ' (out + 176) 8 = g ∧
      μ'.readN pt n = μ.readN (it + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (it + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (Blob.encodeNat n).length - n) ∧
      (∀ a, a < 4294967296 → b ≤ a → (a < b + 272 ∨ b + 296 ≤ a) → (a < out ∨ out + 184 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a)) ∨
    (0 < n ∧ alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 39634 ω μ x 45975 ω' μ' x (7 * n + 2000)) := by
  have hS1 := H.hS1
  rcases vv_any (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω μ s b (b + 272) rd it rlen n pb S0 S1 H
      h1 h7 h8 hR0 hR8 hn hrl hrl32 henc hsrc ⟨by omega, hbs.2.1⟩ hSTk ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inl (by omega)) with
    ⟨pt, s2, ω1, μ1, va, r1, H1, keep, keepd, o0, o8, o16, od, z0, z8, fr1, f0, f1, f5, f6⟩ | ⟨hpos, ha, ω1, μ1, r1⟩
  · have hst := H1.st
    -- the frame from μ, at b and above (outside the trace's Vec and the reader)
    have kb : ∀ o, b ≤ o → (o + 8 ≤ b + 272 ∨ b + 296 ≤ o) → o + 8 ≤ b + 424 → rdN μ1 o 8 = rdN μ o 8 :=
      fun o h1 h2 h3 => rdN_frame fun j hj => fr1 _ (by omega) (by omega) (by omega) (by omega)
    obtain ⟨ω2, μ2, r2, k1, k2, k3, k4, k5, k7, k8, k9, s32, s40, s48, s56, s64, s72, s80, s88, fr2, rd2, wr2⟩ :=
      op_fill1 (p := p) (P := P) (R := env.rel cap) x ω1 μ1 b out g (by rw [f1, h1]) (by rw [f5, h5])
        (by rw [kb _ (by omega) (by omega) (by omega)]; exact m24) (by rw [o0]; omega) hg
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr hout.1)
        (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => hst a (by omega) (by omega))
    have hw2 : ∀ a, μ2.writable a = μ1.writable a := wr2
    obtain ⟨ω3, μ3, r3, l1, l2, l3, l4, l5, l9, l11, t96, t104, t112, t120, t128, t136, t144, t152, t0, fr3, rd3,
        wr3⟩ :=
      op_fill2 (p := p) (P := P) (R := env.rel cap) x ω2 μ2 b out (rdN μ1 (b + 272) 8) (rdN μ1 (b + 80) 8)
        (rdN μ1 (b + 88) 8) k1 k5 k7 k8 k9 (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr hout.1)
        (fun a h1 h2 => by rw [rd2]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => by rw [hw2]; exact hst a (by omega) (by omega))
    obtain ⟨ω4, μ4, r4, n0, n1, n5, n6, u8, u16, u24, u160, u168, u176, fr4, rd4, wr4⟩ :=
      op_fill3 (p := p) (P := P) (R := env.rel cap) x ω3 μ3 b out (rdN μ1 (b + 280) 8) (rdN μ1 (b + 288) 8) g
        (rdN μ2 (b + 152) 8) (rdN μ2 (b + 160) 8) l1 l5 (by rw [l2, k2]) (by rw [l3, k3]) (by rw [l4, k4]) l9 l11
        (rdN_lt64 _ _) (rdN_lt64 _ _) hg (rdN_lt64 _ _) (rdN_lt64 _ _)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr hout.1)
        (fun a h1 h2 => by rw [rd3, rd2]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => by rw [wr3, hw2]; exact hst a (by omega) (by omega))
    -- the b frame, unchanged by the fill (all of it at out)
    have kf : ∀ o, b ≤ o → o + 8 ≤ b + 424 → ∀ μ' : Memory, (∀ a, a < 4294967296 → (a < out ∨ out + 184 ≤ a) →
        μ'.read a = μ1.read a) → rdN μ' o 8 = rdN μ1 o 8 :=
      fun o h1 h2 μ' h => rdN_frame fun j hj => h _ (by omega) (Or.inl (by omega))
    have f21 : ∀ a, a < 4294967296 → (a < out ∨ out + 184 ≤ a) → μ2.read a = μ1.read a :=
      fun a h0 h => fr2 a h0 (by omega)
    have f31 : ∀ a, a < 4294967296 → (a < out ∨ out + 184 ≤ a) → μ3.read a = μ1.read a :=
      fun a h0 h => by rw [fr3 a h0 (by omega) (by omega), f21 a h0 h]
    have f41 : ∀ a, a < 4294967296 → (a < out ∨ out + 184 ≤ a) → μ4.read a = μ1.read a :=
      fun a h0 h => by rw [fr4 a h0 (by omega) (by omega), f31 a h0 h]
    -- slot words, from their fill to μ4
    have w2 : ∀ o, out + 32 ≤ o → o + 8 ≤ out + 96 → rdN μ4 o 8 = rdN μ2 o 8 := fun o h1 h2 =>
      by rw [rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega),
        rdN_frame fun j hj => fr3 _ (by omega) (by omega) (by omega)]
    have w3 : ∀ o, out + 32 ≤ o → o + 8 ≤ out + 160 → rdN μ4 o 8 = rdN μ3 o 8 := fun o h0 h1 =>
      rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega)
    have lo4 : ∀ a, a < 2147483648 → μ4.read a = μ1.read a := fun a ha => f41 a (by omega) (Or.inl (by omega))
    refine Or.inl ⟨pt, s2, ω4, μ4, va, ((((r1.trans (op_ret2 (p := p) (P := P) (R := env.rel cap) x ω1 μ1
        (by rw [f0, h0]))).trans r2).trans r3).trans r4).mono (by omega),
      HeapCtxC.keep_hi H1 lo4 (fun a => by rw [wr4, wr3, wr2]), keep, fun c hc hu a ha => ?_,
      by rw [n0, kf _ (by omega) (by omega) μ3 f31, kb _ (by omega) (by omega) (by omega)], n1,
      by rw [n5, kf _ (by omega) (by omega) μ3 f31, kb _ (by omega) (by omega) (by omega)],
      by rw [n6, kf _ (by omega) (by omega) μ3 f31, kb _ (by omega) (by omega) (by omega)],
      by rw [rdN_frame fun j hj => fr4 _ (by omega) (by omega) (by omega), t0, o0], by rw [u8, o8], by rw [u16, o16],
      by rw [u24, kf _ (by omega) (by omega) μ3 f31, kb _ (by omega) (by omega) (by omega)],
      by rw [w2 _ (by omega) (by omega), s32, kb _ (by omega) (by omega) (by omega)],
      by rw [w2 _ (by omega) (by omega), s40, kb _ (by omega) (by omega) (by omega), Nat.add_zero],
      ⟨by rw [w2 _ (by omega) (by omega), s48, kb _ (by omega) (by omega) (by omega)],
        by rw [w2 _ (by omega) (by omega), s56, kb _ (by omega) (by omega) (by omega)],
        by rw [w2 _ (by omega) (by omega), s64, kb _ (by omega) (by omega) (by omega)],
        by rw [w2 _ (by omega) (by omega), s72, kb _ (by omega) (by omega) (by omega)]⟩,
      ⟨by rw [w2 _ (by omega) (by omega), s80, kb _ (by omega) (by omega) (by omega)],
        by rw [w2 _ (by omega) (by omega), s88, kb _ (by omega) (by omega) (by omega)],
        by rw [w3 _ (by omega) (by omega), t96, kb _ (by omega) (by omega) (by omega)],
        by rw [w3 _ (by omega) (by omega), t104, kb _ (by omega) (by omega) (by omega)]⟩,
      ⟨by rw [w3 _ (by omega) (by omega), t112, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)],
        by rw [w3 _ (by omega) (by omega), t120, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)],
        by rw [w3 _ (by omega) (by omega), t128, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)],
        by rw [w3 _ (by omega) (by omega), t136, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)]⟩,
      ⟨by rw [w3 _ (by omega) (by omega), t144, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)],
        by rw [w3 _ (by omega) (by omega), t152, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)],
        by rw [u160, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)],
        by rw [u168, kf _ (by omega) (by omega) μ2 f21, kb _ (by omega) (by omega) (by omega)]⟩,
      u176, ?_, ?_, ?_, fun a h0 hb' h2 h3 h4 => by rw [f41 a h0 h3, fr1 a h0 hb' h2 h4]⟩
    · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
      have := H.hbT
      unfold InDataA at ha
      rw [lo4 a (by omega), keepd c hc hu a ha]
    · rcases va with ⟨rfl, -, -⟩ | ⟨-, -, hnew, -⟩
      · simp [PVM.Memory.readN]
      · have := Services.Bootstrap.Decode.VecU8.chunk_in H1.wf hnew rfl
        simp only at this
        have := H1.hb0
        have := H1.hbT
        rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => lo4 _ (by omega)), od]
    · rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => f41 _ (by omega) (by omega)), z0]
    · rw [PVM.Memory.readN_congr (μ := μ1) (fun j hj => f41 _ (by omega) (by omega)), z8]
  · exact Or.inr ⟨hpos, ha, ω1, μ1, r1.mono (by omega)⟩

end Services.Bootstrap.Acc
