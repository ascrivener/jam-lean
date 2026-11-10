import Services.Bootstrap.Acc.Inputs.CompactU64
import Services.Bootstrap.Alloc.Rep

/-!
# The `u64` compact decoder (46856), composed

`cu_pre` reads the prefix octet; `cu_tail_zero`, `cu_tail_mid` and `cu_tail_ff` finish the three
forms of `Dec.compact` (GP v0.8.0 Appendix C's ℰ for naturals); `cu_call` decodes ℰ(g).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **46856 → 39982**: `cu_head` and the read of the prefix octet into s + 8 (s = sp − 40). -/
theorem cu_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp rd ptr len : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat rd)
    (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296) (hlen : 1 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ sp - 128 ∨ sp ≤ rd) (hpf : ptr + 16 ≤ sp - 128 ∨ sp ≤ ptr)
    (hwf : ∀ a, sp - 128 ≤ a → a < sp → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : μ.readable ptr = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    ∃ ω' μ', FreeStepsH p R 46856 ω μ x 39982 ω' μ' x 80 ∧
      ω'[1] = UInt64.ofNat (sp - 40) ∧ ω'[5] = UInt64.ofNat 1 ∧ ω'[6] = UInt64.ofNat rd ∧
      ω'[7] = UInt64.ofNat 0 ∧ rdN μ' (sp - 40 + 8) 1 = rdN μ ptr 1 ∧
      rdN μ' (sp - 40 + 32) 8 = ω[0].toNat ∧ rdN μ' (sp - 40 + 24) 8 = ω[5].toNat ∧
      rdN μ' (sp - 40 + 16) 8 = ω[6].toNat ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 1) ∧
      (∀ a, a < 4294967296 → (a < sp - 128 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, s32, s24, s16, fr1, rd1, wr1⟩ :=
    cu_head (p := p) (P := P) (R := R) x ω μ sp rd h1 h7 ⟨by omega, hsp.2⟩ (by omega)
      (fun a h1 h2 => hwf a (by omega) h2)
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ptr := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 len := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 1968 39982 (sp - 40) rd (sp - 40 + 8) ptr len 1 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_983]) bs_39982
      ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ hptr (by decide) hlen.1 hlen.2
      (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1, show a = ptr by omega]; exact hra) hR0' hR8'
  have k : ∀ o, sp - 40 + 16 ≤ o → o + 8 ≤ sp → rdN μ2 o 8 = rdN μ1 o 8 := fun o h1 h2 =>
    rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
  refine ⟨ω2, μ2, (r1.trans r2).mono (by omega), by rw [e1, a1], by rw [e5, a5], by rw [e6, a6], e7, ?_,
    by rw [k _ (by omega) (by omega), s32], by rw [k _ (by omega) (by omega), s24],
    by rw [k _ (by omega) (by omega), s16], q0, q8, fun a h0 hs hr => ?_,
    fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  · unfold rdN; rw [qb]
    exact congrArg _ (PVM.Memory.readN_congr fun j hj => fr1 _ (by omega) (by omega))
  · by_cases hb : a < sp - 40 + 8 ∨ sp - 40 + 8 + 1 ≤ a
    · rw [fr2 a h0 (by omega) hr hb, fr1 a h0 (by omega)]
    · omega
/-- A zero word's tail is zero. -/
theorem decodeLE_tail_zero (μ : Memory) (a l : Nat) (hl : l ≤ 8) (h : rdN μ a 8 = 0) :
    Num.decodeLE (μ.readN (a + l) (8 - l)) = 0 := by
  have e : μ.readN a 8 = μ.readN a l ++ μ.readN (a + l) (8 - l) := by
    rw [← PVM.Memory.readN_split]; congr 1; omega
  unfold rdN at h
  rw [e, decodeLE_append] at h
  have : 0 < 256 ^ (μ.readN a l).length := Nat.pow_pos (by decide)
  rcases Nat.mul_eq_zero.mp (by omega : 256 ^ (μ.readN a l).length * Num.decodeLE (μ.readN (a + l) (8 - l)) = 0)
    with h' | h'
  · omega
  · exact h'

/-- **39982 → 46889**, a prefix octet b with l < 8 leading ones, b ∉ {0, 255}: `cu_mid`, the read
    of the l octets ℰ_l(lo), and `cu_post`: ω₈ = lo + (b mod 2^(7−l))·2^(8l). -/
theorem cu_tail_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s rd ptr len b l lo r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0)
    (hs : 65536 + 88 ≤ s ∧ s + 40 < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296) (hlen : l ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ s - 88 ∨ s + 40 ≤ rd) (hpf : ptr + 16 ≤ s - 88 ∨ s + 40 ≤ ptr)
    (hwf : ∀ a, s - 88 ≤ a → a < s + 40 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + l → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hb : rdN μ (s + 8) 1 = b) (hl : l < 8) (hb0 : 0 < b) (hb1 : 256 - 2 ^ (8 - l) ≤ b)
    (hb2 : b < 256 - 2 ^ (7 - l))
    (hlo : μ.readN ptr l = Num.encodeLE l lo) (hlo' : lo < 2 ^ (8 * l))
    (m16 : rdN μ (s + 16) 8 = r6) (m24 : rdN μ (s + 24) 8 = r5) (m32 : rdN μ (s + 32) 8 = 2106) :
    ∃ ω' μ', FreeStepsH p R 39982 ω μ x 46889 ω' μ' x 200 ∧
      ω'[1] = UInt64.ofNat (s + 40) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat (lo + b % 2 ^ (7 - l) * 2 ^ (8 * l)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + l) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - l) ∧
      (∀ a, a < 4294967296 → (a < s - 88 ∨ s + 40 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hb256 : b < 256 := by rw [← hb]; exact rdN_lt μ _ 1
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, w0, w8, fr1, rd1, wr1⟩ :=
    cu_mid (p := p) (P := P) (R := R) x ω μ s rd b l h1 h6 h7 ⟨by omega, hs.2⟩ (by omega)
      (fun a h1 h2 => hwf a (by omega) h2) hb hl hb0 hb1 hb2
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ptr := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 len := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 1972 40170 s rd (s + 8) ptr len l a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_985]) bs_40170
      ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ hptr (by omega) hlen.1 hlen.2
      (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a h1 h2) hR0' hR8'
  have m0' : rdN μ2 s 8 = sxw 1 b % 18446744073709551616 := by
    rw [rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega) (Or.inl (by omega))]; exact w0
  have m8' : rdN μ2 (s + 8) 8 = lo := by
    have e : μ2.readN (s + 8) 8 = μ2.readN (s + 8) l ++ μ2.readN (s + 8 + l) (8 - l) := by
      rw [← PVM.Memory.readN_split]; congr 1; omega
    have t : μ2.readN (s + 8 + l) (8 - l) = μ1.readN (s + 8 + l) (8 - l) :=
      PVM.Memory.readN_congr fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega))
    have hp : μ1.readN ptr l = Num.encodeLE l lo := by
      rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hlo
    unfold rdN
    rw [e, decodeLE_append, qb, hp, t, decodeLE_tail_zero μ1 (s + 8) l (by omega) w8, Num.decodeLE_encodeLE,
      Nat.mod_eq_of_lt hlo']
    simp
  have k : ∀ o, s + 16 ≤ o → o + 8 ≤ s + 40 → rdN μ2 o 8 = rdN μ o 8 := fun o h1 h2 => by
    rw [rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)),
      rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega))]
  obtain ⟨ω3, r3, f0, f1, f5, f6, f7, f8⟩ :=
    cu_post (p := p) (P := P) (R := R) x ω2 μ2 s b l lo r5 r6 (by rw [e1, a1]) (by rw [e6, a6]) e7
      ⟨by omega, hs.2⟩ (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) h2))
      hl hb256 hlo' m0' m8' (by rw [k _ (by omega) (by omega), m16]) (by rw [k _ (by omega) (by omega), m24])
      (by rw [k _ (by omega) (by omega), m32])
  refine ⟨ω3, μ2, ((r1.trans r2).trans r3).mono (by omega), f1, f5, f6, f7, f8, q0, q8,
    fun a h0 hs' hr => ?_, fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  by_cases hb : s ≤ a ∧ a < s + 40
  · by_cases hb' : a < s + 8 ∨ s + 8 + l ≤ a
    · rw [fr2 a h0 (by omega) hr hb']
      by_cases hc : a < s ∨ s + 16 ≤ a
      · exact fr1 a h0 hc
      · omega
    · omega
  · rw [fr2 a h0 (by omega) hr (by omega), fr1 a h0 (by omega)]

/-- **39982 → 46889**, the prefix octet 255: `cu_ff`, the read of ℰ₈(g), and `cu_ff_post`: ω₈ = g. -/
theorem cu_tail_ff {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (s rd ptr len g r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat s) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0)
    (hs : 65536 + 88 ≤ s ∧ s + 40 < 4294967296) (hrd : 65536 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + 16 < 4294967296) (hlen : 8 ≤ len ∧ len < 4294967296)
    (hrf : rd + 16 ≤ s - 88 ∨ s + 40 ≤ rd) (hpf : ptr + 16 ≤ s - 88 ∨ s + 40 ≤ ptr)
    (hwf : ∀ a, s - 88 ≤ a → a < s + 40 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hra : ∀ a, ptr ≤ a → a < ptr + 8 → μ.readable a = true)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len)
    (hb : rdN μ (s + 8) 1 = 255) (hg : μ.readN ptr 8 = Num.encodeLE 8 g) (hg' : g < 18446744073709551616)
    (m16 : rdN μ (s + 16) 8 = r6) (m24 : rdN μ (s + 24) 8 = r5) (m32 : rdN μ (s + 32) 8 = 2106) :
    ∃ ω' μ', FreeStepsH p R 39982 ω μ x 46889 ω' μ' x 200 ∧
      ω'[1] = UInt64.ofNat (s + 40) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat g ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 8) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 8) ∧
      (∀ a, a < 4294967296 → (a < s - 88 ∨ s + 40 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ :=
    cu_ff (p := p) (P := P) (R := R) x ω μ s rd h1 h6 h7 ⟨by omega, hs.2⟩ (by omega)
      (fun a h1 h2 => hwf a (by omega) h2) hb
  have hR0' : μ1.readN rd 8 = Num.encodeLE 8 ptr := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0
  have hR8' : μ1.readN (rd + 8) 8 = Num.encodeLE 8 len := by
    rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8
  obtain ⟨ω2, μ2, r2, e0, e1, -, -, -, e5, e6, -, e7, q0, q8, qb, fr2, rd2, wr2⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 1970 40035 s rd (s + 8) ptr len 8 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_984]) bs_40035
      ⟨by omega, by omega⟩ hrd ⟨by omega, by omega⟩ hptr (by omega) hlen.1 hlen.2
      (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a h1 h2) hR0' hR8'
  have m8' : rdN μ2 (s + 8) 8 = g := by
    unfold rdN
    rw [qb, PVM.Memory.readN_congr (μ := μ) (fun j hj => fr1 _ (by omega) (by omega)), hg,
      Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hg']
  have k : ∀ o, s + 16 ≤ o → o + 8 ≤ s + 40 → rdN μ2 o 8 = rdN μ o 8 := fun o h1 h2 => by
    rw [rdN_frame fun j hj => fr2 _ (by omega) (Or.inr (by omega)) (by omega) (Or.inr (by omega)),
      rdN_frame fun j hj => fr1 _ (by omega) (Or.inr (by omega))]
  obtain ⟨ω3, r3, f0, f1, f5, f6, f7, f8⟩ :=
    cu_ff_post (p := p) (P := P) (R := R) x ω2 μ2 s g r5 r6 (by rw [e1, a1]) ⟨by omega, hs.2⟩
      (fun a h1 h2 => by rw [rd2, rd1]; exact Memory.readable_of_writable (hwf a (by omega) h2))
      m8' (by rw [k _ (by omega) (by omega), m16]) (by rw [k _ (by omega) (by omega), m24])
      (by rw [k _ (by omega) (by omega), m32])
  refine ⟨ω3, μ2, ((r1.trans r2).trans r3).mono (by omega), f1, f5, f6, by rw [f7, e7], f8, q0, q8,
    fun a h0 hs' hr => ?_, fun a => by rw [rd2, rd1], fun a => by rw [wr2, wr1]⟩
  rw [fr2 a h0 (by omega) hr (by omega), fr1 a h0 (by omega)]

end Services.Bootstrap.Acc
