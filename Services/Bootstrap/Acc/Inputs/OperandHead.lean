import Services.Bootstrap.Acc.Inputs.ItemOperand
import Services.Bootstrap.Acc.Inputs.CompactU64Call
import Services.Bootstrap.Acc.Inputs.ReadVec

/-!
# `AccumulateItem::decode` (45126), the operand arm's head composed (46300 → 46889)

The four hashes (`op_h0` … `op_h4` with `read_any`) and the gas (`cu_call`): host-generic.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- Four words at o in μ' are the four at i in μ. -/
def Words4 (μ' : Memory) (o : Nat) (μ : Memory) (i : Nat) : Prop :=
  rdN μ' o 8 = rdN μ i 8 ∧ rdN μ' (o + 8) 8 = rdN μ (i + 8) 8 ∧ rdN μ' (o + 16) 8 = rdN μ (i + 16) 8 ∧
    rdN μ' (o + 24) 8 = rdN μ (i + 24) 8

/-- A piece of equal reads. -/
theorem readN_sub {μ μ' : Memory} {o i n : Nat} (h : μ'.readN o n = μ.readN i n) {k m : Nat}
    (hk : k + m ≤ n) : μ'.readN (o + k) m = μ.readN (i + k) m := by
  have e : ∀ j, j < n → μ'.read (o + j) = μ.read (i + j) := fun j hj => by
    have := congrArg (fun l => l[j]?) h
    simpa [PVM.Memory.readN, hj] using this
  simp only [PVM.Memory.readN]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.add_assoc, Nat.add_assoc]
  exact e (k + j) (by simp at h1; omega)

/-- A hash copied word by word from the buffer, which held the reader's 32 octets. -/
theorem words_of_copy {μ0 μ1 μ2 μ3 : Memory} {o ptr B : Nat}
    (hb : μ2.readN B 32 = μ1.readN ptr 32) (k1 : ∀ j, j < 32 → μ1.read (ptr + j) = μ0.read (ptr + j))
    (w0 : rdN μ3 o 8 = rdN μ2 B 8) (w1 : rdN μ3 (o + 8) 8 = rdN μ2 (B + 8) 8)
    (w2 : rdN μ3 (o + 16) 8 = rdN μ2 (B + 16) 8) (w3 : rdN μ3 (o + 24) 8 = rdN μ2 (B + 24) 8) :
    Words4 μ3 o μ0 ptr := by
  have hb' : μ2.readN B 32 = μ0.readN ptr 32 := by rw [hb]; exact PVM.Memory.readN_congr fun j hj => k1 j hj
  have r : ∀ k, k + 8 ≤ 32 → rdN μ2 (B + k) 8 = rdN μ0 (ptr + k) 8 := fun k hk => by
    unfold rdN; rw [readN_sub hb' hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [w0]; have := r 0 (by omega); simpa using this
  · rw [w1]; exact r 8 (by omega)
  · rw [w2]; exact r 16 (by omega)
  · rw [w3]; exact r 24 (by omega)

/-- Words kept by a later change outside them. -/
theorem Words4.keep {μ μ' μ0 : Memory} {o i : Nat} (w : Words4 μ o μ0 i)
    (h : ∀ j, j < 32 → μ'.read (o + j) = μ.read (o + j)) : Words4 μ' o μ0 i := by
  obtain ⟨w0, w1, w2, w3⟩ := w
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rdN_frame fun j hj => h j (by omega)]; exact w0
  · rw [rdN_frame (μ := μ) (μ' := μ') (a := o + 8) (n := 8) fun j hj => by
      rw [Nat.add_assoc]; exact h (8 + j) (by omega)]; exact w1
  · rw [rdN_frame (μ := μ) (μ' := μ') (a := o + 16) (n := 8) fun j hj => by
      rw [Nat.add_assoc]; exact h (16 + j) (by omega)]; exact w2
  · rw [rdN_frame (μ := μ) (μ' := μ') (a := o + 24) (n := 8) fun j hj => by
      rw [Nat.add_assoc]; exact h (24 + j) (by omega)]; exact w3

/-- ℰ(x) has at most 9 octets. -/
theorem encodeNat_length_le (x : Nat) : (Blob.encodeNat x).length ≤ 9 := by
  unfold Blob.encodeNat
  split
  · simp
  · split
    · rename_i l hl
      have := List.mem_of_find?_eq_some hl
      simp at this ⊢
      omega
    · simp

/-- **The operand arm's head, 46300 → 46889** (GP v0.8.0 §12, 𝕌: p, e, a, y and ℰ(g)): from the tag 0
    read into b + 272, the four 32-octet hashes at ip copied to b + 32, + 64, + 96, + 136 (as words), and
    the gas g (from ℰ(g) at ip + 128) in ω₈, with ω₇ = 0; `out` kept at b + 24 and the reader advanced
    past them. Memory changes only in the frames [b − 128, b + 424) and the reader. -/
theorem op_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (b out rd ip rlen g : Nat) (h1 : ω[1] = UInt64.ofNat b) (h5 : ω[5] = UInt64.ofNat rd)
    (h6 : ω[6] = UInt64.ofNat out) (h7 : ω[7] = UInt64.ofNat 0) (mt : rdN μ (b + 272) 1 = 0)
    (hb : 2147483648 + 312 ≤ b ∧ b + 424 < 4294967296 ∧ b % 8 = 0) (hout : out < 18446744073709551616)
    (hrd : b + 424 ≤ rd ∧ rd + 16 < 4294967296) (hip : 65536 ≤ ip ∧ ip < 2147483648)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 128 + (Blob.encodeNat g).length ≤ rlen) (hrl32 : rlen < 4294967296)
    (hra : ∀ a, ip ≤ a → a < ip + 128 + (Blob.encodeNat g).length → μ.readable a = true)
    (hg : g < 18446744073709551616)
    (henc : μ.readN (ip + 128) (Blob.encodeNat g).length = Blob.encodeNat g)
    (hwf : ∀ a, b - 128 ≤ a → a < b + 424 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 46300 ω μ x 46889 ω' μ' x 3000 ∧
      ω'[1] = UInt64.ofNat b ∧ ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat g ∧
      rdN μ' (b + 24) 8 = out ∧
      Words4 μ' (b + 32) μ ip ∧ Words4 μ' (b + 64) μ (ip + 32) ∧ Words4 μ' (b + 96) μ (ip + 64) ∧
      Words4 μ' (b + 136) μ (ip + 96) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 128 + (Blob.encodeNat g).length) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 128 - (Blob.encodeNat g).length) ∧
      (∀ a, a < 4294967296 → (a < b - 128 ∨ b + 424 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → b + 304 ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  have hl := encodeNat_length_le g
  -- p
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, a8, a9, s24, fr1, rd1, wr1⟩ :=
    op_h0 (p := p) (P := P) (R := R) x ω μ b out rd h1 h5 h6 h7 mt ⟨by omega, by omega⟩ hout hrd64
      (fun a h1 h2 => hwf a (by omega) h2)
  have g1 : ∀ a, a < 4294967296 → (a < b ∨ b + 424 ≤ a) → μ1.read a = μ.read a := fun a h0 h =>
    fr1 a h0 (by omega) (by omega)
  obtain ⟨ω2, μ2, r2, e0, e1, e5, e6, e7, q0_2, q8_2, qb2, fr2, rd2, wr2⟩ :=
    read_any (p := p) (P := P) (R := R) x ω1 μ1 2084 46375 b rd (b + 272) ip rlen 32 a0 a1 a7 a8 a9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1041]) bs_46375
      ⟨by omega, by omega, hb.2.2⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a (by omega) (by omega)) (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => g1 _ (by omega) (by omega))]; exact hR0) (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => g1 _ (by omega) (by omega))]; exact hR8)
  obtain ⟨ω3, μ3, r3, c0, c1, c5, c6, c7, c8, c9, w0, w1, w2, w3, fr3, rd3, wr3⟩ :=
    op_h1 (p := p) (P := P) (R := R) x ω2 μ2 b rd (by rw [e1, a1]) (by rw [e5, a5]) e7 ⟨by omega, by omega⟩ hrd64
      (fun a h1 h2 => by rw [wr2, wr1]; exact hwf a (by omega) h2)
  have H1 : Words4 μ3 (b + 32) μ ip :=
    words_of_copy qb2 (fun j hj => g1 _ (by omega) (by omega)) w0 w1 w2 w3
  have g3 : ∀ a, a < 4294967296 → (a < b - 88 ∨ b + 424 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h hr => by rw [fr3 a h0 (by omega) (by omega), fr2 a h0 (by omega) hr (by omega), g1 a h0 (by omega)]
  have q0_2' : μ3.readN rd 8 = Num.encodeLE 8 (ip + 32) := by
    rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => fr3 _ (by omega) (by omega) (by omega))]; exact q0_2
  have q8_2' : μ3.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 32) := by
    rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => fr3 _ (by omega) (by omega) (by omega))]; exact q8_2
  obtain ⟨ω4, μ4, r4, f0, f1, f5, f6, f7, q0_4, q8_4, qb4, fr4, rd4, wr4⟩ :=
    read_any (p := p) (P := P) (R := R) x ω3 μ3 2086 46442 b rd (b + 272) (ip + 32) (rlen - 32) 32 c0 c1 c7 c8 c9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1042]) bs_46442
      ⟨by omega, by omega, hb.2.2⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3, rd2, rd1]; exact hra a (by omega) (by omega)) q0_2' q8_2'
  obtain ⟨ω5, μ5, r5, d0, d1, d5, d6, d7, d8, d9, v0, v1, v2, v3, fr5, rd5, wr5⟩ :=
    op_h2 (p := p) (P := P) (R := R) x ω4 μ4 b rd (by rw [f1, c1]) (by rw [f5, c5]) f7
      ⟨by omega, by omega⟩ hrd64 (fun a h1 h2 => by rw [wr4, wr3, wr2, wr1]; exact hwf a (by omega) h2)
  have H2 : Words4 μ5 (b + 64) μ (ip + 32) :=
    words_of_copy qb4 (fun j hj => g3 _ (by omega) (by omega) (by omega)) v0 v1 v2 v3
  have H1' : Words4 μ5 (b + 32) μ ip := H1.keep fun j hj => by
    rw [fr5 _ (by omega) (by omega) (by omega), fr4 _ (by omega) (by omega) (by omega) (by omega)]
  have g5 : ∀ a, a < 4294967296 → (a < b - 88 ∨ b + 424 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ5.read a = μ.read a :=
    fun a h0 h hr => by rw [fr5 a h0 (by omega) (by omega), fr4 a h0 (by omega) hr (by omega), g3 a h0 h hr]
  have q0_4' : μ5.readN rd 8 = Num.encodeLE 8 (ip + 32 + 32) := by
    rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (by omega) (by omega))]; exact q0_4
  have q8_4' : μ5.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 32 - 32) := by
    rw [PVM.Memory.readN_congr (μ := μ4) (fun j hj => fr5 _ (by omega) (by omega) (by omega))]; exact q8_4
  obtain ⟨ω6, μ6, r6, k0, k1, k5, k6, k7, q0_6, q8_6, qb6, fr6, rd6, wr6⟩ :=
    read_any (p := p) (P := P) (R := R) x ω5 μ5 2088 46508 b rd (b + 272) (ip + 32 + 32) (rlen - 32 - 32) 32 d0 d1 d7 d8 d9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1043]) bs_46508
      ⟨by omega, by omega, hb.2.2⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr5, wr4, wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd5, rd4, rd3, rd2, rd1]; exact hra a (by omega) (by omega)) q0_4' q8_4'
  obtain ⟨ω7, μ7, r7, l0, l1, l5, l6, l7, l8, l9, u0, u1, u2, u3, fr7, rd7, wr7⟩ :=
    op_h3 (p := p) (P := P) (R := R) x ω6 μ6 b rd (by rw [k1, d1]) (by rw [k6, d6]) k7
      ⟨by omega, by omega⟩ hrd64 (fun a h1 h2 => by rw [wr6, wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) h2)
  have H3 : Words4 μ7 (b + 96) μ (ip + 32 + 32) :=
    words_of_copy qb6 (fun j hj => g5 _ (by omega) (by omega) (by omega)) u0 u1 u2 u3
  have H1'' : Words4 μ7 (b + 32) μ ip := H1'.keep fun j hj => by
    rw [fr7 _ (by omega) (by omega) (by omega), fr6 _ (by omega) (by omega) (by omega) (by omega)]
  have H2' : Words4 μ7 (b + 64) μ (ip + 32) := H2.keep fun j hj => by
    rw [fr7 _ (by omega) (by omega) (by omega), fr6 _ (by omega) (by omega) (by omega) (by omega)]
  have g7 : ∀ a, a < 4294967296 → (a < b - 88 ∨ b + 424 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h hr => by rw [fr7 a h0 (by omega) (by omega), fr6 a h0 (by omega) hr (by omega), g5 a h0 h hr]
  have q0_6' : μ7.readN rd 8 = Num.encodeLE 8 (ip + 32 + 32 + 32) := by
    rw [PVM.Memory.readN_congr (μ := μ6) (fun j hj => fr7 _ (by omega) (by omega) (by omega))]; exact q0_6
  have q8_6' : μ7.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 32 - 32 - 32) := by
    rw [PVM.Memory.readN_congr (μ := μ6) (fun j hj => fr7 _ (by omega) (by omega) (by omega))]; exact q8_6
  obtain ⟨ω8, μ8, r8, m0, m1, m5, m6, m7, q0_8, q8_8, qb8, fr8, rd8, wr8⟩ :=
    read_any (p := p) (P := P) (R := R) x ω7 μ7 2090 46571 b rd (b + 272) (ip + 32 + 32 + 32) (rlen - 32 - 32 - 32) 32 l0 l1 l7 l8 l9
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1044]) bs_46571
      ⟨by omega, by omega, hb.2.2⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr7, wr6, wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd7, rd6, rd5, rd4, rd3, rd2, rd1]; exact hra a (by omega) (by omega)) q0_6' q8_6'
  obtain ⟨ω9, μ9, r9, n0, n1, n5, n6, n7, t0, t1, t2, t3, fr9, rd9, wr9⟩ :=
    op_h4 (p := p) (P := P) (R := R) x ω8 μ8 b rd (by rw [m1, l1]) (by rw [m6, l6]) m7
      ⟨by omega, by omega⟩ hrd64
      (fun a h1 h2 => by rw [wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) h2)
  have H4 : Words4 μ9 (b + 136) μ (ip + 32 + 32 + 32) :=
    words_of_copy qb8 (fun j hj => g7 _ (by omega) (by omega) (by omega)) t0 t1 t2 t3
  have g9 : ∀ a, a < 4294967296 → (a < b - 88 ∨ b + 424 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ9.read a = μ.read a :=
    fun a h0 h hr => by rw [fr9 a h0 (by omega), fr8 a h0 (by omega) hr (by omega), g7 a h0 h hr]
  have q0_8' : μ9.readN rd 8 = Num.encodeLE 8 (ip + 128) := by
    rw [PVM.Memory.readN_congr (μ := μ8) (fun j hj => fr9 _ (by omega) (by omega)), q0_8]; all_goals (congr 1 <;> omega)
  have q8_8' : μ9.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 128) := by
    rw [PVM.Memory.readN_congr (μ := μ8) (fun j hj => fr9 _ (by omega) (by omega)), q8_8]; all_goals (congr 1 <;> omega)
  -- the gas
  obtain ⟨ω10, μ10, r10, o1, o5, o6, o7, o8, z0, z8, fr10, rd10, wr10⟩ :=
    cu_call (p := p) (P := P) (R := R) x ω9 μ9 b rd (ip + 128) (rlen - 128) g n0 n1 n7
      ⟨by omega, by omega⟩ ⟨by omega, hrd.2⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [wr9, wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr9, wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [rd9, rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1]; exact hra a (by omega) (by omega))
      q0_8' q8_8' hg
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => g9 _ (by omega) (by omega) (by omega))]; exact henc)
  have kk : ∀ o, b ≤ o → o + 32 ≤ b + 424 → ∀ j, j < 32 → μ10.read (o + j) = μ9.read (o + j) :=
    fun o h1 h2 j hj => fr10 _ (by omega) (by omega) (by omega)
  -- the frame from μ7 to μ10, between b and b + 136
  have k79 : ∀ a, b ≤ a → a < b + 136 → μ10.read a = μ7.read a := fun a h1 h2 => by
    rw [fr10 a (by omega) (by omega) (by omega), fr9 a (by omega) (Or.inl (by omega)),
      fr8 a (by omega) (by omega) (by omega) (Or.inl (by omega))]
  have k57 : ∀ a, b ≤ a → a < b + 96 → μ7.read a = μ5.read a := fun a h1 h2 => by
    rw [fr7 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      fr6 a (by omega) (by omega) (by omega) (Or.inl (by omega))]
  have k35 : ∀ a, b ≤ a → a < b + 64 → μ5.read a = μ3.read a := fun a h1 h2 => by
    rw [fr5 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      fr4 a (by omega) (by omega) (by omega) (Or.inl (by omega))]
  have k13 : ∀ a, b ≤ a → a < b + 32 → μ3.read a = μ1.read a := fun a h1 h2 => by
    rw [fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      fr2 a (by omega) (by omega) (by omega) (Or.inl (by omega))]
  have run : FreeStepsH p R 46300 ω μ x 46889 ω10 μ10 x 3000 :=
    (((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans
      r10).mono (by omega)
  refine ⟨ω10, μ10, run, o1, by rw [o6, n6], o7, o8, ?_, ?_, ?_, ?_, ?_,
    z0, z8,
    fun a h0 h hr => by rw [fr10 a h0 (by omega) hr, g9 a h0 (by omega) hr],
    fun a h0 h hr => by
      rw [fr10 a h0 (by omega) hr, fr9 a h0 (by omega), fr8 a h0 (by omega) hr (by omega),
        fr7 a h0 (by omega) (by omega), fr6 a h0 (by omega) hr (by omega), fr5 a h0 (by omega) (by omega),
        fr4 a h0 (by omega) hr (by omega), fr3 a h0 (by omega) (by omega), fr2 a h0 (by omega) hr (by omega),
        fr1 a h0 (by omega) (by omega)],
    fun a => by rw [rd10, rd9, rd8, rd7, rd6, rd5, rd4, rd3, rd2, rd1],
    fun a => by rw [wr10, wr9, wr8, wr7, wr6, wr5, wr4, wr3, wr2, wr1]⟩
  · rw [rdN_frame fun j hj => k79 _ (by omega) (by omega), rdN_frame fun j hj => k57 _ (by omega) (by omega),
      rdN_frame fun j hj => k35 _ (by omega) (by omega), rdN_frame fun j hj => k13 _ (by omega) (by omega)]
    exact s24
  · exact H1''.keep fun j hj => k79 _ (by omega) (by omega)
  · exact H2'.keep fun j hj => k79 _ (by omega) (by omega)
  · rw [(show ip + 64 = ip + 32 + 32 by omega)]
    exact H3.keep fun j hj => k79 _ (by omega) (by omega)
  · rw [(show ip + 96 = ip + 32 + 32 + 32 by omega)]
    exact H4.keep fun j hj => fr10 _ (by omega) (by omega) (by omega)

end Services.Bootstrap.Acc
