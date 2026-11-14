import Services.Bootstrap.Refine.Entry
import Services.Bootstrap.ReaderBig

/-!
# `Instructions::decode` in refine: after the instruction list

`Instructions::decode` runs inlined in refine with its frame at G = M − 136 (4803 … 4839). After
`Vec<Instruction>::decode` (482) returns its `Vec` `{cap, ptr, len}` at G (20420), it reads the 32-octet salt
(`read_big`, 58434) into G + 80 and writes `Instructions { instructions, salt }` to M + 168 = ω₅ (20548 … 20607),
then returns to refine (158 → 4842). GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's code); `Spec.refine`'s
`decode (Dec.payload C) y`.
-/

namespace Services.Bootstrap.Refine.DecodeTail

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 20420 … 20466: the `Vec` `{cap, ptr, len}` at G (cap not the error word 2^64 − 1) is kept at G + 56, the
    salt's buffer G + 80 … G + 112 zeroed, and the reader (ω₆) called for 32 octets into G + 80 (return
    address 924 → 20473). Memory changes only at G + 56 … G + 112. -/
theorem dt1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (G cap ptr len rd : Nat)
    (hG : 65536 ≤ G ∧ G + 136 ≤ 4294967296 ∧ G % 8 = 0) (hcap : cap < 18446744073709551616)
    (hce : cap ≠ 18446744073709551615) (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hrd : rd < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat G) (h6 : ω[6] = UInt64.ofNat rd)
    (s0 : μ.readN G 8 = Num.encodeLE 8 cap) (s8 : μ.readN (G + 8) 8 = Num.encodeLE 8 ptr)
    (s16 : μ.readN (G + 16) 8 = Num.encodeLE 8 len)
    (hw : ∀ a, G ≤ a → a < G + 112 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20420 ω μ x 58434 ω' μ' x 20 ∧ ω'[0] = UInt64.ofNat 924 ∧ ω'[1] = ω[1] ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (G + 80) ∧
      ω'[9] = UInt64.ofNat 32 ∧
      μ'.readN (G + 56) 8 = Num.encodeLE 8 cap ∧ μ'.readN (G + 64) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (G + 72) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < G + 56 ∨ G + 112 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hG0, hG1, hG8⟩ := hG
  have rc := rd8 hcap s0
  have rp := rd8 hptr s8
  have rl := rd8 hlen s16
  have hce' : ¬ cap = 18446744073709551615 := hce
  have hr : ∀ a, G ≤ a → a < G + 112 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hG0, hG1, hG8, hce', hr, hw, rc, rp, rl, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6, Nat.mod_eq_of_lt hrd]
    post_simp

/-- 20473 … 20587, the salt read (ω₇ = 0): `Instructions { {cap, ptr, len}, salt }` is assembled at G (the
    salt's words w₀ … w₃ from G + 80), with its fields in ω₁₁, ω₁₂, ω₆ and ω₇ … ω₁₀. Memory changes only at
    G … G + 56. -/
theorem dt3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (G cap ptr len w0 w1 w2 w3 : Nat) (hG : 65536 ≤ G ∧ G + 136 ≤ 4294967296 ∧ G % 8 = 0)
    (hcap : cap < 18446744073709551616) (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (hw3 : w3 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h7 : ω[7] = UInt64.ofNat 0)
    (s56 : μ.readN (G + 56) 8 = Num.encodeLE 8 cap) (s64 : μ.readN (G + 64) 8 = Num.encodeLE 8 ptr)
    (s72 : μ.readN (G + 72) 8 = Num.encodeLE 8 len)
    (s80 : μ.readN (G + 80) 8 = Num.encodeLE 8 w0) (s88 : μ.readN (G + 88) 8 = Num.encodeLE 8 w1)
    (s96 : μ.readN (G + 96) 8 = Num.encodeLE 8 w2) (s104 : μ.readN (G + 104) 8 = Num.encodeLE 8 w3)
    (hw : ∀ a, G ≤ a → a < G + 112 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20473 ω μ x 20590 ω' μ' x 20 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧
      ω'[6] = UInt64.ofNat len ∧ ω'[7] = UInt64.ofNat w0 ∧ ω'[8] = UInt64.ofNat w1 ∧ ω'[9] = UInt64.ofNat w2 ∧
      ω'[10] = UInt64.ofNat w3 ∧ ω'[11] = UInt64.ofNat cap ∧ ω'[12] = UInt64.ofNat ptr ∧
      (∀ a, a < 4294967296 → (a < G ∨ G + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hG0, hG1, hG8⟩ := hG
  have rc := rd8 hcap s56
  have rp := rd8 hptr s64
  have rl := rd8 hlen s72
  have r0 := rd8 hw0 s80
  have r1 := rd8 hw1 s88
  have r2 := rd8 hw2 s96
  have r3 := rd8 hw3 s104
  have hr : ∀ a, G ≤ a → a < G + 112 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hG0, hG1, hG8, hr, hw, rc, rp, rl, r0, r1, r2, r3, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hcap,
      Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hlen, Nat.mod_eq_of_lt hw0, Nat.mod_eq_of_lt hw1,
      Nat.mod_eq_of_lt hw2, Nat.mod_eq_of_lt hw3]
    post_simp

/-- 20590 … 20624: `Instructions` written to dst = ω₅ (`{cap, ptr, len}`, then the salt's four words), and the
    return (158 → 4842) with ω₁ = G + 136 and ω₅, ω₆ restored from G + 120, G + 112. Memory changes only at
    dst … dst + 56. -/
theorem dt4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (G dst cap ptr len w0 w1 w2 w3 r5 r6 : Nat) (hG : 65536 ≤ G ∧ G + 136 ≤ 4294967296 ∧ G % 8 = 0)
    (hd : 65536 ≤ dst ∧ dst + 56 ≤ 4294967296 ∧ (dst + 56 ≤ G + 112 ∨ G + 136 ≤ dst))
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hcap : cap < 18446744073709551616) (hptr : ptr < 18446744073709551616) (hlen : len < 18446744073709551616)
    (hw0 : w0 < 18446744073709551616) (hw1 : w1 < 18446744073709551616) (hw2 : w2 < 18446744073709551616)
    (hw3 : w3 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h5 : ω[5] = UInt64.ofNat dst) (h6 : ω[6] = UInt64.ofNat len)
    (h7 : ω[7] = UInt64.ofNat w0) (h8 : ω[8] = UInt64.ofNat w1) (h9 : ω[9] = UInt64.ofNat w2)
    (h10 : ω[10] = UInt64.ofNat w3) (h11 : ω[11] = UInt64.ofNat cap) (h12 : ω[12] = UInt64.ofNat ptr)
    (s128 : μ.readN (G + 128) 8 = Num.encodeLE 8 158) (s120 : μ.readN (G + 120) 8 = Num.encodeLE 8 r5)
    (s112 : μ.readN (G + 112) 8 = Num.encodeLE 8 r6)
    (hr : ∀ a, G + 112 ≤ a → a < G + 136 → μ.readable a = true)
    (hw : ∀ a, dst ≤ a → a < dst + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20590 ω μ x 4842 ω' μ' x 20 ∧ ω'[1] = UInt64.ofNat (G + 136) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN dst 8 = Num.encodeLE 8 cap ∧ μ'.readN (dst + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (dst + 16) 8 = Num.encodeLE 8 len ∧ μ'.readN (dst + 24) 8 = Num.encodeLE 8 w0 ∧
      μ'.readN (dst + 32) 8 = Num.encodeLE 8 w1 ∧ μ'.readN (dst + 40) 8 = Num.encodeLE 8 w2 ∧
      μ'.readN (dst + 48) 8 = Num.encodeLE 8 w3 ∧
      (∀ a, a < 4294967296 → (a < dst ∨ dst + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hG0, hG1, hG8⟩ := hG
  obtain ⟨hd0, hd1, hd2⟩ := hd
  have r128 := rd8 (by decide) s128
  have r120 := rd8 hr5 s120
  have r112 := rd8 hr6 s112
  have hr2 : ∀ a, dst ≤ a → a < dst + 56 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, h8, h9, h10, h11, h12, hG0, hG1, hG8, hd0, hd1, hd2, hr, hr2, hw, r128, r120, r112,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hr5,
      Nat.mod_eq_of_lt hr6, Nat.mod_eq_of_lt hcap, Nat.mod_eq_of_lt hptr, Nat.mod_eq_of_lt hlen,
      Nat.mod_eq_of_lt hw0, Nat.mod_eq_of_lt hw1, Nat.mod_eq_of_lt hw2, Nat.mod_eq_of_lt hw3]
    post_simp

/-- **`Instructions::decode`'s tail** (20420 … 4842): from the `Vec<Instruction>` `{cap, ptr, len}` at G (not the
    error word), the reader at rd over the payload's rest (P1, L1 ≥ 32), the 32-octet salt read and
    `Instructions` written to dst (`{cap, ptr, len}`, the salt), then the return to refine with ω₁ = G + 136
    and ω₅, ω₆ restored. Memory changes only at [G − 88, G + 112), the reader and dst … dst + 56. -/
theorem tail {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (G dst rd cap ptr len P1 L1 r5 r6 : Nat) (salt : List UInt8)
    (hG : 65536 + 88 ≤ G ∧ G + 136 ≤ 4294967296 ∧ G % 8 = 0)
    (hd : G + 136 ≤ dst ∧ dst + 56 ≤ 4294967296)
    (hrd : G + 136 ≤ rd ∧ rd + 16 < 4294967296 ∧ (rd + 16 ≤ dst ∨ dst + 56 ≤ rd))
    (hP1 : 65536 ≤ P1 ∧ P1 + 32 + 88 + 24 ≤ G) (hL : 32 ≤ L1) (hL1 : L1 < 4294967296)
    (hcap : cap < 18446744073709551616) (hce : cap ≠ 18446744073709551615) (hptr : ptr < 18446744073709551616)
    (hlen : len < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat G) (h5 : ω[5] = UInt64.ofNat dst) (h6 : ω[6] = UInt64.ofNat rd)
    (s0 : μ.readN G 8 = Num.encodeLE 8 cap) (s8 : μ.readN (G + 8) 8 = Num.encodeLE 8 ptr)
    (s16 : μ.readN (G + 16) 8 = Num.encodeLE 8 len)
    (s128 : μ.readN (G + 128) 8 = Num.encodeLE 8 158) (s120 : μ.readN (G + 120) 8 = Num.encodeLE 8 r5)
    (s112 : μ.readN (G + 112) 8 = Num.encodeLE 8 r6)
    (sR0 : μ.readN rd 8 = Num.encodeLE 8 P1) (sR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 L1)
    (ssalt : μ.readN P1 32 = salt)
    (hwf : ∀ a, G - 88 ≤ a → a < G + 136 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwd : ∀ a, dst ≤ a → a < dst + 56 → μ.writable a = true)
    (hra : ∀ a, P1 ≤ a → a < P1 + 32 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 20420 ω μ x 4842 ω' μ' x 600 ∧ ω'[1] = UInt64.ofNat (G + 136) ∧
      ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN dst 8 = Num.encodeLE 8 cap ∧ μ'.readN (dst + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (dst + 16) 8 = Num.encodeLE 8 len ∧ μ'.readN (dst + 24) 32 = salt ∧
      μ'.readN rd 8 = Num.encodeLE 8 (P1 + 32) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (L1 - 32) ∧
      (∀ a, a < 4294967296 → (a < G - 88 ∨ G + 112 ≤ a) → (a < rd ∨ rd + 16 ≤ a) → (a < dst ∨ dst + 56 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hG0, hG1, hG8⟩ := hG
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a56, a64, a72, afr, ard, awr⟩ := dt1 (p := p) (P := P)
    (R := R) x ω μ G cap ptr len rd ⟨by omega, by omega, hG8⟩ hcap hce hptr hlen (by omega) h1 h6 s0 s8 s16
    (fun a h1 h2 => hwf a (by omega) (by omega))
  have k1 : ∀ a l, a + l ≤ 4294967296 → (a + l ≤ G + 56 ∨ G + 112 ≤ a) → μ1.readN a l = μ.readN a l :=
    fun a l h h' => Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, bR0, bR8, bbuf, bfr, brd, bwr⟩ := read_big (p := p) (P := P) (R := R)
    x ω1 μ1 924 20473 G rd (G + 80) P1 L1 32 a0 (a1.trans h1) a7 a8 a9 ⟨by decide, by decide, by decide⟩ jte_461
    bs_20473 ⟨by omega, by omega, hG8⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨hP1.1, by omega⟩ (by decide)
    hL hL1 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
    (fun a h1 h2 => by rw [awr]; exact hwf a h1 (by omega)) (fun a h1 h2 => by rw [awr]; exact hwr a h1 h2)
    (fun a h1 h2 => by rw [awr]; exact hwf a (by omega) (by omega)) (fun a h1 h2 => by rw [ard]; exact hra a h1 h2)
    (by rw [k1 _ _ (by omega) (by omega)]; exact sR0) (by rw [k1 _ _ (by omega) (by omega)]; exact sR8)
  have k2 : ∀ a l, a + l ≤ 4294967296 → G ≤ a → (a + l ≤ G + 80 ∨ G + 112 ≤ a) → a + l ≤ rd →
      μ2.readN a l = μ1.readN a l :=
    fun a l h h0 h' h'' => Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega))
  have w : ∀ i, i < 4 → μ2.readN (G + 80 + 8 * i) 8 = Num.encodeLE 8 (rdN μ2 (G + 80 + 8 * i) 8) :=
    fun i _ => (encodeLE_rdN μ2 _ 8).symm
  obtain ⟨ω3, μ3, run3, c1, c5, c6, c7, c8, c9, c10, c11, c12, cfr, crd, cwr⟩ := dt3 (p := p) (P := P) (R := R)
    x ω2 μ2 G cap ptr len (rdN μ2 (G + 80) 8) (rdN μ2 (G + 88) 8) (rdN μ2 (G + 96) 8) (rdN μ2 (G + 104) 8)
    ⟨by omega, by omega, hG8⟩ hcap hptr hlen (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
    (b1.trans (a1.trans h1)) b7
    (by rw [k2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact a56)
    (by rw [k2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact a64)
    (by rw [k2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact a72)
    (encodeLE_rdN μ2 _ 8).symm (encodeLE_rdN μ2 _ 8).symm (encodeLE_rdN μ2 _ 8).symm (encodeLE_rdN μ2 _ 8).symm
    (fun a h1 h2 => by rw [bwr, awr]; exact hwf a (by omega) (by omega))
  have k3 : ∀ a l, a + l ≤ 4294967296 → G + 112 ≤ a → a + l ≤ rd → μ3.readN a l = μ.readN a l :=
    fun a l h h0 h' => Memory.readN_congr (fun j hj => by
      rw [cfr _ (by omega) (by omega), bfr _ (by omega) (by omega) (by omega) (by omega), afr _ (by omega) (by omega)])
  obtain ⟨ω4, μ4, run4, d1, d5, d6, d0, d8, d16, d24, d32, d40, d48, dfr, drd, dwr⟩ := dt4 (p := p) (P := P)
    (R := R) x ω3 μ3 G dst cap ptr len (rdN μ2 (G + 80) 8) (rdN μ2 (G + 88) 8) (rdN μ2 (G + 96) 8)
    (rdN μ2 (G + 104) 8) r5 r6 ⟨by omega, by omega, hG8⟩ ⟨by omega, by omega, Or.inr hd.1⟩ hr5 hr6 hcap hptr hlen
    (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _) (rdN_lt64 _ _)
    (c1.trans (b1.trans (a1.trans h1))) (by rw [c5, b5, a5, h5]) c6 c7 c8 c9 c10 c11 c12
    (by rw [k3 _ _ (by omega) (by omega) (by omega)]; exact s128)
    (by rw [k3 _ _ (by omega) (by omega) (by omega)]; exact s120)
    (by rw [k3 _ _ (by omega) (by omega) (by omega)]; exact s112)
    (fun a h1 h2 => by rw [crd, brd, ard]; exact Memory.readable_of_writable (hwf a (by omega) (by omega)))
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact hwd a h1 h2)
  refine ⟨ω4, μ4, (run1.trans (run2.trans (run3.trans run4))).mono (by omega), d1, d5, d6, d0, d8, d16, ?_, ?_, ?_,
    fun a h0 h1 h2 h3 => ?_, fun a => by rw [drd, crd, brd, ard], fun a => by rw [dwr, cwr, bwr, awr]⟩
  · -- the salt: four words, each as read into G + 80
    have e : ∀ i, i < 4 → rdN μ2 (G + 80 + 8 * i) 8 = rdN μ1 (P1 + 8 * i) 8 := fun i hi => by
      unfold rdN
      rw [Pass.readN_sub μ2 (G + 80) 32 (8 * i) 8 _ bbuf (by omega), ← Pass.readN_sub μ1 P1 32 (8 * i) 8 _ rfl (by omega)]
    have sw : ∀ i, i < 4 → μ4.readN (dst + 24 + 8 * i) 8 = μ.readN (P1 + 8 * i) 8 := fun i hi => by
      have hk : μ1.readN (P1 + 8 * i) 8 = μ.readN (P1 + 8 * i) 8 := k1 _ _ (by omega) (by omega)
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
      · rw [show dst + 24 + 8 * 0 = dst + 24 by omega, d24, show G + 80 = G + 80 + 8 * 0 by omega, e 0 (by omega),
          encodeLE_rdN, hk]
      · rw [show dst + 24 + 8 * 1 = dst + 32 by omega, d32, show G + 88 = G + 80 + 8 * 1 by omega, e 1 (by omega),
          encodeLE_rdN, hk]
      · rw [show dst + 24 + 8 * 2 = dst + 40 by omega, d40, show G + 96 = G + 80 + 8 * 2 by omega, e 2 (by omega),
          encodeLE_rdN, hk]
      · rw [show dst + 24 + 8 * 3 = dst + 48 by omega, d48, show G + 104 = G + 80 + 8 * 3 by omega, e 3 (by omega),
          encodeLE_rdN, hk]
    rw [← ssalt, show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl, Pass.readN_add2, Pass.readN_add2, Pass.readN_add2,
      Pass.readN_add2 μ P1, Pass.readN_add2 μ, Pass.readN_add2 μ]
    have s0' := sw 0 (by omega); have s1' := sw 1 (by omega); have s2' := sw 2 (by omega); have s3' := sw 3 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at s0' s1' s2' s3'
    rw [s0', show dst + 24 + 8 = dst + 24 + 8 * 1 by omega, sw 1 (by omega),
      show dst + 24 + 8 + 8 = dst + 24 + 8 * 2 by omega, sw 2 (by omega),
      show dst + 24 + 8 + 8 + 8 = dst + 24 + 8 * 3 by omega, sw 3 (by omega)]
  · rw [Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega)), Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega))]
    exact bR0
  · rw [Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega)), Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega))]
    exact bR8
  · rw [dfr a h0 h3, cfr a h0 (by omega), bfr a h0 (by omega) h2 (by omega), afr a h0 (by omega)]

end Services.Bootstrap.Refine.DecodeTail
