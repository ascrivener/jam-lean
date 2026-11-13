import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.CodeAAll

/-!
# `Designate`'s copy loop (49775 … 49856)

49597 builds the validator keys' serialisation (GP §6.3 and §C, each key 336 octets: Bandersnatch 32,
Ed25519 32, BLS 144, metadata 128) in a `Vec<u8>` `{cap, ptr, len}` at S + 24, its frame base S
(ω₁). The keys are Rust structs of 336 octets whose fields lie in the order metadata (+ 0),
Bandersnatch (+ 128), Ed25519 (+ 160), BLS (+ 192). Each turn of the loop:
* stores the next key's address s + 336 at S + 16;
* appends the four fields in the serialisation's order with `extend_from_slice` (58508, `extend_ok`);
* steps ω₆ (the octets left) down by 336, reloads ω₅ := s + 336, and goes round again while ω₆ ≠ 0.

`seg_head`, `seg1`, `seg2`, `seg3` and `seg_tail` are the straight-line pieces between the calls.
-/

namespace Services.Bootstrap.Acc.Handlers.DesignateLoop

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- One key's serialisation (GP §6.3), read from the Rust struct at s. -/
def keyBytes (μ : Memory) (s : Nat) : List UInt8 :=
  μ.readN (s + 128) 32 ++ μ.readN (s + 160) 32 ++ μ.readN (s + 192) 144 ++ μ.readN s 128

/-- 49775 … 58508: s + 336 stored at S + 16, the first call `extend(S + 24, s + 128, 32)`, return 2204. -/
theorem seg_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat s)
    (hS : S + 48 < 4294967296) (hs : s + 336 < 4294967296)
    (hw : ∀ a, S + 16 ≤ a → a < S + 24 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 49775 ω μ x 58508 ω' (μ.writeN (S + 16) (Num.encodeLE 8 (s + 336))) x 6 ∧
      ω'[0] = UInt64.ofNat 2204 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 24) ∧ ω'[8] = UInt64.ofNat (s + 128) ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hS, hs, hw, bs_58508]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
    all_goals try (congr 1; omega)

/-- A call `extend(S + 24, s + o, n)` returning through `ret`, set up from 49798 / 49814 / 49831. -/
theorem seg_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s i o n ret : Nat) (hi : (i = 49798 ∧ o = 160 ∧ n = 32 ∧ ret = 2206) ∨
      (i = 49814 ∧ o = 192 ∧ n = 144 ∧ ret = 2208) ∨ (i = 49831 ∧ o = 0 ∧ n = 128 ∧ ret = 2210))
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat s)
    (hS : S + 48 < 4294967296) (hs : s + 336 < 4294967296) :
    ∃ ω', FreeStepsH p R i ω μ x 58508 ω' μ x 4 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 24) ∧ ω'[8] = UInt64.ofNat (s + o) ∧ ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  rcases hi with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, hS, hs, bs_58508]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5, Nat.add_zero]
      all_goals try (congr 1; omega)

/-- 49846 … 49853: ω₆ := ω₆ − 336, ω₅ := the word at S + 16; round again (49775) while ω₆ ≠ 0
    (`tail_again`), else on to 49856 (`tail_done`). -/
theorem tail_gen {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S r s' : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : 336 ≤ r)
    (hr64 : r < 18446744073709551616) (hS : S + 48 < 4294967296) (hs' : s' < 18446744073709551616)
    (m : μ.readN (S + 16) 8 = Num.encodeLE 8 s')
    (hrd : ∀ a, S + 16 ≤ a → a < S + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 49846 ω μ x (if r = 336 then 49856 else 49775) ω' μ x 3 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s' ∧ ω'[6] = UInt64.ofNat (r - 336) := by
  have m' := Services.Bootstrap.Encode.Writer.rd8 hs' m
  rw [show ω = regsNF ω [] from rfl]
  rcases Nat.eq_or_lt_of_le hr with he | hlt
  · subst he
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [↓reduceIte]
      pvm_go [h1, h6, hS, m', hrd, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
      all_goals try (congr 1; omega)
  · have hne : r ≠ 336 := by omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [hne, ↓reduceIte]
      pvm_go [h1, h6, hS, m', hrd, hr64, hne, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
      all_goals try (congr 1; omega)

theorem readN_keep {μ μ' : Memory} {a n : Nat} (h : ∀ b, a ≤ b → b < a + n → μ'.read b = μ.read b) :
    μ'.readN a n = μ.readN a n :=
  Memory.readN_congr (fun j hj => h (a + j) (by omega) (by omega))

open Services.Bootstrap.Encode.Writer in
/-- **One turn of the loop** (49775 … 49853): with the frame at S, the next key at s, r ≥ 336 octets
    left and room in the vector `{cap, q, L}` at S + 24 for 336 more, the key's serialisation
    (`keyBytes`) is appended at q + L and L := L + 336, ω₅ := s + 336, ω₆ := r − 336; then round
    again (49775) or, if r = 336, on to 49856. Memory changes only in [S − 80, S), at S + 16 and
    S + 40 (one word each) and in [q + L, q + L + 336). -/
theorem iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s r cap q L : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat s)
    (h6 : ω[6] = UInt64.ofNat r) (hr : 336 ≤ r) (hr64 : r < 18446744073709551616)
    (hS : 65536 + 128 ≤ S ∧ S + 48 < 4294967296 ∧ S % 8 = 0)
    (vc : μ.readN (S + 24) 8 = Num.encodeLE 8 cap) (vq : μ.readN (S + 32) 8 = Num.encodeLE 8 q)
    (vl : μ.readN (S + 40) 8 = Num.encodeLE 8 L) (hroom : L + 336 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (hdst : 65536 ≤ q + L ∧ q + L + 336 + 16 ≤ S - 80) (hsrc : 65536 ≤ s ∧ s + 336 + 16 ≤ S - 80)
    (hdj : q + L + 336 + 24 ≤ s ∨ s + 336 + 24 ≤ q + L)
    (hrs : ∀ a, s ≤ a → a < s + 336 → μ.readable a = true)
    (hwd : ∀ a, q + L ≤ a → a < q + L + 336 → μ.writable a = true)
    (hwf : ∀ a, S - 80 ≤ a → a < S + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 49775 ω μ x (if r = 336 then 49856 else 49775) ω' μ' x 4000 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (s + 336) ∧ ω'[6] = UInt64.ofNat (r - 336) ∧
      μ'.readN (q + L) 336 = keyBytes μ s ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 (L + 336) ∧
      (∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 24 ≤ a) →
        (a < S + 40 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 336 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have hrf : ∀ a, S - 80 ≤ a → a < S + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  -- the head: s + 336 at S + 16
  obtain ⟨ω0, run0, a0, a1, a5, a6, a7, a8, a9⟩ := seg_head (p := p) (P := P) (R := R) x ω μ S s h1 h5
    (by omega) (by omega) (fun a h1 h2 => hwf a (by omega) (by omega))
  let μ0 := μ.writeN (S + 16) (Num.encodeLE 8 (s + 336))
  have k0 : ∀ a, a < 4294967296 → (a < S + 16 ∨ S + 24 ≤ a) → μ0.read a = μ.read a := fun a h0 h1 =>
    Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have rd0 : ∀ a, μ0.readable a = μ.readable a := fun a => Memory.readable_writeN ..
  have wr0 : ∀ a, μ0.writable a = μ.writable a := fun a => Memory.writable_writeN ..
  -- extend 1: Bandersnatch, 32 octets from s + 128
  obtain ⟨ω1, μ1, run1, b0, b1, b5, b6, bd, bl, bfr, brd, bwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω0 μ0
    S (S + 24) (s + 128) 32 cap q L 2204 49798 ⟨by omega, by omega, hS8⟩ a0 a1 a7 a8 a9 (by omega) hcap
    (by rw [readN_keep (fun b h1 h2 => k0 b (by omega) (by omega))]; exact vc)
    (by rw [readN_keep (fun b h1 h2 => k0 b (by omega) (by omega))]; exact vq)
    (by rw [readN_keep (fun b h1 h2 => k0 b (by omega) (by omega))]; exact vl)
    (by omega) (by omega) ⟨hdst.1, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_1101 bs_49798
    (fun a h1 h2 => by rw [rd0]; exact hrf a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr0]; exact hwf a (by omega) (by omega))
    (fun a h1 h2 => by rw [rd0]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr0]; exact hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr0]; exact hwf a (by omega) (by omega))
  have K1 : ∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 24 ≤ a) →
      (a < S + 40 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 32 ≤ a) → μ1.read a = μ.read a :=
    fun a h0 h1 h2 h3 h4 => by rw [bfr a h0 h1 h4 h3, k0 a h0 h2]
  -- extend 2: Ed25519, 32 octets from s + 160
  obtain ⟨ω1', run1', c0, c1, c5, c6, c7, c8, c9⟩ := seg_mid (p := p) (P := P) (R := R) x ω1 μ1 S s 49798 160 32 2206
    (Or.inl ⟨rfl, rfl, rfl, rfl⟩) b1 (b5.trans a5) (by omega) (by omega)
  obtain ⟨ω2, μ2, run2, d0, d1, d5, d6, dd, dl, dfr, drd, dwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω1' μ1
    S (S + 24) (s + 160) 32 cap q (L + 32) 2206 49814 ⟨by omega, by omega, hS8⟩ c0 c1 c7 c8 c9 (by omega) hcap
    (by rw [readN_keep (fun b h1 h2 => K1 b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vc)
    (by rw [readN_keep (fun b h1 h2 => K1 b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vq)
    bl (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_1102 bs_49814
    (fun a h1 h2 => by rw [brd, rd0]; exact hrf a (by omega) (by omega))
    (fun a h1 h2 => by rw [bwr, wr0]; exact hwf a (by omega) (by omega))
    (fun a h1 h2 => by rw [brd, rd0]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [bwr, wr0]; exact hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [bwr, wr0]; exact hwf a (by omega) (by omega))
  have K2 : ∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 24 ≤ a) →
      (a < S + 40 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 64 ≤ a) → μ2.read a = μ.read a :=
    fun a h0 h1 h2 h3 h4 => by
      rw [dfr a h0 h1 (by omega) h3]
      rcases Nat.lt_or_ge a (q + L) with h | h
      · exact K1 a h0 h1 h2 h3 (Or.inl h)
      · exact K1 a h0 h1 h2 h3 (Or.inr (by omega))
  -- extend 3: BLS, 144 octets from s + 192
  obtain ⟨ω2', run2', e0, e1, e5, e6, e7, e8, e9⟩ := seg_mid (p := p) (P := P) (R := R) x ω2 μ2 S s 49814 192 144 2208
    (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) d1 (d5.trans c5) (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, f0, f1, f5, f6, fd, fl, ffr, frd, fwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω2' μ2
    S (S + 24) (s + 192) 144 cap q (L + 32 + 32) 2208 49831 ⟨by omega, by omega, hS8⟩ e0 e1 e7 e8 e9 (by omega)
    hcap
    (by rw [readN_keep (fun b h1 h2 => K2 b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vc)
    (by rw [readN_keep (fun b h1 h2 => K2 b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vq)
    dl (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (by omega) ⟨by decide, by decide, by decide⟩ jte_1103 bs_49831
    (fun a h1 h2 => by rw [drd, brd, rd0]; exact hrf a (by omega) (by omega))
    (fun a h1 h2 => by rw [dwr, bwr, wr0]; exact hwf a (by omega) (by omega))
    (fun a h1 h2 => by rw [drd, brd, rd0]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [dwr, bwr, wr0]; exact hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [dwr, bwr, wr0]; exact hwf a (by omega) (by omega))
  have K3 : ∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 24 ≤ a) →
      (a < S + 40 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 208 ≤ a) → μ3.read a = μ.read a :=
    fun a h0 h1 h2 h3 h4 => by
      rw [ffr a h0 h1 (by omega) h3]
      rcases Nat.lt_or_ge a (q + L) with h | h
      · exact K2 a h0 h1 h2 h3 (Or.inl h)
      · exact K2 a h0 h1 h2 h3 (Or.inr (by omega))
  -- extend 4: metadata, 128 octets from s
  obtain ⟨ω3', run3', g0, g1, g5, g6, g7, g8, g9⟩ := seg_mid (p := p) (P := P) (R := R) x ω3 μ3 S s 49831 0 128 2210
    (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)) f1 (f5.trans e5)
    (by omega) (by omega)
  obtain ⟨ω4, μ4, run4, i0, i1, i5, i6, id, il, ifr, ird, iwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω3' μ3
    S (S + 24) (s + 0) 128 cap q (L + 32 + 32 + 144) 2210 49846 ⟨by omega, by omega, hS8⟩ g0 g1 g7 g8 g9
    (by omega) hcap
    (by rw [readN_keep (fun b h1 h2 => K3 b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vc)
    (by rw [readN_keep (fun b h1 h2 => K3 b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vq)
    fl (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
    (by omega) ⟨by decide, by decide, by decide⟩ jte_1104 bs_49846
    (fun a h1 h2 => by rw [frd, drd, brd, rd0]; exact hrf a (by omega) (by omega))
    (fun a h1 h2 => by rw [fwr, dwr, bwr, wr0]; exact hwf a (by omega) (by omega))
    (fun a h1 h2 => by rw [frd, drd, brd, rd0]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [fwr, dwr, bwr, wr0]; exact hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [fwr, dwr, bwr, wr0]; exact hwf a (by omega) (by omega))
  have K4 : ∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 24 ≤ a) →
      (a < S + 40 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 336 ≤ a) → μ4.read a = μ.read a :=
    fun a h0 h1 h2 h3 h4 => by
      rw [ifr a h0 h1 (by omega) h3]
      rcases Nat.lt_or_ge a (q + L) with h | h
      · exact K3 a h0 h1 h2 h3 (Or.inl h)
      · exact K3 a h0 h1 h2 h3 (Or.inr (by omega))
  -- the word at S + 16 survives the calls
  have w16 : μ4.readN (S + 16) 8 = Num.encodeLE 8 (s + 336) := by
    have : μ4.readN (S + 16) 8 = μ0.readN (S + 16) 8 := readN_keep fun b h1 h2 => by
      rw [ifr b (by omega) (by omega) (by omega) (by omega), ffr b (by omega) (by omega) (by omega) (by omega),
        dfr b (by omega) (by omega) (by omega) (by omega), bfr b (by omega) (by omega) (by omega) (by omega)]
    rw [this]
    exact Memory.readN_writeN_same _ _ _ _ (by simp) (by first | (simp [two32]; done) | (simp [two32]; omega))
  have h6' : ω4[6] = UInt64.ofNat r := by
    rw [i6, g6, f6, e6, d6, c6, b6, a6, h6]
  obtain ⟨ω5, run5, j1, j5, j6⟩ := tail_gen (p := p) (P := P) (R := R) x ω4 μ4 S r (s + 336) i1 h6' hr hr64
    (by omega) (by omega) w16
    (fun a h1 h2 => by rw [ird, frd, drd, brd, rd0]; exact hrf a (by omega) (by omega))
  refine ⟨ω5, μ4, ?_, j1, j5, j6, ?_, ?_, K4, fun a => ?_, fun a => ?_⟩
  · exact (((((((((run0.trans run1).trans run1').trans run2).trans run2').trans run3).trans run3').trans
      run4).trans run5).mono (by omega))
  · -- the key's four fields, each from its own call and kept by the later ones
    have src : ∀ o n, o + n ≤ 336 → μ0.readN (s + o) n = μ.readN (s + o) n := fun o n h =>
      readN_keep fun b h1 h2 => k0 b (by omega) (by omega)
    have p1 : μ4.readN (q + L) 32 = μ.readN (s + 128) 32 := by
      rw [← src 128 32 (by omega), ← bd]
      exact readN_keep fun b h1 h2 => by
        rw [ifr b (by omega) (by omega) (by omega) (by omega), ffr b (by omega) (by omega) (by omega) (by omega),
          dfr b (by omega) (by omega) (by omega) (by omega)]
    have p2 : μ4.readN (q + L + 32) 32 = μ.readN (s + 160) 32 := by
      rw [← src 160 32 (by omega), ← readN_keep (μ := μ0) (μ' := μ1) (a := s + 160) (n := 32)
        (fun b h1 h2 => bfr b (by omega) (by omega) (by omega) (by omega)), ← dd]
      exact readN_keep fun b h1 h2 => by
        rw [ifr b (by omega) (by omega) (by omega) (by omega), ffr b (by omega) (by omega) (by omega) (by omega)]
    have p3 : μ4.readN (q + L + 32 + 32) 144 = μ.readN (s + 192) 144 := by
      rw [← src 192 144 (by omega), ← readN_keep (μ := μ0) (μ' := μ1) (a := s + 192) (n := 144)
        (fun b h1 h2 => bfr b (by omega) (by omega) (by omega) (by omega)),
        ← readN_keep (μ := μ1) (μ' := μ2) (a := s + 192) (n := 144)
        (fun b h1 h2 => dfr b (by omega) (by omega) (by omega) (by omega)), ← fd]
      exact readN_keep fun b h1 h2 => by
        rw [ifr b (by omega) (by omega) (by omega) (by omega)]
    have p4 : μ4.readN (q + L + 32 + 32 + 144) 128 = μ.readN (s + 0) 128 := by
      rw [← src 0 128 (by omega), ← readN_keep (μ := μ0) (μ' := μ1) (a := s + 0) (n := 128)
        (fun b h1 h2 => bfr b (by omega) (by omega) (by omega) (by omega)),
        ← readN_keep (μ := μ1) (μ' := μ2) (a := s + 0) (n := 128)
        (fun b h1 h2 => dfr b (by omega) (by omega) (by omega) (by omega)),
        ← readN_keep (μ := μ2) (μ' := μ3) (a := s + 0) (n := 128)
        (fun b h1 h2 => ffr b (by omega) (by omega) (by omega) (by omega)), ← id]
      rw [show q + L + 32 + 32 + 144 = q + (L + 32 + 32 + 144) by omega]
    rw [show (336 : Nat) = 32 + (32 + (144 + 128)) from rfl, Memory.readN_split, Memory.readN_split,
      Memory.readN_split, p1, show q + L + 32 + 32 = q + L + 32 + 32 from rfl, p2, p3, p4]
    simp only [keyBytes, Nat.add_zero, List.append_assoc]
  · rw [il]
  · rw [ird, frd, drd, brd, rd0]
  · rw [iwr, fwr, dwr, bwr, wr0]

/-- The serialisations of the k keys from s on (GP §6.3: the keys one after another). -/
def keysBytes (μ : Memory) (s : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => keyBytes μ s ++ keysBytes μ (s + 336) k

theorem keyBytes_congr {μ μ' : Memory} {s : Nat} (h : ∀ a, s ≤ a → a < s + 336 → μ'.read a = μ.read a) :
    keyBytes μ' s = keyBytes μ s := by
  simp only [keyBytes]
  rw [readN_keep (fun b h1 h2 => h b (by omega) (by omega)), readN_keep (fun b h1 h2 => h b (by omega) (by omega)),
    readN_keep (fun b h1 h2 => h b (by omega) (by omega)), readN_keep (fun b h1 h2 => h b (by omega) (by omega))]

theorem keysBytes_congr {μ μ' : Memory} : ∀ (k s : Nat),
    (∀ a, s ≤ a → a < s + 336 * k → μ'.read a = μ.read a) → keysBytes μ' s k = keysBytes μ s k
  | 0, _, _ => rfl
  | k + 1, s, h => by
    simp only [keysBytes]
    rw [keyBytes_congr (fun a h1 h2 => h a h1 (by omega)),
      keysBytes_congr k (s + 336) (fun a h1 h2 => h a (by omega) (by omega))]

/-- **The loop** (49775 … 49856): k ≥ 1 keys from s (ω₆ = 336 · k octets), the vector at S + 24 with
    room for them: their serialisations (`keysBytes`) are appended at q + L, and L := L + 336 · k.
    Memory changes only in [S − 80, S), at S + 16 and S + 40 and in [q + L, q + L + 336 · k). -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (S cap q : Nat)
    (hS : 65536 + 128 ≤ S ∧ S + 48 < 4294967296 ∧ S % 8 = 0) (hcap : cap < 18446744073709551616) :
    ∀ (k : Nat) (ω : Regs) (μ : Memory) (s L : Nat), 0 < k →
    ω[1] = UInt64.ofNat S → ω[5] = UInt64.ofNat s → ω[6] = UInt64.ofNat (336 * k) →
    336 * k < 18446744073709551616 →
    μ.readN (S + 24) 8 = Num.encodeLE 8 cap → μ.readN (S + 32) 8 = Num.encodeLE 8 q →
    μ.readN (S + 40) 8 = Num.encodeLE 8 L → L + 336 * k ≤ cap →
    (65536 ≤ q + L ∧ q + L + 336 * k + 16 ≤ S - 80) → (65536 ≤ s ∧ s + 336 * k + 16 ≤ S - 80) →
    (q + L + 336 * k + 24 ≤ s ∨ s + 336 * k + 24 ≤ q + L) →
    (∀ a, s ≤ a → a < s + 336 * k → μ.readable a = true) →
    (∀ a, q + L ≤ a → a < q + L + 336 * k → μ.writable a = true) →
    (∀ a, S - 80 ≤ a → a < S + 48 → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 49775 ω μ x 49856 ω' μ' x (4000 * k) ∧
      ω'[1] = UInt64.ofNat S ∧
      μ'.readN (q + L) (336 * k) = keysBytes μ s k ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 (L + 336 * k) ∧
      (∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 16 ∨ S + 24 ≤ a) →
        (a < S + 40 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 336 * k ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)
  | 0, _, _, _, _, hk, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, ω, μ, s, L, _, h1, h5, h6, hr64, vc, vq, vl, hroom, hdst, hsrc, hdj, hrs, hwd, hwf => by
    obtain ⟨ω1, μ1, run1, a1, a5, a6, ad, al, afr, ard, awr⟩ := iter (p := p) (P := P) (R := R) x ω μ S s
      (336 * (k + 1)) cap q L h1 h5 h6 (by omega) hr64 hS vc vq vl (by omega) hcap ⟨hdst.1, by omega⟩
      ⟨hsrc.1, by omega⟩ (by omega) (fun a h1 h2 => hrs a h1 (by omega))
      (fun a h1 h2 => hwd a h1 (by omega)) hwf
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨ω1, μ1, ?_, a1, ?_, ?_, ?_, ard, awr⟩
      · simpa using run1
      · simpa [keysBytes] using ad
      · simpa using al
      · simpa using afr
    · have hne : 336 * (k + 1) ≠ 336 := by omega
      simp only [hne, ↓reduceIte] at run1
      have keep1 : ∀ a, a < 4294967296 → (a < S - 80 ∨ S + 48 ≤ a) → (a < q + L ∨ q + L + 336 ≤ a) →
          μ1.read a = μ.read a := fun a h0 h1 h2 => afr a h0 (by omega) (by omega) (by omega) h2
      obtain ⟨ω2, μ2, run2, b1, bd, bl, bfr, brd, bwr⟩ := loop (p := p) (P := P) x S cap q hS hcap k ω1 μ1 (s + 336) (L + 336) hk
        a1 a5 (by rw [a6]; congr 1) (by omega)
        (by rw [readN_keep (fun b h1 h2 => afr b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vc)
        (by rw [readN_keep (fun b h1 h2 => afr b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vq)
        al (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        (fun a h1 h2 => by rw [ard]; exact hrs a (by omega) (by omega))
        (fun a h1 h2 => by rw [awr]; exact hwd a (by omega) (by omega))
        (fun a h1 h2 => by rw [awr]; exact hwf a h1 h2)
      refine ⟨ω2, μ2, ?_, b1, ?_, ?_, ?_, fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩
      · exact (run1.trans run2).mono (by omega)
      · rw [show 336 * (k + 1) = 336 + 336 * k by omega, Memory.readN_split,
          show q + L + 336 = q + (L + 336) by omega, bd,
          readN_keep (fun b h1 h2 => bfr b (by omega) (by omega) (by omega) (by omega) (by omega)), ad,
          keysBytes_congr k (s + 336) (fun a h1 h2 => keep1 a (by omega) (by omega) (by omega))]
        rfl
      · rw [bl]; congr 1; omega
      · intro a h0 h1 h2 h3 h4
        rw [bfr a h0 h1 h2 h3 (by omega), afr a h0 h1 h2 h3 (by omega)]

end Services.Bootstrap.Acc.Handlers.DesignateLoop
