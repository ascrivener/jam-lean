import Services.Bootstrap.Acc.Handlers.DesignateLoop

/-!
# `Assign`'s copy loop (40336 … 40365)

40215 (`Assign`'s callee, its frame at S = ω₁) builds the authorizer queue's serialisation (GP §B.7
Ω_A: 32-octet hashes one after another) in a `Vec<u8>` `{cap, ptr, len}` at S + 32. Each turn of the
loop:
* stores the next hash's address s + 32 at S + 24;
* appends the 32 octets at s with `extend_from_slice` (58508, `extend_ok`), return 1978 (40356);
* steps ω₅ (the octets left) down by 32, reloads ω₆ := s + 32, and goes round again while ω₅ ≠ 0.
-/

namespace Services.Bootstrap.Acc.Handlers.AssignLoop

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Acc.Handlers.DesignateLoop

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 40336 … 58508: s + 32 stored at S + 24, the call `extend(S + 32, s, 32)`, return 1978. -/
theorem seg_head {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat s)
    (hS : S + 56 < 4294967296) (hs : s + 32 < 4294967296)
    (hw : ∀ a, S + 24 ≤ a → a < S + 32 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 40336 ω μ x 58508 ω' (μ.writeN (S + 24) (Num.encodeLE 8 (s + 32))) x 6 ∧
      ω'[0] = UInt64.ofNat 1978 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat s ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat s ∧ ω'[9] = UInt64.ofNat 32 := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h6, hS, hs, hw, bs_58508]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h6]
    all_goals try (congr 1; omega)

/-- 40356 … 40362: ω₅ := ω₅ − 32, ω₆ := the word at S + 24; round again (40336) while ω₅ ≠ 0,
    else on to 40365. -/
theorem tail_gen {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S r s' : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat r) (hr : 32 ≤ r)
    (hr64 : r < 18446744073709551616) (hS : S + 56 < 4294967296) (hs' : s' < 18446744073709551616)
    (m : μ.readN (S + 24) 8 = Num.encodeLE 8 s')
    (hrd : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 40356 ω μ x (if r = 32 then 40365 else 40336) ω' μ x 3 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (r - 32) ∧ ω'[6] = UInt64.ofNat s' := by
  have m' := Services.Bootstrap.Encode.Writer.rd8 hs' m
  rw [show ω = regsNF ω [] from rfl]
  rcases Nat.eq_or_lt_of_le hr with he | hlt
  · subst he
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [↓reduceIte]
      pvm_go [h1, h5, hS, m', hrd, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try (congr 1; omega)
  · have hne : r ≠ 32 := by omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · simp only [hne, ↓reduceIte]
      pvm_go [h1, h5, hS, m', hrd, hr64, hne, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_⟩
      all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
        ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, h5]
      all_goals try (congr 1; omega)

open Services.Bootstrap.Encode.Writer in
/-- **One turn of the loop** (40336 … 40362): the 32 octets at s appended at q + L to the vector
    `{cap, q, L}` at S + 24 + 8, L := L + 32, ω₆ := s + 32, ω₅ := r − 32; round again (40336) or, if
    r = 32, on to 40365. Memory changes only in [S − 80, S), at S + 24 and S + 48 (one word each)
    and in [q + L, q + L + 32). -/
theorem iter {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S s r cap q L : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat r)
    (h6 : ω[6] = UInt64.ofNat s) (hr : 32 ≤ r) (hr64 : r < 18446744073709551616)
    (hS : 65536 + 128 ≤ S ∧ S + 56 < 4294967296 ∧ S % 8 = 0)
    (vc : μ.readN (S + 32) 8 = Num.encodeLE 8 cap) (vq : μ.readN (S + 40) 8 = Num.encodeLE 8 q)
    (vl : μ.readN (S + 48) 8 = Num.encodeLE 8 L) (hroom : L + 32 ≤ cap)
    (hcap : cap < 18446744073709551616)
    (hdst : 65536 ≤ q + L ∧ q + L + 32 + 16 ≤ S - 80) (hsrc : 65536 ≤ s ∧ s + 32 + 16 ≤ S - 80)
    (hdj : q + L + 32 + 24 ≤ s ∨ s + 32 + 24 ≤ q + L)
    (hrs : ∀ a, s ≤ a → a < s + 32 → μ.readable a = true)
    (hwd : ∀ a, q + L ≤ a → a < q + L + 32 → μ.writable a = true)
    (hwf : ∀ a, S - 80 ≤ a → a < S + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 40336 ω μ x (if r = 32 then 40365 else 40336) ω' μ' x 600 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (r - 32) ∧ ω'[6] = UInt64.ofNat (s + 32) ∧
      μ'.readN (q + L) 32 = μ.readN s 32 ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (L + 32) ∧
      (∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 24 ∨ S + 32 ≤ a) →
        (a < S + 48 ∨ S + 56 ≤ a) → (a < q + L ∨ q + L + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hS0, hS1, hS8⟩ := hS
  have hrf : ∀ a, S - 80 ≤ a → a < S + 56 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  obtain ⟨ω0, run0, a0, a1, a5, a6, a7, a8, a9⟩ := seg_head (p := p) (P := P) (R := R) x ω μ S s h1 h6
    (by omega) (by omega) (fun a h1 h2 => hwf a (by omega) (by omega))
  let μ0 := μ.writeN (S + 24) (Num.encodeLE 8 (s + 32))
  have k0 : ∀ a, a < 4294967296 → (a < S + 24 ∨ S + 32 ≤ a) → μ0.read a = μ.read a := fun a h0 h1 =>
    Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)
  have rd0 : ∀ a, μ0.readable a = μ.readable a := fun a => Memory.readable_writeN ..
  have wr0 : ∀ a, μ0.writable a = μ.writable a := fun a => Memory.writable_writeN ..
  obtain ⟨ω1, μ1, run1, b0, b1, b5, b6, bd, bl, bfr, brd, bwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω0 μ0
    S (S + 32) s 32 cap q L 1978 40356 ⟨by omega, by omega, hS8⟩ a0 a1 a7 a8 a9 (by omega) hcap
    (by rw [readN_keep (fun b h1 h2 => k0 b (by omega) (by omega))]; exact vc)
    (by rw [readN_keep (fun b h1 h2 => k0 b (by omega) (by omega))]; exact vq)
    (by rw [readN_keep (fun b h1 h2 => k0 b (by omega) (by omega))]; exact vl)
    (by omega) (by omega) ⟨hdst.1, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_988 bs_40356
    (fun a h1 h2 => by rw [rd0]; exact hrf a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr0]; exact hwf a (by omega) (by omega))
    (fun a h1 h2 => by rw [rd0]; exact hrs a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr0]; exact hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr0]; exact hwf a (by omega) (by omega))
  have w24 : μ1.readN (S + 24) 8 = Num.encodeLE 8 (s + 32) := by
    rw [readN_keep fun b h1 h2 => bfr b (by omega) (by omega) (by omega) (by omega)]
    exact Memory.readN_writeN_same _ _ _ _ (by simp) (by first | (simp [two32]; done) | (simp [two32]; omega))
  have h5' : ω1[5] = UInt64.ofNat r := by rw [b5, a5, h5]
  obtain ⟨ω2, run2, c1, c5, c6⟩ := tail_gen (p := p) (P := P) (R := R) x ω1 μ1 S r (s + 32) b1 h5' hr hr64
    (by omega) (by omega) w24 (fun a h1 h2 => by rw [brd, rd0]; exact hrf a (by omega) (by omega))
  refine ⟨ω2, μ1, ((run0.trans run1).trans run2).mono (by omega), c1, c5, c6, ?_, ?_,
    fun a h0 h1 h2 h3 h4 => ?_, fun a => by rw [brd, rd0], fun a => by rw [bwr, wr0]⟩
  · rw [bd]; exact readN_keep fun b h1 h2 => k0 b (by omega) (by omega)
  · rw [bl]
  · rw [bfr a h0 h1 h4 h3, k0 a h0 h2]

/-- **The loop** (40336 … 40365): k ≥ 1 hashes from s (ω₅ = 32 · k octets), the vector at S + 32 with
    room for them: the 32 · k octets at s are appended at q + L, and L := L + 32 · k. Memory changes
    only in [S − 80, S), at S + 24 and S + 48 and in [q + L, q + L + 32 · k). -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (S cap q : Nat)
    (hS : 65536 + 128 ≤ S ∧ S + 56 < 4294967296 ∧ S % 8 = 0) (hcap : cap < 18446744073709551616) :
    ∀ (k : Nat) (ω : Regs) (μ : Memory) (s L : Nat), 0 < k →
    ω[1] = UInt64.ofNat S → ω[5] = UInt64.ofNat (32 * k) → ω[6] = UInt64.ofNat s →
    32 * k < 18446744073709551616 →
    μ.readN (S + 32) 8 = Num.encodeLE 8 cap → μ.readN (S + 40) 8 = Num.encodeLE 8 q →
    μ.readN (S + 48) 8 = Num.encodeLE 8 L → L + 32 * k ≤ cap →
    (65536 ≤ q + L ∧ q + L + 32 * k + 16 ≤ S - 80) → (65536 ≤ s ∧ s + 32 * k + 16 ≤ S - 80) →
    (q + L + 32 * k + 24 ≤ s ∨ s + 32 * k + 24 ≤ q + L) →
    (∀ a, s ≤ a → a < s + 32 * k → μ.readable a = true) →
    (∀ a, q + L ≤ a → a < q + L + 32 * k → μ.writable a = true) →
    (∀ a, S - 80 ≤ a → a < S + 56 → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 40336 ω μ x 40365 ω' μ' x (600 * k) ∧
      ω'[1] = UInt64.ofNat S ∧
      μ'.readN (q + L) (32 * k) = μ.readN s (32 * k) ∧ μ'.readN (S + 48) 8 = Num.encodeLE 8 (L + 32 * k) ∧
      (∀ a, a < 4294967296 → (a < S - 80 ∨ S ≤ a) → (a < S + 24 ∨ S + 32 ≤ a) →
        (a < S + 48 ∨ S + 56 ≤ a) → (a < q + L ∨ q + L + 32 * k ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)
  | 0, _, _, _, _, hk, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hk (by decide)
  | k + 1, ω, μ, s, L, _, h1, h5, h6, hr64, vc, vq, vl, hroom, hdst, hsrc, hdj, hrs, hwd, hwf => by
    obtain ⟨ω1, μ1, run1, a1, a5, a6, ad, al, afr, ard, awr⟩ := iter (p := p) (P := P) (R := R) x ω μ S s
      (32 * (k + 1)) cap q L h1 h5 h6 (by omega) hr64 hS vc vq vl (by omega) hcap ⟨hdst.1, by omega⟩
      ⟨hsrc.1, by omega⟩ (by omega) (fun a h1 h2 => hrs a h1 (by omega))
      (fun a h1 h2 => hwd a h1 (by omega)) hwf
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨ω1, μ1, ?_, a1, ?_, ?_, ?_, ard, awr⟩
      · simpa using run1
      · simpa using ad
      · simpa using al
      · simpa using afr
    · have hne : 32 * (k + 1) ≠ 32 := by omega
      simp only [hne, ↓reduceIte] at run1
      obtain ⟨ω2, μ2, run2, b1, bd, bl, bfr, brd, bwr⟩ := loop (p := p) (P := P) x S cap q hS hcap k ω1 μ1
        (s + 32) (L + 32) hk a1 (by rw [a5]; congr 1) a6 (by omega)
        (by rw [readN_keep (fun b h1 h2 => afr b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vc)
        (by rw [readN_keep (fun b h1 h2 => afr b (by omega) (by omega) (by omega) (by omega) (by omega))]; exact vq)
        al (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
        (fun a h1 h2 => by rw [ard]; exact hrs a (by omega) (by omega))
        (fun a h1 h2 => by rw [awr]; exact hwd a (by omega) (by omega))
        (fun a h1 h2 => by rw [awr]; exact hwf a h1 h2)
      refine ⟨ω2, μ2, ?_, b1, ?_, ?_, ?_, fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩
      · exact (run1.trans run2).mono (by omega)
      · rw [show 32 * (k + 1) = 32 + 32 * k by omega, Memory.readN_split, Memory.readN_split,
          show q + L + 32 = q + (L + 32) by omega, bd,
          readN_keep (fun b h1 h2 => bfr b (by omega) (by omega) (by omega) (by omega) (by omega)), ad,
          readN_keep (fun b h1 h2 => afr b (by omega) (by omega) (by omega) (by omega) (by omega))]
      · rw [bl]; congr 1; omega
      · intro a h0 h1 h2 h3 h4
        rw [bfr a h0 h1 h2 h3 (by omega), afr a h0 h1 h2 h3 (by omega)]

end Services.Bootstrap.Acc.Handlers.AssignLoop
