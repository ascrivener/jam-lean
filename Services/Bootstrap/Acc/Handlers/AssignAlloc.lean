import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `Assign`'s buffer (40215 … 41177, 40302 … 40336)

40215 (`Assign`'s callee, its frame at S = ω₁, the queue's length n at S + 24 and ω₅ = 32 · n)
checks 32 · n + 3 ≤ 2³⁷ − 32, takes the allocator's lock and calls `alloc_impl` (41177) for n + 1
units of alignment 1, not zeroed, return address 1976 (40302). There the lock is cleared and the
vector `{cap: 32 · n + 3, ptr, len: 0}` set up at S + 32 for the copy loop (40336).
-/

namespace Services.Bootstrap.Acc.Handlers.AssignAlloc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A word read back from its encoding. -/
theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- **40215 … 41177**, n hashes, 32 · n + 3 ≤ 2³⁷ − 32 and n + 1 < 2³¹: the lock taken (the scratch
    at 196608 … 196616 used), 196792 at S + 16, and the call of `alloc_impl` with ω₇ = 196792,
    ω₈ = 1 (alignment), ω₉ = n + 1 units, ω₁₀ = 0 (not zeroed), return address 1976; ω₅ kept. -/
theorem lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S n : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat (32 * n))
    (hn : 32 * n + 3 ≤ 137438953440) (hn1 : n + 1 < 2147483648)
    (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1)
    (hS : S0 ≤ S ∧ S + 32 ≤ S1 ∧ HT ≤ S ∧ S1 < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 40215 ω μ x 41177 ω' μ' x 40 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧ ω'[9] = UInt64.ofNat (n + 1) ∧
      ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 1976 ∧ ω'[5] = ω[5] ∧ ω'[1] = ω[1] ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 196792 ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
        (a < S + 16 ∨ S + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  have r24 := rd8 (by omega) m24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, hn, hn1, r24, hand, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_,
      fun a ha h1 h2 h3 => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rd_simp []
      rfl
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    all_goals rd_simp []
    all_goals try rfl

/-- **40302 … 40336**, `alloc_impl` returned a block ptr ≠ 0: the lock byte cleared; the vector
    `{cap: 32 · n + 3, ptr, len: 0}` set up at S + 32; n ≠ 0, so on to the copy loop (40336) with
    ω₅ = 32 · n and ω₆ (the queue's address) kept. -/
theorem unlock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S n ptr : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat (32 * n))
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 4294967296)
    (hn : 0 < n) (hn' : 32 * n + 3 < 4294967296)
    (m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 196792) (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (hS : 206852 ≤ S ∧ S + 56 < 4294967296)
    (hwf : ∀ a, S + 16 ≤ a → a < S + 56 → μ.writable a = true) (hwl : μ.writable 206848 = true) :
    ∃ ω' μ', FreeStepsH p R 40302 ω μ x 40336 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat (32 * n) ∧ ω'[6] = ω[6] ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 (32 * n + 3) ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 0 ∧ μ'.read 206848 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → (a < S + 32 ∨ S + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S + 16 ≤ a → a < S + 56 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  have hn0 : n % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have r16 := rd8 (by decide) m16
  have r24 := rd8 (by omega) m24
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, hp0', hn0, hptr, hn', r16, r24, hwf, hr, hwl, hrl, hS,
    rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h5]
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat]
    all_goals rd_simp [PVM.read_writeN_single]
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **`alloc_impl` returned null** (ω₇ = 0 at 40302): the lock byte is cleared and the branch at
    40318 goes to the trap at 40234 (☇, GP §A.5.1). -/
theorem allocNull {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S : Nat) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = 0)
    (m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 196792) (hS : S + 24 < 4294967296)
    (hrf : ∀ a, S + 16 ≤ a → a < S + 24 → μ.readable a = true) (hwl : μ.writable 206848 = true) :
    ∃ ω' μ', FreeRunH p R 40302 ω μ x .panic ω' μ' x := by
  have r16 := rd8 (by decide) m16
  have run : ∃ ω' μ', FreeStepsH p R 40302 ω μ x 40234 ω' μ' x 6 := by
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?ω', ?μ', ?run⟩
    case run => pvm_go [h1, h7, r16, hS, hrf, hwl, ↓rdN_fold]
  obtain ⟨ω', μ', hs⟩ := run
  have hd := d_40234 (p := p) (P := P)
  have hst : P.freeStep 40234 ω' μ' = (.panic, P.next 40234, ω', μ') := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have he := FreeExit.step (p := p) hd.1 hst (by decide)
  exact ⟨ω', μ', hs.run (.exit (FreeRun.exit (by simpa using he)) (by simp))⟩

/-- **40365 … 40397**, after the loop: the `assign` call's registers (GP Ω_A: c = ω₇, o = ω₈,
    a = ω₉): ω₇ := the u16 core index at cp (the word at S), ω₈ := ptr (the queue's
    serialisation, the word at S + 40), ω₉ := the u32 assigner at ap (the word at S + 8); ω₅ := 0
    (the capacity is not 0), ω₆ := ptr. -/
theorem preCall {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S cap ptr cp ap core a : Nat) (h1 : ω[1] = UInt64.ofNat S)
    (hS : S + 48 < 4294967296) (hcap : 0 < cap) (hcap' : cap < 18446744073709551616)
    (hptr : ptr < 18446744073709551616) (hcp : cp + 2 < 4294967296) (hap : ap + 4 < 4294967296)
    (m0 : μ.readN S 8 = Num.encodeLE 8 cp) (m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 ap)
    (m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 cap) (m40 : μ.readN (S + 40) 8 = Num.encodeLE 8 ptr)
    (mc : μ.readN cp 2 = Num.encodeLE 2 core) (ma : μ.readN ap 4 = Num.encodeLE 4 a)
    (hc : core < 65536) (ha : a < 4294967296)
    (hrf : ∀ a, S ≤ a → a < S + 48 → μ.readable a = true)
    (hrc : ∀ a, cp ≤ a → a < cp + 2 → μ.readable a = true)
    (hra : ∀ x, ap ≤ x → x < ap + 4 → μ.readable x = true) :
    ∃ ω', FreeStepsH p R 40365 ω μ x 40397 ω' μ x 12 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat core ∧ ω'[8] = UInt64.ofNat ptr ∧
      ω'[9] = UInt64.ofNat a ∧ ω'[5] = UInt64.ofNat 0 ∧ ω'[6] = UInt64.ofNat ptr := by
  have r0 := rd8 (by omega) m0
  have r8 := rd8 (by omega) m8
  have r32 := rd8 hcap' m32
  have r40 := rd8 hptr m40
  have rc : rdN μ cp 2 = core := by
    show Num.decodeLE _ = _
    rw [mc, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hc]
  have ra : rdN μ ap 4 = a := by
    show Num.decodeLE _ = _
    rw [ma, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt ha]
  have hlt : ¬ cap % 18446744073709551616 < 1 := by rw [Nat.mod_eq_of_lt hcap']; omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, r0, r8, r32, r40, rc, ra, hlt, hrf, hrc, hra, hcp, hap, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

end Services.Bootstrap.Acc.Handlers.AssignAlloc
