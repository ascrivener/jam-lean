import Services.Bootstrap.Acc.Inputs.FetchVec

/-!
# `Designate`'s buffer (49597 … 41177)

49597 (`Designate`'s callee, its frame at S = ω₁) sizes the keys' serialisation, L = 336 · n for n
keys (GP §6.3), saves the source `Vec`'s address (ω₅) at S + 16 and n at S + 8, checks
L ≤ 2³⁷ − 32, takes the allocator's lock (the word at 206848) and calls `alloc_impl` (41177) for
⌈L/32⌉ units of alignment 1, not zeroed, return address 2202 (49733).
-/

namespace Services.Bootstrap.Acc.Handlers.DesignateAlloc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A word read back from its encoding. -/
theorem rd8 {μ : Memory} {a w : Nat} (hw : w < 2 ^ 64) (h : μ.readN a 8 = Num.encodeLE 8 w) : rdN μ a 8 = w := by
  show Num.decodeLE _ = _
  rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]

/-- **49597 … 41177**, n > 0 keys, L = 336 · n ≤ 2³⁷ − 32: the source `Vec`'s address v at S + 16,
    n at S + 8, the lock taken (the scratch at 196608 … 196616 used), 196792 at S, and the call of
    `alloc_impl` with ω₇ = 196792, ω₈ = 1 (alignment), ω₉ = ⌈L/32⌉, ω₁₀ = 0 (not zeroed), return
    address 2202; ω₅ = L. -/
theorem lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S v n : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v)
    (h6 : ω[6] = UInt64.ofNat n) (hn : 0 < n) (hL : 336 * n + 31 < 68719476736)
    (hv : v < 18446744073709551616)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1)
    (hS : S0 ≤ S ∧ S + 24 ≤ S1 ∧ HT ≤ S ∧ S1 < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 49597 ω μ x 41177 ω' μ' x 40 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat ((336 * n + 31) / 32) ∧ ω'[10] = UInt64.ofNat 0 ∧ ω'[0] = UInt64.ofNat 2202 ∧
      ω'[6] = UInt64.ofNat 1 ∧ ω'[5] = UInt64.ofNat (336 * n) ∧ ω'[1] = ω[1] ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 v ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 n ∧
      μ'.readN S 8 = Num.encodeLE 8 196792 ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) →
        (a < S ∨ S + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, hn, hv, hand, show 137438953440 ≥ 336 * n by omega, hwr, hr,
    rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_, ?_, ?_,
      ?_, fun a ha h1 h2 h3 => ?_, fun a => ?_⟩
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
        List.lookup_nil, Option.getD_none]
    all_goals rd_simp []
    all_goals try rfl

/-- **49733 … 49775**, `alloc_impl` returned a block ptr ≠ 0 for L octets: the lock byte cleared;
    the vector `{cap: L, ptr, len: 0}` set up at S + 24; ω₅ := the keys' address s (the word at
    v + 8, the source `Vec`'s pointer) and ω₆ := 336 · n, the loop's entry. -/
theorem unlock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S v n s L ptr : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat L)
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 4294967296) (hL : L < 4294967296)
    (hn : 0 < n) (hn336 : 336 * n < 18446744073709551616) (hs : s < 18446744073709551616)
    (m0 : μ.readN S 8 = Num.encodeLE 8 196792) (m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n)
    (m16 : μ.readN (S + 16) 8 = Num.encodeLE 8 v) (mv : μ.readN (v + 8) 8 = Num.encodeLE 8 s)
    (hS : 206852 ≤ S ∧ S + 48 < 4294967296) (hv : S + 48 ≤ v) (hv' : v + 16 < 4294967296)
    (hwf : ∀ a, S ≤ a → a < S + 48 → μ.writable a = true) (hwl : μ.writable 206848 = true)
    (hrv : ∀ a, v + 8 ≤ a → a < v + 16 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 49733 ω μ x 49775 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat s ∧ ω'[6] = UInt64.ofNat (336 * n) ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 L ∧ μ'.readN (S + 32) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (S + 40) 8 = Num.encodeLE 8 0 ∧ μ'.read 206848 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → (a < S + 24 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  have hn' : n % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; omega
  have r0 := rd8 (by decide) m0
  have r8 := rd8 (by omega) m8
  have r16 := rd8 (by omega) m16
  have rv := rd8 hs mv
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h7, hp0', hn', hptr, hL, r0, r8, r16, rv, hwf, hr, hwl, hrl, hrv, hS, hv,
    rdN_writeN_disjoint, ↓rdN_fold]
  case post =>
    refine ⟨?_, ?_, by reg_val, ?_, ?_, ?_, ?_, fun a ha h1 h2 => ?_, fun a => ?_, fun a => ?_⟩
    · simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, ↓reduceIte, PVM.getD_some']
    all_goals rd_simp [PVM.read_writeN_single]
    all_goals try rfl

/-- **`alloc_impl` returned null** (ω₇ = 0 at 49733): the lock byte is cleared and the branch at
    49745 goes to the trap at 49639, so accumulate ends in ☇ (GP §A.5.1). -/
theorem allocNull {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S : Nat) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = 0)
    (m0 : μ.readN S 8 = Num.encodeLE 8 196792) (hS : S + 8 < 4294967296)
    (hrf : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true) (hwl : μ.writable 206848 = true) :
    ∃ ω' μ', FreeRunH p R 49733 ω μ x .panic ω' μ' x := by
  have r0 := rd8 (by decide) m0
  have run : ∃ ω' μ', FreeStepsH p R 49733 ω μ x 49639 ω' μ' x 6 := by
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?ω', ?μ', ?run⟩
    case run => pvm_go [h1, h7, r0, hS, hrf, hwl, ↓rdN_fold]
  obtain ⟨ω', μ', hs⟩ := run
  have hd := d_49639 (p := p) (P := P)
  have hst : P.freeStep 49639 ω' μ' = (.panic, P.next 49639, ω', μ') := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have he := FreeExit.step (p := p) hd.1 hst (by decide)
  exact ⟨ω', μ', hs.run (.exit (FreeRun.exit (by simpa using he)) (by simp))⟩

/-- **49856 … 49874**, after the loop: the `designate` call's registers, ω₇ = ptr (the keys'
    serialisation) and ω₈ = n (GP Ω_D: o = ω₇, z = ω₈), return address 2212 in ω₀, ω₅ = 9. -/
theorem preCall {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S n ptr : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 48 < 4294967296)
    (hn : n < 18446744073709551616) (hptr : ptr < 18446744073709551616)
    (m8 : μ.readN (S + 8) 8 = Num.encodeLE 8 n) (m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 ptr)
    (hrf : ∀ a, S ≤ a → a < S + 48 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 49856 ω μ x 49874 ω' μ x 8 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat ptr ∧ ω'[8] = UInt64.ofNat n ∧
      ω'[5] = UInt64.ofNat 9 ∧ ω'[0] = UInt64.ofNat 2212 := by
  have r8 := rd8 hn m8
  have r32 := rd8 hptr m32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h1, hS, r8, r32, hrf, ↓rdN_fold]
  case post =>
    refine ⟨?_, by reg_val, by reg_val, by reg_val, by reg_val⟩
    simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **49877 … 49910**, `designate` returned r = OK (0) or HUH (2⁶⁴ − 9): the result's index b is
    the octet at 69076 + (r + 9) mod 2⁶⁴ (a table in the read-only data), loaded into ω₅; the
    vector's capacity L ≠ 0 sends it on to the free of the buffer (49910). -/
theorem postCall {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S r L b : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat 9)
    (h7 : ω[7] = UInt64.ofNat r)
    (hr : r = 0 ∨ r = 18446744073709551607) (hS : S + 48 < 4294967296)
    (hL : 0 < L) (hL64 : L < 18446744073709551616)
    (m24 : μ.readN (S + 24) 8 = Num.encodeLE 8 L)
    (htab : μ.readN (69076 + (r + 9) % 18446744073709551616) 1 = [UInt8.ofNat b]) (hb : b < 256)
    (hrt : μ.readable (69076 + (r + 9) % 18446744073709551616) = true)
    (hrf : ∀ a, S ≤ a → a < S + 48 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 49877 ω μ x 49910 ω' μ x 12 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat b ∧ ω'[8] = UInt64.ofNat L := by
  have r24 := rd8 hL64 m24
  have hL' : L % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hL64]; omega
  have rt : rdN μ (69076 + (r + 9) % 18446744073709551616) 1 = b := by
    show Num.decodeLE _ = _
    rw [htab]; simp [Num.decodeLE, Nat.mod_eq_of_lt hb]
  rcases hr with rfl | rfl
  all_goals
    simp only [Nat.reduceAdd, Nat.reduceMod] at rt hrt
    rw [show ω = regsNF ω [] from rfl]
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h5, h7, hS, r24, hL', rt, hrt, hrf, ↓rdN_fold]
    · refine ⟨?_, by reg_val, by reg_val⟩
      simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]

/-- **49910 … 42327**: the buffer ptr (the word at S + 32) to be freed: the lock taken (the
    scratch at 196608 … 196616 used) and the call of `free_impl` with ω₇ = 196792, ω₈ = ptr, return
    address 2214 (49968); ω₆ = 196792, ω₅ and ω₁ kept. -/
theorem freeLock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S ptr : Nat) (h1 : ω[1] = UInt64.ofNat S) (hptr : ptr < 18446744073709551616)
    (m32 : μ.readN (S + 32) 8 = Num.encodeLE 8 ptr)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1)
    (hS : S0 ≤ S ∧ S + 48 ≤ S1 ∧ HT ≤ S ∧ S1 < 4294967296) :
    ∃ ω' μ', FreeStepsH p R 49910 ω μ x 42327 ω' μ' x 20 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat ptr ∧ ω'[0] = UInt64.ofNat 2214 ∧
      ω'[6] = UInt64.ofNat 196792 ∧ ω'[5] = ω[5] ∧ ω'[1] = ω[1] ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  have r32 := rd8 hptr m32
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, r32, hand, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val,
      fun a ha h1 h2 => ?_, fun a => ?_⟩
    all_goals rd_simp []

/-- **49968 … 10070**, back from `free_impl` with ω₆ = 196792 and the result's index b in ω₅: the
    lock byte cleared, ω₇ := b, and the return to 10070 (address 354 at S + 64) with ω₅, ω₆ restored
    from S + 56, S + 48 and the frame closed (ω₁ := S + 72). -/
theorem unlockRet {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S b r5 r6 : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat b)
    (h6 : ω[6] = UInt64.ofNat 196792) (hb : b < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (m64 : μ.readN (S + 64) 8 = Num.encodeLE 8 354) (m56 : μ.readN (S + 56) 8 = Num.encodeLE 8 r5)
    (m48 : μ.readN (S + 48) 8 = Num.encodeLE 8 r6) (hS : 206852 ≤ S ∧ S + 72 < 4294967296)
    (hrf : ∀ a, S + 48 ≤ a → a < S + 72 → μ.readable a = true) (hwl : μ.writable 206848 = true) :
    ∃ ω', FreeStepsH p R 49968 ω μ x 10070 ω' (μ.writeN 206848 [UInt8.ofNat 0]) x 12 ∧
      ω'[7] = UInt64.ofNat b ∧ ω'[1] = UInt64.ofNat (S + 72) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 := by
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  have r64 := rd8 (by decide) m64
  have r56 := rd8 hr5 m56
  have r48 := rd8 hr6 m48
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, hS, hwl, hrl, hrf, rdN_writeN_disjoint, r64, r56, r48, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']

end Services.Bootstrap.Acc.Handlers.DesignateAlloc
