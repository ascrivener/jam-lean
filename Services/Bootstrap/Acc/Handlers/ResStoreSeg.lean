import Services.Bootstrap.Acc.Handlers.ResStore
import Services.Bootstrap.Acc.Handlers.RecentSlotWrite

/-!
# The results store (36170): the straight-line segments

`on_work_item`'s results write (GP v0.8.0 Appendix B, Ω_W) through 36170, in the callee frame
S = sp − 96 that `rs_pre` sets up (kp at S + 16, n at S + 24, ω₀, ω₅, ω₆ saved at S + 88, S + 80,
S + 72):
- `rs_vec` (36217 → 30977): `alloc` returned ptr ≠ 0; the value's `Vec { 144·n + 4, ptr, 0 }` at
  S + 32, n as a `u32` at S + 56, and the call of the length prefix (return address 1694);
  `rs_null`: ptr = 0 → the trap at 36528;
- `rs_zero` (36263 → 33843, n = 0): the value's `Vec` moved (capacity to S + 24, length to S + 8,
  ptr in ω₆) and the key encoder called with out S + 32 and the key value kp (return address 1704);
- `rs_set` (36432 → 48104): `set(out S + 56, key, value)` (return address 1706), the value's ptr
  saved at S;
- `rs_ret`: `set`'s returns → 36456;
- `rs_d1` (36456 → 40613): `set`'s result word r saved at S + 16, its octet b at S + 64 in ω₆, and
  `dealloc` of the key's buffer (return address 1708);
- `rs_d2` (36482 → 40613): `dealloc` of the value's buffer (return address 1710);
- `rs_end` (36499 → the return): ω₇ := −1 if r ≠ −1 (`Ok`), else b; ω₀, ω₅, ω₆ restored.
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Alloc Services.Bootstrap.Acc Services.Bootstrap.Spec
  Services.Bootstrap.Acc.Handlers.KeyEnc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **36217, `alloc` returned 0**: on to the trap at 36528. -/
theorem rs_null {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) : FreeStepsH p R 36217 ω μ x 36528 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h7, bs_36528]

/-- The trap at 36528 (`handle_alloc_error`): ☇ (GP §A.5.1). -/
theorem trap_36528 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (ω : Regs) (μ : Memory) :
    FreeExit p 36528 ω μ .panic ω μ := by
  have hd := d_36528 (p := p) (P := P)
  have hs : P.freeStep 36528 ω μ = (.panic, P.next 36528, ω, μ) := by
    simp [Program.freeStep, hd.2.1, Program.exec, Program.finalState, memoryException]
  have := FreeExit.step (p := p) hd.1 hs (by decide)
  simpa using this

/-- **36217 … 36257, `alloc` returned ptr ≠ 0** (ω₇), ω₅ = 144·n, n < 2³² at S + 24: the `Vec
    { 144·n + 4, ptr, 0 }` at S + 32, n as a `u32` at S + 56, and the call of the length prefix
    (30977) with ω₇ = S + 56, ω₈ = S + 32 and return address 1694. -/
theorem rs_vec {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S n ptr : Nat) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat (144 * n))
    (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0) (hptr : ptr < 18446744073709551616)
    (hn : n < 4294967296) (hS : S + 96 < 4294967296)
    (mn : μ.readN (S + 24) 8 = Num.encodeLE 8 n)
    (hr : ∀ a, S + 24 ≤ a → a < S + 32 → μ.readable a = true)
    (hw : ∀ a, S + 32 ≤ a → a < S + 60 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36217 ω μ x 30977 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1694 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 56) ∧ ω'[8] = UInt64.ofNat (S + 32) ∧
      μ'.readN (S + 32) 8 = Num.encodeLE 8 (144 * n + 4) ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 0 ∧ μ'.readN (S + 56) 4 = Num.encodeLE 4 n ∧
      (∀ a, a < 4294967296 → (a < S + 32 ∨ S + 60 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hptr]; exact hp0
  have rn := Handlers.DesignateAlloc.rd8 (by omega) mn
  have hsh' : n >>> 32 = 0 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hn
  have hsh : (n % 18446744073709551616) >>> (32 % 64) = 0 := by
    rw [Nat.mod_eq_of_lt (by omega)]; exact hsh'
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hp0', hS, rn, hsh, hsh', hr, hw, bs_30977, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h5]

/-- **36263 … 36426, n = 0** (at S + 24): the value's capacity v (S + 32) moved to S + 24, its length ℓ
    (S + 48) to S + 8, its ptr (S + 40) in ω₆, and the call of the key encoder (33843) with out S + 32,
    the key value kp (S + 16) and return address 1704. -/
theorem rs_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S v ptr len kp : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 96 < 4294967296)
    (hv : v < 2 ^ 64) (hptr : ptr < 2 ^ 64) (hlen : len < 2 ^ 64) (hkp : kp < 2 ^ 64)
    (mn : μ.readN (S + 24) 8 = Num.encodeLE 8 0) (mv : μ.readN (S + 32) 8 = Num.encodeLE 8 v)
    (mp : μ.readN (S + 40) 8 = Num.encodeLE 8 ptr) (ml : μ.readN (S + 48) 8 = Num.encodeLE 8 len)
    (mk : μ.readN (S + 16) 8 = Num.encodeLE 8 kp)
    (hr : ∀ a, S + 16 ≤ a → a < S + 56 → μ.readable a = true)
    (hw : ∀ a, S + 8 ≤ a → a < S + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36263 ω μ x 33843 ω' μ' x 11 ∧
      ω'[0] = UInt64.ofNat 1704 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat ptr ∧
      ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat kp ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 v ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 16 ≤ a) → (a < S + 24 ∨ S + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rn := Handlers.DesignateAlloc.rd8 (by decide) mn
  have rv := Handlers.DesignateAlloc.rd8 hv mv
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have rl := Handlers.DesignateAlloc.rd8 hlen ml
  have rk := Handlers.DesignateAlloc.rd8 hkp mk
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, rn, rv, rp, rl, rk, hr, hw, bs_36405, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, ?_, ?_, ?_, ?_, ?_, fun a ha h1' h2' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **36432 … 36450**: the call of `set` (48104) with out S + 56, the key (ptr kp at S + 40, length kz at
    S + 48), the value (ptr vp in ω₆, length vz at S + 8) and return address 1706; vp saved at S. -/
theorem rs_set {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S kp kz vp vz : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat vp)
    (hS : S + 96 < 4294967296) (hkp : kp < 2 ^ 64) (hkz : kz < 2 ^ 64) (hvz : vz < 2 ^ 64)
    (hvp : vp < 2 ^ 64)
    (mkp : μ.readN (S + 40) 8 = Num.encodeLE 8 kp) (mkz : μ.readN (S + 48) 8 = Num.encodeLE 8 kz)
    (mvz : μ.readN (S + 8) 8 = Num.encodeLE 8 vz)
    (hr : ∀ a, S + 8 ≤ a → a < S + 56 → μ.readable a = true)
    (hw : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36432 ω μ x 48104 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1706 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat kp ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (S + 56) ∧ ω'[8] = UInt64.ofNat kp ∧ ω'[9] = UInt64.ofNat kz ∧
      ω'[10] = UInt64.ofNat vp ∧ ω'[11] = UInt64.ofNat vz ∧ μ'.readN S 8 = Num.encodeLE 8 vp ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rkp := Handlers.DesignateAlloc.rd8 hkp mkp
  have rkz := Handlers.DesignateAlloc.rd8 hkz mkz
  have rvz := Handlers.DesignateAlloc.rd8 hvz mvz
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h6, hS, rkp, rkz, rvz, hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, ?_, by reg_val, by reg_val, ?_, by reg_val, ?_,
      fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)
    all_goals try (simp only [h6, UInt64.toNat_ofNat']; congr 1; omega)

/-- **`set`'s returns** (the `jumpInd` at 48158, 48250 or 48235) with ω₀ = 1706: on to 36456. -/
theorem rs_ret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (e : Nat) (he : e = 48158 ∨ e = 48250 ∨ e = 48235) (h0 : ω[0] = UInt64.ofNat 1706) :
    FreeStepsH p R e ω μ x 36456 ω μ x 1 := by
  rcases he with rfl | rfl | rfl
  all_goals
    rw [show ω = regsNF ω [] from rfl]
    pvm_go [h0]

/-- **36456 … 36476**, the key's capacity kc ≠ 0 (at S + 32): `set`'s result word r (at S + 56) saved at
    S + 16, the octet b at S + 64 in ω₆, and the call of `dealloc` (40613) with ω₇ = ω₅ (the key's
    buffer) and return address 1708. -/
theorem rs_d1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S kc r b : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 96 < 4294967296)
    (hkc : kc < 2 ^ 64) (hk0 : kc ≠ 0) (hr64 : r < 2 ^ 64) (hb : b < 256)
    (mk : μ.readN (S + 32) 8 = Num.encodeLE 8 kc) (mr : μ.readN (S + 56) 8 = Num.encodeLE 8 r)
    (mb : μ.readN (S + 64) 1 = Num.encodeLE 1 b)
    (hr : ∀ a, S + 32 ≤ a → a < S + 72 → μ.readable a = true)
    (hw : ∀ a, S + 16 ≤ a → a < S + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 36456 ω μ x 40613 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1708 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat b ∧
      ω'[7] = ω[5] ∧ μ'.readN (S + 16) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (a < S + 16 ∨ S + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rk := Handlers.DesignateAlloc.rd8 hkc mk
  have rr := Handlers.DesignateAlloc.rd8 hr64 mr
  have rb : rdN μ (S + 64) 1 = b := by
    show Num.decodeLE _ = _; rw [mb, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hb]
  have hk0' : kc % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hkc]; exact hk0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hS, rk, rr, rb, hk0', hr, hw, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, ?_, ?_, ?_, fun a ha h1' => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1]
    all_goals try simp only [PVM.getElem_regsNF, List.lookup_nil, Option.getD_none]
    all_goals try rd_simp []
    all_goals try rfl
    all_goals try (congr 1; omega)

/-- **36482 … 36493**, the value's capacity c ≠ 0 (at S + 24): the call of `dealloc` (40613) with
    ω₇ = the word at S (the value's buffer) and return address 1710. Memory is kept. -/
theorem rs_d2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S c ptr : Nat) (h1 : ω[1] = UInt64.ofNat S) (hS : S + 96 < 4294967296)
    (hc : c < 2 ^ 64) (hc0 : c ≠ 0) (hptr : ptr < 2 ^ 64)
    (mc : μ.readN (S + 24) 8 = Num.encodeLE 8 c) (mp : μ.readN S 8 = Num.encodeLE 8 ptr)
    (hr : ∀ a, S ≤ a → a < S + 32 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 36482 ω μ x 40613 ω' μ x 5 ∧
      ω'[0] = UInt64.ofNat 1710 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat ptr := by
  have rc := Handlers.DesignateAlloc.rd8 hc mc
  have rp := Handlers.DesignateAlloc.rd8 hptr mp
  have hc0' : c % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt hc]; exact hc0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hS, rc, rp, hc0', hr, ↓rdN_fold]
  · refine ⟨by reg_val, ?_, by reg_val, by reg_val, by reg_val⟩
    simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some', h1,
      List.lookup_nil, Option.getD_none]

/-- **36499 … 36525, the return**: ω₇ := −1 if `set`'s result word r (at S + 16) is not −1 (`Ok`), else
    ω₆ (the error code b); ω₀, ω₅, ω₆ restored from S + 88, S + 80, S + 72, the frame popped, and the
    return through ω₀ = 294 to 8477 (row 9's call). -/
theorem rs_end {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (S r b v5 v6 : Nat) (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat b)
    (hS : S + 96 < 4294967296) (hb : b < 2 ^ 64) (hr64 : r < 2 ^ 64) (hv5 : v5 < 2 ^ 64) (hv6 : v6 < 2 ^ 64)
    (mr : μ.readN (S + 16) 8 = Num.encodeLE 8 r) (m0 : μ.readN (S + 88) 8 = Num.encodeLE 8 294)
    (m5 : μ.readN (S + 80) 8 = Num.encodeLE 8 v5) (m6 : μ.readN (S + 72) 8 = Num.encodeLE 8 v6)
    (hr : ∀ a, S + 16 ≤ a → a < S + 96 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 36499 ω μ x 8477 ω' μ x 10 ∧
      ω'[1] = UInt64.ofNat (S + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧ ω'[6] = UInt64.ofNat v6 ∧
      ω'[7] = (if r = 18446744073709551615 then UInt64.ofNat b else UInt64.ofNat 18446744073709551615) := by
  have rr := Handlers.DesignateAlloc.rd8 hr64 mr
  have r0 := Handlers.DesignateAlloc.rd8 (by decide) m0
  have r5 := Handlers.DesignateAlloc.rd8 hv5 m5
  have r6 := Handlers.DesignateAlloc.rd8 hv6 m6
  rw [show ω = regsNF ω [] from rfl]
  by_cases hr1 : r = 18446744073709551615
  · subst hr1
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h6, hS, rr, r0, r5, r6, hr, ↓rdN_fold]
    · refine ⟨?_, by reg_val, by reg_val, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6]
      all_goals try (congr 1; omega)
      all_goals try rw [Nat.mod_eq_of_lt hb]
  · have hr1' : (r + 1) % 18446744073709551616 ≠ 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · pvm_go [h1, h6, hS, rr, r0, r5, r6, hr, hr1', ↓rdN_fold]
    · refine ⟨?_, by reg_val, by reg_val, ?_⟩
      all_goals simp [PVM.getElem_regsNF, PVM.lookup_cons_nat, h1, h6, hr1]
      all_goals try (congr 1; omega)

end Services.Bootstrap.Acc.Handlers.ResStore
