import Services.Bootstrap.Fmt.Spec

/-!
# `<u32 as fmt::LowerHex>::fmt` (60525), frame-only

The function renders the value's hex digits, least significant first, into its 16-octet frame,
from sp − 9 down. It looks each digit up in the table at 71060 (`0123456789abcdef`), then calls
`pad_integral` (61857) with the digits and the prefix `0x` (71076). With plain options the prefix
isn't written, and `pad_integral` is the sink's `write_str` (`pad_plain`).

These are the steps:
- `hx_entry`: 60525 … 60546;
- `hx_iter`: one digit;
- `hx_loop`: the loop, at most 8 digits;
- `hx_call`: the call;
- `hx_ret`: the return.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- A 32-bit word loaded signed, then cut to 32 bits again, is the word. -/
theorem sext32_low (x : Nat) (hx : x < 4294967296) :
    (UInt64.ofNat ((if x < 2147483648 then (x : Int) else (x : Int) - 4294967296) %
      18446744073709551616).toNat).toNat % 4294967296 = x := by
  split
  · have : ((x : Int) % 18446744073709551616).toNat = x := by omega
    rw [this, UInt64.toNat_ofNat']
    omega
  · rename_i h
    have h2 : ((x : Int) - 4294967296) % 18446744073709551616 = ((x + 18446744069414584320 : Nat) : Int) := by
      omega
    rw [h2, Int.toNat_natCast, UInt64.toNat_ofNat']
    omega

/-- 60525 … 60545: a 16-octet frame at T = sp − 16 (ω₀ at T + 8), the `Formatter` (ω₈) kept in ω₂,
    the value read (signed) from ω₇ into ω₉, the digit cursor T + 7 in ω₇, the table 71060 in ω₈,
    and the count 0 in ω₁₂. -/
theorem hx_entry {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v F r0 : Nat) (hsp : 65536 + 16 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h8 : ω[8] = UInt64.ofNat F) (hr0 : r0 < 18446744073709551616) (hF : F < 18446744073709551616)
    (hv : v + 4 < 4294967296) (hvf : v + 4 ≤ sp - 16 ∨ sp ≤ v)
    (hrv : ∀ a, v ≤ a → a < v + 4 → μ.readable a = true)
    (hw : ∀ a, sp - 16 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 60525 ω μ x 60546 ω' μ' x 8 ∧
      ω'[1] = UInt64.ofNat (sp - 16) ∧ ω'[2] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = UInt64.ofNat (sp - 16 + 7) ∧ ω'[8] = UInt64.ofNat 71060 ∧ ω'[9].toNat % 4294967296 = rdN μ v 4 ∧
      ω'[12] = UInt64.ofNat 0 ∧ rdN μ' (sp - 16 + 8) 8 = r0 ∧
      (∀ a, a < 4294967296 → (a < sp - 16 + 8 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 16 ≤ a → a < sp → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h7, h8, hsp, hr0, hF, hv, hvf, hrv, hw, hr, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals post_simp [rdN_writeN_disjoint, rdN_writeN_same8]
    exact sext32_low _ (rdN_lt μ v 4)

/-- 60546 … 60568: one digit. From the cursor A (ω₇), the table (ω₈) and the word w (ω₉) whose low 32
    bits are v: the digit for v mod 16 is stored at A, the cursor moves to A − 1, the count (ω₁₂)
    goes up by one and v / 16 goes to ω₉. The loop goes on while v / 16 ≠ 0. -/
theorem hx_iter {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (A w k : Nat) (hA : 65536 ≤ A ∧ A < 4294967296) (hw64 : w < 18446744073709551616) (hk : k < 100)
    (h7 : ω[7] = UInt64.ofNat A) (h8 : ω[8] = UInt64.ofNat 71060) (h9 : ω[9] = UInt64.ofNat w)
    (h12 : ω[12] = UInt64.ofNat k)
    (hro : ∀ a, 71060 ≤ a → a < 71076 → μ.readable a = true) (hw : μ.writable A = true) :
    ∃ ω' μ', FreeStepsH p R 60546 ω μ x (if (w % 4294967296) / 16 = 0 then 60571 else 60546) ω' μ' x 12 ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (A - 1) ∧
      ω'[8] = UInt64.ofNat 71060 ∧ ω'[9] = UInt64.ofNat ((w % 4294967296) / 16) ∧ ω'[12] = UInt64.ofNat (k + 1) ∧
      (∀ a, a < 4294967296 → a ≠ A → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  by_cases hz : (w % 4294967296) / 16 = 0
  · rw [if_pos hz]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h7, h8, h9, h12, hA, hw64, hz, hk, hro, hw, bitwise_and_m15, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [hz, h8]
  · rw [if_neg hz]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · apply FreeStepsH.step_decode (d_60546 (p := p) (P := P))
      · pvm_simp []
      pvm_go [h7, h8, h9, h12, hA, hw64, hz, hk, hro, hw, bitwise_and_m15, ↓rdN_fold]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha => ?_, fun a => ?_, fun a => ?_⟩
      all_goals post_simp [hz, h8]

/-- **The digit loop** (60546 … 60568), for a value v (the low 32 bits of ω₉) below 16^j: it writes
    c digits, 1 ≤ c ≤ j, at A − c + 1 … A, leaves the cursor at A − c and the count at k + c, and
    reaches 60571. -/
theorem hx_loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) :
    ∀ (j w A k : Nat) (ω : Regs) (μ : Memory), w < 18446744073709551616 → w % 4294967296 < 16 ^ j →
      1 ≤ j → k + j < 100 → 65536 + j ≤ A → A < 4294967296 →
      ω[7] = UInt64.ofNat A → ω[8] = UInt64.ofNat 71060 → ω[9] = UInt64.ofNat w →
      ω[12] = UInt64.ofNat k →
      (∀ a, 71060 ≤ a → a < 71076 → μ.readable a = true) →
      (∀ a, A + 1 - j ≤ a → a ≤ A → μ.writable a = true) →
      ∃ ω' μ' c, 1 ≤ c ∧ c ≤ j ∧ FreeStepsH p R 60546 ω μ x 60571 ω' μ' x (12 * c) ∧
        ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat (A - c) ∧
        ω'[12] = UInt64.ofNat (k + c) ∧
        (∀ a, a < 4294967296 → (a + c ≤ A ∨ A < a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro j
  induction j with
  | zero => intro w A k ω μ _ _ h; omega
  | succ j ih =>
    intro w A k ω μ hw64 hv hj hk hA0 hA1 h7 h8 h9 h12 hro hwr
    obtain ⟨ω1, μ1, run1, a1, a2, a5, a6, a7, a8, a9, a12, fr1, rd1, wr1⟩ := hx_iter (p := p) (P := P) (R := R)
      x ω μ A w k ⟨by omega, hA1⟩ hw64 (by omega) h7 h8 h9 h12 hro (hwr A (by omega) (Nat.le_refl _))
    by_cases hz : (w % 4294967296) / 16 = 0
    · rw [if_pos hz] at run1
      exact ⟨ω1, μ1, 1, Nat.le_refl _, by omega, run1.mono (by omega), a1, a2, a5, a6, a7, a12,
        fun a h1 h2 => fr1 a h1 (by omega), rd1, wr1⟩
    · rw [if_neg hz] at run1
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h | h
        · subst h; simp at hv; omega
        · exact h
      have hv' : (w % 4294967296 / 16) % 4294967296 < 16 ^ j := by
        rw [Nat.pow_succ] at hv
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      obtain ⟨ω2, μ2, c, hc1, hc2, run2, b1, b2, b5, b6, b7, b12, fr2, rd2, wr2⟩ :=
        ih (w % 4294967296 / 16) (A - 1) (k + 1) ω1 μ1 (by omega) hv' hj1 (by omega) (by omega) (by omega)
          a7 a8 a9 a12 (fun a h1 h2 => by rw [rd1]; exact hro a h1 h2)
          (fun a h1 h2 => by rw [wr1]; exact hwr a (by omega) (by omega))
      refine ⟨ω2, μ2, c + 1, by omega, by omega, (run1.trans run2).mono (by omega), b1.trans a1, b2.trans a2,
        b5.trans a5, b6.trans a6, by rw [b7]; congr 1; omega, by rw [b12]; congr 1; omega,
        fun a h1 h2 => by rw [fr2 a h1 (by omega), fr1 a h1 (by omega)], fun a => by rw [rd2, rd1],
        fun a => by rw [wr2, wr1]⟩

/-- 60571 … 60589: the digits are T + 8 − c … T + 8; `pad_integral` (61857) is called with the
    `Formatter` (ω₂), the prefix `0x` (71076, 2 octets) and the digits, returning to 60595 (2618). -/
theorem hx_call {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T F c : Nat) (hT : 65536 ≤ T ∧ T + 16 < 4294967296) (hc : c ≤ 8) (hF : F < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat T) (h2 : ω[2] = UInt64.ofNat F) (h12 : ω[12] = UInt64.ofNat c) :
    ∃ ω', FreeStepsH p R 60571 ω μ x 61857 ω' μ x 8 ∧
      ω'[0] = UInt64.ofNat 2618 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat F ∧
      ω'[10] = UInt64.ofNat 2 ∧ ω'[11] = UInt64.ofNat (T + 8 - c) ∧ ω'[12] = UInt64.ofNat c := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h2, h12, hT, hc]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h2, h12, Nat.mod_eq_of_lt hF]

/-- 60595 … 60601: ω₀ reloaded from T + 8, the frame closed, return. -/
theorem hx_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (T r0 t : Nat) (hT : 65536 ≤ T ∧ T + 16 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (rr : rdN μ (T + 8) 8 = r0)
    (hret : 0 < r0 ∧ r0 ≤ 2806 ∧ r0 % 2 = 0) (hjt : P.jumpTable.getD (r0 / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) (hr : ∀ a, T + 8 ≤ a → a < T + 16 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 60595 ω μ x t ω' μ x 3 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (T + 16) ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hT, rr, hret, hjt, hbt, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (show r0 < 18446744073709551616 by omega)]

/-- **`<u32 as fmt::LowerHex>::fmt`, frame-only** (60525): called with the address v of a u32 (ω₇),
    a `Formatter` F into the `String` W with plain options (ω₈), and a return address ω₀ that
    `djump` resolves to `t`, it either:
    - returns `Ok` (ω₇ = 0) to `t`, with ω₀, ω₁, ω₅, ω₆ as they were. The `String` has gained n ≤ 8
      octets (the digits, unspecified), the context is kept, and the frame `Keeps`: from sp up only
      W … W + 24 changes. Or
    - reaches a failed allocator call. -/
theorem hex32 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W v cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 464 ≤ sp ∧ sp % 8 = 0 ∧ 2147484112 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hvv : sp ≤ v ∧ v + 4 < 4294967296) (hrv : ∀ a, v ≤ a → a < v + 4 → μ.readable a = true)
    (hn : len + 8 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 8 ∧
      FreeStepsH p R 60525 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2300) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 60525 ω μ x (1073741824 + 2500) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  -- the entry
  obtain ⟨ω1, μ1, run1, a1, a2, a5, a6, a7, a8, a9, a12, sv, fr1, rd1, wr1⟩ := hx_entry (p := p) (P := P) (R := R)
    x ω μ sp v F ret ⟨by omega, by omega⟩ h0 h1 h7 h8 (by omega) (by omega) (by omega) (Or.inr hvv.1) hrv
    (fun a h1 h2 => hst a (by omega) (by omega))
  -- the digits
  have h9 : ω1[9] = UInt64.ofNat ω1[9].toNat := UInt64.ofNat_toNat.symm
  obtain ⟨ω2, μ2, c, hc1, hc2, run2, b1, b2, b5, b6, b7, b12, fr2, rd2, wr2⟩ := hx_loop (p := p) (P := P) (R := R) x
    8 ω1[9].toNat (sp - 16 + 7) 0 ω1 μ1 (UInt64.toNat_lt _) (by rw [a9]; have := rdN_lt μ v 4; simpa using this)
    (by omega) (by omega) (by omega) (by omega) a7 a8 h9 a12
    (fun a h1 h2 => by rw [rd1]; exact hf.vrd a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  -- the call
  obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c10, c11, c12⟩ := hx_call (p := p) (P := P) (R := R) x ω2 μ2 (sp - 16) F c
    ⟨by omega, by omega⟩ hc2 (by omega) (b1.trans a1) (b2.trans a2) (by rw [b12, Nat.zero_add])
  have k12 : ∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h1 h2 => by
    rw [fr2 a h1 (by omega), fr1 a h1 (by omega)]
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1]
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => k12 a (by omega) (Or.inl (by omega))) wr12
  have hf2 : Fmtr s₀ s μ2 F W cap len := hf.congr (fun j hj => k12 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k12 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k12 a (by omega) (Or.inl (by omega)), rd12 a⟩)
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ2 s :=
    Keeps.of_frame (Z := fun a => sp - 16 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k12 a ha (by omega)) rd12 wr12 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun d hd hu a ha => by
        have := chunk_bounds H.wf (hf.str.base d hd hu)
        have := H.hbT
        unfold InData at ha; omega)
  rcases pad_plain (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω3 μ2 s₀ s (sp - 16) F W (sp - 16 + 8 - c) c cap
      len 2618 60595 v5 v6 2 H2 hba hf2 c0 (c1.trans (b1.trans a1)) (c5.trans (b5.trans (a5.trans h5)))
      (c6.trans (b6.trans (a6.trans h6))) c7 c10 c11 c12 ⟨hv.1, hv.2, by omega⟩ (by decide) jte_1308 bs_60595
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2⟩ (by omega)
      (Or.inr ⟨by omega, by omega, Or.inl (by omega)⟩)
      (fun a h1 h2 => by rw [rd12]; exact Memory.readable_of_writable (hst a (by omega) (by omega))) with
    ⟨ω4, μ4, x4, s', cap', run4, H4, hb4, hf4, hc1', hc2', K4, e0, e1, e5, e6, e7⟩ | hx
  · obtain ⟨ω5, run5, f0, f1, f5, f6, f7⟩ := hx_ret (p := p) (P := P) (R := R) x4 ω4 μ4 (sp - 16) ret t
      ⟨by omega, by omega⟩ e1 (by
        rw [rdN_frame (fun j hj => K4.hi _ (by omega) (by omega) (by omega)),
          rdN_frame (fun j hj => fr2 _ (by omega) (by omega))]; exact sv)
      hret hjt hbt (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    have K := K1.trans' (K4.mono (sp' := sp) (by omega) (fun _ h => h))
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω5, μ4, x4, s', cap', c, hc2,
      ((((run1.trans run2).trans run3).trans run4).trans run5).mono (by omega), H4, hb4, hf4, hc1', hc2', K,
      f0, by rw [f1, show sp - 16 + 16 = sp by omega], f5.trans e5, f6.trans e6, f7.trans e7⟩
  · exact Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono (by omega))

end Services.Bootstrap.Fmt
