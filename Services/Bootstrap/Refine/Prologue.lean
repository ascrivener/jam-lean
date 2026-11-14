import Services.Bootstrap.Refine.ExitRun

/-!
# Refine's prologue after the arguments' decode (4680 … 4792)

After the SDK's argument fetch (44241) and the decode of the arguments (c, i, s, the payload y and the hash) into
refine's frame at M + 168 (return 1484 → 4680), refine keeps the payload's `Vec<u8>` (capacity at M + 88, buffer
at M + 112) and the item index (M + 80), and logs a line formatting the service id (`format!` 59375, template
66657, the id at M + 244 with its `Display` 2616; then `log` and the `String`'s free), reaching
`Instructions::decode` at 4792 with |y| in ω₆. `pro1` is 4680 … 59375; the line, 59375 … 4792, is the
hypothesis `ArgsLineOk`, to be discharged by the fmt summaries. GP v0.8.0 Appendix B.4 (Ψ_R running bootstrap's
code), B.7 (log, which leaves the host context).
-/

namespace Services.Bootstrap.Refine.Prologue

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.PassLoop
  Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem sext_small {w : Nat} (h : w < 2147483648) :
    ((if w < 2147483648 then (w : Int) else (w : Int) - 4294967296) % 18446744073709551616).toNat = w := by
  rw [if_pos h]; omega

theorem sext_low {w : Nat} (h : w < 4294967296) :
    ((if w < 2147483648 then (w : Int) else (w : Int) - 4294967296) % 18446744073709551616).toNat % 4294967296
      = w := by
  split <;> omega

/-- **The service id's log line** (59375 … 4792, a hypothesis): `format!` of the line with template 66657 and the
    argument at M + 272 (the u32 at M + 244, `Display` 2616) into the `String` at M + 168, the `log` (4770) and the
    `String`'s free (40613 → 4792), from refine's frame at M with the allocator's context: the run reaches 4792
    with the host context, ω₁ and ω₆ kept, the allocator's context for some heap s', every allocated chunk of s
    still allocated with its data, the globals (`Glob`) and the heap's base kept, and the stack from M up kept apart from the `String` at M + 168 … M + 192; or
    an allocation fails. To be discharged by the fmt summaries (`Services/Bootstrap/Fmt`). -/
def ArgsLineOk (p : ByteArray) (cap0 : Nat) (env : RefineHost.Env) (pb S0 S1 : Nat) : Prop :=
  ∀ (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State) (M sv : Nat),
    HeapCtx env pb S0 S1 μ s → S0 + 7560 ≤ M → M + 632 ≤ S1 → M % 8 = 0 → sv < 4294967296 →
    ω[0] = UInt64.ofNat 154 → ω[1] = UInt64.ofNat M → ω[7] = UInt64.ofNat (M + 168) →
    ω[8] = UInt64.ofNat 66657 → ω[9] = UInt64.ofNat (M + 272) →
    μ.readN (M + 272) 8 = Num.encodeLE 8 (M + 244) → μ.readN (M + 280) 8 = Num.encodeLE 8 2616 →
    μ.readN (M + 244) 4 = Num.encodeLE 4 sv →
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 59375 ω μ x 4792 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = ω[1] ∧ ω'[6] = ω[6] ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 168 ∨ M + 192 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ s'.base = s.base) ∨
    ∃ N, ExhaustsX env cap0 pb p 59375 ω μ x N

/-- 4680 … 4742 → 59375: from the arguments decoded at M + 168 (the payload's `Vec<u8>` {cap, q, Ly} at M + 168,
    M + 176, M + 184; the item index w < 2^31 and the service id sv < 2^32 as 32-bit words at M + 224, M + 228):
    the payload's capacity and buffer to M + 88, M + 112, w to M + 80, ω₆ = Ly, the id to M + 244, the format
    argument {M + 244, 2616} at M + 272, and the call of `format!` (59375; return address 154 → 4749) with
    ω₇ = M + 168, ω₈ = 66657, ω₉ = M + 272. Memory changes only at M + 80 … M + 96, M + 112 … M + 120,
    M + 244 … M + 248 and M + 272 … M + 288. -/
theorem pro1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (M cap q Ly w sv : Nat)
    (hM : 65536 ≤ M ∧ M + 632 ≤ 4294967296 ∧ M % 8 = 0) (hcap : cap < 18446744073709551616)
    (hq : q < 18446744073709551616) (hLy : Ly < 18446744073709551616) (hw : w < 2147483648)
    (hsv : sv < 4294967296)
    (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 cap) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 q)
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 Ly) (s224 : μ.readN (M + 224) 4 = Num.encodeLE 4 w)
    (s228 : μ.readN (M + 228) 4 = Num.encodeLE 4 sv)
    (hwr : ∀ a, M ≤ a → a < M + 632 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 4680 ω μ x 59375 ω' μ' x 20 ∧ ω'[0] = UInt64.ofNat 154 ∧ ω'[1] = UInt64.ofNat M ∧
      ω'[5] = ω[5] ∧ ω'[6] = UInt64.ofNat Ly ∧ ω'[7] = UInt64.ofNat (M + 168) ∧ ω'[8] = UInt64.ofNat 66657 ∧
      ω'[9] = UInt64.ofNat (M + 272) ∧
      μ'.readN (M + 80) 8 = Num.encodeLE 8 w ∧ μ'.readN (M + 88) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (M + 112) 8 = Num.encodeLE 8 q ∧ μ'.readN (M + 244) 4 = Num.encodeLE 4 sv ∧
      μ'.readN (M + 272) 8 = Num.encodeLE 8 (M + 244) ∧ μ'.readN (M + 280) 8 = Num.encodeLE 8 2616 ∧
      (∀ a, a < 4294967296 → (a < M + 80 ∨ (M + 96 ≤ a ∧ a < M + 112) ∨ (M + 120 ≤ a ∧ a < M + 244) ∨
        (M + 248 ≤ a ∧ a < M + 272) ∨ M + 288 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have rc := rd8 hcap s168
  have rq := rd8 hq s176
  have rl := rd8 hLy s184
  have hr : ∀ a, M ≤ a → a < M + 632 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hwr a h1 h2)
  have rw4 : rdN μ (M + 224) 4 = w := by
    unfold rdN; rw [s224, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by omega)]
  have rs4 : rdN μ (M + 228) 4 = sv := by
    unfold rdN; rw [s228, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hsv]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, hM0, hM1, hM8, hr, hwr, rc, rq, rl, rw4, rs4, sext_small hw, sext_low hsv, rdN_writeN_disjoint,
      ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hLy, rw4, rs4,
      sext_small hw, sext_low hsv]
    all_goals try (congr 1; omega)
    post_simp

/-- **4680 … 4792**: `pro1` and the log line (`ArgsLineOk`): from the decoded arguments at M + 168 with the
    allocator's context, `Instructions::decode` is reached with ω₁ = M, ω₆ = Ly, the payload's `Vec<u8>` kept at
    M + 88 / M + 112, the item index at M + 80, the allocator's context for some heap s' keeping every allocated
    chunk with its data, the globals, and the stack from M up apart from M + 80 … M + 96, M + 112 … M + 120,
    M + 168 … M + 192, M + 244 … M + 248 and M + 272 … M + 288; or an allocation fails. -/
theorem tail4680 {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap0 : Nat) {pb : Nat}
    (line : ArgsLineOk p cap0 env pb S0 S1) (x : RefineCtx) (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (M cap q Ly w sv : Nat)
    (hM : S0 + 7560 ≤ M ∧ M + 632 ≤ S1 ∧ M % 8 = 0) (hcap : cap < 18446744073709551616)
    (hq : q < 18446744073709551616) (hLy : Ly < 18446744073709551616) (hw : w < 2147483648)
    (hsv : sv < 4294967296) (h1 : ω[1] = UInt64.ofNat M)
    (s168 : μ.readN (M + 168) 8 = Num.encodeLE 8 cap) (s176 : μ.readN (M + 176) 8 = Num.encodeLE 8 q)
    (s184 : μ.readN (M + 184) 8 = Num.encodeLE 8 Ly) (s224 : μ.readN (M + 224) 4 = Num.encodeLE 4 w)
    (s228 : μ.readN (M + 228) 4 = Num.encodeLE 4 sv) :
    (∃ (ω' : Regs) (μ' : Memory) (s' : State) (N : Nat),
      FreeStepsH p (refineContractK cap0 env) 4680 ω μ x 4792 ω' μ' x N ∧ HeapCtx env pb S0 S1 μ' s' ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[6] = UInt64.ofNat Ly ∧
      μ'.readN (M + 80) 8 = Num.encodeLE 8 w ∧ μ'.readN (M + 88) 8 = Num.encodeLE 8 cap ∧
      μ'.readN (M + 112) 8 = Num.encodeLE 8 q ∧
      (∀ a, a < 4294967296 → M ≤ a → (a < M + 80 ∨ (M + 96 ≤ a ∧ a < M + 112) ∨ (M + 120 ≤ a ∧ a < M + 168) ∨
        (M + 192 ≤ a ∧ a < M + 244) ∨ (M + 248 ≤ a ∧ a < M + 272) ∨ M + 288 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) ∧ s'.base = s.base) ∨
    ∃ N, ExhaustsX env cap0 pb p 4680 ω μ x N := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  have hS0d : S0 = 4278050816 := rfl
  have hS1d : S1 = 4278059008 := rfl
  obtain ⟨ω1, μ1, run1, a0, a1, -, a6, a7, a8, a9, m80, m88, m112, m244, m272, m280, fr1, rd1, wr1⟩ :=
    pro1 (p := p) (P := P) (R := refineContractK cap0 env) x ω μ M cap q Ly w sv ⟨by omega, by omega, hM8⟩ hcap hq
      hLy hw hsv h1 s168 s176 s184 s224 s228 (fun a h1 h2 => H.st a (by omega) (by omega))
  have lo : ∀ a, a < M → μ1.read a = μ.read a := fun a h => fr1 a (by omega) (Or.inl (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := Decode.GrowOne.ctx_high H (fun a h => lo a (by omega)) wr1
  rcases line x ω1 μ1 s M sv H1 (by omega) (by omega) hM8 hsv a0 a1 a7 a8 a9 m272 m280 m244 with
    ⟨ω2, μ2, s2, N2, run2, H2, e1, e6, fr2, keep2, gl2, base2⟩ | ⟨N, hx⟩
  · have k21 : ∀ a l, M ≤ a → a + l ≤ 4294967296 → (a + l ≤ M + 168 ∨ M + 192 ≤ a) → μ2.readN a l = μ1.readN a l :=
      fun a l h0 h1 h2 => Memory.readN_congr (fun j hj => fr2 _ (by omega) (by omega) (by omega))
    refine Or.inl ⟨ω2, μ2, s2, _, run1.trans run2, H2, by rw [e1, a1], by rw [e6, a6],
      by rw [k21 _ _ (by omega) (by omega) (by omega)]; exact m80,
      by rw [k21 _ _ (by omega) (by omega) (by omega)]; exact m88,
      by rw [k21 _ _ (by omega) (by omega) (by omega)]; exact m112,
      fun a h0 h1 h2 => (fr2 a h0 h1 (by omega)).trans (fr1 a h0 (by omega)), fun d hd hu => ?_,
      fun a ha => ?_, base2⟩
    · obtain ⟨hd2, hdd⟩ := keep2 d hd hu
      have := (Decode.VecU8.chunk_in H.wf hd hu).2.2
      have hbT := H.hbT
      exact ⟨hd2, fun a ha => (hdd a ha).trans (lo a (by unfold InData at ha; omega))⟩
    · have hg := ha; unfold Glob at hg
      exact (gl2 a ha).trans (lo a (by omega))
  · exact Or.inr ⟨_, ExhaustsX.pre run1 hx⟩

end Services.Bootstrap.Refine.Prologue
