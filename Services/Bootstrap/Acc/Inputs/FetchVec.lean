import Services.Bootstrap.Acc.Inputs.FetchStep
import Services.Bootstrap.CodeAAll
import PVM.Logic.Go
import Services.Bootstrap.Alloc.AllocWrap

/-!
# The SDK's `fetch_vec` (47417) for the accumulate inputs, in segments

`fetch_vec(kind)` at 47417 fetches a value into a fresh zeroed `Vec<u8>` in two phases: a
`fetch` with a null buffer for the length L (47490), then the block (`alloc_impl`, 41177, under the
allocator's lock), then a second `fetch` into it (47690). Kind 14 (the inputs ℰ(↕**i**), GP v0.8.0
eq. `fetch`) is in the no-argument mask 20359, so both calls pass ω₁₁ = ω₁₂ = 0.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **47417 … 47490**, kind 14: the frame of 64 octets (ω₀, ω₅, ω₆ and `out` saved), the kind and
    its two argument words copied to sp − 40 … sp − 56, and the registers of a `fetch` with a null
    buffer: ω₇ = ω₈ = ω₉ = 0, ω₁₀ = 14, ω₁₁ = ω₁₂ = 0. -/
theorem fv_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp out args a1 a2 : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat args)
    (hsp : 65536 + 64 ≤ sp ∧ sp < 4294967296) (hargs : 65536 ≤ args ∧ args + 24 < 4294967296) (hdis : sp ≤ args)
    (hout : out < 18446744073709551616)
    (r0 : μ.readN args 8 = Num.encodeLE 8 14) (r1 : μ.readN (args + 8) 8 = Num.encodeLE 8 a1)
    (r2 : μ.readN (args + 16) 8 = Num.encodeLE 8 a2) (ha1 : a1 < 18446744073709551616)
    (ha2 : a2 < 18446744073709551616)
    (hra : ∀ a, args ≤ a → a < args + 24 → μ.readable a = true)
    (hwf : ∀ a, sp - 64 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 47417 ω μ x 47490 ω' μ' x 30 ∧
      ω'[1] = UInt64.ofNat (sp - 64) ∧ ω'[7] = UInt64.ofNat 0 ∧ ω'[8] = UInt64.ofNat 0 ∧
      ω'[9] = UInt64.ofNat 0 ∧ ω'[10] = UInt64.ofNat 14 ∧ ω'[11] = UInt64.ofNat 0 ∧
      ω'[12] = UInt64.ofNat 0 ∧
      ω'[0] = ω[0] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (sp - 8) 8 = Num.encodeLE 8 ω[0].toNat ∧ μ'.readN (sp - 16) 8 = Num.encodeLE 8 ω[5].toNat ∧
      μ'.readN (sp - 24) 8 = Num.encodeLE 8 ω[6].toNat ∧ μ'.readN (sp - 32) 8 = Num.encodeLE 8 out ∧
      μ'.readN (sp - 40) 8 = Num.encodeLE 8 14 ∧
      (∀ a, a < 4294967296 → (a < sp - 64 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 64 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, r0, r1, r2, hra, hwf, hr]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try rfl
    all_goals try simp only [show sp - 64 + 56 = sp - 8 from by omega, show sp - 64 + 48 = sp - 16 from by omega,
      show sp - 64 + 40 = sp - 24 from by omega, show sp - 64 + 32 = sp - 32 from by omega,
      show sp - 64 + 24 = sp - 40 from by omega]
    all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]
    all_goals try rfl
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **47490 … 47541**, kind 14: the first `fetch`, with a null buffer, returns the length
    L = |ℰ(↕**i**)| in ω₇ and writes nothing; L is neither an error code nor 0, so the code moves it
    to ω₅ and calls on to 47541 (return address 2120). -/
theorem fv_fetch1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : cap < 2 ^ 64) (h287 : 287 ≤ cap) (env : AccEnv) (x : AccCtx) (ω : Regs) (μ : Memory)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat 0) (h9 : ω[9] = UInt64.ofNat 0)
    (h10 : ω[10] = UInt64.ofNat 14) (hL0 : 0 < (inputsEnc env).length)
    (hL : (inputsEnc env).length < 9223372036854775808) :
    ∃ ω', FreeStepsH p (accContractK cap env) 47490 ω μ x 47541 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 2120 ∧ ω'[5] = UInt64.ofNat (inputsEnc env).length ∧
      ω'[7] = UInt64.ofNat (inputsEnc env).length ∧
      ω'[1] = ω[1] ∧ ω'[2] = ω[2] ∧ ω'[3] = ω[3] ∧ ω'[4] = ω[4] ∧ ω'[6] = ω[6] ∧ ω'[8] = ω[8] ∧
      ω'[9] = ω[9] ∧ ω'[10] = ω[10] ∧ ω'[11] = ω[11] ∧ ω'[12] = ω[12] := by
  have r7 : reg ω 7 = 0 := by unfold reg; rw [show ω.get 7 = ω[7] from rfl, h7]; rfl
  have r8 : reg ω 8 = 0 := by unfold reg; rw [show ω.get 8 = ω[8] from rfl, h8]; rfl
  have r9 : reg ω 9 = 0 := by unfold reg; rw [show ω.get 9 = ω[9] from rfl, h9]; rfl
  have r10 : reg ω 10 = 14 := by unfold reg; rw [show ω.get 10 = ω[10] from rfl, h10]; rfl
  have hst := fetch14_step cap hcap env ω μ x 0 0 0 r7 r8 r9 r10 (by unfold memGas; omega)
    (by simp [Memory.rangeWritable])
  have hm : μ.writeN 0 (((inputsEnc env).drop (min 0 (inputsEnc env).length)).take
      (min 0 ((inputsEnc env).length - min 0 (inputsEnc env).length))) = μ := by simp
  rw [hm] at hst
  generalize hLd : (inputsEnc env).length = L at hst hL0 hL ⊢
  have e7 : (setR7 ω L)[7] = UInt64.ofNat L := by
    unfold setR7; rw [Vector.getElem_set]; simp
  have eo : ∀ j : Nat, (hj : j < 13) → j ≠ 7 → (setR7 ω L)[j] = ω[j] := by
    intro j hj h; unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]
  rw [show setR7 ω L = regsNF (setR7 ω L) [] from rfl] at hst
  refine ⟨?ω', FreeStepsH.host_decode (d_47490 (p := p) (P := P)) hst ?run, ?post⟩
  case run =>
    pvm_go [e7, Nat.mod_eq_of_lt (show L < 18446744073709551616 by omega)]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, e7]
    all_goals try rfl
    all_goals first
      | exact eo _ (by decide) (by decide)
      | simp only [UInt64.ofNat_toNat]

/-- **47541 … 41177**, L > 0: L ≤ 2³⁷ − 32, the allocator's lock taken (the word at 206848, the
    scratch at 196608 … 196616 used), and the call of `alloc_impl` for ⌈L/32⌉ units of alignment 1
    with the zero flag set: ω₇ = 196792, ω₈ = 1, ω₉ = ⌈L/32⌉, ω₁₀ = 1, return address 2122. -/
theorem fv_lock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (L : Nat) (h5 : ω[5] = UInt64.ofNat L) (hL : L + 31 < 68719476736)
    (hl : rdN μ 206848 1 = 0) {HT S0 S1 : Nat} (hH : 206864 ≤ HT) (hwr : WrAt μ HT S0 S1) :
    ∃ ω' μ', FreeStepsH p R 47541 ω μ x 41177 ω' μ' x 30 ∧
      ω'[7] = UInt64.ofNat 196792 ∧ ω'[8] = UInt64.ofNat 1 ∧
      ω'[9] = UInt64.ofNat ((L + 31) / 32) ∧ ω'[10] = UInt64.ofNat 1 ∧ ω'[0] = UInt64.ofNat 2122 ∧
      ω'[6] = UInt64.ofNat 196792 ∧ ω'[5] = ω[5] ∧ ω'[1] = ω[1] ∧ ω'[4] = ω[4] ∧
      (∀ a, a < 4294967296 → (a < 196608 ∨ 196616 ≤ a) → (a < 206848 ∨ 206852 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.writable a = μ.writable a) ∧
      ∀ j : Fin 13, j.val ∉ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11] → ω'[j] = ω[j] := by
  have hr := hwr.rd
  have hand := lock_test (w := rdN μ 206848 4) (by rw [rdN4_mod]; exact hl)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h5, hand, show 137438953440 ≥ L by omega, hwr, hr, rdN_writeN_disjoint, ↓rdN_fold,
    ↓loadI_fold]
  case post =>
    refine ⟨by reg_val, by reg_val, ?_, by reg_val, by reg_val, by reg_val, by reg_val, by reg_val, ?_,
      fun a ha h1 h2 => ?_, fun a => ?_, by reg_frame⟩
    · reg_val
    · simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some',
        List.lookup_nil, Option.getD_none]
      rd_simp []
      simp
    · rd_simp []
    · rd_simp [hwr]

/-- **47631 … 47690**, kind 14: the lock byte cleared, the block `ptr` ≠ 0 saved at sp, and the
    registers of the second `fetch`: ω₇ = ptr, ω₈ = 0, ω₉ = L, ω₁₀ = 14, ω₁₁ = ω₁₂ = 0. -/
theorem fv_unlock {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr L : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat L)
    (h6 : ω[6] = UInt64.ofNat 196792) (h7 : ω[7] = UInt64.ofNat ptr) (hp0 : ptr ≠ 0)
    (hsp : 65536 ≤ sp ∧ sp + 64 < 4294967296) (hptr : ptr < 4294967296) (hL : L < 4294967296)
    (m24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 14)
    (hwf : ∀ a, sp ≤ a → a < sp + 64 → μ.writable a = true) (hwl : μ.writable 206848 = true)
    (dl : 206848 < sp) :
    ∃ ω' μ', FreeStepsH p R 47631 ω μ x 47690 ω' μ' x 20 ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat L ∧ ω'[7] = UInt64.ofNat ptr ∧
      ω'[8] = UInt64.ofNat 0 ∧ ω'[9] = UInt64.ofNat L ∧ ω'[10] = UInt64.ofNat 14 ∧
      ω'[11] = UInt64.ofNat 0 ∧ ω'[12] = UInt64.ofNat 0 ∧ ω'[6] = UInt64.ofNat 18446744073709551607 ∧
      μ'.readN sp 8 = Num.encodeLE 8 ptr ∧ μ'.read 206848 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → (a < sp ∨ sp + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  have hrl : μ.readable 206848 = true := Memory.readable_of_writable hwl
  have hp0' : ptr % 18446744073709551616 ≠ 0 := by rw [Nat.mod_eq_of_lt (by omega)]; exact hp0
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, m24, hwf, hr, hwl, hrl, hp0']
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h7]
    all_goals try rfl
    all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]
    all_goals try rfl
    all_goals try (intro a ha1 ha2 ha3; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint,
      PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_ne'])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])
    all_goals try (simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, PVM.Memory.writeN_cons,
      PVM.Memory.writeN_nil, PVM.read_write_eq']; rfl)

/-- **47692 … 47722**: the second `fetch` returned L (not an error code); `Some(Vec { cap: L,
    ptr, len: L })` is stored at `out` (read from sp + 32, `ptr` from sp), ω₀, ω₅, ω₆ are restored
    from the frame and the frame popped, at the return's `jumpInd`. -/
theorem fv_store {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp ptr out L r0 r5 r6 : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat L) (h6 : ω[6] = UInt64.ofNat 18446744073709551607)
    (h7 : ω[7] = UInt64.ofNat L) (hL : L < 4294967296)
    (hsp : 65536 ≤ sp ∧ sp + 64 < 4294967296) (hout : 65536 ≤ out ∧ out + 24 < 4294967296)
    (hptr : ptr < 18446744073709551616)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (m0 : μ.readN sp 8 = Num.encodeLE 8 ptr) (m32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 out)
    (m40 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r6) (m48 : μ.readN (sp + 48) 8 = Num.encodeLE 8 r5)
    (m56 : μ.readN (sp + 56) 8 = Num.encodeLE 8 r0)
    (hrf : ∀ a, sp ≤ a → a < sp + 64 → μ.readable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true)
    (dos : out + 24 ≤ sp ∨ sp + 64 ≤ out) :
    ∃ ω' μ', FreeStepsH p R 47692 ω μ x 47722 ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 64) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN out 8 = Num.encodeLE 8 L ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hro : ∀ a, out ≤ a → a < out + 24 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwo a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h5, h6, h7, m0, m32, m40, m48, m56, hrf, hwo, hro,
    Nat.mod_eq_of_lt (show L < 18446744073709551616 by omega)]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h5, h7]
    all_goals try rfl
    all_goals try simp only [show out + 0 = out from rfl]
    all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_disjoint, PVM.Memory.readN_writeN_same]
    all_goals try rfl
    all_goals try (intro a ha1 ha2; simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint])
    all_goals try (intro a; simp only [Memory.readable_writeN, Memory.writable_writeN])

/-- **47631 … 47722**, kind 14, after `alloc_impl` returned a block `ptr` ≠ 0 for L octets: the
    allocator's lock byte (206848) cleared, `ptr` saved at sp, the second `fetch` (47690) writes
    ℰ(↕**i**) at `ptr` and returns L, and `Some(Vec { cap: L, ptr, len: L })` is stored at `out`;
    ω₀, ω₅, ω₆ are restored and the frame popped, at the return's `jumpInd`. -/
theorem fv_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (cap : Nat)
    (hcap : cap < 2 ^ 64) (env : AccEnv) (x : AccCtx) (ω : Regs) (μ : Memory)
    (sp ptr out r0 r5 r6 : Nat)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat (inputsEnc env).length)
    (h6 : ω[6] = UInt64.ofNat 196792) (h7 : ω[7] = UInt64.ofNat ptr)
    (hL0 : 0 < (inputsEnc env).length) (hcost : 287 + memGas 400 (inputsEnc env).length ≤ cap)
    (hsp : 65536 ≤ sp ∧ sp + 64 < 4294967296) (hout : 65536 ≤ out ∧ out + 24 < 4294967296)
    (hptr : 65536 ≤ ptr ∧ ptr + (inputsEnc env).length < 4294967296)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (m24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 14) (m32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 out)
    (m40 : μ.readN (sp + 40) 8 = Num.encodeLE 8 r6) (m48 : μ.readN (sp + 48) 8 = Num.encodeLE 8 r5)
    (m56 : μ.readN (sp + 56) 8 = Num.encodeLE 8 r0)
    (hwf : ∀ a, sp ≤ a → a < sp + 64 → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true)
    (hwp : ∀ a, ptr ≤ a → a < ptr + (inputsEnc env).length → μ.writable a = true)
    (hwl : μ.writable 206848 = true)
    (dpo : ptr + (inputsEnc env).length ≤ out ∨ out + 24 ≤ ptr)
    (dps : ptr + (inputsEnc env).length ≤ sp ∨ sp + 64 ≤ ptr)
    (dos : out + 24 ≤ sp ∨ sp + 64 ≤ out)
    (dl : 206848 < ptr ∧ 206848 < sp ∧ 206848 < out) :
    ∃ ω' μ', FreeStepsH p (accContractK cap env) 47631 ω μ x 47722 ω' μ' x 41 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 64) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN out 8 = Num.encodeLE 8 (inputsEnc env).length ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 (inputsEnc env).length ∧
      μ'.readN ptr (inputsEnc env).length = inputsEnc env ∧ μ'.read 206848 = 0 ∧
      (∀ a, a < 4294967296 → a ≠ 206848 → (a < sp ∨ sp + 8 ≤ a) → (a < out ∨ out + 24 ≤ a) →
        (a < ptr ∨ ptr + (inputsEnc env).length ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hL32 : (inputsEnc env).length < 4294967296 := by omega
  obtain ⟨ω1, μ1, run1, a1, a5, a7, a8, a9, a10, a11, a12, a6, k0, kl, kfr, krd, kwr⟩ :=
    fv_unlock (p := p) (P := P) (R := accContractK cap env) x ω μ sp ptr (inputsEnc env).length h1 h5 h6 h7
      (by omega) ⟨hsp.1, by omega⟩ (by omega) hL32 m24 hwf hwl dl.2.1
  have r7 : reg ω1 7 = ptr := by
    unfold reg; rw [show ω1.get 7 = ω1[7] from rfl, a7, UInt64.toNat_ofNat_of_lt' (show ptr < 2 ^ 64 by omega)]
  have r8 : reg ω1 8 = 0 := by unfold reg; rw [show ω1.get 8 = ω1[8] from rfl, a8]; rfl
  have r9 : reg ω1 9 = (inputsEnc env).length := by
    unfold reg
    rw [show ω1.get 9 = ω1[9] from rfl, a9, UInt64.toNat_ofNat_of_lt' (show (inputsEnc env).length < 2 ^ 64 by omega)]
  have r10 : reg ω1 10 = 14 := by unfold reg; rw [show ω1.get 10 = ω1[10] from rfl, a10]; rfl
  have hst := fetch14_step cap hcap env ω1 μ1 x ptr 0 (inputsEnc env).length r7 r8 r9 r10 hcost
    (by
      simp only [Nat.zero_min, Nat.sub_zero, Nat.min_self]
      exact rangeWritable_of (by omega) fun a h1 h2 => by rw [kwr]; exact hwp a h1 h2)
  simp only [Nat.zero_min, Nat.sub_zero, Nat.min_self, List.drop_zero, List.take_length] at hst
  generalize hμ2 : μ1.writeN ptr (inputsEnc env) = μ2 at hst
  have s7 : (setR7 ω1 (inputsEnc env).length)[7] = UInt64.ofNat (inputsEnc env).length := by
    unfold setR7; rw [Vector.getElem_set]; simp
  have so : ∀ j : Nat, (hj : j < 13) → j ≠ 7 → (setR7 ω1 (inputsEnc env).length)[j] = ω1[j] := by
    intro j hj h; unfold setR7; rw [Vector.getElem_set]; simp [Ne.symm h]
  -- the block written, everything else of μ1 kept
  have k2 : ∀ a, a < 4294967296 → (a < ptr ∨ ptr + (inputsEnc env).length ≤ a) → μ2.read a = μ1.read a := by
    intro a h1 h2; rw [← hμ2]
    exact PVM.Memory.read_writeN_disjoint _ _ _ _ (by omega) (by unfold PVM.two32; omega) (by unfold PVM.two32; omega)
  have e2 : μ2.readN ptr (inputsEnc env).length = inputsEnc env := by
    rw [← hμ2]; exact PVM.Memory.readN_writeN_same _ _ _ _ rfl (by unfold PVM.two32; omega)
  have rd2 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [← hμ2, Memory.readable_writeN, krd]
  have wr2 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [← hμ2, Memory.writable_writeN, kwr]
  have rdN2 : ∀ q n, q + n ≤ 4294967296 → (q + n ≤ ptr ∨ ptr + (inputsEnc env).length ≤ q) →
      (q + n ≤ 206848 ∨ 206848 < q) → (q + n ≤ sp ∨ sp + 8 ≤ q) → μ2.readN q n = μ.readN q n := by
    intro q n h0 h1 h2 h3
    apply PVM.Memory.readN_congr
    intro j hj
    rw [k2 _ (by omega) (by omega), kfr _ (by omega) (by omega) (by omega)]
  obtain ⟨ω3, μ3, run3, b0, b1, b5, b6, c0, c8, c16, cfr, crd, cwr⟩ :=
    fv_store (p := p) (P := P) (R := accContractK cap env) x (setR7 ω1 (inputsEnc env).length) μ2 sp ptr out
      (inputsEnc env).length r0 r5 r6 (by rw [so 1 (by decide) (by decide), a1])
      (by rw [so 5 (by decide) (by decide), a5]) (by rw [so 6 (by decide) (by decide), a6]) s7 hL32
      ⟨hsp.1, by omega⟩ hout (by omega) hr0 hr5 hr6
      (by rw [← hμ2, PVM.Memory.readN_writeN_disjoint _ _ _ _ _ (by omega) (by unfold PVM.two32; omega)
        (by unfold PVM.two32; omega)]; exact k0)
      (by rw [rdN2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact m32)
      (by rw [rdN2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact m40)
      (by rw [rdN2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact m48)
      (by rw [rdN2 _ _ (by omega) (by omega) (by omega) (by omega)]; exact m56)
      (fun a h1 h2 => by rw [rd2]; exact Memory.readable_of_writable (hwf a h1 h2))
      (fun a h1 h2 => by rw [wr2]; exact hwo a h1 h2) dos
  refine ⟨ω3, μ3, (run1.trans (FreeStepsH.host_decode (d_47690 (p := p) (P := P)) hst run3)).mono (by omega),
    b0, b1, b5, b6, c0, c8, c16, ?_, ?_, ?_, fun a => (crd a).trans (rd2 a), fun a => (cwr a).trans (wr2 a)⟩
  · rw [PVM.Memory.readN_congr (μ' := μ3) (μ := μ2) (a := ptr) (n := (inputsEnc env).length)
      (fun j hj => cfr (ptr + j) (by omega) (by omega))]; exact e2
  · rw [cfr _ (by omega) (by omega), k2 _ (by omega) (by omega)]; exact kl
  · intro a h0 hl hs ho hp
    rw [cfr a h0 ho, k2 a h0 hp, kfr a h0 hl hs]

end Services.Bootstrap.Acc
