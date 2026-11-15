import Services.Bootstrap.Acc.Inputs.InputsPre
import Services.Bootstrap.Acc.Inputs.GlueFree
import Services.Bootstrap.Acc.HeapHost
import Services.Bootstrap.Decode.AllocZeroedCall
import Services.Bootstrap.Acc.Inputs.ReadVecCall
import Services.Bootstrap.Acc.Inputs.OperandCall
import Services.Bootstrap.Decode.LoopAPass

/-!
# `fetch_vec(14)`, 47417 → 47722

The SDK's `fetch_vec` of kind 14 (GP v0.8.0 Appendix B, `fetch`: ℰ(↕**i**), the accumulation inputs) in
its two phases: the length L by a `fetch` with a null buffer, a zeroed block of ⌈L/32⌉ units from the
allocator under its lock (`alloc_implZ_callG`, the lock held throughout: `HeapCtxL`), then a second
`fetch` into the block and `Some(Vec { L, ptr, L })` at out. A failed allocation traps
(`handle_alloc_error`, 47554).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall Services.Bootstrap.Decode.AllocZeroedCall

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **`fetch_vec(14)`, 47417 → 47722** (L = |ℰ(↕**i**)| > 0): from the allocator's context, with the
    arguments (14 and two words) at args and out on the stack above sp. Either a block `ptr` (the data of
    a fresh chunk of ⌈L/32⌉ + 1 units) holds ℰ(↕**i**), `Some(Vec { L, ptr, L })` is at out, the context
    holds for the new state keeping every allocated chunk and its data, the stack from sp is kept off
    out, and ω₀, ω₅, ω₆ are as at the call (at the return's `jumpInd`); or the allocation failed and the
    run reaches the trap at 47554. -/
theorem fv_call (aenv : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (hcost : 287 + memGas 400 (inputsEnc aenv).length ≤ cap)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (x : AccCtx) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out args a1 a2 S0 S1 : Nat)
    (H : HeapCtxC aenv.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat args)
    (hL0 : 0 < (inputsEnc aenv).length) (hL : (inputsEnc aenv).length + 31 < 68719476736)
    (hsp : 2147483800 + 64 ≤ sp) (hSTk : S0 + 64 + 152 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hargs : sp ≤ args ∧ args + 24 ≤ S1)
    (dao : args + 24 ≤ out ∨ out + 24 ≤ args)
    (r0 : μ.readN args 8 = Num.encodeLE 8 14) (r1 : μ.readN (args + 8) 8 = Num.encodeLE 8 a1)
    (r2 : μ.readN (args + 16) 8 = Num.encodeLE 8 a2) (ha1 : a1 < 18446744073709551616)
    (ha2 : a2 < 18446744073709551616) :
    (∃ ptr s' ω' μ', FreeStepsH p (accContractK cap aenv) 47417 ω μ x 47722 ω' μ' x
        (96 * (((inputsEnc aenv).length + 31) / 32) + 700) ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      rdN μ' out 8 = (inputsEnc aenv).length ∧ rdN μ' (out + 8) 8 = ptr ∧
      rdN μ' (out + 16) 8 = (inputsEnc aenv).length ∧
      HeapCtxC aenv.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (⟨ptr - 32, ((inputsEnc aenv).length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, ((inputsEnc aenv).length + 31) / 32 + 1, true⟩) ∧
      μ'.readN ptr (inputsEnc aenv).length = inputsEnc aenv ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (accContractK cap aenv) 47417 ω μ x 47554 ω' μ' x
        (96 * (((inputsEnc aenv).length + 31) / 32) + 700)) := by
  have hS1 := H.hS1
  have hst := H.st
  have hc64 : cap < 2 ^ 64 := by rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl]; exact hcap
  generalize hLd : (inputsEnc aenv).length = L at hL0 hL hcost ⊢
  have req1 : 1 ≤ (L + 31) / 32 := by omega
  have reqL : L ≤ 32 * ((L + 31) / 32) := by omega
  -- 47417 → 47490
  obtain ⟨ω1, μ1, run1, b1, b7, b8, b9, b10, -, -, b0, -, -, -, b5, b6, m8, m16, m24, m32, m40, fr1, rd1, wr1⟩ :=
    fv_pre (p := p) (P := P) (R := accContractK cap aenv) x ω μ sp out args a1 a2 h1 h7 h8 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ hargs.1 (by omega) r0 r1 r2 ha1 ha2
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (Or.inl (by omega))
  have H1 : HeapCtxC aenv.code pb S0 S1 μ1 s := HeapCtxC.keep_hi H lo1 wr1
  -- 47490 → 47541, the length
  obtain ⟨ω2, run2, c0, c5, -, c1, -, -, -, c6, -, -, -, -, -⟩ :=
    fv_fetch1 (p := p) (P := P) cap hc64 (by omega) aenv x ω1 μ1 b7 b8 b9 b10 (by omega) (by omega)
  rw [hLd] at c5
  -- 47541 → 41177, the lock taken
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H1.pages
  obtain ⟨ω3, μ3, run3, d7, d8, d9, d10, d0, d6, d5, d1, -, fr3, wr3, -⟩ :=
    fv_lock (p := p) (P := P) (R := accContractK cap aenv) x ω2 μ1 L c5 hL H1.lock (HT := 4096 * ph) (by omega)
      (HeapPages.wrAt hp hhb H1.st)
  have HL : HeapCtxL aenv.code pb S0 S1 μ3 s := ⟨μ1, H1, fr3, wr3⟩
  have e1 : ω3[1] = UInt64.ofNat (sp - 64) := by rw [d1, c1, b1]
  -- 41177 → 47631, the zeroed block
  rcases alloc_implZ_callG (p := p) (P := P) (hb := hb) (accHeapHost aenv) cap hcap1 hcap x ω3 μ3 s (sp - 64)
      ((L + 31) / 32) 1 2122 47631 pb S0 S1 HL e1 d7 d8 d9 d10 (by decide) d0 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1060]) bs_47631 req1 (by omega) (by omega)
      ⟨by omega, by omega⟩ with
    ⟨ptr, s', ω4, μ4, -, run4, HL4, keep4, hnew, hfresh, -, keepd4, e7, stk4, -, f1, f5, f6⟩ |
    ⟨-, ω4, μ4, run4, e7, stk4, wst, wl, -, f1, f5, f6⟩
  · have HL4' := HL4
    obtain ⟨μ₀, H₀, hag, hwa⟩ := HL4'
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H₀.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0' := H₀.hb0
    have hbT' := H₀.hbT
    have hst4 : ∀ a, S0 ≤ a → a < S1 → μ4.writable a = true := fun a h1 h2 => by rw [hwa]; exact H₀.st a h1 h2
    obtain ⟨ph', h48', hhb', hp', hHTs', hHT'⟩ := H₀.pages
    have hwl : μ4.writable 206848 = true := by
      rw [hwa]; exact HeapPages.wrAt hp' hhb' H₀.st 206848 (Or.inl ⟨by omega, by omega⟩)
    have hwp : ∀ a, ptr ≤ a → a < ptr + L → μ4.writable a = true := fun a h1 h2 => by
      rw [hwa]; exact heapC_writable_data H₀ hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩
    -- the frame words, from fv_pre to 47631
    have kf : ∀ o, sp - 64 ≤ o → o + 8 ≤ sp → μ4.readN o 8 = μ1.readN o 8 := fun o h1 h2 =>
      PVM.Memory.readN_congr fun j hj => by
        rw [stk4 _ (by omega) (by omega), fr3 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    have h6' : ω4[6] = UInt64.ofNat 196792 := by rw [f6, d6]
    have h5' : ω4[5] = UInt64.ofNat L := by rw [f5, d5, c5]
    have h1' : ω4[1] = UInt64.ofNat (sp - 64) := by rw [f1, e1]
    obtain ⟨ω5, μ5, run5, g0, g1, g5, g6, o0, o8, o16, dat, lk, fr5, rd5, wr5⟩ :=
      fv_post (p := p) (P := P) cap hc64 aenv x ω4 μ4 (sp - 64) ptr out ω[0].toNat ω[5].toNat ω[6].toNat h1'
        (by rw [hLd]; exact h5') h6' e7 (by omega) (by rw [hLd]; exact hcost) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        ⟨by omega, by rw [hLd]; omega⟩ (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        (by rw [kf _ (by omega) (by omega)]; rw [show sp - 64 + 24 = sp - 40 by omega]; exact m40)
        (by rw [kf _ (by omega) (by omega)]; rw [show sp - 64 + 32 = sp - 32 by omega]; exact m32)
        (by rw [kf _ (by omega) (by omega)]; rw [show sp - 64 + 40 = sp - 24 by omega]; exact m24)
        (by rw [kf _ (by omega) (by omega)]; rw [show sp - 64 + 48 = sp - 16 by omega]; exact m16)
        (by rw [kf _ (by omega) (by omega)]; rw [show sp - 64 + 56 = sp - 8 by omega]; exact m8)
        (fun a h1 h2 => hst4 a (by omega) (by omega)) (fun a h1 h2 => hst4 a (by omega) (by omega))
        (by rw [hLd]; exact hwp) hwl (by rw [hLd]; omega) (by rw [hLd]; omega) (by omega) ⟨by omega, by omega, by omega⟩
    rw [hLd] at dat fr5 o0 o16
    have lk' : rdN μ5 206848 1 = 0 := by simp [rdN, Memory.readN, lk]; rfl
    have k5 : ∀ a, a < 4294967296 → a ≠ 206848 → (a < sp - 64 ∨ sp - 64 + 8 ≤ a) → (a < out ∨ out + 24 ≤ a) →
        (a < ptr ∨ ptr + L ≤ a) → μ5.read a = μ4.read a := fr5
    refine Or.inl ⟨ptr, s', ω5, μ5, ((((run1.trans run2).trans run3).trans
        (FreeStepsH.ofAccGrow run4)).trans run5).mono (by omega),
      by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 64 + 64 = sp by omega],
      by rw [g5, UInt64.ofNat_toNat], by rw [g6, UInt64.ofNat_toNat],
      by unfold rdN; rw [o0, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega),
      by unfold rdN; rw [o8, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega),
      by unfold rdN; rw [o16, Num.decodeLE_encodeLE]; exact Nat.mod_eq_of_lt (by omega),
      heapL_release_data HL4 hnew lk' (fun a ha ha' hc => k5 a (by omega) ha' (Or.inl (by omega)) (Or.inl (by omega))
        (by dsimp only at hc; omega)) wr5,
      keep4, fun c hc hu a ha => ?_, hnew, hfresh, dat, fun a h0 ha ho => ?_⟩
    · have hne : (⟨ptr - 32, (L + 31) / 32 + 1, true⟩ : Chunk) ≠ c := Ne.symm (hfresh c hc hu)
      have hap := Services.Bootstrap.Decode.LoopA.InData.apart H₀.wf (keep4 c hc hu) hnew hne ha
      unfold Services.Bootstrap.Decode.LoopA.InData at hap
      dsimp only at hap
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc hu
      have := H.hb0
      have := H.hbT
      unfold InDataA at ha
      rw [k5 a (by omega) (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (by omega), keepd4 c hc hu a ha.1 ha.2,
        fr3 a (by omega) (Or.inr (by omega)) (Or.inr (by omega)), lo1 a (by omega)]
    · rw [k5 a h0 (by omega) (Or.inr (by omega)) ho (Or.inr (by omega)), stk4 a h0 (by omega),
        fr3 a h0 (Or.inr (by omega)) (Or.inr (by omega)), fr1 a h0 (Or.inr ha)]
  · obtain ⟨ω5, μ5, run5⟩ := fv_null (p := p) (P := P) (R := accContractK cap aenv) x ω4 μ4 (sp - 64)
      (by rw [f1, e1]) (by rw [f6, d6]) e7 (fun a h1 h2 => wst a (by omega) (by omega)) wl
    exact Or.inr ⟨ω5, μ5, ((((run1.trans run2).trans run3).trans (FreeStepsH.ofAccGrow run4)).trans run5).mono
      (by omega)⟩

end Services.Bootstrap.Acc
