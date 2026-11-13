import Services.Bootstrap.Acc.Wrappers.Get
import Services.Bootstrap.Acc.Wrappers.GrowS
import Services.Bootstrap.Acc.Wrappers.HeapL
import Services.Bootstrap.Acc.Inputs.FetchVecCall

/-!
# The SDK's `get` (47857) as runs of `accContractS`

From the call with the key at ω₈ (ω₉ octets) and out at ω₇: Ω_R (GP v0.8.0 Appendix B) on this
service's storage, then `Option<Vec<u8>>` at out, with the context and the answer stream kept.
- `get_none`: an absent key, `None` (the capacity word −1) at out (47927);
- `get_empty`: an empty value, `Some(Vec { 0, 1, 0 })` (47957);
- `get_some`: a value w, 0 < |w|, |w| + 31 < 2³⁶: a zeroed block of ⌈|w|/32⌉ units from the allocator
  under its lock, the second Ω_R into it, `Some(Vec { |w|, ptr, |w| })` (48102); or `alloc_impl`
  returned null (48047, ω₇ = 0) and the run reaches the allocation-failure trap 47977.

The key is read twice, so it must survive the allocation: these lemmas take it on the stack above
the frame. Values with |w| + 31 ≥ 2³⁶ (the 32-bit unit count overflows) and longer than 2³⁷ − 32
(the size check traps) are not covered yet.
-/

namespace Services.Bootstrap.Acc
open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall Services.Bootstrap.Decode.AllocZeroedCall
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem reg_of {ω : Regs} {k : Fin 13} {n : Nat} (h : ω[k] = UInt64.ofNat n) (hn : n < 2 ^ 64) : reg ω k = n := by
  unfold reg; rw [show ω.get k = ω[k] from rfl, h, UInt64.toNat_ofNat_of_lt' hn]

theorem readRegs_7 (ω : Regs) (v : Option (List UInt8)) :
    (readRegs ω v)[7] = UInt64.ofNat (match v with | none => Result.NONE | some v => v.length) := by
  cases v <;> (unfold readRegs setR7; rw [Vector.getElem_set]; simp only [↓reduceIte])

theorem readRegs_ne (ω : Regs) (v : Option (List UInt8)) (j : Nat) (hj : j < 13) (h : j ≠ 7) :
    (readRegs ω v)[j] = ω[j] := by
  unfold readRegs setR7; rw [Vector.getElem_set]; simp [Ne.symm h]

theorem readN_of_rdN {μ : Memory} {a n v : Nat} (h : rdN μ a n = v) : μ.readN a n = Num.encodeLE n v := by
  have e := encodeLE_decodeLE (μ.readN a n)
  rw [Memory.length_readN] at e
  rw [← e]; unfold rdN at h; rw [h]

/-- **The SDK's `get`, 47857 → 47927, for an absent key**: `None` at out, ω₀, ω₅, ω₆ restored and
    the frame popped, at the return's `jumpInd`; the context and the stream kept. -/
theorem get_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (sp out kO kZ : Nat) (key : List UInt8)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat kO)
    (h9 : ω[9] = UInt64.ofNat kZ) (hkZ : kZ < 2 ^ 32)
    (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 8 < 4294967296)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 8 → μ.writable a = true)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (dk : kO + kZ ≤ sp - 48 ∨ sp ≤ kO) (hkr : kO + kZ ≤ 4294967296)
    (hv : c.1.self.storage.get? key = none) :
    ∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 47857 ω μ (c, f) 47927 ω' μ' (c, f) 40 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN out 8 = Num.encodeLE 8 18446744073709551615 ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < out ∨ out + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, b1, b5, b7, b10, b11, b12, m40, m32, m24, m16, m8, fr1, rd1, wr1, bo⟩ :=
    gr_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 hsp hwf
  have hk1 : μ1.rangeReadable kO kZ = true := by
    rw [← hk]; unfold Memory.rangeReadable; simp only [rd1]
  have hkey1 : μ1.readN kO kZ = key := by
    rw [← hkey]; apply PVM.Memory.readN_congr; intro j hj
    exact fr1 _ (by omega) (by omega)
  have hst : KeepCtx (accContractS env) 4 ω1 μ1 (c, f) .cont (readRegs ω1 none) (readMem μ1 0 0 none) (c, f) := by
    have := read_stepS env ω1 μ1 (c, f) kO kZ 0 0 key (reg_of b7 (by decide))
      (reg_of ((bo 8 (by decide)).trans h8) (by omega)) (reg_of ((bo 9 (by decide)).trans h9) (by omega))
      (reg_of b10 (by decide)) (reg_of b11 (by decide)) (reg_of b12 (by decide)) hkZ (by decide) hk1 hkey1
      (by simp [Memory.rangeWritable])
    rw [hv] at this
    exact ⟨this, rfl⟩
  simp only [readMem] at hst
  have e7 : (readRegs ω1 none)[7] = UInt64.ofNat 18446744073709551615 := readRegs_7 ω1 none
  have e1 : (readRegs ω1 none)[1] = UInt64.ofNat (sp - 48) := (readRegs_ne ω1 none 1 (by decide) (by decide)).trans b1
  have hrf : ∀ a, sp - 48 ≤ a → a < sp - 48 + 48 → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega))
  have hwo1 : ∀ a, out ≤ a → a < out + 8 → μ1.writable a = true := fun a h1 h2 => by rw [wr1]; exact hwo a h1 h2
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, fr2, rd2, wr2⟩ :=
    gr_none (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) (readRegs ω1 none) μ1 (sp - 48) out
      ω[0].toNat ω[5].toNat ω[6].toNat e1 e7 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (readN_of_rdN (m16.trans (by rw [h7, UInt64.toNat_ofNat_of_lt' (show out < 2 ^ 64 by omega)]))) (readN_of_rdN m24) (readN_of_rdN m32) (readN_of_rdN m40) hrf hwo1 (by omega)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  refine ⟨ω2, μ2, ((run1.trans (FreeStepsH.host_decode (d_47886 (p := p) (P := P)) hst run2))).mono (by omega),
    by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 48 + 48 = sp by omega], by rw [g5, UInt64.ofNat_toNat],
    by rw [g6, UInt64.ofNat_toNat], o0, fun a h0 hs ho => ?_, fun a => (rd2 a).trans (rd1 a),
    fun a => (wr2 a).trans (wr1 a)⟩
  rw [fr2 a h0 ho, fr1 a h0 (by omega)]

/-- **The SDK's `get`, 47857 → 47957, for an empty value**: `Some(Vec { 0, 1, 0 })` at out, ω₀, ω₅, ω₆ restored and
    the frame popped, at the return's `jumpInd`; the context and the stream kept. -/
theorem get_empty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : AccEnv)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (sp out kO kZ : Nat) (key : List UInt8)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat kO)
    (h9 : ω[9] = UInt64.ofNat kZ) (hkZ : kZ < 2 ^ 32)
    (hsp : 65536 + 48 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 24 < 4294967296)
    (hwf : ∀ a, sp - 48 ≤ a → a < sp → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true)
    (hk : μ.rangeReadable kO kZ = true) (hkey : μ.readN kO kZ = key)
    (dk : kO + kZ ≤ sp - 48 ∨ sp ≤ kO) (hkr : kO + kZ ≤ 4294967296)
    (hv : c.1.self.storage.get? key = some []) :
    ∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 47857 ω μ (c, f) 47957 ω' μ' (c, f) 40 ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN out 8 = Num.encodeLE 8 0 ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 1 ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 0 ∧
      (∀ a, a < 4294967296 → (a < sp - 48 ∨ sp ≤ a) → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, b1, b5, b7, b10, b11, b12, m40, m32, m24, m16, m8, fr1, rd1, wr1, bo⟩ :=
    gr_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 hsp hwf
  have hk1 : μ1.rangeReadable kO kZ = true := by
    rw [← hk]; unfold Memory.rangeReadable; simp only [rd1]
  have hkey1 : μ1.readN kO kZ = key := by
    rw [← hkey]; apply PVM.Memory.readN_congr; intro j hj
    exact fr1 _ (by omega) (by omega)
  have hst : KeepCtx (accContractS env) 4 ω1 μ1 (c, f) .cont (readRegs ω1 (some [])) (readMem μ1 0 0 (some [])) (c, f) := by
    have := read_stepS env ω1 μ1 (c, f) kO kZ 0 0 key (reg_of b7 (by decide))
      (reg_of ((bo 8 (by decide)).trans h8) (by omega)) (reg_of ((bo 9 (by decide)).trans h9) (by omega))
      (reg_of b10 (by decide)) (reg_of b11 (by decide)) (reg_of b12 (by decide)) hkZ (by decide) hk1 hkey1
      (by simp [Memory.rangeWritable])
    rw [hv] at this
    exact ⟨this, rfl⟩
  simp only [readMem, List.take_nil, PVM.Memory.writeN_nil] at hst
  have e7 : (readRegs ω1 (some []))[7] = UInt64.ofNat 0 := readRegs_7 ω1 (some [])
  have e1 : (readRegs ω1 (some []))[1] = UInt64.ofNat (sp - 48) := (readRegs_ne ω1 (some []) 1 (by decide) (by decide)).trans b1
  have hrf : ∀ a, sp - 48 ≤ a → a < sp - 48 + 48 → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hwf a h1 (by omega))
  have hwo1 : ∀ a, out ≤ a → a < out + 24 → μ1.writable a = true := fun a h1 h2 => by rw [wr1]; exact hwo a h1 h2
  obtain ⟨ω2, μ2, run2, g0, g1, g5, g6, o0, o8, o16, fr2, rd2, wr2⟩ :=
    gr_empty (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) (readRegs ω1 (some [])) μ1 (sp - 48) out
      ω[0].toNat ω[5].toNat ω[6].toNat e1 e7 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (readN_of_rdN (m16.trans (by rw [h7, UInt64.toNat_ofNat_of_lt' (show out < 2 ^ 64 by omega)]))) (readN_of_rdN m24) (readN_of_rdN m32) (readN_of_rdN m40) hrf hwo1 (by omega)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
  refine ⟨ω2, μ2, ((run1.trans (FreeStepsH.host_decode (d_47886 (p := p) (P := P)) hst run2))).mono (by omega),
    by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 48 + 48 = sp by omega], by rw [g5, UInt64.ofNat_toNat],
    by rw [g6, UInt64.ofNat_toNat], o0, o8, o16, fun a h0 hs ho => ?_, fun a => (rd2 a).trans (rd1 a),
    fun a => (wr2 a).trans (wr1 a)⟩
  rw [fr2 a h0 ho, fr1 a h0 (by omega)]

/-- **The SDK's `get`, 47857 → 48102, for a value w with 0 < |w|, |w| + 31 < 2³⁶**: either a zeroed
    block `ptr` (the data of a fresh chunk of ⌈|w|/32⌉ + 1 units) holds w and `Some(Vec { |w|, ptr,
    |w| })` is at out, the allocator's context holds for the new state keeping every allocated chunk
    and its data, the stack from sp is kept off out, and ω₀, ω₅, ω₆ are as at the call (at the
    return's `jumpInd`); or `alloc_impl` returned null (48047, ω₇ = 0) and the run reaches the
    allocation-failure trap 47977. The context and the stream are kept. -/
theorem get_some (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out kO kZ S0 S1 : Nat)
    (key w : List UInt8) (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat kO)
    (h9 : ω[9] = UInt64.ofNat kZ) (hkZ : kZ < 2 ^ 32)
    (hw0 : 0 < w.length) (hwL : w.length + 31 < 68719476736)
    (hsp : 2147483800 + 48 ≤ sp) (hSTk : S0 + 48 + 152 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hkO : sp ≤ kO ∧ kO + kZ ≤ S1)
    (hkey : μ.readN kO kZ = key) (hv : c.1.self.storage.get? key = some w) :
    (∃ ptr s' ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 47857 ω μ (c, f) 48102 ω' μ' (c, f)
        (96 * ((w.length + 31) / 32) + 700) ∧
      ω'[0] = ω[0] ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN out 8 = Num.encodeLE 8 w.length ∧ μ'.readN (out + 8) 8 = Num.encodeLE 8 ptr ∧
      μ'.readN (out + 16) 8 = Num.encodeLE 8 w.length ∧ μ'.readN ptr w.length = w ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      (⟨ptr - 32, (w.length + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (w.length + 31) / 32 + 1, true⟩) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a)) ∨
    (∃ ω' μ', FreeStepsH p (KeepCtx (accContractS env)) 47857 ω μ (c, f) 48047 ω' μ' (c, f)
        (96 * ((w.length + 31) / 32) + 700) ∧ ω'[7] = UInt64.ofNat 0 ∧
      ∃ ω'' μ'', FreeStepsH p (KeepCtx (accContractS env)) 48047 ω' μ' (c, f) 47977 ω'' μ'' (c, f) 10) := by
  have hS1 := H.hS1
  have hst := H.st
  generalize hLd : w.length = L at hw0 hwL ⊢
  have req1 : 1 ≤ (L + 31) / 32 := by omega
  -- 47857 → 47886
  obtain ⟨ω1, μ1, run1, b1, b5, b7, b10, b11, b12, m40, m32, m24, m16, m8, fr1, rd1, wr1, bo1⟩ :=
    gr_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω μ sp h1 ⟨by omega, by omega⟩
      (fun a h1 h2 => hst a (by omega) (by omega))
  have lo1 : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (Or.inl (by omega))
  have H1 : HeapCtxC env.code pb S0 S1 μ1 s := HeapCtxC.keep_hi H lo1 wr1
  have hk1 : μ1.rangeReadable kO kZ = true := Services.Witness.rangeReadable_of
    (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega))) (by omega)
  have hkey1 : μ1.readN kO kZ = key := by
    rw [← hkey]; apply PVM.Memory.readN_congr; intro j hj
    exact fr1 _ (by omega) (Or.inr (by omega))
  -- the first read: the length
  have hR1 : KeepCtx (accContractS env) 4 ω1 μ1 (c, f) .cont (readRegs ω1 (some w)) μ1 (c, f) := by
    have := read_stepS env ω1 μ1 (c, f) kO kZ 0 0 key (reg_of b7 (by decide))
      (reg_of ((bo1 8 (by decide)).trans h8) (by omega)) (reg_of ((bo1 9 (by decide)).trans h9) (by omega))
      (reg_of b10 (by decide)) (reg_of b11 (by decide)) (reg_of b12 (by decide)) hkZ (by decide) hk1 hkey1
      (by simp [Memory.rangeWritable])
    rw [hv] at this
    simp only [readMem, List.take_zero, PVM.Memory.writeN_nil] at this
    exact ⟨this, rfl⟩
  have e7 : (readRegs ω1 (some w))[7] = UInt64.ofNat L := by rw [readRegs_7]; simp [hLd]
  -- 47888 → 47974 → 41177
  obtain ⟨ω2, run2, c6, c7, c0, bo2⟩ :=
    gr_mid (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) (readRegs ω1 (some w)) μ1 L e7 hw0 (by omega)
  have c1 : ω2[1] = UInt64.ofNat (sp - 48) :=
    (bo2 1 (by decide)).trans ((readRegs_ne ω1 (some w) 1 (by decide) (by decide)).trans b1)
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H1.pages
  obtain ⟨ω3, μ3, run3, d7, d8, d9, d10, d0, d6, d5, d1, -, m0, fr3, rd3, wr3, bo3⟩ :=
    gr_lock (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ1 (sp - 48) L c1 c6 c7 hwL
      ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega)) H1.lock
      (HT := 4096 * ph) (by omega) (HeapPages.wrAt hp hhb H1.st) (by omega)
  have HL : HeapCtxL env.code pb S0 S1 μ3 s :=
    HeapCtxL.of_lo H1 (fun a ha h1 h2 => fr3 a (by omega) h1 h2 (Or.inl (by omega))) wr3
  have e1 : ω3[1] = UInt64.ofNat (sp - 48) := d1.trans c1
  -- 41177 → 48047, the zeroed block
  rcases alloc_implZ_callG (p := p) (P := P) (hb := hb) (accHeapHost env) cap hcap1 hcap c ω3 μ3 s (sp - 48)
      ((L + 31) / 32) 1 2132 48047 pb S0 S1 HL e1 d7 d8 d9 d10 (by decide) d0 ⟨by decide, by decide, by decide⟩
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1065]) bs_48047 req1 (by omega) (by omega)
      ⟨by omega, by omega⟩ with
    ⟨ptr, s', ω4, μ4, -, run4, HL4, keep4, hnew, hfresh, -, keepd4, e7', stk4, -, f1, f5, f6⟩ |
    ⟨-, ω4, μ4, run4, e7', stk4, wst, wl, -, f1, f5, f6⟩
  · obtain ⟨-, run4S⟩ := FreeStepsH.growS f run4
    have HL4' := HL4
    obtain ⟨μ₀, H₀, hag, hwa⟩ := HL4'
    obtain ⟨Nb1, Nb2, Nb3⟩ := Services.Bootstrap.Decode.VecU8.chunk_in H₀.wf hnew rfl
    dsimp only at Nb1 Nb2 Nb3
    have hb0' := H₀.hb0
    have hbT' := H₀.hbT
    obtain ⟨ph', h48', hhb', hp', hHTs', hHT'⟩ := H₀.pages
    have hwl : μ4.writable 206848 = true := by
      rw [hwa]; exact HeapPages.wrAt hp' hhb' H₀.st 206848 (Or.inl ⟨by omega, by omega⟩)
    have hwp : ∀ a, ptr ≤ a → a < ptr + L → μ4.writable a = true := fun a h1 h2 => by
      rw [hwa]; exact heapC_writable_data H₀ hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩
    have hst4 : ∀ a, S0 ≤ a → a < S1 → μ4.writable a = true := fun a h1 h2 => by rw [hwa]; exact H₀.st a h1 h2
    -- the frame words: gr_pre's, then kept by gr_lock (off sp - 48 … sp - 40) and the allocation
    have kf : ∀ o, sp - 48 + 8 ≤ o → o + 8 ≤ sp → μ4.readN o 8 = μ1.readN o 8 := fun o h1 h2 =>
      PVM.Memory.readN_congr fun j hj => by
        rw [stk4 _ (by omega) (by omega), fr3 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
    have m0' : μ4.readN (sp - 48) 8 = Num.encodeLE 8 196792 := by
      rw [← m0]; exact PVM.Memory.readN_congr fun j hj => stk4 _ (by omega) (by omega)
    have ek : ω[9].toNat = kZ := by rw [h9, UInt64.toNat_ofNat_of_lt' (show kZ < 2 ^ 64 by omega)]
    obtain ⟨ω5, μ5, run5, u7, u8, u9, u10, u11, u12, u5, hμ5, bo5⟩ :=
      gr_unlock (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 (sp - 48) ptr kZ (f1.trans e1) e7'
        (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ m0'
        (by rw [kf _ (by omega) (by omega)]; exact readN_of_rdN (m8.trans ek))
        (fun a h1 h2 => Memory.readable_of_writable (hst4 a (by omega) (by omega))) hwl (by omega)
    subst hμ5
    -- the second read: w into the block
    have kμ5 : ∀ a, a < 4294967296 → sp ≤ a → (μ4.writeN 206848 [0]).read a = μ.read a := fun a h0 ha => by
      rw [PVM.Memory.read_writeN_of_not_mem _ _ _ _ (fun k hk => by
          simp at hk; simp only [two32]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h0]; omega),
        stk4 a h0 (by omega), fr3 a h0 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)),
        fr1 a h0 (Or.inr ha)]
    have wr5 : ∀ a, (μ4.writeN 206848 [0]).writable a = μ4.writable a := fun a => Memory.writable_writeN _ _ _ _
    have hk5 : (μ4.writeN 206848 [0]).rangeReadable kO kZ = true := Services.Witness.rangeReadable_of
      (fun a h1 h2 => by rw [Memory.readable_writeN]; exact Memory.readable_of_writable (hst4 a (by omega) (by omega)))
      (by omega)
    have hkey5 : (μ4.writeN 206848 [0]).readN kO kZ = key := by
      rw [← hkey]; apply PVM.Memory.readN_congr; intro j hj
      exact kμ5 _ (by omega) (by omega)
    have e8 : ω5[8] = UInt64.ofNat kO := u8.trans (f5.trans (d5.trans ((bo2 5 (by decide)).trans
      ((readRegs_ne ω1 (some w) 5 (by decide) (by decide)).trans (b5.trans h8)))))
    have e12 : ω5[12] = UInt64.ofNat L := u12.trans (f6.trans (d6.trans c6))
    have hR2 : KeepCtx (accContractS env) 4 ω5 (μ4.writeN 206848 [0]) (c, f) .cont (readRegs ω5 (some w))
        ((μ4.writeN 206848 [0]).writeN ptr w) (c, f) := by
      have := read_stepS env ω5 (μ4.writeN 206848 [0]) (c, f) kO kZ ptr L key (reg_of u7 (by decide))
        (reg_of e8 (by omega)) (reg_of u9 (by omega)) (reg_of u10 (by omega)) (reg_of u11 (by decide))
        (reg_of e12 (by omega)) hkZ (by omega) hk5 hkey5
        (by
          rw [hv]; simp only [Option.map_some, Option.getD_some, hLd, Nat.min_self]
          exact rangeWritable_of (by omega) fun a h1 h2 => by rw [wr5]; exact hwp a h1 h2)
      rw [hv] at this
      simp only [readMem, ← hLd, List.take_length] at this
      exact ⟨this, rfl⟩
    -- 48079 → 48102, the store
    have kW : ∀ a, a < 4294967296 → (a < ptr ∨ ptr + L ≤ a) →
        ((μ4.writeN 206848 [0]).writeN ptr w).read a = (μ4.writeN 206848 [0]).read a := fun a h0 ha =>
      PVM.Memory.read_writeN_of_not_mem _ _ _ _ (fun k hk => by
        rw [hLd] at hk; simp only [two32]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h0]; omega)
    have kL : ∀ a, a < 4294967296 → a ≠ 206848 → (μ4.writeN 206848 [0]).read a = μ4.read a := fun a h0 ha =>
      PVM.Memory.read_writeN_of_not_mem _ _ _ _ (fun k hk => by
        simp at hk; simp only [two32]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h0]; omega)
    have kf6 : ∀ o, sp - 48 + 8 ≤ o → o + 8 ≤ sp →
        ((μ4.writeN 206848 [0]).writeN ptr w).readN o 8 = μ1.readN o 8 := fun o h1 h2 => by
      rw [← kf o h1 h2]; exact PVM.Memory.readN_congr fun j hj => by
        rw [kW _ (by omega) (Or.inr (by omega)), kL _ (by omega) (by omega)]
    have wrW : ∀ a, ((μ4.writeN 206848 [0]).writeN ptr w).writable a = μ4.writable a := fun a => by
      rw [Memory.writable_writeN, wr5]
    have rr : ∀ j : Nat, (hj : j < 13) → j ≠ 7 → (readRegs ω5 (some w))[j] = ω5[j] := readRegs_ne ω5 (some w)
    obtain ⟨ω6, μ6, run6, g0, g1, g5, g6, o0, o8, o16, fr6, rd6, wr6⟩ :=
      gr_store (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) (readRegs ω5 (some w))
        ((μ4.writeN 206848 [0]).writeN ptr w) (sp - 48) out ptr L ω[0].toNat ω[5].toNat ω[6].toNat
        ((rr 1 (by decide) (by decide)).trans ((bo5 1 (by decide)).trans (f1.trans e1)))
        ((rr 5 (by decide) (by decide)).trans u5)
        ((rr 6 (by decide) (by decide)).trans ((bo5 6 (by decide)).trans (f6.trans (d6.trans c6))))
        (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        (by rw [kf6 _ (by omega) (by omega)]
            exact readN_of_rdN (m16.trans (by rw [h7, UInt64.toNat_ofNat_of_lt' (show out < 2 ^ 64 by omega)])))
        (by rw [kf6 _ (by omega) (by omega)]; exact readN_of_rdN m24)
        (by rw [kf6 _ (by omega) (by omega)]; exact readN_of_rdN m32)
        (by rw [kf6 _ (by omega) (by omega)]; exact readN_of_rdN m40)
        (fun a h1 h2 => Memory.readable_of_writable (by rw [wrW]; exact hst4 a (by omega) (by omega)))
        (fun a h1 h2 => by rw [wrW]; exact hst4 a (by omega) (by omega)) (Or.inr (by omega))
        (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
    have k6 : ∀ a, a < 4294967296 → (a < out ∨ out + 24 ≤ a) → a ≠ 206848 → (a < ptr ∨ ptr + L ≤ a) →
        μ6.read a = μ4.read a := fun a h0 ho hl hp => by rw [fr6 a h0 ho, kW a h0 hp, kL a h0 hl]
    have lk6 : rdN μ6 206848 1 = 0 := by
      have : μ6.read 206848 = 0 := by
        rw [fr6 _ (by omega) (Or.inl (by omega)), kW _ (by omega) (Or.inl (by omega))]
        simp only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq']
      simp [rdN, Memory.readN, this]; rfl
    refine Or.inl ⟨ptr, s', ω6, μ6, ((((((run1.trans (FreeStepsH.host_decode (d_47886 (p := p) (P := P)) hR1 run2)).trans
        run3).trans run4S).trans run5).trans (FreeStepsH.host_decode (d_48077 (p := p) (P := P)) hR2 run6))).mono
        (by omega),
      by rw [g0, UInt64.ofNat_toNat], by rw [g1, show sp - 48 + 48 = sp by omega],
      by rw [g5, UInt64.ofNat_toNat], by rw [g6, UInt64.ofNat_toNat], o0, o8, o16, ?_,
      heapL_release_data HL4 hnew lk6 (fun a ha ha' hc => k6 a (by omega) (Or.inl (by omega)) ha'
        (by dsimp only at hc; omega)) (fun a => (wr6 a).trans (wrW a)),
      keep4, fun d hd hu a ha => ?_, hnew, hfresh, fun a h0 ha ho => ?_⟩
    · rw [PVM.Memory.readN_congr (μ' := μ6) (μ := (μ4.writeN 206848 [0]).writeN ptr w) (a := ptr) (n := L)
        (fun j hj => fr6 (ptr + j) (by omega) (Or.inl (by omega)))]
      rw [← hLd]; exact PVM.Memory.readN_writeN_same _ _ _ _ rfl (by unfold PVM.two32; omega)
    · have hne : (⟨ptr - 32, (L + 31) / 32 + 1, true⟩ : Chunk) ≠ d := Ne.symm (hfresh d hd hu)
      have hap := Services.Bootstrap.Decode.LoopA.InData.apart H₀.wf (keep4 d hd hu) hnew hne ha
      unfold Services.Bootstrap.Decode.LoopA.InData at hap
      dsimp only at hap
      have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hd hu
      have := H.hb0
      have := H.hbT
      unfold InDataA at ha
      rw [k6 a (by omega) (Or.inl (by omega)) (by omega) (by omega), keepd4 d hd hu a ha.1 ha.2,
        fr3 a (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)), lo1 a (by omega)]
    · rw [fr6 a h0 ho, kW a h0 (Or.inr (by omega)), kμ5 a h0 ha]
  · -- the allocation failed: 48047 with ω₇ = 0, then the trap
    obtain ⟨-, run4S⟩ := FreeStepsH.growS f run4
    have m0' : μ4.readN (sp - 48) 8 = Num.encodeLE 8 196792 := by
      rw [← m0]; exact PVM.Memory.readN_congr fun j hj => stk4 _ (by omega) (by omega)
    obtain ⟨ω5, μ5, run5⟩ := gr_null (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 (sp - 48)
      (f1.trans e1) e7' ⟨by omega, by omega⟩ m0'
      (fun a h1 h2 => Memory.readable_of_writable (wst a (by omega) (by omega))) wl
    exact Or.inr ⟨ω4, μ4, (((run1.trans (FreeStepsH.host_decode (d_47886 (p := p) (P := P)) hR1 run2)).trans
      run3).trans run4S).mono (by omega), e7', ω5, μ5, run5⟩

end Services.Bootstrap.Acc
