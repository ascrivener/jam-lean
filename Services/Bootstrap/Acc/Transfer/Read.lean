import Services.Bootstrap.Acc.Transfer.GetKeyCall
import Services.Bootstrap.Acc.Transfer.Count
import Services.Bootstrap.Acc.Transfer.ReadShort
import Services.Bootstrap.Acc.Transfer.Head
import Services.Bootstrap.Acc.Transfer.CopyVal
import Services.Bootstrap.Acc.Transfer.Trap
import Services.Bootstrap.Decode.DeallocCall

/-!
# `on_transfer`, part 1: the memo's copy and the counter's read (7159 → 7326)

Spec `onTransfer`'s first line: `n := ((← op (read "transfer-count")).bind (decode (fixedN 4))).getD 0`
(quirk Q12: a value that does not decode reads as 0).

`tr_read` composes:
- `tr_head` and `memcpy_val`: the memo's 128 octets (at ω₈, in the item's slot) are copied to sp + 1144;
- `tr_gk_pre`, `gk_call`: `get("transfer-count")` into the 24-octet `Option<Vec<u8>>` at sp + 1568, or a
  heap trap (3895, 47977);
- `trd_none` (absent), or `trd_some` and `read_exact_val` (≥ 4 octets) / `read_exact_short` (< 4), then
  `trd_free` and `dealloc_callG` and `trd_back` (the value's chunk freed) or `trd_nofree` (empty), and
  `trd_n`: ω₆ = the counter, sign-extended (`sxw 4`), or 0 when the read failed.

The state at 7326: the allocator's context for the new state, every allocated chunk of s₀ and its data
kept, the memo's copy at sp + 1144, the source (u32) at sp + 472, the amount at sp + 1000, the key's
address 65956 at sp + 512, and from sp up nothing else changed but scratch words (`TrRdW`).
-/

namespace Services.Bootstrap.Acc
open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Picoalloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.DeallocCall Services.Bootstrap.Spec
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The key "transfer-count". -/
def trKey : List UInt8 := "transfer-count".toUTF8.toList

/-- Spec `onTransfer`'s counter from the value read under "transfer-count" (quirk Q12). -/
def trCount (v : Option Bytes) : Nat := (v.bind (decode (Dec.fixedN 4))).getD 0

theorem decode_fixedN4 (w : Bytes) :
    decode (Dec.fixedN 4) w = if 4 ≤ w.length then some (Num.decodeLE (w.take 4)) else none := by
  by_cases h : 4 ≤ w.length <;>
    simp [h, decode, Dec.fixedN, Dec.take, StateT.run, bind, StateT.bind, pure, StateT.pure, Option.map]

theorem trCount_lt (v : Option Bytes) : trCount v < 4294967296 := by
  unfold trCount
  cases v with
  | none => simp
  | some w =>
    simp only [Option.bind_some, decode_fixedN4]
    split
    · simp only [Option.getD_some]
      have := PVM.decodeLE_lt (w.take 4)
      have hl : (w.take 4).length = 4 := by simp; omega
      rw [hl] at this; exact this
    · simp

/-- The scratch words `tr_read` writes from sp up (besides the memo, source, amount and key words). -/
def TrRdW (sp a : Nat) : Prop :=
  (sp + 240 ≤ a ∧ a < sp + 256) ∨ (sp + 472 ≤ a ∧ a < sp + 476) ∨ (sp + 512 ≤ a ∧ a < sp + 520) ∨
  (sp + 744 ≤ a ∧ a < sp + 760) ∨ (sp + 1000 ≤ a ∧ a < sp + 1008) ∨ (sp + 1144 ≤ a ∧ a < sp + 1272) ∨
  (sp + 1568 ≤ a ∧ a < sp + 1592)

/-- An allocated chunk's data lies below 2³¹ (the heap ends at base + 2³⁰). -/
theorem heapC_data_lt {code : ByteArray} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtxC code pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) {a : Nat} (ha : InDataA c a) :
    206864 + 32 ≤ a ∧ a < 2147483648 := by
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  have := H.hbT
  have := H.hb0
  unfold InDataA at ha
  unfold State.top at hm
  simp only [maxSize] at hm
  omega

/-- **`on_transfer`, 7159 → 7326**: the memo copied to sp + 1144, then `get("transfer-count")`
    decoded as Spec `onTransfer` does: ω₆ = `sxw 4 (trCount v)` for the stored value v. Or an
    allocation failed and the run reaches a heap trap (3895, 47977). The context and the stream are
    kept. -/
theorem tr_read (env : AccEnv) (cap pb : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P]
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) {hb : Nat} (s₀ : State) (sp ms S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s₀)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ms)
    (hsp : 2147483800 + 128 + 56 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 400 ≤ sp ∧ sp + 1856 ≤ S1)
    (hms : 65536 ≤ ms ∧ ms + 128 + 24 ≤ sp - 88)
    (hmr : ∀ a, ms ≤ a → a < ms + 128 → μ.readable a = true)
    (hkey : μ.readN 65956 14 = trKey) (hkr : ∀ a, 65956 ≤ a → a < 65970 → μ.readable a = true)
    (hfit : ∀ w, c.1.self.storage.get? trKey = some w → w.length < 9223372036854775808) :
    (∃ s' ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 7159 ω μ (c, f) 7326 ω' μ' (c, f) N ∧
      ω'[1] = UInt64.ofNat sp ∧ ω'[6] = UInt64.ofNat (sxw 4 (trCount (c.1.self.storage.get? trKey))) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
      μ'.readN (sp + 1144) 128 = μ.readN ms 128 ∧
      rdN μ' (sp + 472) 4 = ω[10].toNat % 4294967296 ∧ rdN μ' (sp + 1000) 8 = ω[6].toNat ∧
      rdN μ' (sp + 512) 8 = 65956 ∧
      (∀ w, c.1.self.storage.get? trKey = some w → w.length < 2147483648) ∧
      (∀ a, a < 4294967296 → sp ≤ a → ¬ TrRdW sp a → μ'.read a = μ.read a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    (∃ t ω' μ' N, HeapTrapT t ∧
      FreeStepsH p (KeepCtx (accContractS env)) 7159 ω μ (c, f) t ω' μ' (c, f) N) := by
  have hst := H.st
  have hS1 := H.hS1
  have hwS : ∀ a, sp - 400 ≤ a → a < sp + 1856 → μ.writable a = true := fun a h1 h2 =>
    hst a (by omega) (by omega)
  -- 7159 → 68729 → 7176: the memo's copy
  obtain ⟨ω1, run1, a0, a7, a9, a5, aj⟩ := tr_head (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f)
    ω μ sp h1 ⟨by omega, by omega⟩
  have a1 : ω1[1] = UInt64.ofNat sp := (aj 1 (by decide)).trans h1
  have a8 : ω1[8] = UInt64.ofNat ms := (aj 8 (by decide)).trans h8
  have a6 : ω1[6] = ω[6] := aj 6 (by decide)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, cp2, fr2, rd2, wr2⟩ := memcpy_val (p := p) (P := P)
    (R := KeepCtx (accContractS env)) (c, f) ω1 μ 242 7176 sp (sp + 1144) ms 128 a0 a1 a7 a8 a9 (by decide)
    jte_120 bs_7176 ⟨by omega, by omega, hsp.2⟩ ⟨hms.1, by omega⟩ ⟨by omega, by omega⟩ (.inr (by omega))
    (.inl (by omega)) (.inr (by omega)) hmr (fun a h1 h2 => hwS a (by omega) (by omega))
    (fun a h1 h2 => hwS a (by omega) (by omega))
  -- 7176 → 40494: the helper's frame
  obtain ⟨ω3, μ3, run3, c0, c1, c7, c8, c5, c6, m0, m48, m40, m32, m472, m1000, m512, fr3, rd3, wr3, cj⟩ :=
    tr_gk_pre (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω2 μ2 sp (b1.trans a1)
      ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr2]; exact hwS a (by omega) (by omega))
  rw [b5, a5] at m40 m472
  rw [b6, a6] at m32 m1000
  -- the heap context and the key at 40494
  have fr13 : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha => by
    rw [fr3 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)),
      fr2 a (by omega) (.inl (by omega)) (.inl (by omega))]
  have wr13 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [wr3, wr2]
  have rd13 : ∀ a, μ3.readable a = μ.readable a := fun a => by rw [rd3, rd2]
  have H3 : HeapCtxC env.code pb S0 S1 μ3 s₀ := HeapCtxC.keep_hi H fr13 wr13
  have hkey3 : μ3.readN 65956 14 = trKey := by
    rw [readN_congr2 fun j hj => fr13 _ (by omega)]; exact hkey
  rcases gk_call (p := p) (P := P) (hb := hb) env cap pb hcap1 hcap (c := c) (f := f) ω3 μ3 s₀ (sp - 56) (sp + 1568)
      ω[10].toNat ω[6].toNat S0 S1 trKey H3 c0 c1 c7 c8 c5 c6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (readN_of_rdN m0) (readN_of_rdN m48) (readN_of_rdN m40) (readN_of_rdN m32)
      (UInt64.toNat_lt _) (UInt64.toNat_lt _) hkey3 (fun a h1 h2 => by rw [rd13]; exact hkr a h1 h2) hfit with
    ⟨s4, ω4, μ4, n4, run4, d1, d5, d6, gout, H4, keep4, dat4, fr4, g4⟩ | ⟨t, ω4, μ4, n4, ht, run4⟩
  rotate_left
  · exact .inr ⟨t, ω4, μ4, _, by rcases ht with rfl | rfl <;> simp [HeapTrapT],
      run1.trans (run2.trans (run3.trans run4))⟩
  have d1' : ω4[1] = UInt64.ofNat sp := by rw [d1, show sp - 56 + 56 = sp by omega]
  -- the frame from sp up at 7237
  have fr04 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 1568 ∨ sp + 1592 ≤ a) →
      ¬ (sp + 1144 ≤ a ∧ a < sp + 1272) → (a < sp + 472 ∨ sp + 476 ≤ a) → (a < sp + 512 ∨ sp + 520 ≤ a) →
      (a < sp + 1000 ∨ sp + 1008 ≤ a) → μ4.read a = μ.read a := fun a ha0 ha1 ha2 ha3 ha4 ha5 ha6 => by
    rw [fr4 a ha0 (by omega) ha2, fr3 a ha0 (.inr ha1) ha4 ha5 ha6, fr2 a ha0 (by omega) (.inr ha1)]
  have hrS4 : ∀ a, S0 ≤ a → a < S1 → μ4.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (H4.st a h1 h2)
  have memo4 : ∀ (μ5 : Memory), (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 240 ∨ sp + 256 ≤ a) →
      (a < sp + 744 ∨ sp + 760 ≤ a) → (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ5.read a = μ4.read a) →
      ∀ a, a < 4294967296 → sp ≤ a → ¬ TrRdW sp a → μ5.read a = μ.read a := by
    intro μ5 fr5 a ha0 ha1 hW
    unfold TrRdW at hW
    rw [fr5 a ha0 ha1 (by omega) (by omega) (by omega)]
    exact fr04 a ha0 ha1 (by omega) (by omega) (by omega) (by omega) (by omega)
  have to3 : ∀ (μ5 : Memory), (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 240 ∨ sp + 256 ≤ a) →
      (a < sp + 744 ∨ sp + 760 ≤ a) → (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ5.read a = μ4.read a) →
      ∀ a, sp + 256 ≤ a → a < sp + 744 → μ5.read a = μ3.read a := fun μ5 fr5 a h1 h2 => by
    rw [fr5 a (by omega) (by omega) (by omega) (by omega) (by omega), fr4 a (by omega) (by omega) (by omega)]
  have to3' : ∀ (μ5 : Memory), (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 240 ∨ sp + 256 ≤ a) →
      (a < sp + 744 ∨ sp + 760 ≤ a) → (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ5.read a = μ4.read a) →
      ∀ a, sp + 760 ≤ a → a < sp + 1568 → μ5.read a = μ3.read a := fun μ5 fr5 a h1 h2 => by
    rw [fr5 a (by omega) (by omega) (by omega) (by omega) (by omega), fr4 a (by omega) (by omega) (by omega)]
  -- the common end: from any state at 7326 with the right ω₆ and a frame against μ₄
  have fin : ∀ (s5 : State) (ω5 : Regs) (μ5 : Memory) (N : Nat),
      FreeStepsH p (KeepCtx (accContractS env)) 7237 ω4 μ4 (c, f) 7326 ω5 μ5 (c, f) N →
      ω5[1] = UInt64.ofNat sp → ω5[6] = UInt64.ofNat (sxw 4 (trCount (c.1.self.storage.get? trKey))) →
      HeapCtxC env.code pb S0 S1 μ5 s5 →
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s5 ∧ ∀ a, InDataA d a → μ5.read a = μ4.read a) →
      (∀ a, a < 4294967296 → sp ≤ a → (a < sp + 240 ∨ sp + 256 ≤ a) →
        (a < sp + 744 ∨ sp + 760 ≤ a) → (a < sp + 1568 ∨ sp + 1592 ≤ a) → μ5.read a = μ4.read a) →
      (∀ w, c.1.self.storage.get? trKey = some w → w.length < 2147483648) →
      (∀ a, Glob a → μ5.read a = μ4.read a) →
      ∃ s' ω' μ' N, FreeStepsH p (KeepCtx (accContractS env)) 7159 ω μ (c, f) 7326 ω' μ' (c, f) N ∧
        ω'[1] = UInt64.ofNat sp ∧ ω'[6] = UInt64.ofNat (sxw 4 (trCount (c.1.self.storage.get? trKey))) ∧
        HeapCtxC env.code pb S0 S1 μ' s' ∧
        (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InDataA d a → μ'.read a = μ.read a) ∧
        μ'.readN (sp + 1144) 128 = μ.readN ms 128 ∧
        rdN μ' (sp + 472) 4 = ω[10].toNat % 4294967296 ∧ rdN μ' (sp + 1000) 8 = ω[6].toNat ∧
        rdN μ' (sp + 512) 8 = 65956 ∧
        (∀ w, c.1.self.storage.get? trKey = some w → w.length < 2147483648) ∧
        (∀ a, a < 4294967296 → sp ≤ a → ¬ TrRdW sp a → μ'.read a = μ.read a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a) := by
    intro s5 ω5 μ5 N run5 e1 e6 H5 dat5 fr5 hlt g5
    refine ⟨s5, ω5, μ5, _, run1.trans (run2.trans (run3.trans (run4.trans run5))), e1, e6, H5,
      fun d hd hu => ⟨(dat5 d hd hu).1, fun a ha => ?_⟩, ?_, ?_, ?_, ?_, hlt, memo4 μ5 fr5,
      fun a hg => ?_⟩
    · rw [(dat5 d hd hu).2 a ha, dat4 d hd hu a ha]
      exact fr13 a (heapC_data_lt H hd ha).2
    · rw [readN_congr2 (μ := μ2) fun j hj => by
        rw [to3' μ5 fr5 _ (by omega) (by omega),
          fr3 _ (by omega) (.inr (by omega)) (.inr (by omega)) (.inr (by omega)) (.inr (by omega))]]
      exact cp2
    · rw [rdN_frame (μ := μ3) fun j hj => to3 μ5 fr5 _ (by omega) (by omega)]; exact m472
    · rw [rdN_frame (μ := μ3) fun j hj => to3' μ5 fr5 _ (by omega) (by omega)]; exact m1000
    · rw [rdN_frame (μ := μ3) fun j hj => to3 μ5 fr5 _ (by omega) (by omega)]; exact m512
    · have ha := hg; unfold Glob at ha
      rw [g5 a hg, g4 a hg]; exact fr13 a (by omega)
  -- the result's cases
  generalize hv : c.1.self.storage.get? trKey = v at gout fin hfit ⊢
  rcases v with _ | ⟨_ | ⟨b, w'⟩⟩
  · -- absent: the counter is 0
    obtain ⟨ω5, run5, e6, ej⟩ := trd_none (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 sp
      d1' ⟨by omega, by omega⟩ gout (fun a h1 h2 => hrS4 a (by omega) (by omega))
    exact .inl (fin s4 ω5 μ4 _ run5 ((ej 1 (by decide)).trans d1') (by rw [e6]; rfl) H4
      (fun d hd hu => ⟨keep4 d hd hu, fun a _ => rfl⟩) (fun a _ _ _ _ _ => rfl)
      (fun w hw => by cases hw) (fun a _ => rfl))
  · -- empty: `read_exact` fails, the counter is 0
    obtain ⟨g0, g8, g16⟩ := gout
    obtain ⟨ω5, μ5, run5, e0, e1, e5, e7, e8, e9, r744, r752, r248, fr5, rd5, wr5, ej⟩ :=
      trd_some (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 sp 0 1 0 d1'
        ⟨by omega, by omega⟩ g0 g8 g16 (by decide) (by decide) (by decide)
        (fun a h1 h2 => H4.st a (by omega) (by omega))
    obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, fr6, rd6, wr6⟩ :=
      read_exact_short (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω5 μ5 sp (sp + 744) 4 0 246
        7288 ⟨by omega, by omega⟩ e0 e1 e7 e9 (by decide) (by decide) (by decide) jte_122 bs_7288 r752
        (.inr (by omega)) (by omega) (fun a h1 h2 => by rw [rd5]; exact hrS4 a (by omega) (by omega))
        (fun a h1 h2 => by rw [wr5]; exact H4.st a (by omega) (by omega))
    obtain ⟨ω7, run7, g6, gj⟩ := trd_nofree (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω6 μ6 sp
      (f1.trans e1) (f5.trans e5) ⟨by omega, by omega⟩
      (fun a h1 h2 => by rw [rd6, rd5]; exact hrS4 a (by omega) (by omega))
    obtain ⟨ω8, run8, h6', hj⟩ := trd_n (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω7 μ6 1
      ((gj 7 (by decide)).trans f7) (by decide)
    have fr46 : ∀ a, a < 4294967296 → sp ≤ a → (a < sp + 248 ∨ sp + 256 ≤ a) → (a < sp + 744 ∨ sp + 760 ≤ a) →
        (a < sp + 1568 ∨ sp + 1572 ≤ a) → μ6.read a = μ4.read a := fun a ha0 ha1 ha2 ha3 ha4 => by
      rw [fr6 a ha0 (.inr ha1), fr5 a ha0 ha2 ha3 ha4]
    have H6 : HeapCtxC env.code pb S0 S1 μ6 s4 := HeapCtxC.keep_hi H4
      (fun a ha => by
        rw [fr6 a (by omega) (.inl (by omega)), fr5 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))])
      (fun a => by rw [wr6, wr5])
    refine .inl (fin s4 ω8 μ6 _ (run5.trans (run6.trans (run7.trans run8)))
      ((hj 1 (by decide)).trans ((gj 1 (by decide)).trans (f1.trans e1))) ?_ H6
      (fun d hd hu => ⟨keep4 d hd hu, fun a ha => ?_⟩)
      (fun a ha0 ha1 ha2 ha3 ha4 => fr46 a ha0 ha1 (by omega) ha3 (by omega))
      (fun w hw => by cases hw; decide)
      (fun a hg => by
        have ha := hg; unfold Glob at ha
        rw [fr6 a (by omega) (.inl (by omega)), fr5 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]))
    · rw [h6']; simp [trCount, decode_fixedN4]; rfl
    · have := heapC_data_lt H4 (keep4 d hd hu) ha
      rw [fr6 a (by omega) (.inl (by omega)), fr5 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))]
  · -- a value W = b :: w' of length ≥ 1
    obtain ⟨ptr, g0, g8, g16, gW, gch, g32, gfr⟩ := gout
    generalize hW : b :: w' = W at g0 g8 g16 gW gch gfr hfit fin ⊢
    have hW1 : 1 ≤ W.length := by rw [← hW]; simp
    have hWl : W.length < 9223372036854775808 := hfit W rfl
    generalize hch : (⟨ptr - 32, (W.length + 31) / 32 + 1, true⟩ : Chunk) = ch at gch gfr
    have hchA : ch.addr + 32 = ptr := by rw [← hch]; dsimp only; omega
    have hchU : ch.used = true := by rw [← hch]
    have hchD : ∀ a, ptr ≤ a → a < ptr + W.length → InDataA ch a := fun a h1 h2 => by
      rw [← hch]; unfold InDataA; dsimp only; omega
    have hpb := heapC_data_lt H4 gch (hchD ptr (by omega) (by omega))
    have hpe := heapC_data_lt H4 gch (hchD (ptr + W.length - 1) (by omega) (by omega))
    obtain ⟨ω5, μ5, run5, e0, e1, e5, e7, e8, e9, r744, r752, r248, fr5, rd5, wr5, ej⟩ :=
      trd_some (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω4 μ4 sp W.length ptr W.length d1'
        ⟨by omega, by omega⟩ g0 g8 g16 (by omega) (by omega) (by omega)
        (fun a h1 h2 => H4.st a (by omega) (by omega))
    have k45 : ∀ a, a < 2147483648 → μ5.read a = μ4.read a := fun a ha =>
      fr5 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega))
    -- `read_exact(4)`: Ok with the first 4 octets at sp + 1568, or Err (1) when |W| < 4
    obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, r7v, fr6, rd6, wr6⟩ : ∃ ω6 μ6, FreeStepsH p (KeepCtx (accContractS env))
        58434 ω5 μ5 (c, f) 7288 ω6 μ6 (c, f) (if 4 ≤ W.length then 7 * 4 + 350 else 28) ∧
        ω6[0] = ω5[0] ∧ ω6[1] = ω5[1] ∧ ω6[5] = ω5[5] ∧ ω6[6] = ω5[6] ∧
        (if 4 ≤ W.length then ω6[7] = UInt64.ofNat 0 ∧ rdN μ6 (sp + 1568) 4 = Num.decodeLE (W.take 4)
          else ω6[7] = UInt64.ofNat 1) ∧
        (∀ a, a < 4294967296 → (a < sp - 88 ∨ sp ≤ a) → (a < sp + 744 ∨ sp + 760 ≤ a) →
          (a < sp + 1568 ∨ sp + 1572 ≤ a) → μ6.read a = μ5.read a) ∧
        (∀ a, μ6.readable a = μ5.readable a) ∧ (∀ a, μ6.writable a = μ5.writable a) := by
      by_cases h4 : 4 ≤ W.length
      · obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, cp6, -, -, fr6, rd6, wr6⟩ :=
          read_exact_val (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω5 μ5 sp (sp + 744) (sp + 1568)
            4 ptr W.length 246 7288 ⟨by omega, by omega, hsp.2⟩ e0 e1 e7 e8 e9 (by decide) jte_122 bs_7288
            r744 r752 h4 (.inr (by omega)) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
            (.inr (by omega)) (.inl (by omega)) (.inr (by omega)) (.inl (by omega))
            (fun a h1 h2 => by
              rw [rd5]; exact Memory.readable_of_writable (heapC_writable_data H4 gch hchU (hchD a h1 (by omega))))
            (fun a h1 h2 => by rw [wr5]; exact H4.st a (by omega) (by omega))
            (fun a h1 h2 => by rw [wr5]; exact H4.st a (by omega) (by omega))
            (fun a h1 h2 => by rw [wr5]; exact H4.st a (by omega) (by omega))
        refine ⟨ω6, μ6, by rw [if_pos h4]; exact run6, f0, f1, f5, f6, ?_,
          fun a ha0 ha1 ha2 ha3 => fr6 a ha0 (by omega) ha1 ha2, rd6, wr6⟩
        rw [if_pos h4]
        refine ⟨f7, ?_⟩
        unfold rdN
        rw [cp6, readN_congr2 (μ := μ4) fun j hj => k45 _ (by omega), ← readN_take μ4 ptr W.length 4 h4, gW]
      · obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, f7, fr6, rd6, wr6⟩ :=
          read_exact_short (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω5 μ5 sp (sp + 744) 4
            W.length 246 7288 ⟨by omega, by omega⟩ e0 e1 e7 e9 (by omega) (by decide) (by decide) jte_122
            bs_7288 r752 (.inr (by omega)) (by omega)
            (fun a h1 h2 => by rw [rd5]; exact hrS4 a (by omega) (by omega))
            (fun a h1 h2 => by rw [wr5]; exact H4.st a (by omega) (by omega))
        refine ⟨ω6, μ6, by rw [if_neg h4]; exact run6, f0, f1, f5, f6, by rw [if_neg h4]; exact f7,
          fun a ha0 ha1 _ _ => fr6 a ha0 (by omega), rd6, wr6⟩
    have k46 : ∀ a, a < 2147483648 → μ6.read a = μ4.read a := fun a ha => by
      rw [fr6 a (by omega) (.inl (by omega)) (.inl (by omega)) (.inl (by omega)), k45 a ha]
    have r7n : ∃ r, ω6[7] = UInt64.ofNat r ∧ r < 2 ∧
        (if r = 0 then sxw 4 (rdN μ6 (sp + 1568) 4) else 0) = sxw 4 (trCount (some W)) := by
      by_cases h4 : 4 ≤ W.length
      · rw [if_pos h4] at r7v
        refine ⟨0, r7v.1, by decide, ?_⟩
        rw [if_pos rfl, r7v.2]; simp [trCount, decode_fixedN4, h4]
      · rw [if_neg h4] at r7v
        refine ⟨1, r7v, by decide, ?_⟩
        simp [trCount, decode_fixedN4, h4]; rfl
    obtain ⟨r, hr7, hr2, hrv⟩ := r7n
    -- the value's chunk freed
    obtain ⟨ω7, μ7, run7, g0', g1', g7', g6', m240, fr7, rd7, wr7⟩ :=
      trd_free (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω6 μ6 sp W.length ptr
        (f1.trans e1) (f5.trans e5) ⟨by omega, by omega⟩ (by omega) (by omega)
        (by rw [rdN_frame (μ := μ5) fun j hj => fr6 _ (by omega) (.inr (by omega)) (.inl (by omega))
          (.inl (by omega))]; exact r248)
        (fun a h1 h2 => by rw [wr6, wr5]; exact H4.st a (by omega) (by omega))
    have H7 : HeapCtxC env.code pb S0 S1 μ7 s4 := HeapCtxC.keep_hi H4
      (fun a ha => by rw [fr7 a (by omega) (.inl (by omega)), k46 a ha]) (fun a => by rw [wr7, wr6, wr5])
    obtain ⟨ω8, μ8, run8, H8, -, -, -, fr8, glob8, dat8, h0', h1', h5', h6'⟩ :=
      dealloc_callG (p := p) (P := P) (R := KeepCtx (accContractS env)) env.code pb S0 S1 (c, f) ω7 μ7 s4 sp ptr
        248 7315 ch H7 gch (by rw [← hch]) hchA g0' g1' g7' (by decide) jte_123 bs_7315 (by omega)
        ⟨by omega, by omega⟩
    obtain ⟨ω9, run9, i7, ij⟩ := trd_back (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω8 μ8 sp
      (h1'.trans g1') ⟨by omega, by omega⟩
      (fun a h1 h2 => by
        have := H8.st a (by omega) (by omega); exact Memory.readable_of_writable this)
    have r240 : rdN μ8 (sp + 240) 8 = r := by
      rw [rdN_frame (μ := μ7) fun j hj => fr8 _ (by omega) (by omega), m240, hr7]
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨ω10, run10, k6, kj⟩ := trd_n (p := p) (P := P) (R := KeepCtx (accContractS env)) (c, f) ω9 μ8 r
      (by rw [i7, r240]) (by omega)
    refine .inl (fin (free s4 ptr) ω10 μ8 _ (run5.trans (run6.trans (run7.trans (run8.trans (run9.trans run10)))))
      ((kj 1 (by decide)).trans ((ij 1 (by decide)).trans (h1'.trans g1'))) ?_ H8
      (fun d hd hu => ?_) (fun a ha0 ha1 ha2 ha3 ha4 => ?_) (fun w hw => by cases hw; omega) (fun a hg => ?_))
    · have e6 := (ij 6 (by decide)).trans (h6'.trans g6')
      rw [k6, ← hrv]
      by_cases hr0 : r = 0
      · simp only [hr0, ↓reduceIte]; exact e6
      · simp [hr0]
    · have hd4 := keep4 d hd hu
      have hne := gfr d hd hu
      obtain ⟨hdm, hdd⟩ := dat8 d hd4 hu hne
      refine ⟨hdm, fun a ha => ?_⟩
      have := heapC_data_lt H4 hd4 ha
      rw [hdd a ha, fr7 a (by omega) (.inl (by omega)), k46 a this.2]
    · rw [fr8 a ha0 ha1, fr7 a ha0 (by omega), fr6 a ha0 (.inr ha1) (by omega) (by omega),
        fr5 a ha0 (by omega) (by omega) (by omega)]
    · have ha := hg; unfold Glob at ha
      rw [glob8 a hg, fr7 a (by omega) (.inl (by omega)), k46 a (by omega)]

end Services.Bootstrap.Acc
