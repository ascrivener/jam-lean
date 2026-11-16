import Services.Bootstrap.Fmt.FieldSliceHexSteps
import Services.Bootstrap.Fmt.FieldWriteNestedPlain

/-!
# 57922, a slice of octets in hex, as an argument

`slice_hex_ok`: 57922 called with the address v of a slice's (pointer a, length len) pair,
1 ≤ len < 1027, each octet where `ValAt` puts it, writes 2·len octets (each octet as `{:02x}`
through a nested `core::fmt::write`), frame-only: an `ArgOk` with M = 2·len.

It assumes the template 70833 in read-only data (`RO70833`, the named hypothesis on the octets
70833 … 70840: 0xC3, the options word 0x69000020, the width 2, the end byte 0).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The template 70833** (`{:02x}`, 8 octets of read-only data): 0xC3, the options word 0x69000020,
    the width 2, the end byte 0. A named hypothesis on the vendored blob's read-only data. -/
def RO70833 (μ : Memory) : Prop :=
  rdN μ 70833 1 = 195 ∧ rdN μ 70834 4 = 1761607712 ∧ rdN μ 70838 2 = 2 ∧ rdN μ 70840 1 = 0

theorem RO70833.congr {μ μ' : Memory} (h : RO70833 μ) (k : ∀ a, 70833 ≤ a → a < 70841 → μ'.read a = μ.read a) :
    RO70833 μ' :=
  ⟨by rw [rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact h.1,
   by rw [rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact h.2.1,
   by rw [rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact h.2.2.1,
   by rw [rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact h.2.2.2⟩

/-- A value where `ValAt` puts it, for the caller's memory μA and spA, is where `ValAt` puts it for any
    memory the run reaches and any lower stack pointer. -/
theorem ValAt.rebase {env : RefineHost.Env} {pb S0 S1 spA sp a n : Nat} {E : Nat → Prop} {sA s : State}
    {μA μ : Memory} (h : ValAt μA sA spA S1 a n) (H : HeapCtx env pb S0 S1 μ s) (hS : S0 ≤ spA)
    (hsp : sp ≤ spA) (K : Keeps pb spA E sA μA μ s) : ValAt μ sA sp S1 a n := by
  have := H.hSb
  rcases h with ⟨h1, h2, h3⟩ | h
  · exact Or.inl ⟨by omega, h2, fun b hb1 hb2 => by
      rw [(K.access b (Or.inr (by unfold pageSize; omega))).1]; exact h3 b hb1 hb2⟩
  · exact Or.inr h

/-- 57922's frame at T: ω₀, ω₅, ω₆ at T + 96, T + 88, T + 80, the sink (W, 77016) at T + 48, T + 40,
    2532 at T + 32, the template 70833 at T + 24. -/
structure SH (μ : Memory) (T W r0 v5 v6 : Nat) : Prop where
  r0 : rdN μ (T + 96) 8 = r0
  r5 : rdN μ (T + 88) 8 = v5
  r6 : rdN μ (T + 80) 8 = v6
  w : rdN μ (T + 48) 8 = W
  vt : rdN μ (T + 40) 8 = 77016
  fn : rdN μ (T + 32) 8 = 2532
  tp : rdN μ (T + 24) 8 = 70833

theorem SH.congr {μ μ' : Memory} {T W r0 v5 v6 : Nat} (h : SH μ T W r0 v5 v6)
    (k : ∀ a, (T + 24 ≤ a ∧ a < T + 56) ∨ (T + 80 ≤ a ∧ a < T + 104) → μ'.read a = μ.read a) :
    SH μ' T W r0 v5 v6 :=
  ⟨by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.r0,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.r5,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.r6,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.w,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.vt,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.fn,
   by rw [rdN_frame (fun j hj => k _ (by omega))]; exact h.tp⟩

/-- The octets the loop changes from T up: the `String` W and the argument cells T + 56 … T + 80. -/
def shE (T W a : Nat) : Prop := (W ≤ a ∧ a < W + 24) ∨ (T + 56 ≤ a ∧ a < T + 80)

/-- **The loop** (57976 … 58025) over the last m of len octets from a: each written by the nested
    `core::fmt::write`, then 58215. -/
theorem sh_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T W a len r0 v5 v6 : Nat) (hS : S0 ≤ spA)
    (hT : S0 + Z + 96 ≤ T ∧ T % 8 = 0 ∧ 2147483648 + Z + 96 ≤ T ∧ T + 104 ≤ spA)
    (hW : T + 104 ≤ W ∧ W + 24 ≤ S1) (hlen : len < 1027)
    (helts : ∀ j, j < len → ValAt μA sA spA S1 (a + j) 1) (ha : a + len < 18446744073709551616)
    (hRO : RO70833 μA) :
    ∀ m, 1 ≤ m → m ≤ len → ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (cap ln : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Str sA s μ W cap ln →
    Keeps pb spA (fun a => W ≤ a ∧ a < W + 24) sA μA μ s → RoW μ → SH μ T W r0 v5 v6 →
    ω[1] = UInt64.ofNat T → ω[5] = UInt64.ofNat m → ω[9] = UInt64.ofNat (a + (len - m)) →
    ln + 2 * m < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ 2 * m ∧
      FreeStepsH p R 57976 ω μ x 58215 ω' μ' x' (m * 536875500 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (ln + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (ln + n))) ∧ Keeps pb T (shE T W) sA μ μ' s' ∧
      ω'[1] = UInt64.ofNat T) ∨
    Exhausts p R pb 57976 ω μ x (2147483648 + m * 536875500 - 2 * cap) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
  intro _ hk ω μ x s cap ln H hba hs KA hro hsh h1 h5 h9 hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  have hcap := hs.lt
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → T ≤ a) → ∀ d ∈ chunks sA, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  -- the call
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, m56, m64, m72, fr1, rd1, wr1⟩ := sh_iter (p := p)
    (P := P) (R := R) x ω μ T W 77016 (a + (len - (k + 1))) (k + 1) ⟨by omega, by omega⟩ h1 h5 h9 (by omega)
    hsh.w hsh.vt hsh.fn hsh.tp (fun c h1 h2 => hst c (by omega) (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => fr1 c (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb T (shE T W) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => T + 56 ≤ c ∧ c < T + 80) hs.base (fun c hc hz => fr1 c hc (by omega)) rd1 wr1
      (fun c hz => hst c (by omega) (by omega)) (fun c hz h => Or.inr hz)
      (fun c hz hg => by unfold Glob at hg; omega) (hzd _ (fun c hz => by omega))
  have KA1 : Keeps pb spA (fun a => W ≤ a ∧ a < W + 24) sA μA μ1 s := by
    have := KA.trans' (K1.lift (sp' := spA) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun c h h' => by
      unfold shE at h; omega))
    rwa [Nat.max_self] at this
  have hro1 := K1.ro_low H
  have hs1 : Str sA s μ1 W cap ln := hs.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
    ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
  have hRO1 : RO70833 μ1 := hRO.congr (fun c h1 h2 => by
    rw [fr1 c (by omega) (Or.inl (by omega))]
    exact KA.ro c (by omega) (Or.inl (by unfold pageSize; omega))
      (by rw [← (KA.access c (Or.inl (by unfold pageSize; omega))).2]; exact H.ro c (by omega)))
  have hro1' : RoW μ1 := hro.congr (fun c h1 h2 => hro1 c h2)
  obtain ⟨q0, q1, q2, q3⟩ := hRO1
  have hok := u8hexref_okW (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μ1 sA T W (T + 56) (a + (len - (k + 1))) (by omega)
    ⟨by omega, by omega, Or.inl (by omega)⟩
    (fun c h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst c (by omega) (by omega))) m56
    ((helts (len - (k + 1)) (by omega)).rebase H1 hS (by omega) KA1)
  rcases fmt_write_c3 (p := p) (P := P) (R := R) env pb S0 S1 Z hZ T W 70833 (T + 64) 2536 58012 (k + 1)
      (a + (len - (k + 1))) 1761607712 2 (T + 56) 2532 57917 2 536875002 x ω1 μ1 sA s cap ln H1 hba hs1 a0 a1 a5
      a6 a7 a8 a9 a10 ⟨by omega, by omega⟩ (by omega) jte_1267 bs_58012 ⟨by omega, hT.2.1, by omega⟩
      ⟨by omega, hW.2⟩ hro1'
      ⟨q0, q1, by omega, q2, fun c h1 h2 => hro1'.vrd c (by omega) (by omega)⟩
      ⟨q3, hro1'.vrd _ (by omega) (by omega)⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, by omega, Or.inl (by omega)⟩
      (fun c h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst c (by omega) (by omega))) m64 m72
      (by omega) jte_1265 bs_57917 hok (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hnM, run2, H2, hb2, hs2, hc21, hc22, K2, e0, e1, e5, e6, e7⟩ | hx
  · have K12 : Keeps pb T (shE T W) sA μ μ2 s2 := by
      have := K1.trans' (K2.mono (Nat.le_refl _) (fun c h => Or.inl h))
      rwa [Nat.max_self] at this
    have hcap2 := hs2.lt
    obtain ⟨ω3, run3, c1, c5, c9⟩ := sh_next (p := p) (P := P) (R := R) x2 ω2 μ2 (k + 1) (a + (len - (k + 1)))
      ⟨by omega, by omega⟩ (by omega) e5 e6 e7
    by_cases hz : k + 1 - 1 = 0
    · rw [if_pos hz] at run3
      exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by omega, ((run1.trans run2).trans run3).mono (by omega), H2, hb2, hs2,
        hc21, by omega, K12, c1.trans e1⟩
    · rw [if_neg hz] at run3
      have KA2 : Keeps pb spA (fun a => W ≤ a ∧ a < W + 24) sA μA μ2 s2 := by
        have := KA.trans' (K12.lift (sp' := spA) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun c h h' => by
          unfold shE at h; omega))
        rwa [Nat.max_self] at this
      have hsh2 : SH μ2 T W r0 v5 v6 := hsh.congr (fun c hc => K12.hi c (by omega) (by omega) (by unfold shE; omega))
      rcases ih (by omega) (by omega) ω3 μ2 x2 s2 cap2 (ln + n) H2 (by rw [hb2]; exact hba) hs2 KA2
          (hro.congr (fun c h1 h2 => K12.ro_low H c h2)) hsh2 (c1.trans e1) (by rw [c5, show k + 1 - 1 = k by omega]) (by rw [c9]; congr 1; omega)
          (by omega) with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g1⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          (((run1.trans run2).trans run3).trans run').mono (by omega), H', hb'.trans hb2,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g1⟩
        have := K12.trans' K'
        rwa [Nat.max_self] at this
      · have := hs2.lt
        exact Or.inr ((Exhausts.pre ((run1.trans run2).trans run3) hx).mono (by omega))
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **A slice of octets in hex** (57922) for the `String` W: v the address of the slice's (pointer a,
    length len) pair (16 octets at or above spA, apart from W, readable), 1 ≤ len < 1027, each octet where `ValAt`
    puts it, and the template 70833 (`RO70833`): 2·len octets written. It needs 800 octets of stack.
    The Ok path takes at most 2(cap' − cap) + 536875500·len + 100 steps; the constant also carries the
    2³⁰ steps a failed allocator call may need beyond it. -/
theorem slice_hex_okW {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 800 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA W v a len : Nat) (hS : S0 ≤ spA)
    (hv : spA ≤ v ∧ v + 16 ≤ S1 ∧ (v + 16 ≤ W ∨ W + 24 ≤ v)) (hrv : ∀ b, v ≤ b → b < v + 16 → μA.readable b = true)
    (rp : rdN μA v 8 = a) (rl : rdN μA (v + 8) 8 = len) (hl : 1 ≤ len ∧ len < 1027)
    (helts : ∀ j, j < len → ValAt μA sA spA S1 (a + j) 1) (ha : a + len < 18446744073709551616)
    (hRO : RO70833 μA) :
    ArgOkWp p P R env pb S0 S1 Z μA sA spA W 57922 v (2 * len) (1073741924 + len * 536875500) := by
  intro ω μ x s sp F cap ln ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  have hro : ∀ c, c < 196608 → μ.writable c = false := H.ro
  have hcap := hf.str.lt
  have kv : ∀ j, j < 16 → μ.read (v + j) = μA.read (v + j) := fun j hj => K.hi _ (by omega) (by omega) (by omega)
  -- 57922 … 57975
  obtain ⟨ω1, μ1, run1, a1, a5, a9, s96, s88, s80, s48, s40, s32, s24, fr1, rd1, wr1⟩ := sh_entry (p := p)
    (P := P) (R := R) x ω μ sp v F ret v5 v6 a len W 77016 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
    ⟨by omega, hv5, hv6⟩ ⟨by omega, Or.inr (by omega)⟩ ⟨by omega, Or.inr hF.1⟩
    (by rw [rdN_frame (fun j hj => kv j (by omega))]; exact rp)
    (by rw [rdN_frame (μ := μA) (fun j hj => by rw [show v + 8 + j = v + (8 + j) by omega]; exact kv _ (by omega))]; exact rl)
    hl hf.buf hf.vt
    (fun b h1 h2 => by rw [(K.access b (Or.inr (by unfold pageSize; omega))).1]; exact hrv b h1 h2)
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => hst b (by omega) (by omega))
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => fr1 c (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun c => W ≤ c ∧ c < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => sp - 104 ≤ c ∧ c < sp) hf.str.base (fun c hc hz => fr1 c hc (by omega)) rd1 wr1
      (fun c hz => hst c (by omega) (by omega)) (fun c hz h => by omega)
      (fun c hz hg => by unfold Glob at hg; omega)
      (fun d hd hu c hc => by
        have := chunk_bounds H.wf (hf.str.base d hd hu)
        have := H.hbT
        unfold InData at hc; omega)
  have KA1 : Keeps pb spA (fun a => W ≤ a ∧ a < W + 24) sA μA μ1 s := by
    have := K.trans' (K1.lift (sp' := spA) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun c h h' => h))
    rwa [Nat.max_self] at this
  have hro1 := K1.ro_low H
  have hrow : RoW μ1 := (RoW.mk hf.vws hf.vwc hf.vrd).congr (fun c h1 h2 => hro1 c h2)
  have hs1 : Str sA s μ1 W cap ln := hf.str.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
    ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
      rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hf.str.rl)
    hf.str.le
  -- the loop
  rcases sh_loop (p := p) (P := P) (R := R) env pb S0 S1 600 (Nat.le_refl _) HA HR μA sA spA (sp - 104) W a len ret
      v5 v6 hS ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ hl.2 helts ha hRO len hl.1
      (Nat.le_refl _) ω1 μ1 x s cap ln H1 hba hs1 KA1 hrow ⟨s96, s88, s80, s48, s40, s32, s24⟩ a1 a5
      (by rw [a9, Nat.sub_self, Nat.add_zero]) (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hs2, hc21, hc22, K2, g1⟩ | hx
  · have kT : ∀ c, sp - 104 + 80 ≤ c → c < sp → μ2.read c = μ1.read c := fun c h1 h2 =>
      K2.hi c (by omega) (by omega) (by unfold shE; omega)
    obtain ⟨ω3, run3, e0, e1, e5, e6, e7⟩ := sh_end (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 104) ret t v5 v6
      ⟨by omega, by omega⟩ g1
      (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact s96)
      (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact s88)
      (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact s80) hret hjt hbt
      (fun c h1 h2 => Memory.readable_of_writable (H2.st c (by omega) (by omega)))
    have Kf : Keeps pb sp (fun c => W ≤ c ∧ c < W + 24) sA μ μ2 s2 := by
      have := K1.trans' (K2.lift (sp' := sp) (E' := fun c => W ≤ c ∧ c < W + 24) (by omega) (fun c h h' => by
        unfold shE at h; omega))
      rwa [Nat.max_self] at this
    have kF : ∀ c, F ≤ c → c < F + 24 → μ2.read c = μ.read c := fun c h1 h2 =>
      Kf.hi c (by omega) (by omega) (by omega)
    have kro : ∀ c, 65536 ≤ c → c < 77144 → μ2.read c = μ.read c := fun c h1 h2 =>
      Kf.ro c (by omega) (Or.inl (by unfold pageSize; omega)) (hro c (by omega))
    refine Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by omega, ((run1.trans run2).trans run3).mono (by omega), H2, hb2,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fun c h1 h2 => ?_, hs2⟩, hc21, hc22, Kf, e0,
      by rw [e1, show sp - 104 + 104 = sp by omega], e5, e6, e7⟩
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.buf
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.vt
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.opts
    · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.width
    · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vws
    · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vwc
    · rw [(Kf.access c (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd c h1 h2
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **A slice of octets in hex** (57922) as an argument (`ArgOk`), from `slice_hex_okW`. -/
theorem slice_hex_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 800 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v a len : Nat) (hS : S0 ≤ spA)
    (hv : spA ≤ v ∧ v + 16 ≤ S1) (hrv : ∀ b, v ≤ b → b < v + 16 → μA.readable b = true)
    (rp : rdN μA v 8 = a) (rl : rdN μA (v + 8) 8 = len) (hl : 1 ≤ len ∧ len < 1027)
    (helts : ∀ j, j < len → ValAt μA sA spA S1 (a + j) 1) (ha : a + len < 18446744073709551616)
    (hRO : RO70833 μA) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 57922 v (2 * len) (1073741924 + len * 536875500) := by
  intro ω μ x s sp F W cap ln ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  exact slice_hex_okW (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μA sA spA W v a len hS
    ⟨hv.1, hv.2, Or.inr (by omega)⟩ hrv rp rl hl helts ha hRO ω μ x s sp F cap ln ret t v5 v6 H hba
    (K.mono (Nat.le_refl _) (fun a e => e.elim)) hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn

end Services.Bootstrap.Fmt
