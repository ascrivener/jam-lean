import Services.Bootstrap.Fmt.FieldWriteSpec
import Services.Bootstrap.Fmt.DebugList

/-!
# A nested `core::fmt::write` (64495): one explicit-options argument, the `String` above

A formatter that calls `core::fmt::write` from its own frame (57922, the hex path of 56340, writes
each octet with the template 70833 = `{:02x}`) has its arguments *below* the `String` it writes to,
while `ArgOkO` and `fmt_write_spec` keep the caller's frame from spA up untouched and so need the
`String` below spA. Here:

- `ArgOkW … W …`: an argument's function for the fixed `String` W, keeping the caller's frame from
  spA up except W (W may be above or below spA);
- `ArgOkW.toO`: such a function for every W is an `ArgOkO`;
- `ValAt.readableW`: `ValAt.readable` under such a frame;
- `fmt_write_c3`: `core::fmt::write` over a template of one explicit-options item (0xC3, `SpecAt`)
  and its end, the argument an `ArgOkW` relative to the memory at the call and the stack pointer S.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **An argument's function for the `String` W, called with an options-carrying `Formatter`**: as
    `ArgOkO`, for the given W, with the caller's frame from spA up kept but for W … W + 24 (so W
    need not lie below spA). -/
def ArgOkW (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (μA : Memory) (sA : State) (spA W e v o w M C : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F cap len ret t v5 v6 : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Keeps pb spA (fun a => W ≤ a ∧ a < W + 24) sA μA μ s →
    FmtrO sA s μ F W cap len o w →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat v5 →
    ω[6] = UInt64.ofNat v6 → ω[7] = UInt64.ofNat v → ω[8] = UInt64.ofNat F →
    v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    (S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) → sp ≤ spA → (sp ≤ W ∧ W + 24 ≤ S1) →
    (sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R e ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ FmtrO sA s' μ' F W cap' (len + n) o w ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb e ω μ x (1073741824 + C)

/-- A function that is `ArgOkW` for every `String` is `ArgOkO`. -/
theorem ArgOkW.toO {p : ByteArray} {P : Program} {X : Type} {R : HostRel X} {env : RefineHost.Env}
    {pb S0 S1 Z : Nat} {μA : Memory} {sA : State} {spA e v o w M C : Nat}
    (h : ∀ W, ArgOkW p P R env pb S0 S1 Z μA sA spA W e v o w M C) :
    ArgOkO p P R env pb S0 S1 Z μA sA spA e v o w M C := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW _ hF hn
  exact h W ω μ x s sp F cap len ret t v5 v6 H hba (K.mono (Nat.le_refl _) (fun a e => e.elim)) hf h0 h1 h5 h6 h7
    h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn

/-- `ValAt.readable` under a frame that may change E. -/
theorem ValAt.readableW {env : RefineHost.Env} {pb S0 S1 spA sp a n : Nat} {E : Nat → Prop} {sA s : State}
    {μA μ : Memory} (h : ValAt μA sA spA S1 a n) (hn : 0 < n) (H : HeapCtx env pb S0 S1 μ s) (hS : S0 ≤ spA)
    (hsp : sp ≤ spA) (K : Keeps pb spA E sA μA μ s) :
    (∀ b, a ≤ b → b < a + n → μ.readable b = true) ∧ ((sp ≤ a ∧ a + n ≤ S1) ∨ a + n ≤ 2147483648) := by
  have := H.hSb
  rcases h with ⟨h1, h2, h3⟩ | ⟨c, hc, hu, hd⟩
  · exact ⟨fun b hb1 hb2 => by
      rw [(K.access b (Or.inr (by unfold pageSize; omega))).1]; exact h3 b hb1 hb2, Or.inl ⟨by omega, h2⟩⟩
  · have hc' := K.used c hc hu
    refine ⟨fun b hb1 hb2 => Memory.readable_of_writable (data_writable H hc' hu (by
      have := hd (b - a) (by omega); rwa [show a + (b - a) = b by omega] at this)), ?_⟩
    have := chunk_bounds H.wf hc'
    have := H.hbT
    have h1 := hd (n - 1) (by omega)
    unfold InData at h1
    right; omega

/-- **A nested `core::fmt::write`** (64495) into the `String` W (ω₇, its vtable 77016 in ω₈) over the
    template at tp (ω₉) of one explicit-options item (`SpecAt`: 0xC3, o, w) and the end byte at
    tp + 7, its argument the pair (v, fn) at args (ω₁₀) in the memory μ of the call, at or above the
    stack pointer S and apart from W, fn resolving to an `ArgOkW` function relative to (μ, S): either
    - `Ok` (ω₇ = 0) returned to t, ω₀, ω₁, ω₅, ω₆ as they were, the `String` at most M octets
      longer, within 7M + C + 300 + 2(cap' − cap) steps, the context kept and, from S up, only
      W … W + 24 changed; or
    - a failed allocator call. -/
theorem fmt_write_c3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 600 ≤ Z) (S W tp args ret t v5 v6 o w v fn e M C : Nat)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (cap len : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str s₀ s μ W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat 77016)
    (h9 : ω[9] = UInt64.ofNat tp) (h10 : ω[10] = UInt64.ofNat args)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : S0 + Z + 96 ≤ S ∧ S % 8 = 0 ∧ 2147483648 + Z + 96 ≤ S) (hW : S ≤ W ∧ W + 24 ≤ S1)
    (hro : RoW μ) (hSp : SpecAt μ tp o w) (hend : rdN μ (tp + 7) 1 = 0 ∧ μ.readable (tp + 7) = true)
    (htp : 65536 ≤ tp ∧ tp + 7 + 1 + 24 ≤ 196608)
    (hargs : args % 2 = 0) (hA : S ≤ args ∧ args + 16 < 4294967296 ∧ (args + 16 ≤ W ∨ W + 24 ≤ args))
    (hAr : ∀ a, args ≤ a → a < args + 16 → μ.readable a = true)
    (hav : rdN μ args 8 = v) (haf : rdN μ (args + 8) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true)
    (hok : ArgOkW p P R env pb S0 S1 Z μ s₀ S W e v o w M C) (hn : len + M < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R 64495 ω μ x t ω' μ' x' (7 * M + C + 300 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb S (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 64495 ω μ x (1073741824 + C + 300) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → S - 96 ≤ a) → ∀ d ∈ chunks s₀, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  obtain ⟨hb, ho1, ho, hw1, hrb⟩ := hSp
  -- 64495 … 64611
  obtain ⟨ω1, μ1, run1, a1, a5, a9, a12, m0, m8, m16, m24, m32, m40, m72, m80, m88, fr1, rd1, wr1⟩ :=
    wr_entry (p := p) (P := P) (R := R) x ω μ S W tp args 195 ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
      h9 h10 ⟨by omega, hv.1, hv.2, by omega, by omega, by omega, hargs⟩ hb (by omega) (hrb tp (by omega) (by omega))
      (by omega) hro.vws (fun a h1 h2 => hro.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have kA1 : ∀ a, S ≤ a → a < 4294967296 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a h2 (Or.inr h1)
  -- 64611 … the argument's function
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, n48, n56, n64, n68, n70, fr2, rd2, wr2⟩ :=
    wr_spec (p := p) (P := P) (R := R) x ω1 μ1 (S - 96) W tp 0 args v fn e o w ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega) a1 a5 a9 a12 m8 m16 m24
      (by rw [show args + 16 * 0 = args by omega, rdN_frame (fun j hj => kA1 _ (by omega) (by omega))]; exact hav)
      (by rw [show args + 16 * 0 + 8 = args + 8 by omega, rdN_frame (fun j hj => kA1 _ (by omega) (by omega))]
          exact haf)
      (by rw [rdN_frame (fun j hj => fr1 _ (by omega) (Or.inl (by omega)))]; exact ho1) ho
      (by rw [rdN_frame (fun j hj => fr1 _ (by omega) (Or.inl (by omega)))]; exact hw1)
      (fun a h1 h2 => by rw [rd1]; exact hrb a h1 h2) hfn hje hbe
      (fun a h1 h2 => by rw [rd1]; exact hAr a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr1]; exact hst a (by omega) (by omega)))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have k12 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S ≤ a) → μ2.read a = μ.read a := fun a h1 h2 => by
    rw [fr2 a h1 (by omega), fr1 a h1 h2]
  have rd12 : ∀ a, μ2.readable a = μ.readable a := fun a => by rw [rd2, rd1]
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => k12 a (by omega) (Or.inl (by omega))) wr12
  have K2 : Keeps pb S (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ2 s :=
    Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S) hs.base (fun a ha hz => k12 a ha (by omega)) rd12 wr12
      (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
      (fun a hz hg => by unfold Glob at hg; omega) (hzd _ (fun a hz => hz.1))
  have hro2 := K2.ro_low H
  have hf2 : FmtrO s₀ s μ2 (S - 96 + 48) W cap len o w :=
    ⟨n48, by rw [show S - 96 + 48 + 8 = S - 96 + 56 by omega]; exact n56,
     by rw [show S - 96 + 48 + 16 = S - 96 + 64 by omega]; exact n64,
     by rw [show S - 96 + 48 + 20 = S - 96 + 68 by omega]; exact n68,
     by rw [show S - 96 + 48 + 22 = S - 96 + 70 by omega]; exact n70,
     (hro.congr (fun a h1 h2 => hro2 a h2)).vws, (hro.congr (fun a h1 h2 => hro2 a h2)).vwc,
     (hro.congr (fun a h1 h2 => hro2 a h2)).vrd,
     hs.update (fun j hj => k12 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ) (μ' := μ2) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, k12 _ (by omega) (Or.inr (by omega))])).trans hs.rl)
      hs.le⟩
  rcases hok ω2 μ2 x s (S - 96) (S - 96 + 48) cap len 2732 64843 0 (tp + 7) H2 hba K2 hf2 b0 (b1.trans a1)
      b5 b6 b7 b8 (by omega) (by omega) (by decide) jte_1365 bs_64843 ⟨by omega, by omega, by omega⟩ (by omega)
      ⟨by omega, hW.2⟩ ⟨by omega, by omega, Or.inl (by omega)⟩ hn with
    ⟨ω3, μ3, x3, s3, cap3, n, hnM, run3, H3, hb3, hf3, hc31, hc32, K3, e0, e1, e5, e6, e7⟩ | hx
  · -- 64843 … 64600
    obtain ⟨ω4, μ4, run4, f0, f1, f6, fi, fr4, rd4, wr4⟩ := wr_spec_ret (p := p) (P := P) (R := R) x3 ω3 μ3 (S - 96) 0
      ⟨by omega, by omega⟩ (by omega) e1 e5 e7 (fun a h1 h2 => H3.st a (by omega) (by omega))
    have kT : ∀ a, S - 96 + 72 ≤ a → a < S → μ4.read a = μ1.read a := fun a h1 h2 => by
      rw [fr4 a (by omega) (by omega), K3.hi a (by omega) (by omega) (by omega), fr2 a (by omega) (by omega)]
    have H4 : HeapCtx env pb S0 S1 μ4 s3 := ctx_hi H3 (fun a ha => fr4 a (by omega) (Or.inl (by omega))) wr4
    have kro : ∀ a, a < 196608 → μ4.read a = μ.read a ∧ μ4.readable a = μ.readable a := fun a ha =>
      ⟨by rw [fr4 a (by omega) (Or.inl (by omega)), (K3.ro_low H2 a ha).1, (K2.ro_low H a ha).1],
       by rw [rd4, (K3.ro_low H2 a ha).2, (K2.ro_low H a ha).2]⟩
    -- the template's end
    obtain ⟨ω5, run5, g0, g1, g5, g6, g7⟩ := wr_end (p := p) (P := P) (R := R) x3 ω4 μ4 (S - 96) (tp + 7) ret t
      v5 v6 ⟨by omega, by omega⟩ (by omega) (f1.trans e1) (by rw [f6, e6])
      (by rw [rdN_frame (fun j hj => (kro _ (by omega)).1)]; exact hend.1)
      (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact m88)
      (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact m80)
      (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact m72) hret hjt hbt
      (by rw [(kro _ (by omega)).2]; exact hend.2)
      (fun a h1 h2 => Memory.readable_of_writable (H4.st a (by omega) (by omega)))
    have K4 : Keeps pb S (fun a => W ≤ a ∧ a < W + 24) s₀ μ3 μ4 s3 :=
      Keeps.of_frame (Z := fun a => S - 96 + 24 ≤ a ∧ a < S - 96 + 32) hf3.str.base
        (fun a ha hz => fr4 a ha (by omega)) rd4 wr4 (fun a hz => H3.st a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun d hd hu a ha => by
          have := chunk_bounds H3.wf (hf3.str.base d hd hu)
          have := H3.hbT
          unfold InData at ha; omega)
    have K := (K2.trans' (K3.mono (sp' := S) (by omega) (fun a h => h))).trans' K4
    simp only [Nat.max_self] at K
    have hs4 : Str s₀ s3 μ4 W cap3 (len + n) := hf3.str.update
      (fun j hj => fr4 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ3) (μ' := μ4) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr4 _ (by omega) (Or.inr (by omega))])).trans hf3.str.rl)
      hf3.str.le
    exact Or.inl ⟨ω5, μ4, x3, s3, cap3, n, hnM,
      ((((run1.trans run2).trans run3).trans run4).trans run5).mono (by omega), H4, hb3, hs4, hc31, hc32, K,
      g0, by rw [g1, show S - 96 + 96 = S by omega], g5, g6, g7⟩
  · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))

end Services.Bootstrap.Fmt
