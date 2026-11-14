import Services.Bootstrap.Fmt.Write
import Services.Bootstrap.Fmt.Text

/-!
# `core::fmt::write` into a `String`, with the text

`fmt_write` (Fmt/Write.lean) is stated as a frame: the `String` grows by at most `tlen M ts`
octets. Here the same run is stated with its text. Each argument's function appends known octets
(`ArgOkT`), and the `String` gains the template's text `ttext μ tp ts bsf 0`: each literal's octets
from the template, each argument's octets `bsf i`, in order. The proofs follow Fmt/Write.lean
item by item, on `write_str_text` and `ReallocCopyOk`.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The text of a template** at c, items ts, the arguments from index i on appending `bsf i`,
    `bsf (i + 1)`, …: each literal's n octets (after its byte n), each argument's text. -/
def ttext (μ : Memory) : Nat → List TItem → (Nat → List UInt8) → Nat → List UInt8
  | _, [], _, _ => []
  | c, .lit n :: ts, bsf, i => μ.readN (c + 1) n ++ ttext μ (c + 1 + n) ts bsf i
  | c, .arg :: ts, bsf, i => bsf i ++ ttext μ (c + 1) ts bsf (i + 1)

/-- A template's text is kept by a change that keeps the read-only data. -/
theorem ttext_congr {μ μ' : Memory} {bsf : Nat → List UInt8} :
    ∀ (ts : List TItem) (c : Nat) {i : Nat}, c + tsize ts ≤ 196608 →
      (∀ b, b < 196608 → μ'.read b = μ.read b) → ttext μ' c ts bsf i = ttext μ c ts bsf i := by
  intro ts
  induction ts with
  | nil => intro c i _ _; rfl
  | cons it ts ih =>
    intro c i hc k
    cases it with
    | lit n =>
      simp only [ttext, tsize] at hc ⊢
      rw [readN_congr2 (fun j hj => k _ (by omega)), ih _ (by omega) k]
    | arg =>
      simp only [ttext, tsize] at hc ⊢
      rw [ih _ (by omega) k]

/-- **An argument's formatting function, with its text**: `ArgOk`, and the octets the function
    appends to the `String` are `bs`: when the `String`'s `len` octets were `txt`, its `len + n`
    octets are then `txt ++ bs`, with n = |bs|. -/
def ArgOkT (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 : Nat) (μA : Memory) (sA : State) (spA e v : Nat) (bs : List UInt8) (M C : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len ret t v5 v6 : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Keeps pb spA (fun _ => False) sA μA μ s →
    Fmtr sA s μ F W cap len →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat v5 →
    ω[6] = UInt64.ofNat v6 → ω[7] = UInt64.ofNat v → ω[8] = UInt64.ofNat F →
    v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    (S0 + 600 ≤ sp ∧ sp % 8 = 0 ∧ 2147484248 ≤ sp) → sp ≤ spA → (sp ≤ W ∧ W + 24 ≤ S1) →
    (sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →
    ∀ txt : List UInt8, μ.readN (rdN μ (W + 8) 8) len = txt →
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R e ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧ n = bs.length ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ bs) ∨
    Exhausts p R pb e ω μ x (1073741824 + C)

/-- `ArgsAt` with each argument's text: the (i + j)-th argument's function appends `bsf (i + j)`. -/
def ArgsAtT (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 : Nat) (μA : Memory) (sA : State) (spA args i : Nat) (ts : List TItem) (bsf : Nat → List UInt8) (M C : Nat) : Prop :=
  ∀ j, j < nargs ts → ∃ v fn e, spA ≤ args + 16 * (i + j) ∧ args + 16 * (i + j) + 16 < 4294967296 ∧
    (∀ a, args + 16 * (i + j) ≤ a → a < args + 16 * (i + j) + 16 → μA.readable a = true) ∧
    rdN μA (args + 16 * (i + j)) 8 = v ∧ rdN μA (args + 16 * (i + j) + 8) 8 = fn ∧
    (0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) ∧ P.jumpTable.getD (fn / 2 - 1) 0 = e ∧
    P.isBlockStart e = true ∧ ArgOkT p P R env pb S0 S1 μA sA spA e v (bsf (i + j)) M C

variable {X : Type} {R : HostRel X}

/-- `WrLoop` with the text: the `String` gains `ttext μ c ts bsf i`. -/
def WrLoopT (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 : Nat) (μA : Memory) (sA : State) (spA T W args ret t v5 v6 M C : Nat)
    (bsf : Nat → List UInt8) (ts : List TItem) : Prop :=
  ∀ (c i cap len : Nat) (ω : Regs) (μ : Memory) (x : X) (s : State),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Str sA s μ W cap len →
    Keeps pb spA (fun _ => False) sA μA μ s → WFrame μ T W args i ret v5 v6 → RoW μ →
    Tmpl μ c ts → 65536 ≤ c → c + tsize ts + 24 ≤ 196608 →
    ω[1] = UInt64.ofNat T → ω[6] = UInt64.ofNat c →
    ArgsAtT p P R env pb S0 S1 μA sA spA args i ts bsf M C → i + nargs ts < 268435456 →
    len + tlen M ts < 134217728 →
    ∀ txt : List UInt8, μ.readN (rdN μ (W + 8) 8) len = txt →
    (∃ ω' μ' x' s' cap' n, n ≤ tlen M ts ∧
      FreeStepsH p R 64600 ω μ x t ω' μ' x' (tcost M C ts + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb T (wrE T W) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (T + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ ttext μ c ts bsf i) ∨
    Exhausts p R pb 64600 ω μ x (2147483648 + tcost M C ts - 2 * cap)

/-- `wr_item` with the text. -/
theorem wr_item_text {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocCopyOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T W args ret t v5 v6 M C : Nat)
    (hT : S0 + 600 ≤ T ∧ T % 8 = 0 ∧ 2147484248 ≤ T) (hW : T + 96 ≤ W ∧ W + 24 ≤ spA ∧ W + 24 ≤ S1)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (it : TItem) (ts : List TItem) (bsf : Nat → List UInt8)
    (ih : WrLoopT p P R env pb S0 S1 μA sA spA T W args ret t v5 v6 M C bsf ts)
    (c i cap len : Nat) (ω : Regs) (μ : Memory) (x : X) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str sA s μ W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s) (hF : WFrame μ T W args i ret v5 v6) (hro : RoW μ)
    (hTm : Tmpl μ c (it :: ts)) (hc0 : 65536 ≤ c) (hc1 : c + tsize (it :: ts) + 24 ≤ 196608)
    (h1 : ω[1] = UInt64.ofNat T) (a5 : ω[5] = UInt64.ofNat it.byte) (a9 : ω[9] = UInt64.ofNat c)
    (a12 : ω[12] = UInt64.ofNat W)
    (hA : ArgsAtT p P R env pb S0 S1 μA sA spA args i (it :: ts) bsf M C) (hi : i + nargs (it :: ts) < 268435456)
    (hn : len + tlen M (it :: ts) < 134217728) (txt : List UInt8)
    (htx : μ.readN (rdN μ (W + 8) 8) len = txt) :
    (∃ ω' μ' x' s' cap' n, n ≤ tlen M (it :: ts) ∧
      FreeStepsH p R 64611 ω μ x t ω' μ' x' (tcost M C (it :: ts) - 4 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb T (wrE T W) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (T + 96) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ ttext μ c (it :: ts) bsf i) ∨
    Exhausts p R pb 64611 ω μ x (2147483648 + tcost M C (it :: ts) - 4 - 2 * cap) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → T ≤ a) → ∀ d ∈ chunks sA, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  have hts := tsize_pos ts
  cases it with
  | lit n =>
    simp only [Tmpl, tsize, tlen, tcost, nargs, TItem.byte, ttext] at hTm hc1 hn hA hi a5 ⊢
    obtain ⟨hn1, hn2, hb, hrb, hTm'⟩ := hTm
    obtain ⟨ω1, run1, a1, rfl⟩ : ∃ ω1, FreeStepsH p R 64611 ω μ x 64611 ω1 μ x 0 ∧ ω1[1] = ω[1] ∧ ω1 = ω :=
      ⟨ω, FreeStepsH.refl, rfl, rfl⟩
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7, b8, b9⟩ := wr_lit (p := p) (P := P) (R := R) x ω1 μ T W c n
      ⟨by omega, by omega⟩ (by omega) ⟨hn1, hn2⟩ (by omega) (a1.trans h1) a5 a9 a12 hF.ws
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    rcases write_str_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ sA s T W (c + 1) n cap len 2728
        64633 n (c + 1) H hba hs b0 (b1.trans (a1.trans h1)) b5 b6 b7 b8 b9 ⟨by omega, by omega⟩
        (by decide) jte_1363 bs_64633 ⟨by omega, hT.2.1, by omega⟩ ⟨by omega, hW.2.2⟩ (by omega)
        (Or.inl ⟨by omega, by omega⟩) (fun a h1 h2 => hrb a (by omega) (by omega)) txt htx with
      ⟨ω3, μ3, x3, s3, cap3, run3, H3, hb3, hs3, hc31, hc32, K3, e0, e1, e5, e6, e7, tx3⟩ | hx
    · obtain ⟨ω4, run4, f0, f1, f6⟩ := wr_lit_ret (p := p) (P := P) (R := R) x3 ω3 μ3 c n (by omega) e5 e6 e7
      have kT : ∀ a, T ≤ a → a < W → μ3.read a = μ.read a := fun a h1 h2 =>
        K3.hi a h1 (by omega) (by omega)
      have KA3 : Keeps pb spA (fun _ => False) sA μA μ3 s3 := by
        have := KA.trans' (K3.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by omega))
        rwa [Nat.max_self] at this
      have hro3 := K3.ro_low H
      have := hs3.lt
      rcases ih (c + 1 + n) i cap3 (len + n) ω4 μ3 x3 s3 H3 (by rw [hb3]; exact hba) hs3 KA3
          (hF.congr (fun a ha => kT a (by omega) (by omega))
            (by rw [rdN_frame (fun j hj => kT _ (by omega) (by omega))]; exact hF.idx))
          (hro.congr (fun a h1 h2 => hro3 a h2))
          (Tmpl.congr ts _ hTm' (by omega) hro3) (by omega) (by omega) (f1.trans e1)
          (by rw [f6]) hA hi (by omega) _ tx3 with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7, gT⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7, ?_⟩
        · have := (K3.mono (Nat.le_refl _) (fun a h => Or.inl h)).trans' (E := wrE T W) K'
          rwa [Nat.max_self] at this
        · rw [← Nat.add_assoc, gT, ttext_congr ts _ (by omega) (fun a ha => (hro3 a ha).1), List.append_assoc]
      · exact Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4) hx).mono (by omega))
    · have hle := exh_lit n (tcost M C ts) cap hcap
      exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono hle)
  | arg =>
    simp only [Tmpl, tsize, tlen, tcost, nargs, TItem.byte, ttext] at hTm hc1 hn hA hi a5 ⊢
    obtain ⟨hb, hrb, hTm'⟩ := hTm
    obtain ⟨v, fn, e, hA0, hA1, hAr, hAv, hAf, hfn, hje, hbe, hok⟩ := hA 0 (by simp only [nargs]; omega)
    rw [Nat.add_zero] at hA0 hA1 hAr hAv hAf hok
    obtain ⟨ω1, run1, a1, rfl⟩ : ∃ ω1, FreeStepsH p R 64611 ω μ x 64611 ω1 μ x 0 ∧ ω1[1] = ω[1] ∧ ω1 = ω :=
      ⟨ω, FreeStepsH.refl, rfl, rfl⟩
    have kA : ∀ a, spA ≤ a → a < 4294967296 → μ.read a = μA.read a := fun a h1 h2 => KA.hi a h1 h2 id
    obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, m48, m56, m64, fr2, rd2, wr2⟩ :=
      wr_arg (p := p) (P := P) (R := R) x ω1 μ T W c i args v fn e ⟨by omega, by omega⟩ (by omega) (by omega)
        (by omega) (a1.trans h1) a5 a9 a12 hF.opts hF.vt hF.args hF.idx
        (by rw [rdN_frame (fun j hj => kA _ (by omega) (by omega))]; exact hAv)
        (by rw [rdN_frame (fun j hj => kA _ (by omega) (by omega))]; exact hAf) hfn hje hbe
        (fun a h1 h2 => KA.readable H (by omega) (by omega) (hAr a h1 h2))
        (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
        (fun a h1 h2 => hst a (by omega) (by omega))
    have wr12 : ∀ a, μ2.writable a = μ.writable a := wr2
    have H2 : HeapCtx env pb S0 S1 μ2 s := ctx_hi H (fun a ha => fr2 a (by omega) (Or.inl (by omega))) wr12
    have K2 : Keeps pb T (wrE T W) sA μ μ2 s :=
      Keeps.of_frame (Z := fun a => T + 48 ≤ a ∧ a < T + 72) hs.base
        (fun a ha hz => fr2 a ha (by omega)) rd2 wr12 (fun a hz => hst a (by omega) (by omega))
        (fun a hz h => Or.inr (Or.inr ⟨by omega, hz.2⟩)) (fun a hz hg => by unfold Glob at hg; omega)
        (hzd _ (fun a hz => by omega))
    have KA2 : Keeps pb spA (fun _ => False) sA μA μ2 s := by
      have := KA.trans' (K2.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by
        unfold wrE at h; omega))
      rwa [Nat.max_self] at this
    have hro2 := K2.ro_low H
    have hf2 : Fmtr sA s μ2 (T + 48) W cap len :=
      ⟨m48, by rw [show T + 48 + 8 = T + 56 by omega]; exact m56,
       by rw [show T + 48 + 16 = T + 64 by omega]; exact (rdN_opts m64).1,
       by rw [show T + 48 + 20 = T + 64 + 4 by omega]; exact (rdN_opts m64).2,
       (hro.congr (fun a h1 h2 => hro2 a h2)).vws, (hro.congr (fun a h1 h2 => hro2 a h2)).vwc,
       (hro.congr (fun a h1 h2 => hro2 a h2)).vrd,
       hs.update (fun j hj => fr2 _ (by omega) (Or.inr (by omega)))
        ((rdN_frame (μ := μ) (μ' := μ2) (fun j hj => by
          rw [show W + 16 + j = W + (16 + j) by omega, fr2 _ (by omega) (Or.inr (by omega))])).trans hs.rl)
        hs.le⟩
    have hbl := buf_lt hs H
    have hle := hs.le
    have htx2 : μ2.readN (rdN μ2 (W + 8) 8) len = txt := by
      rw [rdN_frame (μ := μ) (μ' := μ2) (fun j hj => fr2 _ (by omega) (Or.inr (by omega))), ← htx]
      exact readN_congr2 fun j hj => fr2 _ (by omega) (Or.inl (by omega))
    rcases hok ω2 μ2 x s T (T + 48) W cap len 2726 64589 i (c + 1) H2 hba KA2 hf2 b0 (b1.trans (a1.trans h1))
        b5 b6 b7 b8 (by omega) (by omega) (by decide) jte_1362 bs_64589 hT (by omega) ⟨by omega, hW.2.2⟩
        ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) txt htx2 with
      ⟨ω3, μ3, x3, s3, cap3, n, hnM, run3, H3, hb3, hf3, hc31, hc32, K3, e0, e1, e5, e6, e7, hnb, tx3⟩ | hx
    · obtain ⟨ω4, μ4, run4, f0, f1, f6, fi, fr4, rd4, wr4⟩ := wr_arg_ret (p := p) (P := P) (R := R) x3 ω3 μ3 T i
        ⟨by omega, by omega⟩ (by omega) e1 e5 e7 (fun a h1 h2 => H3.st a (by omega) (by omega))
      have K4 : Keeps pb T (wrE T W) sA μ3 μ4 s3 :=
        Keeps.of_frame (Z := fun a => T + 24 ≤ a ∧ a < T + 32) hf3.str.base
          (fun a ha hz => fr4 a ha (by omega)) rd4 wr4 (fun a hz => H3.st a (by omega) (by omega))
          (fun a hz h => Or.inr (Or.inl ⟨by omega, by omega⟩)) (fun a hz hg => by unfold Glob at hg; omega)
          (fun d hd hu a ha => by
            have := chunk_bounds H3.wf (hf3.str.base d hd hu)
            have := H3.hbT
            unfold InData at ha; omega)
      have H4 : HeapCtx env pb S0 S1 μ4 s3 := ctx_hi H3 (fun a ha => fr4 a (by omega) (Or.inl (by omega))) wr4
      have K24 : Keeps pb T (wrE T W) sA μ2 μ4 s3 := by
        have := (K3.mono (Nat.le_refl _) (fun a h => Or.inl h)).trans' (E := wrE T W) K4
        rwa [Nat.max_self] at this
      have K14 : Keeps pb T (wrE T W) sA μ μ4 s3 := by
        have := K2.trans' K24
        rwa [Nat.max_self] at this
      have KA4 : Keeps pb spA (fun _ => False) sA μA μ4 s3 := by
        have := KA.trans' (K14.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by
          unfold wrE at h; omega))
        rwa [Nat.max_self] at this
      have hro4 := K14.ro_low H
      have := hf3.str.lt
      have kT : ∀ a, (T ≤ a ∧ a < T + 24) ∨ (T + 32 ≤ a ∧ a < T + 48) ∨ (T + 72 ≤ a ∧ a < T + 96) →
          μ4.read a = μ.read a := fun a ha => K14.hi a (by omega) (by omega) (by unfold wrE; omega)
      have hF4 : WFrame μ4 T W args (i + 1) ret v5 v6 := hF.congr kT fi
      have hs4 : Str sA s3 μ4 W cap3 (len + n) := hf3.str.update
        (fun j hj => fr4 _ (by omega) (Or.inr (by omega)))
        ((rdN_frame (μ := μ3) (μ' := μ4) (fun j hj => by
          rw [show W + 16 + j = W + (16 + j) by omega, fr4 _ (by omega) (Or.inr (by omega))])).trans hf3.str.rl)
        hf3.str.le
      have hbl3 := buf_lt hf3.str H3
      have htx4 : μ4.readN (rdN μ4 (W + 8) 8) (len + n) = txt ++ bsf i := by
        rw [rdN_frame (μ := μ3) (μ' := μ4) (fun j hj => fr4 _ (by omega) (Or.inr (by omega))), ← tx3]
        exact readN_congr2 fun j hj => fr4 _ (by omega) (Or.inl (by have := hf3.str.le; omega))
      rcases ih (c + 1) (i + 1) cap3 (len + n) ω4 μ4 x3 s3 H4 (by rw [hb3]; exact hba) hs4 KA4 hF4
          (hro.congr (fun a h1 h2 => hro4 a h2)) (Tmpl.congr ts _ hTm' (by omega) hro4) (by omega) (by omega)
          (f1.trans e1) (by rw [f6, e6])
          (fun j hj => by
            obtain ⟨v', fn', e', r⟩ := hA (j + 1) (by simp only [nargs]; omega)
            exact ⟨v', fn', e', by rw [show i + 1 + j = i + (j + 1) by omega]; exact r⟩)
          (by omega) (by omega) _ htx4 with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7, gT⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7, ?_⟩
        · have := K14.trans' K'
          rwa [Nat.max_self] at this
        · rw [← Nat.add_assoc, gT, ttext_congr ts _ (by omega) (fun a ha => (hro4 a ha).1), List.append_assoc]
      · exact Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4) hx).mono (by omega))
    · exact Or.inr ((Exhausts.pre (run1.trans run2) hx).mono (by omega))

/-- **The template loop, with the text** (from 64600): `WrLoopT` for every template. -/
theorem wr_loop_text {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocCopyOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA T W args ret t v5 v6 M C : Nat) (bsf : Nat → List UInt8)
    (hT : S0 + 600 ≤ T ∧ T % 8 = 0 ∧ 2147484248 ≤ T) (hW : T + 96 ≤ W ∧ W + 24 ≤ spA ∧ W + 24 ≤ S1)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    ∀ ts, WrLoopT p P R env pb S0 S1 μA sA spA T W args ret t v5 v6 M C bsf ts := by
  intro ts

  induction ts with
  | nil =>
    intro c i cap len ω μ x s H hba hs KA hF hro hTm hc0 hc1 h1 h6 _ _ _ txt htx
    have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
    have hS1 := H.hS1
    simp only [Tmpl, tsize] at hTm hc1
    obtain ⟨ω', run, e0, e1, e5, e6, e7⟩ := wr_end (p := p) (P := P) (R := R) x ω μ T c ret t v5 v6
      ⟨by omega, by omega⟩ (by omega) h1 h6 hTm.1 hF.r0 hF.r5 hF.r6 hret hjt hbt hTm.2
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    exact Or.inl ⟨ω', μ, x, s, cap, 0, Nat.le_refl _, run.mono (by simp [tcost]), H, rfl,
      by simpa using hs, Nat.le_refl _, by omega, Keeps.rebase (Keeps.refl _ _ _ _ _) hs.base,
      e0, e1, e5, e6, e7, by rw [Nat.add_zero, htx]; simp [ttext]⟩
  | cons it ts ih =>
    intro c i cap len ω μ x s H hba hs KA hF hro hTm hc0 hc1 h1 h6 hA hi hn txt htx
    have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
    have hS1 := H.hS1
    have hts := tsize_pos ts
    have htc := tcost_ge M C ts
    have hcap := hs.lt
    have hb : rdN μ c 1 = it.byte ∧ μ.readable c = true ∧ 1 ≤ it.byte := by
      cases it with
      | lit n => exact ⟨hTm.2.2.1, hTm.2.2.2.1 c (by omega) (by omega), hTm.1⟩
      | arg => exact ⟨hTm.1, hTm.2.1, by simp [TItem.byte]⟩
    have hc1' : c + 1 < 4294967296 := by cases it <;> simp [tsize] at hc1 <;> omega
    obtain ⟨ω1, run1, a0, a1, a5, a9, a12⟩ := wr_head (p := p) (P := P) (R := R) x ω μ T W c it.byte
      ⟨by omega, by omega⟩ (by omega) h1 h6 hb.1 (by omega) hF.str hb.2.1
      (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    rcases wr_item_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA T W args ret t v5 v6 M C hT hW hv
        it ts bsf ih c i cap len ω1 μ x s H hba hs KA hF hro hTm hc0 hc1 (a1.trans h1) a5 a9 a12 hA hi hn txt htx with
      ⟨ω', μ', x', s', cap', n, hn', run', rest⟩ | hx
    · have : 40 ≤ tcost M C (it :: ts) := tcost_ge M C _
      exact Or.inl ⟨ω', μ', x', s', cap', n, hn', (run1.trans run').mono (by omega), rest⟩
    · have : 40 ≤ tcost M C (it :: ts) := tcost_ge M C _
      exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`core::fmt::write` into a `String`, with the text** (64495): `fmt_write` on `ReallocCopyOk`,
    the arguments' functions `ArgOkT` with texts `bsf`; the `String`, whose `len` octets were `txt`,
    then holds `txt ++ ttext μ tp ts bsf 0`: the template's literals and the arguments' texts in
    order. -/
theorem fmt_write_text {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocCopyOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA S W tp args ret t v5 v6 M C : Nat) (ts : List TItem) (bsf : Nat → List UInt8)
    (x : X) (ω : Regs) (μ : Memory) (s : State) (cap len : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str sA s μ W cap len)
    (KA : Keeps pb spA (fun _ => False) sA μA μ s)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat 77016)
    (h9 : ω[9] = UInt64.ofNat tp) (h10 : ω[10] = UInt64.ofNat args)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : S0 + 696 ≤ S ∧ S % 8 = 0 ∧ 2147484344 ≤ S) (hW : S ≤ W ∧ W + 24 ≤ spA ∧ W + 24 ≤ S1)
    (hro : RoW μ) (hTm : Tmpl μ tp ts) (htp : 65536 ≤ tp ∧ tp + tsize ts + 24 ≤ 196608)
    (hargs : args < 18446744073709551616 ∧ args % 2 = 0)
    (hA : ArgsAtT p P R env pb S0 S1 μA sA spA args 0 ts bsf M C) (hi : nargs ts < 268435456)
    (hn : len + tlen M ts < 134217728) (txt : List UInt8)
    (htx : μ.readN (rdN μ (W + 8) 8) len = txt) :
    (∃ ω' μ' x' s' cap' n, n ≤ tlen M ts ∧
      FreeStepsH p R 64495 ω μ x t ω' μ' x' (tcost M C ts + 100 + 2 * (cap' - cap)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str sA s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧ Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ ttext μ tp ts bsf 0) ∨
    Exhausts p R pb 64495 ω μ x (2147483648 + tcost M C ts + 100) := by
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have htc := tcost_ge M C ts
  have hbl := buf_lt hs H
  have hle := hs.le
  have hzd : ∀ (Z : Nat → Prop), (∀ a, Z a → S - 96 ≤ a) → ∀ d ∈ chunks sA, d.used = true → ∀ a, InData d a →
      a < 4294967296 ∧ ¬ Z a := fun Z hZ d hd hu a ha => by
    have := chunk_bounds H.wf (hs.base d hd hu)
    have := H.hbT
    unfold InData at ha
    exact ⟨by omega, fun hz => by have := hZ a hz; omega⟩
  cases ts with
  | nil =>
    simp only [Tmpl, tsize] at hTm htp
    obtain ⟨ω1, μ1, run1, e0, e1, e5, e6, e7, fr1, rd1, wr1⟩ := wr_entry0 (p := p) (P := P) (R := R) x ω μ S tp
      args ret t v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h9 h10 ⟨hv.1, hv.2, by omega, hargs.1, hargs.2⟩ hret hjt
      hbt hTm.1 hTm.2 (by omega) (fun a h1 h2 => hst a (by omega) (by omega))
    have K1 : Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
      Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S) hs.base (fun a ha hz => fr1 a ha (by omega)) rd1 wr1
        (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
        (fun a hz hg => by unfold Glob at hg; omega) (hzd _ (fun a hz => hz.1))
    refine Or.inl ⟨ω1, μ1, x, s, cap, 0, Nat.zero_le _, run1.mono (by simp only [tcost]; omega),
      ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1, rfl, ?_, Nat.le_refl _, by omega, K1,
      e0, e1, e5, e6, e7, ?_⟩
    · rw [Nat.add_zero]
      exact hs.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
        ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
          rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
    · rw [Nat.add_zero, rdN_frame (μ := μ) (μ' := μ1) (fun j hj => fr1 _ (by omega) (Or.inr (by omega))), ← htx]
      simp only [ttext, List.append_nil]
      exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  | cons it ts =>
    have hts := tsize_pos ts
    have hb : rdN μ tp 1 = it.byte ∧ μ.readable tp = true ∧ 1 ≤ it.byte := by
      cases it with
      | lit n => exact ⟨hTm.2.2.1, hTm.2.2.2.1 tp (by omega) (by omega), hTm.1⟩
      | arg => exact ⟨hTm.1, hTm.2.1, by simp [TItem.byte]⟩
    obtain ⟨ω1, μ1, run1, a1, a5, a9, a12, m0, m8, m16, m24, m32, m40, m72, m80, m88, fr1, rd1, wr1⟩ :=
      wr_entry (p := p) (P := P) (R := R) x ω μ S W tp args it.byte ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
        h9 h10 ⟨by omega, hv.1, hv.2, by omega, by omega, hargs.1, hargs.2⟩ hb.1 (by omega) hb.2.1 (by omega) hro.vws
        (fun a h1 h2 => hro.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
    have K1 : Keeps pb S (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
      Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S) hs.base (fun a ha hz => fr1 a ha (by omega)) rd1 wr1
        (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
        (fun a hz hg => by unfold Glob at hg; omega) (hzd _ (fun a hz => hz.1))
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
    have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
      have := KA.trans' (K1.lift (sp' := spA) (E' := fun _ => False) (by omega) (fun a h h' => by omega))
      rwa [Nat.max_self] at this
    have hro1 := K1.ro_low H
    have hs1 : Str sA s μ1 W cap len := hs.update (fun j hj => fr1 _ (by omega) (Or.inr (by omega)))
      ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
    have hF1 : WFrame μ1 (S - 96) W args 0 ret v5 v6 := ⟨m0, m8, m16, m24, m32, m40, m72, m80, m88⟩
    have htx1 : μ1.readN (rdN μ1 (W + 8) 8) len = txt := by
      rw [rdN_frame (μ := μ) (μ' := μ1) (fun j hj => fr1 _ (by omega) (Or.inr (by omega))), ← htx]
      exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
    rcases wr_item_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (S - 96) W args ret t v5 v6 M C
        ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv it ts bsf
        (wr_loop_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (S - 96) W args ret t v5 v6 M C bsf
          ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv hret hjt hbt ts)
        tp 0 cap len ω1 μ1 x s H1 hba hs1 KA1 hF1 (hro.congr (fun a h1 h2 => hro1 a h2))
        (Tmpl.congr _ _ hTm (by omega) hro1) htp.1 htp.2 a1 a5 a9 a12
        (fun j hj => by obtain ⟨v', fn', e', r⟩ := hA j hj; exact ⟨v', fn', e', by rw [Nat.zero_add] at r ⊢; exact r⟩)
        (by omega) hn txt htx1 with
      ⟨ω', μ', x', s', cap', n, hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7, gT⟩ | hx
    · refine Or.inl ⟨ω', μ', x', s', cap', n, hn', (run1.trans run').mono (by omega), H', hb', hs', hc1', hc2',
        ?_, g0, by rw [g1, show S - 96 + 96 = S by omega], g5, g6, g7, ?_⟩
      swap
      · rw [gT, ttext_congr (it :: ts) _ (by omega) (fun a ha => fr1 a (by omega) (Or.inl (by omega)))]
      have := K1.trans' (K'.lift (sp' := S) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun a h h' => by
        unfold wrE at h; omega))
      rwa [Nat.max_self] at this
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
