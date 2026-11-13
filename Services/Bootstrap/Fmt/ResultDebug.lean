import Services.Bootstrap.Fmt.ResultDebugSteps
import Services.Bootstrap.Fmt.DebugTuple
import Services.Bootstrap.Fmt.VecDebug

/-!
# `<Result<u64, HostCallError> as fmt::Debug>::fmt` (17779), frame-only, plain options

- `ref_u64_ok`: `<&u64 as Debug>` (37589) as an entry/field (`RefOk`), the u64 on the stack;
- `ref_hce_ok`: `<&HostCallError as Debug>` (37312), the variant's name from the blob's tables
  (`HceTab`; the eight names of GP v0.8.0's host-call errors WHAT … HUH as the service names them);
- `result_ok`: the `Result` (tag octet at v, `Ok`'s u64 at v + 8, `Err`'s code at v + 1) as an
  `ArgOk`: `Ok(…)` or `Err(…)`, at most 25 octets. The text is not stated.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The `HostCallError` names' (length, address) in the blob's read-only data. -/
def hceTab : List (Nat × Nat) :=
  [(15, 68831), (11, 68846), (12, 68857), (11, 68869), (7, 68880), (6, 68887), (14, 68893), (13, 68907)]

/-- **The name tables of `HostCallError`'s `Debug`**: lengths at 68944 (8-octet words), offsets
    from 69008 at 69008 (4-octet, negative). -/
def HceTab (μ : Memory) : Prop :=
  ∀ t, t < 8 → rdN μ (68944 + 8 * t) 8 = (hceTab.getD t (0, 0)).1 ∧
    rdN μ (69008 + 4 * t) 4 = (hceTab.getD t (0, 0)).2 + 4294967296 - 69008

theorem hceTab_ok : ∀ t, t < 8 → (hceTab.getD t (0, 0)).1 ≤ 15 ∧ 65536 ≤ (hceTab.getD t (0, 0)).2 ∧
    (hceTab.getD t (0, 0)).2 + (hceTab.getD t (0, 0)).1 + 24 ≤ 77144 ∧ 69008 ≤ (hceTab.getD t (0, 0)).2 + 2147483648 ∧
    (hceTab.getD t (0, 0)).2 < 69008 := by decide

theorem hce_exh (q : Nat) (h : q ≤ 15) : 18 + (7 * q + 1073741824 + 2000) ≤ 1073741824 + 2200 := by omega

/-- Read-only words (below 196608) of the caller's memory are kept in every memory a run reaches
    keeping the caller's frame. -/
theorem ro_keep {env : RefineHost.Env} {pb S0 S1 spA : Nat} {sA s : State} {μA μ : Memory}
    (H : HeapCtx env pb S0 S1 μ s) (K : Keeps pb spA (fun _ => False) sA μA μ s) {a n : Nat}
    (ha : a + n ≤ 196608) : rdN μ a n = rdN μA a n :=
  rdN_frame (fun j hj => K.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
    (by rw [← (K.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H.ro _ (by omega)))

/-- **`<&u64 as Debug>::fmt`** (37589, plain options: the decimal digits) as an entry or field,
    for a u64 at or above spA. -/
theorem ref_u64_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : spA ≤ a ∧ a + 8 < 4294967296)
    (hra : ∀ b, a ≤ b → b < a + 8 → μA.readable b = true) :
    RefOk p P R env pb S0 S1 μA sA spA 37589 a 20 2950 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := rf_u64 (p := p) (P := P) (R := R) x ω μ v F a
    ⟨by omega, by omega⟩ h7 h8 hf.opts ra (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec64 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 ⟨hv5, hv6⟩ hret hjt hbt hsp hW hF
      ⟨by omega, ha.2⟩ (fun b h1 h2 => K.readable H hS (by omega) (hra b h1 h2)) (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<&HostCallError as Debug>::fmt`** (37312): the variant's name, at most 15 octets, for an
    error code (below 8) where `ValAt` puts it. -/
theorem ref_hce_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 1)
    (htag : rdN μA a 1 < 8) (htab : HceTab μA) :
    RefOk p P R env pb S0 S1 μA sA spA 37312 a 15 2200 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  have rt : rdN μ a 1 = rdN μA a 1 := by rw [show a = a + 0 by rfl]; exact rdN_frame (fun j hj => ha.read H K _ (by omega))
  have ht : rdN μA a 1 < 8 := htag
  obtain ⟨tL, tu⟩ := htab _ ht
  obtain ⟨b1, b2, b3, b4, b5⟩ := hceTab_ok _ ht
  generalize hceTab.getD (rdN μA a 1) (0, 0) = E at tL tu b1 b2 b3 b4 b5
  obtain ⟨EL, EN⟩ := E
  simp only at tL tu b1 b2 b3 b4 b5
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := he_a (p := p) (P := P) (R := R) x ω μ v F W a (rdN μA a 1)
    _ _ EN ⟨by omega, by omega, by omega⟩ h7 h8 ra rt ht
    ((ro_keep H K (by omega)).trans tL) ((ro_keep H K (by omega)).trans tu) ⟨by omega, by omega⟩ hf.buf hf.vt
    hf.vws hf.vrd (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))) hra
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp W
      EN EL cap len ret t v5 v6 H hba hf.str
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 a9 ⟨hv5, hv6⟩ hret hjt hbt
      ⟨by omega, hsp.2.1, by omega⟩ hW (by omega) (Or.inl ⟨by omega, by omega⟩)
      (fun b h1 h2 => hf.vrd b (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, rest⟩ | hx
  · refine Or.inl ⟨ω2, μ2, x2, s2, cap2, _, b1, (run1.trans run2).mono (by omega), H2, hb2,
      Fmtr.of_keeps hf H K2 ⟨hF.1, by omega⟩ (fun b h1 h2 h => by omega) hs2, hc1, hc2, K2, rest⟩
  · refine Or.inr ((Exhausts.pre run1 hx).mono ?_)
    exact hce_exh EL b1

/-- After `rd_ok` / `rd_err`: `debug_tuple_field1_finish` and the return, for either variant. -/
theorem res_case {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 744 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA e a Mf Cf fn nm nl vt ret' i : Nat)
    (hR : RefOk p P R env pb S0 S1 μA sA spA e a Mf Cf) (hMC : Mf ≤ 20 ∧ Cf ≤ 2950)
    (hnm : 65536 ≤ nm ∧ nm + nl + 24 ≤ 77144 ∧ 0 < nl ∧ nl ≤ 3)
    (hvt : 65536 ≤ vt ∧ vt + 32 ≤ 77144) (rfn : rdN μA (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true)
    (hr' : 0 < ret' ∧ ret' ≤ 2806 ∧ ret' % 2 = 0) (hjr : P.jumpTable.getD (ret' / 2 - 1) 0 = i)
    (hbr : P.isBlockStart i = true) (hi : i = 17856 ∨ i = 17821)
    (x : X) (ω : Regs) (μ : Memory) (s : State) (sp F W cap len ret t v5 v6 : Nat)
    (ω1 : Regs) (μ1 : Memory) (run1 : FreeStepsH p R 17779 ω μ x 62471 ω1 μ1 x 13)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (K : Keeps pb spA (fun _ => False) sA μA μ s)
    (hf : Fmtr sA s μ F W cap len)
    (a0 : ω1[0] = UInt64.ofNat ret') (a1 : ω1[1] = UInt64.ofNat (sp - 16)) (a5 : ω1[5] = UInt64.ofNat v5)
    (a6 : ω1[6] = UInt64.ofNat v6) (a7 : ω1[7] = UInt64.ofNat F) (a8 : ω1[8] = UInt64.ofNat nm)
    (a9 : ω1[9] = UInt64.ofNat nl) (a10 : ω1[10] = UInt64.ofNat (sp - 16)) (a11 : ω1[11] = UInt64.ofNat vt)
    (s8 : rdN μ1 (sp - 16 + 8) 8 = ret) (s0 : rdN μ1 (sp - 16) 8 = a)
    (fr1 : ∀ b, b < 4294967296 → (b < sp - 16 ∨ sp ≤ b) → μ1.read b = μ.read b)
    (rd1 : ∀ b, μ1.readable b = μ.readable b) (wr1 : ∀ b, μ1.writable b = μ.writable b)
    (hv5 : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) (hspA : sp ≤ spA) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hWA : W + 24 ≤ spA) (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len + 25 < 134217728) :
    (∃ ω' μ' x' s' cap' n, n ≤ 25 ∧
      FreeStepsH p R 17779 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 536890000) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 17779 ω μ x (1073741824 + 536890000) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have k1 : ∀ b, b < 4294967296 → (b < sp - 16 ∨ sp ≤ b) → μ1.read b = μ.read b := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun b hb => k1 b (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun b => sp - 16 ≤ b ∧ b < sp) hf.str.base
      (fun b hb hz => k1 b hb (by omega)) rd1 wr1 (fun b hz => hst b (by omega) (by omega))
      (fun b hz h => by omega) (fun b hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at hb; omega)
  have hf1 : Fmtr sA s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun b h1 h2 => ⟨k1 b (by omega) (Or.inl (by omega)), rd1 b⟩)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := K.trans' (K1.lift (sp' := spA) hspA (fun b h hb => by omega))
    rwa [Nat.max_self] at this
  rcases debug_tuple1 (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA e a Mf Cf fn hR x ω1 μ1 s (sp - 16)
      F W nm nl (sp - 16) vt cap len ret' i v5 v6 H1 hba hf1 KA1 a0 a1 a5 a6 a7 a8 a9 a10 a11 hv5
      ⟨hnm.1, by omega, hnm.2.2.1⟩ (fun b h1 h2 => hf1.vrd b (by omega) (by omega)) hvt
      ((ro_keep H1 KA1 (by omega)).trans rfn) hfn hje hbe s0 hr' hjr hbr ⟨by omega, by omega, by omega⟩
      ⟨by omega, hWA⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩ ⟨by omega, by omega, Or.inl (by omega)⟩
      (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := rd_r (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 16) ret t i hi
      ⟨by omega, by omega⟩ b1
      (by rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))]; exact s8) hret hjt hbt
      (fun b h1 h2 => Memory.readable_of_writable (hst2 b (by omega) (by omega)))
    have K := K1.trans' (K2.lift (sp' := sp) (by omega) (fun b h _ => h))
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, by omega, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2, hf2,
      hc1, hc2, K, c0, by rw [c1]; congr 1; omega, c5.trans b5, c6.trans b6, c7.trans b7⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<Result<u64, HostCallError> as Debug>::fmt`** (17779, plain options) as an argument: the
    `Result` at v (at or above spA, 16 octets readable in μA): its tag octet at v; if 0, `Ok` with the
    u64 at v + 8; otherwise `Err` with the error code (below 8) at v + 1. At most 25 octets. Needs
    the vtables' `fmt` words (74064: 1794, `&u64`; 74800: 1764, `&HostCallError`) and `HceTab`. -/
theorem result_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 744 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v : Nat) (hS : S0 ≤ spA) (hv : spA ≤ v ∧ v + 16 ≤ S1)
    (hrv : ∀ b, v ≤ b → b < v + 16 → μA.readable b = true)
    (herr : rdN μA v 1 ≠ 0 → rdN μA (v + 1) 1 < 8) (htab : HceTab μA)
    (hv1 : rdN μA 74064 8 = 1794) (hv2 : rdN μA 74800 8 = 1764) :
    ArgOk p P R env pb S0 S1 Z μA sA spA 17779 v 25 536890000 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have rt : rdN μ v 1 = rdN μA v 1 := by
    rw [show v = v + 0 by rfl]; exact rdN_frame (fun j hj => K.hi _ (by omega) (by omega) id)
  have hrv' : ∀ b, v ≤ b → b < v + 1 → μ.readable b = true := fun b h1 h2 => K.readable H hS (by omega) (hrv b h1 (by omega))
  by_cases h0t : rdN μA v 1 = 0
  · obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := rd_ok (p := p) (P := P)
      (R := R) x ω μ sp v F ret ⟨by omega, by omega⟩ h0 h1 h7 h8 ⟨by omega, by omega, by omega⟩ (Or.inr (by omega))
      (rt.trans h0t) hrv' (fun b h1 h2 => hst b (by omega) (by omega))
    exact res_case (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μA sA spA 37589 (v + 8) 20 2950 1794 67359 2
      74040 696 17856 (ref_u64_ok env pb S0 S1 HA HR μA sA spA (v + 8) hS ⟨by omega, by omega⟩
        (fun b h1 h2 => hrv b (by omega) (by omega))) ⟨by omega, by omega⟩ (by decide) (by decide) hv1
      (by decide) jte_896 bs_37589 (by decide) jte_347 bs_17856 (Or.inl rfl) x ω μ s sp F W cap len ret t v5 v6 ω1
      μ1 run1 H hba K hf a0 a1 (a5.trans h5) (a6.trans h6) a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 ⟨hv5, hv6⟩ hret hjt
      hbt hsp hspA hW hWA hF (by omega)
  · obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := rd_err (p := p) (P := P)
      (R := R) x ω μ sp v F ret ⟨by omega, by omega⟩ h0 h1 h7 h8 ⟨by omega, by omega, by omega⟩ (Or.inr (by omega))
      (by rw [rt]; exact h0t) hrv' (fun b h1 h2 => hst b (by omega) (by omega))
    exact res_case (p := p) (P := P) (R := R) env pb S0 S1 Z hZ HA HR μA sA spA 37312 (v + 1) 15 2200 1764 67361 3
      74776 694 17821 (ref_hce_ok env pb S0 S1 HA HR μA sA spA (v + 1) hS
        (Or.inl ⟨by omega, by omega, fun b h1 h2 => hrv b (by omega) (by omega)⟩) (herr h0t) htab)
      ⟨by omega, by omega⟩ (by decide) (by decide) hv2
      (by decide) jte_881 bs_37312 (by decide) jte_346 bs_17821 (Or.inr rfl) x ω μ s sp F W cap len ret t v5 v6 ω1
      μ1 run1 H hba K hf a0 a1 (a5.trans h5) (a6.trans h6) a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 ⟨hv5, hv6⟩ hret hjt
      hbt hsp hspA hW hWA hF (by omega)

end Services.Bootstrap.Fmt
