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

end Services.Bootstrap.Fmt
