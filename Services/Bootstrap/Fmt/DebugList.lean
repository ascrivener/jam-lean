import Services.Bootstrap.Fmt.DebugListSteps
import Services.Bootstrap.Fmt.DebugRefSteps
import Services.Bootstrap.Fmt.Dec8
import Services.Bootstrap.Fmt.Template

/-!
# `Formatter::debug_list` and its `entry` and `finish`, frame-only

A `DebugList` at D (24 octets, in the caller's frame): the `Formatter` F at D + 0, the result
octet D + 8 (0: `Ok`) and the has-entries octet D + 9 (`DL μ D F h`).

- `debug_list_new` (61708): `"["`, then the `DebugList` at D with no entry;
- `debug_entry` (66019): `", "` after the first entry, then the entry's `Debug::fmt`;
- `debug_finish` (66310): `"]"`.

Each either returns `Ok` with the `String` longer by at most the octets stated (their values are not
stated), the allocator's context kept and from sp up only the `String` and the `DebugList`
changed; or reaches a failed allocator call. Plain options only (no `{:#?}`).

An entry is formatted through a reference: `debug_entry` is given the address v of a slot holding
the entry's address a, and the entry's `fmt` reads the slot. `RefOk e a M C`: a function e that,
called that way, writes at most M octets in 7M + C steps, as `ArgOk` does for an argument.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- **A `DebugList` at D**: the `Formatter` F, the result `Ok`, h entries so far (0 or 1). -/
structure DL (μ : Memory) (D F h : Nat) : Prop where
  fm : rdN μ D 8 = F
  ok : rdN μ (D + 8) 1 = 0
  has : rdN μ (D + 9) 1 = h

/-- What a `DebugList` run changes from sp up: the `String` W and the `DebugList` D. -/
def dlE (W D a : Nat) : Prop := (W ≤ a ∧ a < W + 24) ∨ (D ≤ a ∧ a < D + 10)

variable {X : Type} {R : HostRel X}

/-- A `Formatter` carried over a run that keeps the frame from sp (F at or above sp, outside the
    changed octets E) and leaves a `String` at W. -/
theorem Fmtr.of_keeps {env : RefineHost.Env} {pb S0 S1 sp : Nat} {E : Nat → Prop} {s₀ s s₁ s' : State}
    {μ μ' : Memory} {F W cap len cap' len' : Nat} (hf : Fmtr s₀ s μ F W cap len) (H : HeapCtx env pb S0 S1 μ s)
    (K : Keeps pb sp E s₁ μ μ' s') (hF : sp ≤ F ∧ F + 24 < 4294967296) (hE : ∀ a, F ≤ a → a < F + 24 → ¬ E a)
    (hs : Str s₀ s' μ' W cap' len') : Fmtr s₀ s' μ' F W cap' len' := by
  have kF : ∀ a, F ≤ a → a < F + 24 → μ'.read a = μ.read a := fun a h1 h2 =>
    K.hi a (by omega) (by omega) (hE a h1 h2)
  have kro : ∀ a, 65536 ≤ a → a < 77144 → μ'.read a = μ.read a := fun a h1 h2 =>
    K.ro a (by omega) (Or.inl (by unfold pageSize; omega)) (H.ro a (by omega))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, hs⟩
  · rw [show F = F + 0 by rfl, rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.buf
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.vt
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.opts
  · rw [rdN_frame (fun j hj => kF _ (by omega) (by omega))]; exact hf.width
  · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vws
  · rw [rdN_frame (fun j hj => kro _ (by omega) (by omega))]; exact hf.vwc
  · rw [(K.access a (Or.inl (by unfold pageSize; omega))).1]; exact hf.vrd a h1 h2

/-- **`Formatter::debug_list`** (61708): from the `Formatter` F into W (`Fmtr`), the call writes
    `"["` and builds the `DebugList` at D (in the caller's frame, at or above sp) with no entry. -/
theorem debug_list_new {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W D cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat D) (h8 : ω[8] = UInt64.ofNat F)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 600 ≤ sp ∧ sp % 8 = 0 ∧ 2147484248 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hD : sp ≤ D ∧ D + 24 ≤ S1 ∧ (D + 24 ≤ W ∨ W + 24 ≤ D) ∧ (D + 24 ≤ F ∨ F + 24 ≤ D))
    (hn : len + 1 < 134217728) :
    (∃ ω' μ' x' s' cap', FreeStepsH p R 61708 ω μ x t ω' μ' x' (2 * (cap' - cap) + 2100) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr s₀ s' μ' F W cap' (len + 1) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + 1))) ∧ DL μ' D F 0 ∧
      Keeps pb sp (dlE W D) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6) ∨
    Exhausts p R pb 61708 ω μ x (1073741824 + 2100) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, s16, s8, s0, fr1, rd1, wr1⟩ := dl_a (p := p) (P := P) (R := R)
    x ω μ sp D F W ret v5 v6 ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8
    ⟨by omega, hv.1, hv.2, by omega, by omega⟩ (Or.inr hF.1) hf.buf hf.vt hf.vws
    (fun a h1 h2 => Memory.readable_of_writable (hst a (by omega) (by omega)))
    (fun a h1 h2 => hf.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
  have k1 : ∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have hs1 : Str s₀ s μ1 W cap len := (hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)).str
  have K1 : Keeps pb sp (dlE W D) s₀ μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 24 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 s₀ s (sp - 24) W 72829 1 cap len 2622
      61746 F D H1 hba hs1 a0 a1 a5 a6 a7 a8 a9 ⟨by omega, by omega⟩ (by decide) jte_1310 bs_61746
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ hn (Or.inl ⟨by omega, by omega⟩)
      (fun a h1 h2 => by rw [rd1]; exact hf.vrd a (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    have kk : ∀ o, o + 8 ≤ 24 → rdN μ2 (sp - 24 + o) 8 = rdN μ1 (sp - 24 + o) 8 := fun o ho =>
      rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))
    obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, dF, d8, d9, fr3, rd3, wr3⟩ := dl_b (p := p) (P := P) (R := R) x2 ω2 μ2
      (sp - 24) D F ret t v5 v6 ⟨by omega, by omega⟩ b1 b5 b6 b7 (by omega)
      ⟨by omega, Or.inr (by omega)⟩ ((kk 16 (by omega)).trans s16) ((kk 8 (by omega)).trans s8)
      ((show sp - 24 = sp - 24 + 0 by rfl) ▸ (kk 0 (by omega)).trans s0) hret hjt hbt
      (fun a h1 h2 => Memory.readable_of_writable (hst2 a (by omega) (by omega)))
      (fun a h1 h2 => hst2 a (by omega) (by omega))
    have K3 : Keeps pb sp (dlE W D) s₀ μ2 μ3 s2 :=
      Keeps.of_frame (Z := fun a => D ≤ a ∧ a < D + 10) hs2.base
        (fun a ha hz => fr3 a ha (by omega)) rd3 wr3 (fun a hz => hst2 a (by omega) (by omega))
        (fun a hz h => Or.inr hz) (fun a hz hg => by unfold Glob at hg; omega)
        (fun c hc hu a ha => by
          have := chunk_bounds H2.wf (hs2.base c hc hu)
          have := H2.hbT
          unfold InData at ha; omega)
    have H3 : HeapCtx env pb S0 S1 μ3 s2 := ctx_hi H2 (fun a ha => fr3 a (by omega) (Or.inl (by omega))) wr3
    have K := (K1.trans' (K2.mono (sp' := sp) (by omega) (fun a h => Or.inl h))).trans' K3
    simp only [Nat.max_self] at K
    have hs3 : Str s₀ s2 μ3 W cap2 (len + 1) :=
      hs2.update (fun j hj => fr3 _ (by omega) (by omega))
        ((rdN_frame (fun j hj => fr3 _ (by omega) (by omega))).trans hs2.rl) hs2.le
    have hf3 : Fmtr s₀ s2 μ3 F W cap2 (len + 1) :=
      Fmtr.of_keeps hf H K ⟨hF.1, by omega⟩ (fun a h1 h2 h => by unfold dlE at h; omega) hs3
    refine Or.inl ⟨ω3, μ3, x2, s2, cap2, ((run1.trans run2).trans run3).mono (by omega), H3, hb2, hf3, hc1, hc2,
      ⟨dF, d8, d9⟩, K, c0, by rw [c1]; congr 1; omega, c5, c6⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
