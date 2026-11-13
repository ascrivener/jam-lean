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

/-- **An entry's `Debug::fmt`, called through a reference**: as `ArgOk`, with ω₇ the address v of a
    slot (at or above sp) holding the entry's address a. -/
def RefOk (p : ByteArray) (P : Program) {X : Type} (R : HostRel X) (env : RefineHost.Env)
    (pb S0 S1 : Nat) (μA : Memory) (sA : State) (spA e a M C : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len ret t v5 v6 v : Nat),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → Keeps pb spA (fun _ => False) sA μA μ s →
    Fmtr sA s μ F W cap len →
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat sp → ω[5] = UInt64.ofNat v5 →
    ω[6] = UInt64.ofNat v6 → ω[7] = UInt64.ofNat v → ω[8] = UInt64.ofNat F →
    v5 < 18446744073709551616 → v6 < 18446744073709551616 →
    (0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) → P.jumpTable.getD (ret / 2 - 1) 0 = t →
    P.isBlockStart t = true →
    (S0 + 600 ≤ sp ∧ sp % 8 = 0 ∧ 2147484248 ≤ sp) → sp ≤ spA → (sp ≤ W ∧ W + 24 ≤ S1) →
    (sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →
    (sp ≤ v ∧ v + 8 ≤ S1 ∧ (v + 8 ≤ W ∨ W + 24 ≤ v)) → rdN μ v 8 = a →
    (∃ ω' μ' x' s' cap' n, n ≤ M ∧
      FreeStepsH p R e ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + C) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb e ω μ x (1073741824 + C)

/-- **Where a value of n octets lies**, readable from the caller's (μA, sA, spA): at or above spA
    and readable in μA, or in the data of an allocated chunk of sA. -/
def ValAt (μA : Memory) (sA : State) (spA S1 a n : Nat) : Prop :=
  (spA ≤ a ∧ a + n ≤ S1 ∧ ∀ b, a ≤ b → b < a + n → μA.readable b = true) ∨
  (∃ c ∈ chunks sA, c.used = true ∧ ∀ j, j < n → InData c (a + j))

/-- An allocated chunk's data is writable (as `LoopA.heap_writable_data`, for any S0, S1). -/
theorem data_writable {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {c : Chunk} (hc : c ∈ chunks s) (hu : c.used = true) {a : Nat}
    (ha : InData c a) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hsp := H.wf.2.2.2.2.2.2.2
  unfold SpaceOk at hsp
  have h1 := (hsp c hc).1 hu
  have ht := H.wf.2.2.2.1
  unfold TilesOk at ht
  have hm := ht.mem_lt c hc
  have := H.hb0
  unfold InData at ha
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega

/-- A value where `ValAt` puts it is readable, and lies above sp or below the heap's top, in every
    memory a run reaches keeping the caller's frame. -/
theorem ValAt.readable {env : RefineHost.Env} {pb S0 S1 spA sp a n : Nat} {sA s : State} {μA μ : Memory}
    (h : ValAt μA sA spA S1 a n) (hn : 0 < n) (H : HeapCtx env pb S0 S1 μ s) (hS : S0 ≤ spA) (hsp : sp ≤ spA)
    (K : Keeps pb spA (fun _ => False) sA μA μ s) :
    (∀ b, a ≤ b → b < a + n → μ.readable b = true) ∧ ((sp ≤ a ∧ a + n ≤ S1) ∨ a + n ≤ 2147483648) := by
  rcases h with ⟨h1, h2, h3⟩ | ⟨c, hc, hu, hd⟩
  · exact ⟨fun b hb1 hb2 => K.readable H hS (by omega) (h3 b hb1 hb2), Or.inl ⟨by omega, h2⟩⟩
  · have hc' := K.used c hc hu
    refine ⟨fun b hb1 hb2 => Memory.readable_of_writable (data_writable H hc' hu (by
      have := hd (b - a) (by omega); rwa [show a + (b - a) = b by omega] at this)), ?_⟩
    have := chunk_bounds H.wf hc'
    have := H.hbT
    have h1 := hd (n - 1) (by omega)
    unfold InData at h1
    right; omega

/-- **`<&u8 as Debug>::fmt`** (37527, plain options: the octet's decimal digits) as an entry, for an
    octet where `ValAt` puts it. -/
theorem ref_u8_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 1) :
    RefOk p P R env pb S0 S1 μA sA spA 37527 a 3 2300 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
    hv ra
  have hS1 := H.hS1
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by omega) H hS hspA K
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := rf_u8 (p := p) (P := P) (R := R) x ω μ v F a
    ⟨by omega, by omega⟩ h7 h8 hf.opts
    ra (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec8 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 ⟨hv5, hv6⟩ hret hjt hbt hsp hW hF
      ⟨by omega, by omega⟩ hra (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
