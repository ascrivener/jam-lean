import Services.Bootstrap.Fmt.WriteText
import Services.Bootstrap.Fmt.Dec2
import Services.Bootstrap.SymExec.Dec32All

/-!
# `<u32 as fmt::Display>::fmt` with the text

`Fmt.dec32` (Fmt/Dec4.lean) runs `<u32 as Display>::fmt` with the digits unspecified. Here the
same call is stated with its text: the `String` gains exactly the octets of `Nat.repr y`, the
decimal digits of the u32 y (`decB y`, `SymExec.repr_utf8`). The run is
`SymExec.Dec32.dec32` (68146 … 61857, the digits), `pad_plain_text` (`pad_integral`'s plain
path, on `ReallocCopyOk`) and `dl_ret` (68435, the return).

The digit-pair table at 70844 is read-only data of the program. It is a hypothesis (`Table μ`).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.SymExec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<u32 as fmt::Display>::fmt`, with the text** (68146): called with the address v of a u32 y
    (ω₇), a `Formatter` F into the `String` W with plain options (ω₈), and a return address ω₀ that
    `djump` resolves to `t`, it either:
    - returns `Ok` (ω₇ = 0) to `t`, with ω₀, ω₁, ω₅, ω₆ as they were. The `String`, which held `txt`
      in its `len` octets, holds `txt ++ decB y` (`decB y` = `(Nat.repr y).toUTF8.toList`, n ≤ 10
      octets). The context is kept, and the frame `Keeps`: from sp up only W … W + 24 changes. Or
    - reaches a failed allocator call. -/
theorem dec32_text {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocCopyOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp F W v cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hf : Fmtr s₀ s μ F W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat F)
    (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 600 ≤ sp ∧ sp % 8 = 0 ∧ 2147484248 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hvv : sp ≤ v ∧ v + 4 < 4294967296) (hrv : ∀ a, v ≤ a → a < v + 4 → μ.readable a = true)
    (hn : len + 10 < 134217728) (ht : Dec32.Table μ) (txt : List UInt8)
    (htx : μ.readN (rdN μ (W + 8) 8) len = txt) :
    (∃ ω' μ' x' s' cap', (decB (rdN μ v 4)).length ≤ 10 ∧
      FreeStepsH p R 68146 ω μ x t ω' μ' x' (7 * (decB (rdN μ v 4)).length + 2 * (cap' - cap) + 2500) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧
      Fmtr s₀ s' μ' F W cap' (len + (decB (rdN μ v 4)).length) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + (decB (rdN μ v 4)).length))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + (decB (rdN μ v 4)).length) = txt ++ decB (rdN μ v 4)) ∨
    Exhausts p R pb 68146 ω μ x (1073741824 + 2700) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hbT := H.hbT
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hro : ∀ a, a < 196608 → μ.writable a = false := H.ro
  have hy : rdN μ v 4 < 4294967296 := by simpa using rdN_lt μ v 4
  generalize hyd : rdN μ v 4 = y at hy ⊢
  have hY : μ.readN v 4 = Num.encodeLE 4 y := by rw [← hyd, encodeLE_rdN]
  generalize hnd : (decB y).length = n
  -- 68146 … 61857: the digits, by the executor
  obtain ⟨ω1, μ1, run1, hn10, g0, g1, g7, g11, g12, hd, s8, s16, s24, fr1, pg1⟩ :=
    Dec32.dec32 (R := R) (p := p) (P := P) x ω μ y sp v F ret v5 v6 hy ⟨by omega, by omega⟩ (by omega)
      (by omega) ⟨by omega, by omega⟩ hv.1 hv.2 h0 h1 h5 h6 h7 h8 hY ht hrv
      (fun a h1 h2 => hf.vrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
      (Or.inr hvv.1)
  rw [hnd] at hn10 g11 g12 hd
  have rd1 : ∀ a, μ1.readable a = μ.readable a := fun a => by simp only [Memory.readable, pg1]
  have wr1 : ∀ a, μ1.writable a = μ.writable a := fun a => by simp only [Memory.writable, pg1]
  have k1 : ∀ a, a < 4294967296 → (a < sp - 72 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => k1 a (by omega) (Or.inl (by omega))) wr1
  have hf1 : Fmtr s₀ s μ1 F W cap len := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun a h1 h2 => ⟨k1 a (by omega) (Or.inl (by omega)), rd1 a⟩)
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
    Keeps.of_frame (Z := fun a => sp - 72 ≤ a ∧ a < sp) hf.str.base
      (fun a ha hz => k1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
      (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        unfold InData at ha; omega)
  -- the String's text, kept by the digits' run
  have hbl := buf_lt hf.str H
  have hle := hf.str.le
  have htx1 : μ1.readN (rdN μ1 (W + 8) 8) len = txt := by
    rw [rdN_frame (μ := μ) (μ' := μ1) (fun j hj => k1 _ (by omega) (Or.inr (by omega))), ← htx]
    exact readN_congr2 fun j hj => k1 _ (by omega) (Or.inl (by omega))
  -- 61857: pad_integral's plain path, with the text
  rcases pad_plain_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 s₀ s (sp - 72) F W
      (sp - 24 - n) n cap len 2802 68435 ω1[5].toNat ω1[6].toNat ω1[10].toNat H1 hba hf1 g0 g1
      UInt64.ofNat_toNat.symm UInt64.ofNat_toNat.symm g7 UInt64.ofNat_toNat.symm g11 g12
      ⟨UInt64.toNat_lt _, UInt64.toNat_lt _, UInt64.toNat_lt _⟩
      (by decide) jte_1400 bs_68435
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2⟩ (by omega)
      (Or.inr ⟨by omega, by omega, Or.inl (by omega)⟩)
      (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega)))
      txt htx1 with
    ⟨ω3, μ3, x3, s', cap', run3, H3, hb3, hf3, hc1, hc2, K3, e0, e1, e5, e6, e7, tx3⟩ | hx
  · have K := K1.trans' (K3.mono (sp' := sp) (by omega) (fun _ h => h))
    rw [Nat.max_self] at K
    have kk : ∀ a, sp - 72 + 48 ≤ a → a < sp → μ3.read a = μ1.read a := fun a h1 h2 =>
      K3.hi a (by omega) (by omega) (by omega)
    have rr : rdN μ3 (sp - 72 + 64) 8 = ret := by
      rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show sp - 72 + 64 = sp - 8 by omega]
      exact rdN_of_readN s8 (by omega)
    have r5 : rdN μ3 (sp - 72 + 56) 8 = v5 := by
      rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show sp - 72 + 56 = sp - 16 by omega]
      exact rdN_of_readN s16 hv.1
    have r6 : rdN μ3 (sp - 72 + 48) 8 = v6 := by
      rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show sp - 72 + 48 = sp - 24 by omega]
      exact rdN_of_readN s24 hv.2
    -- 68435: the return
    obtain ⟨ω4, run4, f0, f1, f5, f6, f7⟩ := dl_ret (p := p) (P := P) (R := R) x3 ω3 μ3 (sp - 72) ret v5 v6 t
      ⟨by omega, by omega⟩ e1 rr r5 r6 hret hjt hbt
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
    refine Or.inl ⟨ω4, μ3, x3, s', cap', hn10, ((run1.trans run3).trans run4).mono (by omega), H3, hb3,
      hf3, hc1, hc2, K, f0, by rw [f1, show sp - 72 + 72 = sp by omega], f5, f6, f7.trans e7, ?_⟩
    rw [tx3, hd]
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`{}` of a u32 with its text** (68146) as an argument: a value at v (4 octets, at or above
    spA, readable in μA); the function appends `decB (rdN μA v 4)`, the decimal digits of the u32. -/
theorem dec32T_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocCopyOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA v : Nat) (hS : S0 ≤ spA) (hv : spA ≤ v ∧ v + 4 < 4294967296)
    (hrv : ∀ a, v ≤ a → a < v + 4 → μA.readable a = true) (htA : Dec32.Table μA) :
    ArgOkT p P R env pb S0 S1 μA sA spA 68146 v (decB (rdN μA v 4)) 10 2700 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hF hn
    txt htx
  have ht : Dec32.Table μ := fun j hj => by
    rw [readN_congr2 (fun i hi => K.ro _ (by omega) (Or.inl (by unfold pageSize; omega))
      (by rw [← (K.access _ (Or.inl (by unfold pageSize; omega))).2]; exact H.ro _ (by omega)))]
    exact htA j hj
  have hvA : rdN μ v 4 = rdN μA v 4 := rdN_frame (fun j hj => K.hi _ (by omega) (by omega) id)
  rcases dec32_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω μ sA s sp F W v cap len ret t v5 v6 H hba hf
      h0 h1 h5 h6 h7 h8 ⟨hv5, hv6⟩ hret hjt hbt hsp hW hF ⟨by omega, hv.2⟩
      (fun a h1 h2 => K.readable H hS (by omega) (hrv a h1 h2)) hn ht txt htx with
    ⟨ω', μ', x', s', cap', hn10, run, H', hb', hf', hc1, hc2, K', e0, e1, e5, e6, e7, tx⟩ | hx
  · rw [hvA] at hn10 run hf' hc2 tx
    exact Or.inl ⟨ω', μ', x', s', cap', _, hn10, run.mono (by omega), H', hb', hf', hc1, hc2, K', e0, e1, e5, e6, e7, rfl, tx⟩
  · exact Or.inr hx

end Services.Bootstrap.Fmt
