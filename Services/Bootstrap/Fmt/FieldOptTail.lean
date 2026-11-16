import Services.Bootstrap.Fmt.FieldOptSteps
import Services.Bootstrap.Fmt.OptionDebug

/-!
# A one-field tuple variant's tail: `debug_tuple_field1_finish`, then the return

`fo_tail`: an enum's `Debug` arm that has pushed a 16-octet frame T = sp − 16 (ω₀ at T + 8, the
field's address b at T) and set up `debug_tuple_field1_finish` (62471) with the name (nm, nl) and
the field's vtable vt, whose `fmt` word resolves to the field formatter e (a `RefOk` at b), returns
`Ok` to the caller (through the 3-instruction return i, `fo_r`) or exhausts the heap. Used by the
step-8 formatters 26905 and 36594.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem fo_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z Z' : Nat) (hZ' : 600 ≤ Z') (hZ : Z' + 144 ≤ Z) (HA : AllocOk p R env pb S0 S1)
    (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA e b M C fn e0 k nm nl vt rr i : Nat)
    (hR : RefOk p P R env pb S0 S1 Z' μA sA spA e b M C)
    (hvtA : rdN μA (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true)
    (hrr : 0 < rr ∧ rr ≤ 2806 ∧ rr % 2 = 0) (hji : P.jumpTable.getD (rr / 2 - 1) 0 = i)
    (hbi : P.isBlockStart i = true)
    (hi : i = 28781 ∨ i = 36575 ∨ i = 36635 ∨ i = 26947 ∨ i = 26982)
    (hnm : 65536 ≤ nm ∧ nm + nl + 24 ≤ 196608 ∧ 0 < nl) (hnm' : nm + nl ≤ 77144) (hvt : 65536 ≤ vt ∧ vt + 32 ≤ 77144)
    (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len0 ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (K : Keeps pb spA (fun _ => False) sA μA μ s)
    (hf : Fmtr sA s μ F W cap len0)
    (h5 : ω[5] = UInt64.ofNat v5) (h6 : ω[6] = UInt64.ofNat v6)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) (hspA : sp ≤ spA) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hWA : W + 24 ≤ spA) (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len0 + (nl + M + 2) < 134217728)
    (ω1 : Regs) (μ1 : Memory) (run1 : FreeStepsH p R e0 ω μ x 62471 ω1 μ1 x k)
    (a0 : ω1[0] = UInt64.ofNat rr) (a1 : ω1[1] = UInt64.ofNat (sp - 16)) (a5 : ω1[5] = ω[5])
    (a6 : ω1[6] = ω[6]) (a7 : ω1[7] = UInt64.ofNat F) (a8 : ω1[8] = UInt64.ofNat nm)
    (a9 : ω1[9] = UInt64.ofNat nl) (a10 : ω1[10] = UInt64.ofNat (sp - 16)) (a11 : ω1[11] = UInt64.ofNat vt)
    (s8 : rdN μ1 (sp - 16 + 8) 8 = ret) (s0 : rdN μ1 (sp - 16) 8 = b)
    (fr1 : ∀ a, a < 4294967296 → (a < sp - 16 ∨ sp ≤ a) → μ1.read a = μ.read a)
    (rd1 : ∀ a, μ1.readable a = μ.readable a) (wr1 : ∀ a, μ1.writable a = μ.writable a) :
    (∃ ω' μ' x' s' cap' n, n ≤ nl + M + 2 ∧
      FreeStepsH p R e0 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + (C + 6103 + k)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len0 + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len0 + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb e0 ω μ x (1610612736 + 7 * (nl + M) + C + 6200 + k) := by
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
  have hf1 : Fmtr sA s μ1 F W cap len0 := hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega))) (fun b h1 h2 => ⟨k1 b (by omega) (Or.inl (by omega)), rd1 b⟩)
  have KA1 : Keeps pb spA (fun _ => False) sA μA μ1 s := by
    have := K.trans' (K1.lift (sp' := spA) hspA (fun b h hb => by omega))
    rwa [Nat.max_self] at this
  rcases debug_tuple1 (p := p) (P := P) (R := R) env pb S0 S1 Z' hZ' HA HR μA sA spA e b M C fn hR
      x ω1 μ1 s (sp - 16) F W nm nl (sp - 16) vt cap len0 rr i v5 v6 H1 hba hf1 KA1 a0 a1
      (a5.trans h5) (a6.trans h6) a7 a8 a9 a10 a11 ⟨hv5, hv6⟩
      hnm (fun b h1 h2 => hf1.vrd b (by omega) (by omega)) hvt
      ((ro_keep H1 KA1 (by omega)).trans hvtA) hfn hje hbe s0 hrr hji hbi
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hWA⟩ ⟨by omega, hW.2⟩ ⟨by omega, hF.2.1, hF.2.2⟩
      ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := fo_r (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 16) ret t i
      hi ⟨by omega, by omega⟩ b1
      (by rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))]; exact s8) hret hjt hbt
      (fun b h1 h2 => Memory.readable_of_writable (hst2 b (by omega) (by omega)))
    have K := K1.trans' (K2.lift (sp' := sp) (by omega) (fun b h _ => h))
    rw [Nat.max_self] at K
    exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, hn2, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2,
      hf2, hc1, hc2, K, c0, by rw [c1]; congr 1; omega, c5.trans b5, c6.trans b6, c7.trans b7⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
