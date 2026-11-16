import Services.Bootstrap.Fmt.FieldStruct1Steps
import Services.Bootstrap.Fmt.StructField1
import Services.Bootstrap.Fmt.ResultDebug
import Services.Bootstrap.Fmt.FieldCode

/-!
# One-field structs of refine's Debug line (step 8)

`s1_tail`: a `Debug` impl that has pushed a 24-octet frame T = sp − 24 (ω₀ at T + 16, the field's
address b in the slot T + 8, the field's vtable at T) and set up `debug_struct_field1_finish`
(62816), whose field formatter e is a `RefOk` at b, returns `Ok` through the return i (`s1_r`) or
exhausts the heap. `ref_item_36917_ok`: `<&Item as Debug>` (36917), `Item { key: [u8; 32] }`
(`ref_u8x32_ok`). The text is the binary's own (GP v0.8.0 does not specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem s1_tail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z Z' : Nat) (hZ' : 600 ≤ Z') (hZ : Z' + 192 ≤ Z) (HA : AllocOk p R env pb S0 S1)
    (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA e b M C fn e0 k nm nl fnm fnl vt rr i : Nat)
    (hR : RefOk p P R env pb S0 S1 Z' μA sA spA e b M C)
    (hvtA : rdN μA (vt + 24) 8 = fn)
    (hfn : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true)
    (hrr : 0 < rr ∧ rr ≤ 2806 ∧ rr % 2 = 0) (hji : P.jumpTable.getD (rr / 2 - 1) 0 = i)
    (hbi : P.isBlockStart i = true) (hi : i = 36964 ∨ i = 37114)
    (hnm : 65536 ≤ nm ∧ nm + nl + 24 ≤ 77144) (hfnm : 65536 ≤ fnm ∧ fnm + fnl + 24 ≤ 77144)
    (hvt : 65536 ≤ vt ∧ vt + 32 ≤ 77144)
    (ω : Regs) (μ : Memory) (x : X) (s : State) (sp F W cap len0 ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (K : Keeps pb spA (fun _ => False) sA μA μ s)
    (hf : Fmtr sA s μ F W cap len0)
    (h5 : ω[5] = UInt64.ofNat v5) (h6 : ω[6] = UInt64.ofNat v6)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + Z ≤ sp ∧ sp % 8 = 0 ∧ 2147483648 + Z ≤ sp) (hspA : sp ≤ spA) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hWA : W + 24 ≤ spA) (hF : sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F))
    (hn : len0 + (nl + fnl + M + 7) < 134217728)
    (ω1 : Regs) (μ1 : Memory) (run1 : FreeStepsH p R e0 ω μ x 62816 ω1 μ1 x k)
    (a0 : ω1[0] = UInt64.ofNat rr) (a1 : ω1[1] = UInt64.ofNat (sp - 24)) (a5 : ω1[5] = ω[5])
    (a6 : ω1[6] = ω[6]) (a7 : ω1[7] = UInt64.ofNat F) (a8 : ω1[8] = UInt64.ofNat nm)
    (a9 : ω1[9] = UInt64.ofNat nl) (a10 : ω1[10] = UInt64.ofNat fnm) (a11 : ω1[11] = UInt64.ofNat fnl)
    (a12 : ω1[12] = UInt64.ofNat (sp - 24 + 8))
    (s16 : rdN μ1 (sp - 24 + 16) 8 = ret) (s8 : rdN μ1 (sp - 24 + 8) 8 = b) (s0 : rdN μ1 (sp - 24) 8 = vt)
    (fr1 : ∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ1.read a = μ.read a)
    (rd1 : ∀ a, μ1.readable a = μ.readable a) (wr1 : ∀ a, μ1.writable a = μ.writable a) :
    (∃ ω' μ' x' s' cap' n, n ≤ nl + fnl + M + 7 ∧
      FreeStepsH p R e0 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + (C + 10403 + k)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Fmtr sA s' μ' F W cap' (len0 + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len0 + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb e0 ω μ x (2147483648 + 7 * (nl + fnl + M) + C + 10600 + k) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have k1 : ∀ b, b < 4294967296 → (b < sp - 24 ∨ sp ≤ b) → μ1.read b = μ.read b := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun b hb => k1 b (by omega) (Or.inl (by omega))) wr1
  have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun b => sp - 24 ≤ b ∧ b < sp) hf.str.base
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
  rcases debug_struct1 (p := p) (P := P) (R := R) env pb S0 S1 Z' hZ' HA HR μA sA spA e M C fn
      x ω1 μ1 s (sp - 24) F W nm nl fnm fnl (sp - 24 + 8) vt cap len0 rr i v5 v6
      (Or.inr ⟨b, hR, s8, by omega, by omega, Or.inl (by omega)⟩)
      H1 hba hf1 KA1 a0 a1 (a5.trans h5) (a6.trans h6) a7 a8 a9 a10 a11 a12 ⟨hv5, hv6⟩ hnm hfnm s0 hvt
      ((ro_keep H1 KA1 (by omega)).trans hvtA) hfn hje hbe hrr hji hbi
      ⟨by omega, by omega, by omega⟩ ⟨by omega, hWA⟩ (by omega) (by omega) ⟨by omega, hW.2⟩
      ⟨by omega, hF.2.1, hF.2.2⟩ (by omega) (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hf2, hc1, hc2, K2, b0, b1, b5, b6, b7⟩ | hx
  · have hst2 : ∀ a, S0 ≤ a → a < S1 → μ2.writable a = true := H2.st
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := s1_r (p := p) (P := P) (R := R) x2 ω2 μ2 (sp - 24) ret t i hi
      ⟨by omega, by omega⟩ b1
      (by rw [rdN_frame (fun j hj => K2.hi _ (by omega) (by omega) (by omega))]; exact s16) hret hjt hbt
      (fun b h1 h2 => Memory.readable_of_writable (hst2 b (by omega) (by omega)))
    have K' := K1.trans' (K2.lift (sp' := sp) (by omega) (fun b h _ => h))
    rw [Nat.max_self] at K'
    exact Or.inl ⟨ω3, μ2, x2, s2, cap2, n, hn2, (run1.trans (run2.trans run3)).mono (by omega), H2, hb2,
      hf2, hc1, hc2, K', c0, by rw [c1]; congr 1; omega, c5.trans b5, c6.trans b6, c7.trans b7⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<&Item as Debug>::fmt`** (36917, plain options) as a field or entry (`RefOk`): the slot holds
    the address a of `Item { key: [u8; 32] }`, whose 32 octets are where `ValAt` puts them. At most
    176 octets. It needs 960 octets of stack below the caller (Z) and the vtables' `fmt` words
    (76064: 1712, `&[u8; 32]`; 76000: 1788, `&u8`). -/
theorem ref_item_36917_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 960 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA)
    (helts : ∀ j, j < 32 → ValAt μA sA spA S1 (a + j) 1) (hvt : rdN μA 76064 8 = 1712)
    (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 36917 a 176 3221500000 := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 q H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hq rq
  have hS1 := H.hS1
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, s16, s8, s0, fr1, rd1, wr1⟩ :=
    s1_36917 (p := p) (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega⟩ hq.1 rq
      (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
      (fun b h1 h2 => hst b (by omega) (by omega))
  rcases s1_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 768 (by decide) (by omega) HA HR μA sA spA
      36529 a 162 2147632648 1712 36917 14 68737 4 68757 3 76040 1748 36964
      (ref_u8x32_ok env pb S0 S1 768 (by decide) HA HR μA sA spA a hS helts hrvt)
      hvt (by decide) jte_855 bs_36529F (by decide) jte_873 bs_36964 (Or.inl rfl) (by decide) (by decide)
      (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF
      (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 a12 s16 s8 s0 fr1 rd1 wr1 with
    ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

end Services.Bootstrap.Fmt
