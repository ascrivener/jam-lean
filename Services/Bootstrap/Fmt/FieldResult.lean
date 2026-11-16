import Services.Bootstrap.Fmt.FieldResultSteps
import Services.Bootstrap.Fmt.FieldVecItem
import Services.Bootstrap.Fmt.FieldOptTail
import Services.Bootstrap.Fmt.Field

/-!
# `<&Result<Output, ()> as Debug>::fmt` (36654), step 8

The field of `Instr` tag 22: `Ok(Output { items })` (`ref_output_37067_ok`: a one-field struct
whose field is the `Vec<Item>` at the same address, `ref_vecitem_26504_ok`) or `Err(())`
(`unit_37571_ok`), each as a one-field tuple (`fo_tail`). The text is the binary's own (GP v0.8.0
does not specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<() as Debug>::fmt`** (37571, plain options) as a field (`RefOk`): `"()"` (the field's
    address is not read). At most 2 octets. -/
theorem unit_37571_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) :
    RefOk p P R env pb S0 S1 600 μA sA spA 37571 a 2 2100 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  obtain ⟨ω0, run0, z0, z1, z5, z6, z7, z8, z9⟩ := u37571 (p := p) (P := P) (R := R) x ω μ F (by omega) h8
  obtain ⟨ω1, μ1, run1', a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ := pad_str (p := p) (P := P) (R := R)
    x ω0 μ sp F W ret v5 v6 68930 2 ⟨by omega, by omega⟩ (z0.trans h0) (z1.trans h1) (z5.trans h5) (z6.trans h6) z7
    z8 z9 ⟨by omega, hv5, hv6, by omega, by omega, by omega⟩ (Or.inr hF.1) hf.buf hf.vt hf.opts hf.vws hf.vrd
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => hst b (by omega) (by omega))
  have run1 := run0.trans run1'
  have k1 : ∀ c, c < 4294967296 → (c < sp - 24 ∨ sp ≤ c) → μ1.read c = μ.read c := fr1
  have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun c hc => k1 c (by omega) (Or.inl (by omega))) wr1
  have hs1 : Str sA s μ1 W cap len := (hf.congr (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun j hj => k1 _ (by omega) (Or.inr (by omega)))
    (fun c h1 h2 => ⟨k1 c (by omega) (Or.inl (by omega)), rd1 c⟩)).str
  have K1 : Keeps pb sp (fun c => W ≤ c ∧ c < W + 24) sA μ μ1 s :=
    Keeps.of_frame (Z := fun c => sp - 24 ≤ c ∧ c < sp) hf.str.base
      (fun c hc hz => k1 c hc (by omega)) rd1 wr1 (fun c hz => hst c (by omega) (by omega))
      (fun c hz h => by omega) (fun c hz hg => by unfold Glob at hg; omega)
      (fun c hc hu b hb => by
        have := chunk_bounds H.wf (hf.str.base c hc hu)
        have := H.hbT
        unfold InData at hb; omega)
  rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 sA s sp W 68930 2 cap len ret t v5 v6
      H1 hba hs1 a0 a1 a5 a6 a7 a8 a9 ⟨hv5, hv6⟩ hret hjt hbt ⟨by omega, hsp.2.1, by omega⟩ hW (by omega)
      (Or.inl ⟨by omega, by omega⟩) (fun b h1 h2 => by rw [rd1]; exact hf.vrd b (by omega) (by omega)) with
    ⟨ω2, μ2, x2, s2, cap2, run2, H2, hb2, hs2, hc1, hc2, K2, rest⟩ | hx
  · have K := K1.trans' K2
    rw [Nat.max_self] at K
    refine Or.inl ⟨ω2, μ2, x2, s2, cap2, 2, Nat.le_refl _, (run1.trans run2).mono (by omega), H2, hb2,
      Fmtr.of_keeps hf H K ⟨hF.1, by omega⟩ (fun b h1 h2 h => by omega) hs2, hc1, hc2, K, rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<&Output as Debug>::fmt`** (37067, plain options) as a field (`RefOk`): the slot holds the
    address a of `Output { items: Vec<Item> }` (the `Vec` at a, its 32-octet `Item`s where `ValAt`
    puts them). At most 178 · len + 20 octets. It needs 1320 octets of stack below the caller (Z)
    and the vtables' `fmt` words (76192: 1226, `&Vec<Item>`; 75840: 1746; 76064: 1712; 76000: 1788). -/
theorem ref_output_37067_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 1320 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a ptr len : Nat) (hS : S0 ≤ spA)
    (hv : ValAt μA sA spA S1 a 24) (rp : rdN μA (a + 8) 8 = ptr) (rl : rdN μA (a + 16) 8 = len)
    (hel : ∀ j, j < len → ∀ i, i < 32 → ValAt μA sA spA S1 (ptr + 32 * j + i) 1)
    (hpl : ptr + 32 * len < 4294967296) (hvo : rdN μA 76192 8 = 1226) (hvt : rdN μA 75840 8 = 1746)
    (hvk : rdN μA 76064 8 = 1712) (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 37067 a (178 * len + 20) (6442755472 + 3221528830 * len) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 q H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hq rq
  have hS1 := H.hS1
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, s16, s8, s0, fr1, rd1, wr1⟩ :=
    s1_37067 (p := p) (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega⟩ hq.1 rq
      (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
      (fun b h1 h2 => hst b (by omega) (by omega))
  rcases s1_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 1128 (by decide) (by omega) HA HR μA sA spA
      26504 a (178 * len + 2) (5368983648 + 3221527584 * len + 10000)
      1226 37067 14 68760 6 68766 5 76168 1756 37114
      (ref_vecitem_26504_ok env pb S0 S1 1128 (Nat.le_refl _) HA HR μA sA spA a ptr len hS hv rp rl hel hpl hvt hvk
        hrvt)
      hvo (by decide) jte_612 bs_26504 (by decide) jte_877 bs_37114 (Or.inr rfl) (by decide) (by decide)
      (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF
      (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 a12 s16 s8 s0 fr1 rd1 wr1 with
    ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
  · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
  · exact Or.inr (hx.mono (by omega))

/-- **`<&Result<Output, ()> as Debug>::fmt`** (36654, plain options) as a field (`RefOk`): the slot
    holds the address a of the `Result`, whose first word is where `ValAt` puts it; 2⁶⁴ − 1 is `Err(())`,
    otherwise `Ok(Output)` with the `Output` at a as `ref_output_37067_ok` needs. At most
    178 · len + 24 octets. It needs 1464 octets of stack below the caller (Z) and the vtables' `fmt`
    words (76480: 1754, `&Output`; 76512: 1792, `()`; 76192: 1226; 75840: 1746; 76064: 1712;
    76000: 1788). -/
theorem ref_result_36654_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 1464 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a ptr len : Nat) (hS : S0 ≤ spA) (hv8 : ValAt μA sA spA S1 a 8)
    (hok : rdN μA a 8 ≠ 18446744073709551615 →
      ValAt μA sA spA S1 a 24 ∧ rdN μA (a + 8) 8 = ptr ∧ rdN μA (a + 16) 8 = len ∧
      (∀ j, j < len → ∀ i, i < 32 → ValAt μA sA spA S1 (ptr + 32 * j + i) 1) ∧ ptr + 32 * len < 4294967296)
    (hvr : rdN μA 76480 8 = 1754) (hvu : rdN μA 76512 8 = 1792)
    (hvo : rdN μA 76192 8 = 1226) (hvt : rdN μA 75840 8 = 1746)
    (hvk : rdN μA 76064 8 = 1712) (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 36654 a (178 * len + 24) (7000000000 + 3221530076 * len) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 q H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hq rq
  have hS1 := H.hS1
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  obtain ⟨hra, hla⟩ := hv8.readable (by decide) H hS hspA K
  have hrq : ∀ b, q ≤ b → b < q + 8 → μ.readable b = true :=
    fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))
  have rt : rdN μ a 8 = rdN μA a 8 := by rw [show a = a + 0 by rfl, hv8.rdN H K (by omega)]
  have hw : ∀ c, sp - 16 ≤ c → c < sp → μ.writable c = true := fun c h1 h2 => hst c (by omega) (by omega)
  by_cases he : rdN μA a 8 = 18446744073709551615
  · obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := r36_err (p := p)
      (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega, by omega⟩ hq.1 (by omega) rq (rt.trans he) hrq hra hw
    rcases fo_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 600 (by decide) (by omega) HA HR μA sA spA
        37571 a 2 2100 1792 36654 12 68934 3 76488 1726 36724
        (unit_37571_ok env pb S0 S1 HA HR μA sA spA a)
        hvu (by decide) jte_895 bs_37571 (by decide) jte_862 bs_36724
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
        (by decide) (by decide) (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret hjt hbt
        hsp hspA hW hWA hF (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 with
      ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
    · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
    · exact Or.inr (hx.mono (by omega))
  · obtain ⟨hv, rp, rl, hel, hpl⟩ := hok he
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := r36_ok (p := p)
      (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega, by omega⟩ hq.1 (by omega) rq (by rw [rt]; exact he) hrq hra hw
    rcases fo_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 1320 (by decide) (by omega) HA HR μA sA spA
        37067 a (178 * len + 20) (6442755472 + 3221528830 * len) 1754 36654 12 68932 2 76456 1724 36693
        (ref_output_37067_ok env pb S0 S1 1320 (Nat.le_refl _) HA HR μA sA spA a ptr len hS hv rp rl hel hpl hvo
          hvt hvk hrvt)
        hvr (by decide) jte_876 bs_37067 (by decide) jte_861 bs_36693
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
        (by decide) (by decide) (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret hjt hbt
        hsp hspA hW hWA hF (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 with
      ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
    · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
    · exact Or.inr (hx.mono (by omega))

end Services.Bootstrap.Fmt
