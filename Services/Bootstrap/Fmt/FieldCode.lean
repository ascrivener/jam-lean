import Services.Bootstrap.Fmt.FieldOptTail
import Services.Bootstrap.Fmt.U8x32

/-!
# `<&Code as Debug>::fmt` (26905), step 8

The field of `Instr` tag 17 whose type is an enum with an octet tag at a: tag 0 is `Hash` with the
32 octets at a + 1 (`ref_u8x32_ok`, 36529), any other tag is `Inline` with the `Vec<u8>` at a + 8
(`ref_vec_u8_ok`, 26807); each as a one-field tuple (`debug_tuple1` through `fo_tail`). The text is
the binary's own (GP v0.8.0 does not specify Debug output).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 36529 is a block start (a `CodeF` fact without a named lemma). -/
theorem bs_36529F {p : ByteArray} {P : Program} [h : HasCodeF p P] : P.isBlockStart 36529 = true :=
  h.ok.blockStart (show CodeFact.blockStart 36529 true ∈ Services.Bootstrap.CodeF.facts from
    List.mem_flatten_of_mem (List.mem_flatten_of_mem
      (List.getElem_mem (l := Services.Bootstrap.CodeF.factGroups) (n := 13) (by decide))
      (List.getElem_mem (l := Services.Bootstrap.CodeF.factGroup_13) (n := 46) (by decide)))
      (List.getElem_mem (l := Services.Bootstrap.CodeF.facts_878) (n := 0) (by decide)))

/-- **`<&Code as Debug>::fmt`** (26905, plain options) as a field (`RefOk`): the slot holds the
    address a of the enum, whose tag octet is where `ValAt` puts it. Tag 0 (`Hash`): the 32 octets at
    a + 1 are where `ValAt` puts them. Otherwise (`Inline`): the `Vec<u8>` (cap, ptr, len) at a + 8
    and its len octets are where `ValAt` puts them. At most 5·len + 168 octets. It needs 912 octets
    of stack below the caller (Z) and the vtables' `fmt` words (75552: 1712, `&[u8; 32]`;
    75744: 1250, `&Vec<u8>`; 76000: 1788, `&u8`). -/
theorem ref_code_26905_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 Z : Nat) (hZ : 912 ≤ Z) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a ptr len : Nat) (hS : S0 ≤ spA) (hv : ValAt μA sA spA S1 a 1)
    (hhash : rdN μA a 1 = 0 → ∀ j, j < 32 → ValAt μA sA spA S1 (a + 1 + j) 1)
    (hinl : rdN μA a 1 ≠ 0 →
      ValAt μA sA spA S1 (a + 8) 24 ∧ rdN μA (a + 8 + 8) 8 = ptr ∧ rdN μA (a + 8 + 16) 8 = len ∧
      (∀ j, j < len → ValAt μA sA spA S1 (ptr + j) 1) ∧ ptr + len < 4294967296)
    (hvh : rdN μA 75552 8 = 1712) (hvi : rdN μA 75744 8 = 1250) (hrvt : rdN μA 76000 8 = 1788) :
    RefOk p P R env pb S0 S1 Z μA sA spA 26905 a (5 * len + 168) (2684354560 + 4600 * len + 200000) := by
  intro ω μ x s sp F W cap len0 ret t v5 v6 q H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hq rq
  have hS1 := H.hS1
  have hst : ∀ c, S0 ≤ c → c < S1 → μ.writable c = true := H.st
  obtain ⟨hra, hla⟩ := hv.readable (by decide) H hS hspA K
  have hrq : ∀ b, q ≤ b → b < q + 8 → μ.readable b = true :=
    fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega))
  have rt : rdN μ a 1 = rdN μA a 1 := rdN_frame (fun j hj => hv.read H K j hj)
  have hw : ∀ c, sp - 16 ≤ c → c < sp → μ.writable c = true := fun c h1 h2 => hst c (by omega) (by omega)
  by_cases ht : rdN μA a 1 = 0
  · have hal : a + 16 < 4294967296 := by
      obtain ⟨-, h⟩ := (hhash ht 31 (by omega)).readable (by decide) H hS hspA K
      omega
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := e26_hash (p := p)
      (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega, hal⟩ hq.1 (by omega) rq (rt.trans ht) hrq hra hw
    rcases fo_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 768 (by decide) (by omega) HA HR μA sA spA
        36529 (a + 1) 162 2147632648 1712 26905 14 67902 4 75528 1262 26982
        (ref_u8x32_ok env pb S0 S1 768 (by decide) HA HR μA sA spA (a + 1) hS (hhash ht) hrvt)
        hvh (by decide) jte_855 bs_36529F (by decide) jte_630 bs_26982 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (by decide) (by decide) (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret hjt hbt
        hsp hspA hW hWA hF (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 with
      ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
    · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
    · exact Or.inr (hx.mono (by omega))
  · obtain ⟨hvec, rp, rl, helts, hpl⟩ := hinl ht
    have hal : a + 16 < 4294967296 := by
      obtain ⟨-, h⟩ := hvec.readable (by decide) H hS hspA K
      omega
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, s8, s0, fr1, rd1, wr1⟩ := e26_inline (p := p)
      (P := P) (R := R) x ω μ sp q a F ret ⟨by omega, by omega⟩ h0 h1 h7 h8
      ⟨by omega, by omega, by omega, hal⟩ hq.1 (by omega) rq (by rw [rt]; exact ht) hrq hra hw
    rcases fo_tail (p := p) (P := P) (R := R) env pb S0 S1 Z 768 (by decide) (by omega) HA HR μA sA spA
        26807 (a + 8) (5 * len + 2) (2147483648 + 4500 * len + 5000) 1250 26905 14 68258 6 75720 1260 26947
        (ref_vec_u8_ok env pb S0 S1 768 (Nat.le_refl _) HA HR μA sA spA (a + 8) ptr len hS hvec rp rl helts hpl
          hrvt)
        hvi (by decide) jte_624 bs_26807 (by decide) jte_629 bs_26947 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (by decide) (by decide) (by decide) ω μ x s sp F W cap len0 ret t v5 v6 H hba K hf h5 h6 hv5 hv6 hret hjt hbt
        hsp hspA hW hWA hF (by omega) ω1 μ1 run1 a0 a1 a5 a6 a7 a8 a9 a10 a11 s8 s0 fr1 rd1 wr1 with
      ⟨ω', μ', x', s', cap', n, hn', run, rest⟩ | hx
    · exact Or.inl ⟨ω', μ', x', s', cap', n, by omega, run.mono (by omega), rest⟩
    · exact Or.inr (hx.mono (by omega))

end Services.Bootstrap.Fmt
