import Services.Bootstrap.Fmt.FieldSteps
import Services.Bootstrap.Fmt.DebugList

/-!
# Field formatters of refine's 6159 `Debug` line: the integers

With plain options, for a value where `ValAt` puts it (on the caller's stack or in an allocated
chunk); the text (the decimal digits) is not stated:

- `u32_ok`: `<u32 as Debug>::fmt` (28822) as a field passed by its address (`ArgOk`), at most 10
  octets;
- `u64_ok`: `<u64 as Debug>::fmt` (28843), `ArgOk`, at most 20 octets;
- `ref_u32_ok`: `<&u32 as Debug>::fmt` (37549) as a field passed through a slot (`RefOk`), at most
  10 octets.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`<u32 as Debug>::fmt`** (28822, plain options) as a field passed by its address: a u32 where
    `ValAt` puts it; at most 10 octets. -/
theorem u32_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 4) :
    ArgOk p P R env pb S0 S1 600 μA sA spA 28822 a 10 2710 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := f_u32 (p := p) (P := P) (R := R) x ω μ F (by omega) h8 hf.opts
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec32 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) (a7.trans h7) a8 ⟨hv5, hv6⟩ hret hjt hbt
      ⟨hsp.1, hsp.2.1, by omega⟩ hW hF ⟨by omega, by omega⟩ hra (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<u64 as Debug>::fmt`** (28843, plain options) as a field passed by its address: a u64 where
    `ValAt` puts it; at most 20 octets. -/
theorem u64_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 8) :
    ArgOk p P R env pb S0 S1 600 μA sA spA 28843 a 20 2910 := by
  intro ω μ x s sp F W cap len ret t v5 v6 H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
  have hS1 := H.hS1
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := f_u64 (p := p) (P := P) (R := R) x ω μ F (by omega) h8 hf.opts
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec64 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) (a7.trans h7) a8 ⟨hv5, hv6⟩ hret hjt hbt
      ⟨hsp.1, hsp.2.1, by omega⟩ hW hF ⟨by omega, by omega⟩ hra (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

/-- **`<&u32 as Debug>::fmt`** (37549, plain options) as a field passed through a slot: a u32
    where `ValAt` puts it; at most 10 octets. -/
theorem ref_u32_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (μA : Memory) (sA : State) (spA a : Nat) (hS : S0 ≤ spA) (ha : ValAt μA sA spA S1 a 4) :
    RefOk p P R env pb S0 S1 600 μA sA spA 37549 a 10 2710 := by
  intro ω μ x s sp F W cap len ret t v5 v6 v H hba K hf h0 h1 h5 h6 h7 h8 hv5 hv6 hret hjt hbt hsp hspA hW hWA hF hn
    hv ra
  have hS1 := H.hS1
  have hst : ∀ b, S0 ≤ b → b < S1 → μ.writable b = true := H.st
  obtain ⟨hra, hloc⟩ := ha.readable (by decide) H hS hspA K
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8⟩ := rf_u32 (p := p) (P := P) (R := R) x ω μ v F a
    ⟨by omega, by omega⟩ h7 h8 hf.opts ra (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
    (fun b h1 h2 => Memory.readable_of_writable (hst b (by omega) (by omega)))
  rcases dec32 (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ sA s sp F W a cap len ret t v5 v6 H hba hf
      (a0.trans h0) (a1.trans h1) (a5.trans h5) (a6.trans h6) a7 a8 ⟨hv5, hv6⟩ hret hjt hbt
      ⟨hsp.1, hsp.2.1, by omega⟩ hW hF ⟨by omega, by omega⟩ hra (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn', run2, rest⟩ | hx
  · exact Or.inl ⟨ω2, μ2, x2, s2, cap2, n, hn', (run1.trans run2).mono (by omega), rest⟩
  · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))

end Services.Bootstrap.Fmt
