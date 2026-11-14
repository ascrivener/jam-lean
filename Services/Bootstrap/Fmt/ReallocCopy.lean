import Services.Bootstrap.Fmt.Frame

/-!
# The allocator's call contracts for any code, and `realloc` keeping the old data

`Frame.lean` states `AllocOk` / `ReallocOk`, one call of the allocator's `alloc` / `realloc`
wrapper, under the refine host's code (`HeapCtx env`). Here the same statements are taken over
`HeapCtxC code` for any code, so that they serve accumulate's contract too (`AllocOkC`,
`ReallocOkC`). The refine versions are these at `env.code` (`AllocOk_iff`, `ReallocOk_iff`).

`ReallocCopyOkC` is `ReallocOkC` plus the data copy that Rust's `GlobalAlloc::realloc` promises:
the new block's first min(old data size, new size) octets are the old block's. The old block c's
data area is its 32 · (c.size − 1) octets after the 32-octet header. A `Vec` or `String` whose
contents (len ≤ capacity octets) are written before a growth therefore keeps them across it, for
example `format!`'s text across a mid-format reallocation.

This file only *defines* `ReallocCopyOkC` / `ReallocCopyOk`, with the weakenings
`ReallocCopyOkC.toReallocOkC` / `ReallocCopyOk.toReallocOk`. The instances for the bootstrap
service's code under refine's and accumulate's contracts are proved separately.

These are allocator facts of the bootstrap service binary (`Services/Bootstrap`). The paper
(GP v0.8.0) fixes only the PVM (Appendix A) and the host calls (Appendix B) they run under.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

/-- `AllocOk` for any code `code`: one call of the `alloc` wrapper (40494 → 40611), the context
    being `HeapCtxC code`. -/
def AllocOkC (p : ByteArray) {X : Type} (R : HostRel X) (code : ByteArray) (pb S0 S1 : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp size al : Nat),
    HeapCtxC code pb S0 S1 μ s → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat size →
    ω[8] = UInt64.ofNat al → 1 ≤ al → al ≤ 32 → size + 31 < 68719476736 → 2147483816 ≤ sp →
    S0 + 168 ≤ sp → sp ≤ S1 →
    (∃ ptr s' ω' μ' x', FreeStepsH p R 40494 ω μ x 40611 ω' μ' x' 540 ∧
      HeapCtxC code pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Keeps pb sp (fun _ => False) s μ μ' s' ∧
      (⟨ptr - 32, (size + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d.addr ≠ ptr - 32) ∧ 32 ≤ ptr ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (∃ ω' μ' x', FreeStepsH p R 40494 ω μ x 40611 ω' μ' x' 540 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ∃ hb, alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)

/-- `ReallocOk` for any code `code`: one call of the `realloc` wrapper (40701 → 40821), the
    context being `HeapCtxC code`. -/
def ReallocOkC (p : ByteArray) {X : Type} (R : HostRel X) (code : ByteArray) (pb S0 S1 : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp ptr al size : Nat) (c : Chunk),
    HeapCtxC code pb S0 S1 μ s → s.base % 8 = 0 → c ∈ chunks s → c.used = true → c.addr + 32 = ptr →
    0 < size → size < 536870912 →
    ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat ptr → ω[9] = UInt64.ofNat al →
    ω[10] = UInt64.ofNat size → 1 ≤ al → al ≤ 32 → 2147483968 ≤ sp → sp % 8 = 0 →
    S0 + 320 ≤ sp → sp ≤ S1 →
    (∃ r s' ω' μ' x', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x' (64 * (c.size - 1) + 1300) ∧
      HeapCtxC code pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = r ∧ d.size = (size + 31) / 32 + 1 ∧
        (d.addr = c.addr ∨ ∀ e ∈ chunks s, e.used = true → e.addr ≠ d.addr)) ∧
      ω'[7] = UInt64.ofNat r ∧ ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (∃ ω' μ' x', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x' (64 * (c.size - 1) + 1300) ∧
      ω'[7] = UInt64.ofNat 0 ∧
      ∃ hb, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none)

/-- **`realloc` keeps the old data**: `ReallocOkC`, and on success the new block at `r` starts with
    the old block's first min(32 · (c.size − 1), size) octets (its whole data area, or the new
    size if smaller). This is `GlobalAlloc::realloc`'s contract. -/
def ReallocCopyOkC (p : ByteArray) {X : Type} (R : HostRel X) (code : ByteArray) (pb S0 S1 : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp ptr al size : Nat) (c : Chunk),
    HeapCtxC code pb S0 S1 μ s → s.base % 8 = 0 → c ∈ chunks s → c.used = true → c.addr + 32 = ptr →
    0 < size → size < 536870912 →
    ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat ptr → ω[9] = UInt64.ofNat al →
    ω[10] = UInt64.ofNat size → 1 ≤ al → al ≤ 32 → 2147483968 ≤ sp → sp % 8 = 0 →
    S0 + 320 ≤ sp → sp ≤ S1 →
    (∃ r s' ω' μ' x', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x' (64 * (c.size - 1) + 1300) ∧
      HeapCtxC code pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = r ∧ d.size = (size + 31) / 32 + 1 ∧
        (d.addr = c.addr ∨ ∀ e ∈ chunks s, e.used = true → e.addr ≠ d.addr)) ∧
      (∀ i, i < min (32 * (c.size - 1)) size → μ'.read (r + i) = μ.read (ptr + i)) ∧
      ω'[7] = UInt64.ofNat r ∧ ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (∃ ω' μ' x', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x' (64 * (c.size - 1) + 1300) ∧
      ω'[7] = UInt64.ofNat 0 ∧
      ∃ hb, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none)

/-- `ReallocCopyOkC` under the refine host's code. -/
abbrev ReallocCopyOk (p : ByteArray) {X : Type} (R : HostRel X) (env : RefineHost.Env) (pb S0 S1 : Nat) :
    Prop :=
  ReallocCopyOkC p R env.code pb S0 S1

/-- The refine host's `AllocOk` is `AllocOkC` at its code. -/
theorem AllocOk_iff {p : ByteArray} {X : Type} {R : HostRel X} {env : RefineHost.Env} {pb S0 S1 : Nat} :
    AllocOk p R env pb S0 S1 ↔ AllocOkC p R env.code pb S0 S1 := Iff.rfl

/-- The refine host's `ReallocOk` is `ReallocOkC` at its code. -/
theorem ReallocOk_iff {p : ByteArray} {X : Type} {R : HostRel X} {env : RefineHost.Env} {pb S0 S1 : Nat} :
    ReallocOk p R env pb S0 S1 ↔ ReallocOkC p R env.code pb S0 S1 := Iff.rfl

/-- Dropping the data copy: `ReallocCopyOkC` gives `ReallocOkC`. -/
theorem ReallocCopyOkC.toReallocOkC {p : ByteArray} {X : Type} {R : HostRel X} {code : ByteArray}
    {pb S0 S1 : Nat} (h : ReallocCopyOkC p R code pb S0 S1) : ReallocOkC p R code pb S0 S1 := by
  intro ω μ x s sp ptr al size c H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17
  rcases h ω μ x s sp ptr al size c H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 with
    ⟨r, s', ω', μ', x', run, hc, hb, ho, hk, hd, _, h7, h0, h1, h5, h6⟩ | hf
  · exact Or.inl ⟨r, s', ω', μ', x', run, hc, hb, ho, hk, hd, h7, h0, h1, h5, h6⟩
  · exact Or.inr hf

/-- Dropping the data copy under the refine host: `ReallocCopyOk` gives `ReallocOk`. -/
theorem ReallocCopyOk.toReallocOk {p : ByteArray} {X : Type} {R : HostRel X} {env : RefineHost.Env}
    {pb S0 S1 : Nat} (h : ReallocCopyOk p R env pb S0 S1) : ReallocOk p R env pb S0 S1 :=
  ReallocOk_iff.2 (ReallocCopyOkC.toReallocOkC h)

end Services.Bootstrap.Fmt
