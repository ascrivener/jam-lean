import Services.Bootstrap.Alloc.HeapContract
import Services.Bootstrap.Alloc.AllocWrap
import Services.Bootstrap.Alloc.AllocWrapGrow
import Services.Bootstrap.Alloc.ReallocCases

/-!
# `alloc` (40494) when the model's `alloc` succeeds, as the decoders call it

The allocator's theorems split a successful `alloc` on whether it grows the heap
(`alloc_wrap_refines`, `alloc_wrap_refines_grow`). The decoders' buffers (`finish_grow`, 32989) call
`alloc` without knowing which, so `alloc_ok` states both under one statement, and `alloc_ret` is the
return to `finish_grow`.
-/

namespace Services.Bootstrap.Decode.AllocOk

open PVM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

open Picoalloc Services.Bootstrap.Alloc JAM in
/-- **`alloc` (40494) when the model's `alloc` succeeds**, growing the heap or not: the two cases
    `alloc_wrap_refines` and `alloc_wrap_refines_grow` under one statement, for a heap bound within 14
    pages of the heap's top (as `realloc_wrap_casesG`). -/
theorem alloc_okG {p : ByteArray} {P : Program} [HasCode p P] (env : HeapHost X) (x : X)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp size al q pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s'))
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (env.rel hostCostMax) 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  by_cases hng : s'.allocated = s.allocated
  · obtain ⟨ω', μ', run, rep, wf, e7, cl, ww, stk, e0, e1, e5, e6⟩ :=
      alloc_wrap_refines (p := p) (P := P) (R := env.rel hostCostMax) (HT := 4096 * ph) (S0 := S0) (S1 := S1)
        x ω μ s s' sp size al q hwf hrep h hng h1 h7 h8 hal hal1 hs hsp hsp1 hb0 hbT hA hfo hl hHTs
        hSTk hHT (HeapPages.wrAt hp hhb hst)
    have hb' : s'.base = s.base := by
      have h' := h
      rw [alloc_one hwf.1] at h'
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := alloc1_eq h'
      simp
    exact ⟨ω', μ', run.mono (by omega), rep, wf, e7, cl,
      ⟨ph, HeapPages.of_eq hp ww, by rw [hb', hng]; exact hHT, Nat.le_refl _, hhb⟩,
      fun a h1 h2 => by rw [ww]; exact hst a h1 h2, stk, e0, e1, e5, e6⟩
  · exact alloc_wrap_refines_grow (p := p) (P := P) (hb := hb) (S0 := S0) (S1 := S1) env x ω μ s s' sp
      size al q pb ph hwf hrep hbd h48 hhb hbs h hng h1 h7 h8 hal hal1 hs hsp hsp1 hb0 hbT hA hfo hl
      (Nat.le_trans (alloc_pages hwf h hng) hcost) hHTs hSTk hSb hp hst hHT

/-- `alloc_okG` for the refine contract (`refineHeap env`). -/
theorem alloc_ok {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (x : RefineCtx)
    (ω : Regs) (μ : Memory) {hb : Nat} (s s' : State) (sp size al q pb ph : Nat) (hwf : WF s)
    (hrep : Rep μ s) (hbd : heapBounds env.code = (48, pb)) (h48 : 48 ≤ ph) (hhb : ph ≤ pb)
    (hbs : pb < 4294967296) (hcost : pb ≤ ph + 14)
    (h : alloc (growTo pb) hb 1 ((size + 31) / 32) s = some (q, s'))
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat size) (h8 : ω[8] = UInt64.ofNat al)
    (hal : 1 ≤ al) (hal1 : al ≤ 32) (hs : size + 31 < 68719476736)
    (hsp : 2147483816 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648) (hA : s.allocated < 2147483648)
    (hfo : FirstOk s) (hl : rdN μ 206848 1 = 0)
    {S0 S1 : Nat} (hHTs : 208896 ≤ 4096 * ph) (hSTk : S0 + 168 ≤ sp ∧ sp ≤ S1) (hSb : 4096 * pb ≤ S0)
    (hp : HeapPages μ 48 pb ph) (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hHT : s.base + 32 * s.allocated ≤ 4096 * ph) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 40494 ω μ x 40611 ω' μ' x 540 ∧ Rep μ' s' ∧ WF s' ∧
      ω'[7] = UInt64.ofNat q ∧ rdN μ' 206848 1 = 0 ∧
      (∃ h', HeapPages μ' 48 pb h' ∧ s'.base + 32 * s'.allocated ≤ 4096 * h' ∧ ph ≤ h' ∧ h' ≤ pb) ∧
      (∀ a, S0 ≤ a → a < S1 → μ'.writable a = true) ∧
      (∀ a, a < 4294967296 → sp ≤ a → μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] :=
  alloc_okG (p := p) (P := P) (refineHeap env) x ω μ (hb := hb) s s' sp size al q pb ph hwf hrep hbd h48 hhb hbs hcost h h1 h7 h8 hal hal1 hs hsp hsp1 hb0 hbT hA hfo hl (S0 := S0) (S1 := S1) hHTs hSTk hSb hp hst hHT

/-- 40611: `alloc`'s return, to `finish_grow` (return address 1526, the jump-table entry 33090). -/
theorem alloc_ret {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 1526) : FreeStepsH p R 40611 ω μ x 33090 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

end Services.Bootstrap.Decode.AllocOk
