import Services.Bootstrap.Fmt.LogSteps
import Services.Bootstrap.Decode.DeallocCall
import Services.Bootstrap.Fmt.Format
import Services.Bootstrap.Refine.HostSteps

/-!
# Refine's level-3 `Debug` line after `format!` (6166 … 6209), frame-only

As `log_site` (accumulate's first line) at refine's addresses, under refine's contract: from the
return of `format_inner` (6166) with the `String` at M + 168 (`StrOut`), the `log` call (6187, the
message unspecified; `FreeStepsH.logRef`) and the `String`'s `dealloc` reach 6209 with the
allocator's context kept, `Outside` from M up, every allocated chunk of the state `format!` started
from still allocated with its data, and the context x kept.

- `rl_a`: 6166 … 6185, `log`'s arguments;
- `rl_b`: 6189 … 6202, the capacity nonzero: `dealloc` (40613) returning to 6209 (202);
- `rl_b0`: 6189 … 6194, capacity 0: on to 6209.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA Services.Bootstrap.Refine.HostSteps

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem rl_a {p : ByteArray} {P : Program} [HasCode p P] [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (hsp : sp + 192 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (hr : ∀ a, sp + 168 ≤ a → a < sp + 192 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6166 ω μ x 6187 ω' μ x 6 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = UInt64.ofNat (rdN μ (sp + 176) 8) ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hr, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 176))]

theorem rl_b {p : ByteArray} {P : Program} [HasCode p P] [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp q : Nat) (hsp : sp + 192 < 4294967296) (hq : q < 18446744073709551616) (h1 : ω[1] = UInt64.ofNat sp)
    (h5 : ω[5] = UInt64.ofNat q)
    (hcap : rdN μ (sp + 168) 8 ≠ 0) (hr : ∀ a, sp + 168 ≤ a → a < sp + 176 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6189 ω μ x 40613 ω' μ x 6 ∧
      ω'[0] = UInt64.ofNat 202 ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧ ω'[7] = UInt64.ofNat q := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, hsp, hcap, hr, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 168)), ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1, h5, Nat.mod_eq_of_lt hq]

theorem rl_b0 {p : ByteArray} {P : Program} [HasCode p P] [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp : Nat) (hsp : sp + 192 < 4294967296) (h1 : ω[1] = UInt64.ofNat sp)
    (hcap : rdN μ (sp + 168) 8 = 0) (hr : ∀ a, sp + 168 ≤ a → a < sp + 176 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 6189 ω μ x 6209 ω' μ x 3 ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, hsp, hcap, hr, Nat.mod_eq_of_lt (rdN_lt64 μ (sp + 168)), ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_⟩
    all_goals post_simp [h1]

theorem rdl_post {p : ByteArray} {P : Program} [HasCode p P]  (cap : Nat)
    (hcap : 1000 ≤ cap ∧ cap < 2 ^ 64) (envH : RefineHost.Env) (pb S0 S1 : Nat)
    (x : RefineCtx) (ω : Regs) (μ : Memory) (s₀ s : State) (sp : Nat)
    (H : HeapCtx envH pb S0 S1 μ s) (hso : StrOut s₀ s μ (sp + 168)) (h1 : ω[1] = UInt64.ofNat sp)
    (hsp : 2147483716 ≤ sp ∧ S0 + 40 ≤ sp ∧ sp + 192 ≤ S1) :
    ∃ ω' μ' s', FreeStepsH p (refineContractK cap envH) 6166 ω μ x 6209 ω' μ' x 300 ∧
      HeapCtx envH pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      ω'[1] = ω[1] ∧ ω'[6] = ω[6] := by
  have hS1 := H.hS1
  have hst := H.st
  obtain ⟨scap, slen, hs⟩ := hso
  have hr : ∀ a, sp + 168 ≤ a → a < sp + 192 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  obtain ⟨ω1, run1, a0, a1, a5, a6⟩ := rl_a (p := p) (P := P) (R := refineContractK cap envH) x ω μ sp (by omega) h1 hr
  -- the log call
  have refl : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s ∧ ∀ a, InData d a → μ.read a = μ.read a :=
    fun d hd hu => ⟨hs.base d hd hu, fun _ _ => rfl⟩
  have outR : Outside pb sp (fun _ => False) μ μ :=
    ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩
  have w1 : (setR7 ω1 Result.WHAT)[1] = UInt64.ofNat sp := by
    simp only [setR7, Vector.getElem_set]; simp [a1, h1]
  have w5 : (setR7 ω1 Result.WHAT)[5] = UInt64.ofNat (rdN μ (sp + 176) 8) := by
    simp only [setR7, Vector.getElem_set]; simp [a5]
  have w0 : (setR7 ω1 Result.WHAT)[0] = ω[0] := by simp only [setR7, Vector.getElem_set]; simp [a0]
  have w6 : (setR7 ω1 Result.WHAT)[6] = ω[6] := by simp only [setR7, Vector.getElem_set]; simp [a6]
  by_cases hc0 : scap = 0
  · subst hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6⟩ := rl_b0 (p := p) (P := P) (R := refineContractK cap envH) x
      (setR7 ω1 Result.WHAT) μ sp (by omega) w1 hs.rc (fun a h1 h2 => hr a h1 (by omega))
    refine ⟨ω2, μ, s, run1.trans (FreeStepsH.logRef cap hcap envH (d_6187 (p := p) (P := P)) run2) |>.mono (by omega), H, rfl, outR,
      refl, b1.trans (w1.trans h1.symm), b6.trans w6⟩
  · obtain ⟨c, hc, hcu, hca, -, hcf⟩ := hs.buf.resolve_left hc0
    obtain ⟨ω2, run2, b0, b1, b5, b6, b7⟩ := rl_b (p := p) (P := P) (R := refineContractK cap envH) x
      (setR7 ω1 Result.WHAT) μ sp (rdN μ (sp + 168 + 8) 8) (by omega) (rdN_lt64 μ _) w1 w5
      (by rw [hs.rc]; exact hc0) (fun a h1 h2 => hr a h1 (by omega))
    obtain ⟨ω3, μ3, run3, H3, hb3, hpg, hro, stk, hgl, keep3, c0, c1, c5, c6⟩ :=
      Decode.DeallocCall.dealloc_call (R := refineContractK cap envH) (p := p) (P := P) envH pb S0 S1 x ω2 μ s sp
        (rdN μ (sp + 168 + 8) 8) 202 6209 c H hc hcu hca b0 (b1.trans w1) b7 (by decide) jte_100 bs_6209 hsp.1
        ⟨hsp.2.1, by omega⟩
    have out3 : Outside pb sp (fun _ => False) μ μ3 :=
      ⟨fun b _ => ⟨by unfold Memory.readable; rw [hpg], by unfold Memory.writable; rw [hpg]⟩,
        fun b hb _ hw => hro b hb hw, fun a ha hb _ => stk a hb ha, hgl⟩
    refine ⟨ω3, μ3, free s (rdN μ (sp + 168 + 8) 8),
      (run1.trans (FreeStepsH.logRef cap hcap envH (d_6187 (p := p) (P := P)) (run2.trans run3))).mono (by omega),
      H3, hb3, out3, fun d hd hu => ?_, c1.trans (b1.trans (w1.trans h1.symm)),
      c6.trans (b6.trans w6)⟩
    have hd' := hs.base d hd hu
    have hne : d ≠ c := fun e => hcf d hd hu (by rw [e])
    exact keep3 d hd' hu hne

end Services.Bootstrap.Fmt
