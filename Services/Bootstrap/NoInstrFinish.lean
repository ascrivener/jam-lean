import Services.Bootstrap.ReaderBig
import Services.Bootstrap.OTail

/-!
# Bootstrap's refine on an empty instruction list: the salt's read and the output

From 58434, where the log of s and the instruction list's decode call the reader for the salt's 32
octets: the read (`read_big`) and the rest (`OTail`: the debug log of the empty output, its
encoding ℰ(`BootstrapWorkOutput { [], i }`) and the return), to the halt at 6373 with
ω₇ = 207008, ω₈ = 3 and the octets [0] ⌢ ℰ₂(i) there.
-/

namespace Services.Bootstrap.NoInstrFinish

open PVM JAM Services.Bootstrap Services.Bootstrap.Code

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

theorem finish (p : ByteArray) (P : Program) [HasCode p P] (env : RefineHost.Env) (ω : Regs) (μ : Memory)
    (I : Nat) (hI : I < 65536)
    (f0 : ω[0] = UInt64.ofNat 924)
    (f1 : ω[8] = UInt64.ofNat 4278058320)
    (f2 : ω[9] = UInt64.ofNat 32)
    (f3 : μ.readN 4278058648 8 = Num.encodeLE 8 206913)
    (f4 : μ.readN 4278058656 8 = Num.encodeLE 8 32)
    (f5 : ∀ a, 4278057688 ≤ a → a < 4278059008 → μ.writable a = true)
    (f6 : ∀ a, 196608 ≤ a → a < 208896 → μ.writable a = true)
    (g7 : ω[7] = UInt64.ofNat 4278058648)
    (f7 : ω[1] = UInt64.ofNat 4278058240)
    (f8 : ω[5] = UInt64.ofNat 4278058544)
    (f9 : μ.readN 66099 5 = [10, 82, 101, 116, 117])
    (f10 : μ.readN 66104 8 = [114, 110, 105, 110, 103, 32, 192, 16])
    (f11 : μ.readN 66112 8 = [32, 105, 110, 116, 111, 32, 97, 99])
    (f12 : μ.readN 66120 8 = [99, 117, 109, 117, 108, 97, 116, 101])
    (f13 : μ.readN 66128 1 = [0])
    (f14 : μ.readN 72826 1 = [93])
    (f15 : μ.readN 72829 1 = [91])
    (f16 : μ.readN 77040 8 = [36, 10, 0, 0, 0, 0, 0, 0])
    (f17 : μ.readN 196800 4 = [0, 0, 0, 0])
    (f18 : μ.readN 206512 4 = [128, 40, 3, 0])
    (f19 : μ.readN 206520 8 = [32, 40, 3, 0, 0, 0, 0, 0])
    (f20 : μ.readN 206528 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (f21 : μ.readN 206824 8 = [0, 0, 0, 0, 0, 0, 0, 64])
    (f22 : μ.readN 206832 8 = [0, 0, 0, 0, 32, 0, 0, 0])
    (f23 : μ.readN 206840 4 = [7, 0, 0, 0])
    (f24 : μ.readN 206848 4 = [0, 0, 0, 0])
    (f25 : μ.readN 206880 8 = [0, 0, 0, 0, 7, 0, 0, 0])
    (f26 : μ.readN 206976 8 = [3, 0, 0, 0, 250, 255, 255, 3])
    (f27 : μ.readN 206984 4 = [0, 0, 0, 0])
    (f28 : μ.readN 4278058296 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (f29 : μ.readN 4278058304 8 = [8, 0, 0, 0, 0, 0, 0, 0])
    (f30 : μ.readN 4278058312 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (f31 : μ.readN 4278058352 8 = [33, 0, 0, 0, 0, 0, 0, 0])
    (f32 : μ.readN 4278058360 8 = [160, 40, 3, 0, 0, 0, 0, 0])
    (f33 : μ.readN 4278058368 8 = [158, 0, 0, 0, 0, 0, 0, 0])
    (f34 : μ.readN 4278058464 8 = [33, 0, 0, 0, 0, 0, 0, 0])
    (f35 : μ.readN 4278058488 8 = [64, 40, 3, 0, 0, 0, 0, 0])
    (f36 : μ.readN 4278058984 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (f37 : μ.readN 4278058992 8 = [0, 0, 0, 0, 0, 0, 0, 0])
    (f38 : μ.readN 4278059000 8 = [0, 0, 255, 255, 0, 0, 0, 0])
    (f39 : μ.readN 4278058456 8 = Num.encodeLE 8 I)
    (f40 : ∀ a, 196608 ≤ a → a < 196616 → μ.writable a = true)
    (f41 : ∀ a, 196800 ≤ a → a < 196804 → μ.writable a = true)
    (f42 : ∀ a, 206512 ≤ a → a < 206516 → μ.writable a = true)
    (f43 : ∀ a, 206528 ≤ a → a < 206536 → μ.writable a = true)
    (f44 : ∀ a, 206824 ≤ a → a < 206840 → μ.writable a = true)
    (f45 : ∀ a, 206848 ≤ a → a < 206852 → μ.writable a = true)
    (f46 : ∀ a, 206880 ≤ a → a < 206896 → μ.writable a = true)
    (f47 : ∀ a, 206976 ≤ a → a < 206992 → μ.writable a = true)
    (f48 : ∀ a, 207008 ≤ a → a < 207036 → μ.writable a = true)
    (f49 : ∀ a, 207040 ≤ a → a < 207056 → μ.writable a = true)
    (f50 : ∀ a, 207072 ≤ a → a < 207088 → μ.writable a = true)
    (f51 : ∀ a, 4278058064 ≤ a → a < 4278058376 → μ.writable a = true)
    (f52 : ∀ a, 4278058496 ≤ a → a < 4278058504 → μ.writable a = true)
    (f53 : ∀ a, 4278058544 ≤ a → a < 4278058600 → μ.writable a = true)
    (f54 : ∀ a, 4278058624 ≤ a → a < 4278058680 → μ.writable a = true)
    (f55 : ∀ a, 66099 ≤ a → a < 66129 → μ.readable a = true)
    (f56 : ∀ a, 72826 ≤ a → a < 72827 → μ.readable a = true)
    (f57 : ∀ a, 72829 ≤ a → a < 72830 → μ.readable a = true)
    (f58 : ∀ a, 77040 ≤ a → a < 77048 → μ.readable a = true)
    (f59 : ∀ a, 196608 ≤ a → a < 196616 → μ.readable a = true)
    (f60 : ∀ a, 196800 ≤ a → a < 196804 → μ.readable a = true)
    (f61 : ∀ a, 206512 ≤ a → a < 206516 → μ.readable a = true)
    (f62 : ∀ a, 206520 ≤ a → a < 206536 → μ.readable a = true)
    (f63 : ∀ a, 206824 ≤ a → a < 206844 → μ.readable a = true)
    (f64 : ∀ a, 206848 ≤ a → a < 206852 → μ.readable a = true)
    (f65 : ∀ a, 206880 ≤ a → a < 206888 → μ.readable a = true)
    (f66 : ∀ a, 206976 ≤ a → a < 206988 → μ.readable a = true)
    (f67 : ∀ a, 207008 ≤ a → a < 207011 → μ.readable a = true)
    (f68 : ∀ a, 207076 ≤ a → a < 207084 → μ.readable a = true)
    (f69 : ∀ a, 4278058064 ≤ a → a < 4278058376 → μ.readable a = true)
    (f70 : ∀ a, 4278058456 ≤ a → a < 4278058472 → μ.readable a = true)
    (f71 : ∀ a, 4278058488 ≤ a → a < 4278058496 → μ.readable a = true)
    (f72 : ∀ a, 4278058544 ≤ a → a < 4278058570 → μ.readable a = true)
    (f73 : ∀ a, 4278058624 ≤ a → a < 4278058680 → μ.readable a = true)
    (f74 : ∀ a, 4278058984 ≤ a → a < 4278059008 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p (refineContract env) 58434 ω μ ((∅, []) : RefineCtx) 6373 ω' μ' ((∅, []) : RefineCtx) 2100 ∧
      ω'[0] = UInt64.ofNat 4294901760 ∧ ω'[7] = UInt64.ofNat 207008 ∧ ω'[8] = UInt64.ofNat 3 ∧
      μ'.readN 207008 3 = 0 :: Num.encodeLE 2 I ∧ (∀ a, 207008 ≤ a → a < 207011 → μ'.readable a = true) := by
  obtain ⟨ω1, μ1, run1, k0, k1, k5, k6, k7, kR0, kR8, kbuf, kfr, krd, kwr⟩ :=
    read_big (p := p) (P := P) (R := refineContract env) ((∅, []) : RefineCtx) ω μ 924 20473 4278058240
      4278058648 4278058320 206913 32 32
      f0 f7 g7 f1 f2 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_461]) bs_20473
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (fun a h1 h2 => f5 a (by omega) (by omega)) (fun a h1 h2 => f5 a (by omega) (by omega))
      (fun a h1 h2 => f5 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (f6 a (by omega) (by omega))) f3 f4
  have kfr' : ∀ a, (decide (a < 4294967296) && !(decide (4278058152 ≤ a ∧ a < 4278058240)) &&
      !(decide (4278058648 ≤ a ∧ a < 4278058664)) && !(decide (4278058320 ≤ a ∧ a < 4278058352))) = true →
      μ1.read a = μ.read a := fun a ha => by
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_and,
      Nat.not_lt] at ha
    exact kfr a (by omega) (by omega) (by omega) (by omega)
  clear kfr
  chase_prep at f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38
  refine (fun hO => ?_) (OTail.run p P env ω1 μ1 ((∅, []) : RefineCtx) I hI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · obtain ⟨ω2, μ2, run2, ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12⟩, om0, ⟨om1, om2⟩, ofr, ord, owr⟩ := hO
    refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), o0, o7, o8, ?_, fun a h1 h2 => by rw [ord]; chase⟩
    simp only [Memory.readN_succ', Memory.readN_zero', Num.encodeLE] at om1 om2 ⊢
    simp only [List.cons.injEq, and_true] at om1 om2
    simp only [om0, om1, om2, Nat.mod_mod, Nat.zero_div, List.cons.injEq, and_true]
  all_goals first | (rw [k7]) | exact (Memory.readN_of_frame kfr' 4278058456 8 rfl).trans (by assumption) | chase

end Services.Bootstrap.NoInstrFinish
