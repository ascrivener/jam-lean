import Services.Bootstrap.Encode.EncM
import Services.Bootstrap.Encode.Prefix
import Services.Bootstrap.CodeAAll

namespace Services.Bootstrap.Encode.PrefixBig

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

theorem encodeNat_big (n l : Nat) (hl : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4)
    (hn : 2 ^ (7 * l) ≤ n ∧ n < 2 ^ (7 * (l + 1))) :
    Blob.encodeNat n = UInt8.ofNat (2 ^ 8 - 2 ^ (8 - l) + n / 2 ^ (8 * l)) :: Num.encodeLE l (n % 2 ^ (8 * l)) := by
  have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow (n := 7 * l); omega
  unfold Blob.encodeNat
  rw [ite_eq_right_of_eq_false _ _ (eq_false hn0), show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  rcases hl with rfl | rfl | rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at hn
  · simp [show ¬ n < 128 by omega, hn.1, hn.2]
  · simp [show ¬ n < 128 by omega, show ¬ n < 16384 by omega, hn.1, hn.2]
  · simp [show ¬ n < 128 by omega, show ¬ n < 16384 by omega, show ¬ n < 2097152 by omega,
      hn.1, hn.2]
  · simp [show ¬ n < 128 by omega, show ¬ n < 16384 by omega, show ¬ n < 2097152 by omega,
      show ¬ n < 268435456 by omega, hn.1, hn.2]

theorem encodeNat_small (n : Nat) (hn : 0 < n ∧ n < 128) : Blob.encodeNat n = [UInt8.ofNat n] := by
  unfold Blob.encodeNat
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show n ≠ 0 by omega)),
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp [show 1 ≤ n by omega, hn.2]
  sorry

theorem u8_eq {a b : Nat} (h : a % 256 = b % 256) : UInt8.ofNat a = UInt8.ofNat b :=
  UInt8.toNat_inj.1 (by simpa [UInt8.toNat_ofNat] using h)

/-- What `pvm_go` leaves of a run: memory goals through the writes, closed without unfolding the
    (symbolic) octet arithmetic. -/
macro "pg_fin" : tactic => `(tactic| (
  all_goals try simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same,
    PVM.Memory.readN_writeN_disjoint, PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN,
    PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  all_goals try decide))

set_option hygiene false in
/-- The register and memory goals `pvm_go` leaves for `pg`. -/
macro "pg_post" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
  rotate_left 6
  · refine (PVM.Memory.readN_writeN_same _ _ _ _ rfl (by simp [PVM.two32])).trans ?_
    exact congrArg (fun b => [b]) (u8_eq (by omega))
  all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, r16]
  pg_fin))

theorem pg {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v n l : Nat) (hl : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4)
    (hn : 2 ^ (7 * l) ≤ n ∧ n < 2 ^ (7 * (l + 1)))
    (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h2 : ω[2] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat n)
    (h8 : ω[8] = UInt64.ofNat 128)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 31029 ω μ x 58508 ω' μ' x 400 ∧
      ω'[0] = UInt64.ofNat 1470 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat (8 * l) ∧
      ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat 1 ∧
      μ'.readN (sp + 24) 1 = [UInt8.ofNat (2 ^ 8 - 2 ^ (8 - l) + n / 2 ^ (8 * l))] ∧
      μ'.readN sp 8 = Num.encodeLE 8 n ∧ μ'.readN (sp + 8) 8 = Num.encodeLE 8 l ∧
      μ'.readN (sp + 16) 8 = Num.encodeLE 8 v ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  have r16 : ∀ μ' : Memory, rdN (μ'.writeN (sp + 16) (Num.encodeLE 8 v)) (sp + 16) 8 = v := fun μ' =>
    rd8 hv (Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega))
  rcases hl with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hn ⊢ <;>
    have hn' : n < 18446744073709551616 := by omega
  · have c1 : ¬ n < 128 := by omega
    have c2 : ¬ 16384 ≤ n := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h2, h6, h8, hsp, hw, hr, hn.1, hn.2, c1, c2, Nat.mod_eq_of_lt hn', rdN_writeN_disjoint, ↓rdN_fold]
    · pg_post
  · have c1 : ¬ n < 128 := by omega
    have c1' : 128 ≤ n := by omega
    have c2 : ¬ n < 16384 := by omega
    have c3 : ¬ 2097152 ≤ n := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h2, h6, h8, hsp, hw, hr, hn.1, hn.2, c1, c1', c2, c3, Nat.mod_eq_of_lt hn', rdN_writeN_disjoint,
        ↓rdN_fold]
    · pg_post
  · have c1 : ¬ n < 128 := by omega
    have c1' : 128 ≤ n := by omega
    have c2 : ¬ n < 16384 := by omega
    have c2' : 16384 ≤ n := by omega
    have c3 : ¬ n < 2097152 := by omega
    have c4 : ¬ 268435456 ≤ n := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h2, h6, h8, hsp, hw, hr, hn.1, hn.2, c1, c1', c2, c2', c3, c4, Nat.mod_eq_of_lt hn',
        rdN_writeN_disjoint, ↓rdN_fold]
    · pg_post
  · have c1 : ¬ n < 128 := by omega
    have c1' : 128 ≤ n := by omega
    have c2 : ¬ n < 16384 := by omega
    have c2' : 16384 ≤ n := by omega
    have c3 : ¬ n < 2097152 := by omega
    have c3' : 2097152 ≤ n := by omega
    have c4 : ¬ n < 268435456 := by omega
    have c5 : ¬ 34359738368 ≤ n := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h2, h6, h8, hsp, hw, hr, hn.1, hn.2, c1, c1', c2, c2', c3, c3', c4, c5, Nat.mod_eq_of_lt hn',
        rdN_writeN_disjoint, ↓rdN_fold]
    · pg_post

end Services.Bootstrap.Encode.PrefixBig
