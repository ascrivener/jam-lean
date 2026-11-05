import Services.Bootstrap.DecodeU16
import PVM.Logic.Chase

/-!
# `memcpy` in bootstrap for any length (in progress)

The compiler's `memcpy` at 68729 for n ≥ 16: a head loop aligning the destination (68763), then an
aligned word loop (68804) or, when the source is misaligned by m, a loop splicing the high 8 − m
octets of one aligned source word with the low m of the next (68989), then the byte loop at 68840.
This file holds the arithmetic of the splice (`encodeLE_splice`) and the loops' summaries.
-/

namespace PVM

open Num Exec

/-- Or of a value below 2^k and a multiple of 2^k (below 2^64) is their sum. -/
theorem bitwise_or_add (x y k : Nat) (hk : k ≤ 64) (hx : x < 2 ^ k) (hy : y < 2 ^ (64 - k)) :
    bitwise (· || ·) x (y * 2 ^ k) = x + y * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e1 : x + y * 2 ^ k = 2 ^ k * y + x := by rw [Nat.mul_comm]; omega
  have e2 : y * 2 ^ k = 2 ^ k * y + 0 := by rw [Nat.mul_comm]; omega
  simp only [bitwise, Num.testBit_ofBits, Num.bit_eq_testBit]
  rw [e1, e2, Nat.testBit_two_pow_mul_add _ hx, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos k)]
  by_cases hi : i < k
  · simp only [hi, ite_true, Nat.zero_testBit, Bool.or_false]
    simp only [show i < 64 by omega, decide_true, Bool.true_and]
  · have hxi : x.testBit i = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [hi, ite_false, hxi, Bool.false_or]
    by_cases h64 : i < 64
    · simp [h64]
    · have : y.testBit (i - k) = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h64, this]

theorem decodeLE_append (l₁ l₂ : List UInt8) :
    Num.decodeLE (l₁ ++ l₂) = Num.decodeLE l₁ + 256 ^ l₁.length * Num.decodeLE l₂ := by
  induction l₁ with
  | nil => simp [Num.decodeLE]
  | cons b l ih =>
    simp only [List.cons_append, Num.decodeLE, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length)]
    omega

theorem decodeLE_lt (l : List UInt8) : Num.decodeLE l < 256 ^ l.length := by
  induction l with
  | nil => simp [Num.decodeLE]
  | cons b l ih =>
    simp only [Num.decodeLE, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt
    omega

theorem encodeLE_decodeLE (l : List UInt8) : Num.encodeLE l.length (Num.decodeLE l) = l := by
  induction l with
  | nil => simp [Num.encodeLE]
  | cons b l ih =>
    have hb := b.toNat_lt
    simp only [List.length_cons, Num.encodeLE, Num.decodeLE]
    rw [show (b.toNat + 256 * Num.decodeLE l) % 256 = b.toNat by omega,
      show (b.toNat + 256 * Num.decodeLE l) / 256 = Num.decodeLE l by omega, ih, UInt8.ofNat_toNat]

theorem encodeLE_mod (l v : Nat) : Num.encodeLE l (v % 256 ^ l) = Num.encodeLE l v := by
  induction l generalizing v with
  | zero => simp [Num.encodeLE]
  | succ l ih =>
    simp only [Num.encodeLE]
    rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, ih,
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _)]

/-- The misaligned word of `memcpy`: the high 8 − m octets of `a`, then the low m of `b`. -/
theorem encodeLE_splice (a b : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (m : Nat)
    (hm : 0 < m ∧ m < 8) :
    Num.encodeLE 8 (bitwise (· || ·) (Num.decodeLE a / 2 ^ (8 * m))
      (Num.decodeLE b * 2 ^ (64 - 8 * m) % 18446744073709551616)) = a.drop m ++ b.take m := by
  have hA : Num.decodeLE a = Num.decodeLE (a.take m) + 256 ^ m * Num.decodeLE (a.drop m) := by
    conv => lhs; rw [← List.take_append_drop m a]
    rw [decodeLE_append, List.length_take, ha, Nat.min_eq_left (by omega)]
  have hB : Num.decodeLE b = Num.decodeLE (b.take m) + 256 ^ m * Num.decodeLE (b.drop m) := by
    conv => lhs; rw [← List.take_append_drop m b]
    rw [decodeLE_append, List.length_take, hb, Nat.min_eq_left (by omega)]
  have p256 : ∀ j, (256 : Nat) ^ j = 2 ^ (8 * j) := fun j => by rw [Nat.pow_mul]
  have hat := decodeLE_lt (a.take m)
  have had := decodeLE_lt (a.drop m)
  have hbt := decodeLE_lt (b.take m)
  rw [List.length_take, ha, Nat.min_eq_left (by omega)] at hat
  rw [List.length_drop, ha] at had
  rw [List.length_take, hb, Nat.min_eq_left (by omega)] at hbt
  rw [p256] at hat had hbt
  rw [show 8 * (8 - m) = 64 - 8 * m by omega] at had
  have hH : Num.decodeLE a / 2 ^ (8 * m) = Num.decodeLE (a.drop m) := by
    rw [hA, p256, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hat, Nat.zero_add]
  have h64 : (2 : Nat) ^ 64 = 2 ^ (8 * m) * 2 ^ (64 - 8 * m) := by rw [← Nat.pow_add]; congr 1; omega
  have hL : Num.decodeLE b * 2 ^ (64 - 8 * m) % 18446744073709551616 =
      Num.decodeLE (b.take m) * 2 ^ (64 - 8 * m) := by
    rw [show (18446744073709551616 : Nat) = 2 ^ 64 by rfl, h64, Nat.mul_mod_mul_right, hB, p256,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbt]
  rw [hH, hL, bitwise_or_add _ _ _ (by omega) had
    (by rw [show 64 - (64 - 8 * m) = 8 * m by omega]; exact hbt)]
  have hs := Services.Bootstrap.Num.encodeLE_split (8 - m) m (Num.decodeLE (a.drop m) + Num.decodeLE (b.take m) * 2 ^ (64 - 8 * m))
  rw [show 8 - m + m = 8 by omega] at hs
  rw [hs, ← encodeLE_mod (8 - m), p256, show 8 * (8 - m) = 64 - 8 * m by omega,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt had,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt had, Nat.zero_add]
  have e1 := encodeLE_decodeLE (a.drop m)
  have e2 := encodeLE_decodeLE (b.take m)
  rw [List.length_drop, ha] at e1
  rw [List.length_take, hb, Nat.min_eq_left (by omega)] at e2
  rw [e1, e2]

end PVM

namespace PVM

theorem bitwise_or_comm (a b : Nat) : Exec.bitwise (· || ·) a b = Exec.bitwise (· || ·) b a := by
  simp only [Exec.bitwise, Bool.or_comm]

theorem bitwise_lt (f : Bool → Bool → Bool) (a b : Nat) : Exec.bitwise f a b < 18446744073709551616 :=
  Num.ofBits_lt 64 _

theorem bitwise_mod64 (f : Bool → Bool → Bool) (a b : Nat) :
    Exec.bitwise f a b % 18446744073709551616 = Exec.bitwise f a b := Nat.mod_eq_of_lt (bitwise_lt f a b)

/-- Or of an 8-aligned value and a value below 8 is their sum. -/
theorem bitwise_or_low8 (X m : Nat) (hX : X % 8 = 0) (hm : m < 8) (hX64 : X < 18446744073709551616) :
    Exec.bitwise (· || ·) X m = X + m := by
  rw [bitwise_or_comm, show X = X / 8 * 2 ^ 3 by omega, bitwise_or_add m (X / 8) 3 (by omega) (by omega) (by omega)]
  omega

/-- A sign-extending load of n octets, folded (as `sx8`), so the sign is never split. -/
def sxw (n v : Nat) : Nat := Exec.u64 (Num.signed n v)

theorem loadI_fold (n v : Nat) : Exec.u64 (Num.signed n v) = sxw n v := rfl

theorem sxw_mod (n v : Nat) (hn : n = 2 ∨ n = 4) (hv : v < 2 ^ (8 * n)) :
    sxw n v % 256 ^ n = v % 256 ^ n := by
  rcases hn with rfl | rfl <;>
  · simp only [sxw, Exec.u64, Num.unsigned, Num.signed, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at *
    split <;> omega

/-- Storing the low n octets of a sign-extended n-octet value gives the value back. -/
theorem encodeLE_sxw (n v : Nat) (hn : n = 2 ∨ n = 4) (hv : v < 2 ^ (8 * n)) :
    Num.encodeLE n (sxw n v) = Num.encodeLE n v := by
  rw [← encodeLE_mod n (sxw n v), ← encodeLE_mod n v, sxw_mod n v hn hv]

/-- An n-octet load, folded so `pvm_simp` keeps it whole. -/
def rdN (μ : Memory) (a n : Nat) : Nat := Num.decodeLE (μ.readN a n)

theorem rdN_fold (μ : Memory) (a n : Nat) : Num.decodeLE (μ.readN a n) = rdN μ a n := rfl

theorem rdN_lt (μ : Memory) (a n : Nat) : rdN μ a n < 256 ^ n := by
  have := decodeLE_lt (μ.readN a n); rwa [Memory.length_readN] at this

theorem rdN_lt64 (μ : Memory) (a : Nat) : rdN μ a 8 < 18446744073709551616 := rdN_lt μ a 8

theorem rdN_mod64 (μ : Memory) (a : Nat) : rdN μ a 8 % 18446744073709551616 = rdN μ a 8 :=
  Nat.mod_eq_of_lt (rdN_lt64 μ a)

theorem encodeLE_rdN (μ : Memory) (a n : Nat) : Num.encodeLE n (rdN μ a n) = μ.readN a n := by
  have := encodeLE_decodeLE (μ.readN a n); rwa [Memory.length_readN] at this

theorem store_rd1 (μ : Memory) (a : Nat) :
    [UInt8.ofNat (rdN μ a 1 % 18446744073709551616 % 256)] = μ.readN a 1 := by
  have h := rdN_lt μ a 1
  simp only [Nat.pow_one] at h
  rw [Nat.mod_eq_of_lt (show rdN μ a 1 < 18446744073709551616 by omega), Nat.mod_eq_of_lt h,
    ← encodeLE_rdN μ a 1]
  simp [Num.encodeLE, Nat.mod_eq_of_lt h]

theorem store_rd2 (μ : Memory) (a : Nat) :
    Num.encodeLE 2 (sxw 2 (rdN μ a 2) % 18446744073709551616 % 65536) = μ.readN a 2 := by
  have := rdN_lt μ a 2
  have h := sxw_mod 2 (rdN μ a 2) (Or.inl rfl) (by simpa using this)
  rw [← encodeLE_rdN μ a 2, ← encodeLE_mod 2 (sxw 2 (rdN μ a 2) % 18446744073709551616 % 65536),
    ← encodeLE_mod 2 (rdN μ a 2)]
  congr 1
  simp only [Nat.reducePow] at h ⊢
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]
  exact h

theorem store_rd4 (μ : Memory) (a : Nat) :
    Num.encodeLE 4 (sxw 4 (rdN μ a 4) % 18446744073709551616 % 4294967296) = μ.readN a 4 := by
  have := rdN_lt μ a 4
  have h := sxw_mod 4 (rdN μ a 4) (Or.inr rfl) (by simpa using this)
  rw [← encodeLE_rdN μ a 4, ← encodeLE_mod 4 (sxw 4 (rdN μ a 4) % 18446744073709551616 % 4294967296),
    ← encodeLE_mod 4 (rdN μ a 4)]
  congr 1
  simp only [Nat.reducePow] at h ⊢
  rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]
  exact h

theorem read_writeN_single (μ : Memory) (a c : Nat) (b : UInt8) (h : c = a) :
    (μ.writeN a [b]).read c = b := by
  subst h; simp [Memory.writeN, Memory.read, Memory.write]

theorem readN_congr2 {μ μ' : Memory} {a b n : Nat} (h : ∀ j, j < n → μ'.read (a + j) = μ.read (b + j)) :
    μ'.readN a n = μ.readN b n := by
  simp only [Memory.readN]
  apply List.map_congr_left
  intro j hj
  exact h j (List.mem_range.mp hj)

theorem read_write_eq' (μ : Memory) (a c : Nat) (b : UInt8) (h : c = a) : (μ.write a b).read c = b := by
  subst h; simp [Memory.read, Memory.write]

theorem read_write_ne' (μ : Memory) (a c : Nat) (b : UInt8) (h : c ≠ a) (ha : a < 4294967296)
    (hc : c < 4294967296) : (μ.write a b).read c = μ.read c :=
  Memory.read_write_of_ne μ b (by simp only [two32]; rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]; omega)

theorem read_congr_addr (μ : Memory) (a b : Nat) (h : a = b) : μ.read a = μ.read b := by rw [h]

theorem ofNat_eq_iff (e : Nat) (b : UInt8) : UInt8.ofNat e = b ↔ e % 256 = b.toNat := by
  constructor
  · intro h; subst h; simp [UInt8.toNat_ofNat]
  · intro h; apply UInt8.toNat_inj.mp; rw [UInt8.toNat_ofNat']; exact h

/-- `encodeLE_splice` for words given as values below 2^64. -/
theorem encodeLE_splice' (pw T m : Nat) (hm : 0 < m ∧ m < 8) (hpw : pw < 18446744073709551616)
    (hT : T < 18446744073709551616) :
    Num.encodeLE 8 (Exec.bitwise (· || ·) (pw / 2 ^ (8 * m)) (T * 2 ^ (64 - 8 * m) % 18446744073709551616)) =
      (Num.encodeLE 8 pw).drop m ++ (Num.encodeLE 8 T).take m := by
  have := encodeLE_splice (Num.encodeLE 8 pw) (Num.encodeLE 8 T) (Num.length_encodeLE _ _)
    (Num.length_encodeLE _ _) m hm
  rw [Num.decodeLE_encodeLE, Num.decodeLE_encodeLE] at this
  rwa [show pw % 2 ^ (8 * 8) = pw from Nat.mod_eq_of_lt hpw,
    show T % 2 ^ (8 * 8) = T from Nat.mod_eq_of_lt hT] at this

theorem readN_drop (μ : Memory) (a n m : Nat) : (μ.readN a n).drop m = μ.readN (a + m) (n - m) := by
  apply List.ext_getElem
  · simp [Memory.length_readN]
  · intro j h1 h2
    simp only [List.getElem_drop, Memory.readN, List.getElem_map, List.getElem_range, Nat.add_assoc]

theorem readN_take (μ : Memory) (a n m : Nat) (h : m ≤ n) : (μ.readN a n).take m = μ.readN a m := by
  apply List.ext_getElem
  · simp [Memory.length_readN]; omega
  · intro j h1 h2
    simp only [List.getElem_take, Memory.readN, List.getElem_map, List.getElem_range]

end PVM

namespace Services.Bootstrap

/-- Octets of a word assembled from copies: `μ'.readN a n = μ.readN b n` index by index, each read
    stepping back through the writes (copies by their source, others by disjointness). -/
macro "copy_bytes" : tactic => `(tactic| (
  apply PVM.readN_congr2
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  obtain h | h | h | h | h | h | h | h := this <;> subst h <;>
  (try omega) <;>
  (try simp (disch := omega) only [PVM.Memory.writeN_cons, PVM.Memory.writeN_nil, PVM.read_write_eq',
    PVM.read_write_ne']) <;>
  (try (apply PVM.read_congr_addr; omega))))

open Lean Elab Tactic Meta in
/-- `pvm_go [hs]`: step a `FreeStepsH p R i … i' …` goal one decoded instruction at a time
    (`d_i` from the code facts, each step's equation by `pvm_simp [hs]`) until the pc is `i'`,
    then close it with `FreeStepsH.refl`. -/
elab "pvm_go" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  for _ in [0:400] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let args := t.getAppArgs
    unless t.getAppFn.constName? == some ``PVM.FreeStepsH && args.size ≥ 12 do
      throwError "pvm_go: not a FreeStepsH goal"
    let some i := (← whnfR args[3]!).nat? | throwError "pvm_go: symbolic pc {args[3]!}"
    let j? := (← instantiateMVars args[7]!).nat?
    if j? == some i then
      evalTactic (← `(tactic| first | exact PVM.FreeStepsH.refl | exact PVM.FreeStepsH.refl.mono (by omega)))
      return
    let nm := mkIdent (Name.mkSimple s!"d_{i}")
    let pId := mkIdent `p
    let PId := mkIdent `P
    evalTactic (← `(tactic| apply PVM.FreeStepsH.step_decode ($nm (p := $pId) (P := $PId))))
    evalTactic (← `(tactic| · pvm_simp [$hs,*]))
  throwError "pvm_go: too many steps"

open PVM Services.Bootstrap.Code

set_option maxHeartbeats 8000000

variable {X : Type} {R : HostRel X}

/-- One iteration of the head loop at 68763: copy the octet at `s` to `d`, count down. -/
theorem memcpy_head_iter {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (k s d : Nat) (hC : ω[12] = UInt64.ofNat (k + 1)) (hS : ω[5] = UInt64.ofNat s)
    (hD : ω[6] = UInt64.ofNat d) (hk : k + 1 < 16) (hs : s + k + 1 < 4294967296)
    (hd : d + k + 1 < 4294967296) (hr : μ.readable s = true) (hw : μ.writable d = true) :
    ∃ ω', FreeStepsH p R 68763 ω μ x 68777 ω' (μ.writeN d [μ.read s]) x 6 ∧
      ω'[12] = UInt64.ofNat k ∧ ω'[5] = UInt64.ofNat (s + 1) ∧ ω'[6] = UInt64.ofNat (d + 1) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 10, 12] → ω'[j] = ω[j] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run =>
      apply FreeStepsH.step_decode (d_68763 (p := p) (P := P))
      · pvm_simp []
      apply FreeStepsH.step_decode (d_68764 (p := p) (P := P))
      · pvm_simp [hS, hr]
      apply FreeStepsH.step_decode (d_68766 (p := p) (P := P))
      · pvm_simp [hC]
      apply FreeStepsH.step_decode (d_68769 (p := p) (P := P))
      · pvm_simp [hD, hw]
      apply FreeStepsH.step_decode (d_68771 (p := p) (P := P))
      · pvm_simp [hD]
      apply FreeStepsH.step_decode (d_68774 (p := p) (P := P))
      · pvm_simp [hS]
      exact FreeStepsH.refl
  case post =>
    refine ⟨?r9, ?r8, ?r10, fun j hj => ?rest⟩
    case rest =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3, h4⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3, h4]
    all_goals simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some']

/-- **The head loop of `memcpy`** (68763 … 68777), aligning the destination: with ω₁₂ = k + 1,
    ω₅ = s and ω₆ = d, it copies the k + 1 octets at `s` to `d` (the ranges disjoint) and leaves
    for 68780, changing only ω₅, ω₆, ω₁₀, ω₁₂. -/
theorem memcpy_head_loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) : ∀ (k : Nat) (ω : Regs)
    (μ : Memory) (s d : Nat), ω[12] = UInt64.ofNat (k + 1) → ω[5] = UInt64.ofNat s →
    ω[6] = UInt64.ofNat d → k + 1 < 16 → s + k + 1 < 4294967296 → d + k + 1 < 4294967296 →
    (d + k + 1 ≤ s ∨ s + k + 1 ≤ d) → (∀ a, s ≤ a → a ≤ s + k → μ.readable a = true) →
    (∀ a, d ≤ a → a ≤ d + k → μ.writable a = true) →
    ∃ ω', FreeStepsH p R 68763 ω μ x 68780 ω' (μ.writeN d (μ.readN s (k + 1))) x (7 * (k + 1)) ∧
      ∀ j : Fin 13, j.val ∉ [5, 6, 10, 12] → ω'[j] = ω[j] := by
  intro k
  induction k with
  | zero =>
    intro ω μ s d hC hS hD hk hs hd _ hr hw
    obtain ⟨ω₁, hrun, hC', _, _, hfr⟩ := memcpy_head_iter (p := p) (P := P) (R := R) ω μ x 0 s d hC hS hD hk hs hd
      (hr s (by omega) (by omega)) (hw d (by omega) (by omega))
    refine ⟨regsNF ω₁ [], ?_, hfr⟩
    rw [show μ.readN s (0 + 1) = [μ.read s] by simp [Memory.readN]]
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68777 (p := p) (P := P))
    · pvm_simp [hC']
    exact FreeStepsH.refl
  | succ k ih =>
    intro ω μ s d hC hS hD hk hs hd hdj hr hw
    obtain ⟨ω₁, hrun, hC', hS', hD', hfr⟩ := memcpy_head_iter (p := p) (P := P) (R := R) ω μ x (k + 1) s d hC hS hD hk
      hs hd (hr s (by omega) (by omega)) (hw d (by omega) (by omega))
    obtain ⟨ω₂, hrun₂, hfr₂⟩ := ih (regsNF ω₁ []) (μ.writeN d [μ.read s]) (s + 1) (d + 1) hC' hS'
      hD' (by omega) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [Memory.readable_writeN]; exact hr a (by omega) (by omega))
      (fun a h1 h2 => by rw [Memory.writable_writeN]; exact hw a (by omega) (by omega))
    refine ⟨ω₂, ?_, fun j hj => (hfr₂ j hj).trans (hfr j hj)⟩
    have hmem : μ.writeN d (μ.readN s (k + 1 + 1)) =
        (μ.writeN d [μ.read s]).writeN (d + 1) ((μ.writeN d [μ.read s]).readN (s + 1) (k + 1)) := by
      rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp; omega) (by simp [two32]; omega)
        (by simp [two32]; omega), Services.Bootstrap.readN_succ]
      rfl
    rw [hmem]
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68777 (p := p) (P := P))
    · pvm_simp [hC']
    exact hrun₂

theorem writeN_append (μ : Memory) (d : Nat) (l₁ l₂ : List UInt8) :
    μ.writeN d (l₁ ++ l₂) = (μ.writeN d l₁).writeN (d + l₁.length) l₂ := by
  induction l₁ generalizing μ d with
  | nil => simp [Memory.writeN]
  | cons b l ih =>
    simp only [List.cons_append, Memory.writeN, ih, List.length_cons]
    congr 1; omega

/-- One iteration of the aligned word loop at 68804: copy the word at `s` to `d`. -/
theorem memcpy_word_iter {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (s d e : Nat) (h8 : ω[8] = UInt64.ofNat s) (h11 : ω[11] = UInt64.ofNat d) (h10 : ω[10] = UInt64.ofNat e)
    (hs : s + 8 < 4294967296) (hd : d + 8 < 4294967296) (he : e < 4294967296)
    (hr : ∀ a, s ≤ a → a < s + 8 → μ.readable a = true) (hw : ∀ a, d ≤ a → a < d + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 68804 ω μ x 68815 ω' (μ.writeN d (μ.readN s 8)) x 5 ∧
      ω'[8] = UInt64.ofNat (s + 8) ∧ ω'[11] = UInt64.ofNat (d + 8) ∧ ω'[10] = UInt64.ofNat e ∧
      ∀ j : Fin 13, j.val ∉ [6, 8, 11] → ω'[j] = ω[j] := by
  have hl := encodeLE_decodeLE (μ.readN s 8)
  have hlt := decodeLE_lt (μ.readN s 8)
  rw [Memory.length_readN] at hl hlt
  generalize Num.decodeLE (μ.readN s 8) = v at hl hlt
  rw [← hl]
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run =>
      apply FreeStepsH.step_decode (d_68804 (p := p) (P := P))
      · pvm_simp []
      apply FreeStepsH.step_decode (d_68805 (p := p) (P := P))
      · pvm_simp [h8, hr, ← hl, hlt]
      apply FreeStepsH.step_decode (d_68807 (p := p) (P := P))
      · pvm_simp [h11, hw]
      apply FreeStepsH.step_decode (d_68809 (p := p) (P := P))
      · pvm_simp [h11]
      apply FreeStepsH.step_decode (d_68812 (p := p) (P := P))
      · pvm_simp [h8]
      exact FreeStepsH.refl
  case post =>
    refine ⟨?r8, ?r11, ?r10, fun j hj => ?rest⟩
    case rest =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3]
    all_goals simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none, h10]

/-- **The aligned word loop of `memcpy`** (68804 … 68815): with ω₈ = s, ω₁₁ = d and ω₁₀ = d + 8(k + 1),
    it copies the 8(k + 1) octets at `s` to `d` word by word and leaves for 68818, changing only
    ω₆, ω₈, ω₁₁. -/
theorem memcpy_word_loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) : ∀ (k : Nat) (ω : Regs)
    (μ : Memory) (s d : Nat), ω[8] = UInt64.ofNat s → ω[11] = UInt64.ofNat d →
    ω[10] = UInt64.ofNat (d + 8 * (k + 1)) → s + 8 * (k + 1) < 4294967296 → d + 8 * (k + 1) < 4294967296 →
    (d + 8 * (k + 1) ≤ s ∨ s + 8 * (k + 1) ≤ d) →
    (∀ a, s ≤ a → a < s + 8 * (k + 1) → μ.readable a = true) →
    (∀ a, d ≤ a → a < d + 8 * (k + 1) → μ.writable a = true) →
    ∃ ω', FreeStepsH p R 68804 ω μ x 68818 ω' (μ.writeN d (μ.readN s (8 * (k + 1)))) x (6 * (k + 1)) ∧
      ω'[8] = UInt64.ofNat (s + 8 * (k + 1)) ∧ ω'[11] = UInt64.ofNat (d + 8 * (k + 1)) ∧
      ∀ j : Fin 13, j.val ∉ [6, 8, 11] → ω'[j] = ω[j] := by
  intro k
  induction k with
  | zero =>
    intro ω μ s d h8 h11 h10 hs hd _ hr hw
    obtain ⟨ω₁, hrun, h8', h11', h10', hfr⟩ := memcpy_word_iter (p := p) (P := P) (R := R) ω μ x s d
      (d + 8 * (0 + 1)) h8 h11 h10 (by omega) (by omega) (by omega)
      (fun a h1 h2 => hr a h1 (by omega)) (fun a h1 h2 => hw a h1 (by omega))
    refine ⟨regsNF ω₁ [], ?_, h8', h11', hfr⟩
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68815 (p := p) (P := P))
    · pvm_simp [h11', h10']
    exact FreeStepsH.refl
  | succ k ih =>
    intro ω μ s d h8 h11 h10 hs hd hdj hr hw
    obtain ⟨ω₁, hrun, h8', h11', h10', hfr⟩ := memcpy_word_iter (p := p) (P := P) (R := R) ω μ x s d
      (d + 8 * (k + 1 + 1)) h8 h11 h10 (by omega) (by omega) (by omega)
      (fun a h1 h2 => hr a h1 (by omega)) (fun a h1 h2 => hw a h1 (by omega))
    obtain ⟨ω₂, hrun₂, h8₂, h11₂, hfr₂⟩ := ih (regsNF ω₁ []) (μ.writeN d (μ.readN s 8)) (s + 8) (d + 8) h8' h11'
      (h10'.trans (by congr 1; omega)) (by omega) (by omega) (by omega)
      (fun a h1 h2 => by rw [Memory.readable_writeN]; exact hr a (by omega) (by omega))
      (fun a h1 h2 => by rw [Memory.writable_writeN]; exact hw a (by omega) (by omega))
    refine ⟨ω₂, ?_, by rw [h8₂]; congr 1; omega, by rw [h11₂]; congr 1; omega,
      fun j hj => (hfr₂ j hj).trans (hfr j hj)⟩
    have hmem : μ.writeN d (μ.readN s (8 * (k + 1 + 1))) =
        (μ.writeN d (μ.readN s 8)).writeN (d + 8) ((μ.writeN d (μ.readN s 8)).readN (s + 8) (8 * (k + 1))) := by
      rw [Memory.readN_writeN_disjoint _ _ _ _ _ (by simp [Memory.length_readN]; omega)
        (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega)]
      have := Memory.readN_split μ s 8 (8 * (k + 1))
      rw [show 8 + 8 * (k + 1) = 8 * (k + 1 + 1) by omega] at this
      rw [this, writeN_append, Memory.length_readN]
    rw [hmem]
    refine hrun.trans' ?_
    rw [show ω₁ = regsNF ω₁ [] from rfl]
    apply FreeStepsH.step_decode (d_68815 (p := p) (P := P))
    · pvm_simp [h11', h10']
    exact hrun₂

/-- One iteration of the misaligned loop at 68989. -/
theorem memcpy_shift_iter {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A d e sp m : Nat) (hm : 0 < m ∧ m < 8) (hpw : pw < 18446744073709551616)
    (h4 : ω[4] = UInt64.ofNat pw) (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * m))
    (h11 : ω[11] = UInt64.ofNat d) (h10 : ω[10] = UInt64.ofNat e) (h1 : ω[1] = UInt64.ofNat sp)
    (hA : A + 16 < 4294967296) (hd : d + 16 < 4294967296) (he : e < 4294967296) (hsp : sp + 16 < 4294967296)
    (hsd : sp + 16 ≤ d ∨ d + 8 ≤ sp) (hsA : sp + 16 ≤ A + 8 ∨ A + 16 ≤ sp)
    (hT : μ.readN sp 8 = Num.encodeLE 8 (64 - 8 * m))
    (hr : ∀ a, A + 8 ≤ a → a < A + 16 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 16 → μ.writable a = true)
    (hw : ∀ a, d ≤ a → a < d + 8 → μ.writable a = true) :
    ∃ ω', FreeStepsH p R 68989 ω μ x 69027 ω'
      ((μ.writeN (sp + 8) (Num.encodeLE 8 (pw / 2 ^ (8 * m)))).writeN d
        ((Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m)) x 15 ∧
      ω'[4] = UInt64.ofNat (Num.decodeLE (μ.readN (A + 8) 8)) ∧ ω'[6] = UInt64.ofNat (A + 8) ∧
      ω'[3] = UInt64.ofNat (8 * m) ∧ ω'[11] = UInt64.ofNat (d + 8) ∧ ω'[8] = UInt64.ofNat (d + 16) ∧
      ω'[10] = UInt64.ofNat e ∧ ω'[1] = UInt64.ofNat sp ∧
      ∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8, 11] → ω'[j] = ω[j] := by
  have hq : pw / 2 ^ (8 * m) < 18446744073709551616 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hpw
  have hsplice : Num.encodeLE 8 (Exec.bitwise (fun x1 x2 => x1 || x2) (Num.decodeLE (μ.readN (A + 8) 8) * 2 ^ (64 - 8 * m) % 18446744073709551616)
      (pw / 2 ^ (8 * m))) = (Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m := by
    rw [bitwise_or_comm]
    have := encodeLE_splice (Num.encodeLE 8 pw) (μ.readN (A + 8) 8) (Num.length_encodeLE _ _)
      (Memory.length_readN _ _ _) m hm
    rwa [Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hpw)] at this
  have hl := encodeLE_decodeLE (μ.readN (A + 8) 8)
  have hlt := decodeLE_lt (μ.readN (A + 8) 8)
  rw [Memory.length_readN] at hl hlt
  generalize Num.decodeLE (μ.readN (A + 8) 8) = v at hl hlt hsplice ⊢
  rw [← hl] at hsplice ⊢
  have hrs' : ∀ a, sp ≤ a → a < sp + 16 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run =>
    apply FreeStepsH.step_decode (d_68989 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_68990 (p := p) (P := P))
    · pvm_simp [h4]
    apply FreeStepsH.step_decode (d_68992 (p := p) (P := P))
    · pvm_simp [h6, hr, ← hl, hlt]
    apply FreeStepsH.step_decode (d_68995 (p := p) (P := P))
    · pvm_simp [h3]
    apply FreeStepsH.step_decode (d_68998 (p := p) (P := P))
    · pvm_simp [h1, hrs]
    apply FreeStepsH.step_decode (d_69001 (p := p) (P := P))
    · pvm_simp [h6]
    apply FreeStepsH.step_decode (d_69004 (p := p) (P := P))
    · pvm_simp [h3]
    apply FreeStepsH.step_decode (d_69006 (p := p) (P := P))
    · pvm_simp [h1, hrs', hT]
    apply FreeStepsH.step_decode (d_69008 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_69011 (p := p) (P := P))
    · pvm_simp [h1, hrs']
    apply FreeStepsH.step_decode (d_69014 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_69017 (p := p) (P := P))
    · pvm_simp []
    apply FreeStepsH.step_decode (d_69019 (p := p) (P := P))
    · pvm_simp [h11]
    apply FreeStepsH.step_decode (d_69022 (p := p) (P := P))
    · pvm_simp [h11, hw, hq, bitwise_mod64, hsplice]
    apply FreeStepsH.step_decode (d_69024 (p := p) (P := P))
    · pvm_simp [h11]
    exact FreeStepsH.refl
  case post =>
    refine ⟨?r4, ?r6, ?r3, ?r11, ?r8, ?r10, ?r1, fun j hj => ?rest⟩
    case rest =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, h1, h2, h3, h4, h5, h6]
    all_goals simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
      PVM.getD_some', List.lookup_nil, Option.getD_none, h10, h1]

/-- The spliced word is the source's 8 octets from A + m. -/
theorem splice_readN (μ : Memory) (pw A m : Nat) (hm : 0 < m ∧ m < 8)
    (hdrop : (Num.encodeLE 8 pw).drop m = μ.readN (A + m) (8 - m)) :
    (Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m = μ.readN (A + m) 8 := by
  rw [hdrop, readN_take _ _ _ _ (by omega)]
  have := Memory.readN_split μ (A + m) (8 - m) m
  rw [show 8 - m + m = 8 by omega, show A + m + (8 - m) = A + 8 by omega] at this
  exact this.symm

/-- What the misaligned loop leaves after k + 1 passes from `A`, `d`: the k + 1 words at `d` are the
    source's from A + m, ω₄ holds the next word (its high 8 − m octets the source's), ω₆, ω₁₁ moved
    by 8(k + 1), and memory otherwise unchanged but for the temporary word at sp + 8. -/
def ShiftOk (ω ω' : Regs) (μ μ' : Memory) (m sp A d k : Nat) : Prop :=
  μ'.readN d (8 * (k + 1)) = μ.readN (A + m) (8 * (k + 1)) ∧
    (∃ pw', ω'[4] = UInt64.ofNat pw' ∧ pw' < 18446744073709551616 ∧
      (Num.encodeLE 8 pw').drop m = μ.readN (A + 8 * (k + 1) + m) (8 - m)) ∧
    ω'[6] = UInt64.ofNat (A + 8 * (k + 1)) ∧ ω'[3] = UInt64.ofNat (8 * m) ∧
    ω'[11] = UInt64.ofNat (d + 8 * (k + 1)) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[10] = ω[10] ∧
    (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8, 11] → ω'[j] = ω[j]) ∧
    (∀ a, a < 4294967296 → (a < d ∨ d + 8 * (k + 1) ≤ a) → (a < sp + 8 ∨ sp + 16 ≤ a) → μ'.read a = μ.read a) ∧
    (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **The misaligned loop of `memcpy`** (68989 … 69027), k + 1 passes: see `ShiftOk`. -/
theorem memcpy_shift_loop {p : ByteArray} {P : Program} [HasCode p P] (x : X) (m sp : Nat)
    (hm : 0 < m ∧ m < 8) : ∀ (k : Nat) (ω : Regs) (μ : Memory) (pw A d : Nat),
    ω[4] = UInt64.ofNat pw → pw < 18446744073709551616 →
    (Num.encodeLE 8 pw).drop m = μ.readN (A + m) (8 - m) →
    ω[6] = UInt64.ofNat A → ω[3] = UInt64.ofNat (8 * m) → ω[11] = UInt64.ofNat d →
    ω[10] = UInt64.ofNat (d + 8 * (k + 2)) → ω[1] = UInt64.ofNat sp →
    A + 8 * (k + 2) + 8 < 4294967296 → d + 8 * (k + 2) < 4294967296 → sp + 16 < 4294967296 →
    (d + 8 * (k + 1) ≤ A ∨ A + 8 * (k + 2) ≤ d) → (sp + 16 ≤ d ∨ d + 8 * (k + 1) ≤ sp) →
    (sp + 16 ≤ A ∨ A + 8 * (k + 2) ≤ sp) →
    μ.readN sp 8 = Num.encodeLE 8 (64 - 8 * m) →
    (∀ a, A + 8 ≤ a → a < A + 8 * (k + 2) → μ.readable a = true) →
    (∀ a, sp ≤ a → a < sp + 16 → μ.writable a = true) →
    (∀ a, d ≤ a → a < d + 8 * (k + 1) → μ.writable a = true) →
    ∃ ω' μ', FreeStepsH p R 68989 ω μ x 69030 ω' μ' x (16 * (k + 1)) ∧ ShiftOk ω ω' μ μ' m sp A d k := by
  intro k
  induction k with
  | zero =>
    intro ω μ pw A d h4 hpw hdrop h6 h3 h11 h10 h1 hA hd hsp hdA hsd hsA hT hr hrs hw
    obtain ⟨ω₁, hrun, g4, g6, g3, g11, g8, g10, g1, gfr⟩ := memcpy_shift_iter (p := p) (P := P) (R := R) ω μ x pw A d
      (d + 8 * (0 + 2)) sp m hm hpw h4 h6 h3 h11 h10 h1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hT (fun a h1 h2 => hr a h1 (by omega)) hrs (fun a h1 h2 => hw a h1 (by omega))
    refine ⟨regsNF ω₁ [], (μ.writeN (sp + 8) (Num.encodeLE 8 (pw / 2 ^ (8 * m)))).writeN d
        ((Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m), ?run, ?post⟩
    case run =>
      refine hrun.trans' ?_
      rw [show ω₁ = regsNF ω₁ [] from rfl]
      apply FreeStepsH.step_decode (d_69027 (p := p) (P := P))
      · pvm_simp [g8, g10]
      exact FreeStepsH.refl
    case post =>
      have hW := splice_readN μ pw A m hm hdrop
      rw [hW]
      have hl := encodeLE_decodeLE (μ.readN (A + 8) 8)
      have hlt := decodeLE_lt (μ.readN (A + 8) 8)
      rw [Memory.length_readN] at hl hlt
      refine ⟨?_, ⟨_, g4, hlt, ?_⟩, g6, g3, (by exact g11), g1, g10.trans h10.symm, gfr,
        fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
      · rw [show 8 * (0 + 1) = 8 by rfl, Memory.readN_writeN_same _ _ _ _ (Memory.length_readN _ _ _) (by simp [two32])]
      · rw [hl, readN_drop]
      · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Memory.length_readN]; omega)
          (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega),
          Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
      · simp only [Memory.readable_writeN]
      · simp only [Memory.writable_writeN]
  | succ k ih =>
    intro ω μ pw A d h4 hpw hdrop h6 h3 h11 h10 h1 hA hd hsp hdA hsd hsA hT hr hrs hw
    obtain ⟨ω₁, hrun, g4, g6, g3, g11, g8, g10, g1, gfr⟩ := memcpy_shift_iter (p := p) (P := P) (R := R) ω μ x pw A d
      (d + 8 * (k + 1 + 2)) sp m hm hpw h4 h6 h3 h11 h10 h1 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hT (fun a h1 h2 => hr a h1 (by omega)) hrs (fun a h1 h2 => hw a h1 (by omega))
    have hW := splice_readN μ pw A m hm hdrop
    rw [hW] at hrun
    generalize hμ₁ : (μ.writeN (sp + 8) (Num.encodeLE 8 (pw / 2 ^ (8 * m)))).writeN d (μ.readN (A + m) 8) = μ₁ at hrun
    -- μ₁ agrees with μ off the temporary word and [d, d + 8)
    have e1 : ∀ a, a < 4294967296 → (a < d ∨ d + 8 ≤ a) → (a < sp + 8 ∨ sp + 16 ≤ a) → μ₁.read a = μ.read a := by
      intro a ha0 ha1 ha2
      rw [← hμ₁, Memory.read_writeN_disjoint _ _ _ _ (by simp [Memory.length_readN]; omega)
        (by simp [Memory.length_readN, two32]; omega) (by simp [two32]; omega),
        Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [two32]; omega) (by simp [two32]; omega)]
    have e1N : ∀ a n, a + n < 4294967296 → (a + n ≤ d ∨ d + 8 ≤ a) → (a + n ≤ sp + 8 ∨ sp + 16 ≤ a) →
        μ₁.readN a n = μ.readN a n := fun a n h1 h2 h3 =>
      Memory.readN_congr (fun j hj => e1 (a + j) (by omega) (by omega) (by omega))
    have e1r : ∀ a, μ₁.readable a = μ.readable a := fun a => by rw [← hμ₁]; simp only [Memory.readable_writeN]
    have e1w : ∀ a, μ₁.writable a = μ.writable a := fun a => by rw [← hμ₁]; simp only [Memory.writable_writeN]
    have hl := encodeLE_decodeLE (μ.readN (A + 8) 8)
    have hlt := decodeLE_lt (μ.readN (A + 8) 8)
    rw [Memory.length_readN] at hl hlt
    obtain ⟨ω₂, μ₂, run₂, ⟨k1, ⟨pw₂, k4, k4lt, k4d⟩, k6, k3, k11, k1', k10, kfr, krd, krr, krw⟩⟩ :=
      ih (regsNF ω₁ []) μ₁ (Num.decodeLE (μ.readN (A + 8) 8)) (A + 8) (d + 8) g4 hlt
        (by rw [hl, readN_drop, e1N _ _ (by omega) (by omega) (by omega)])
        g6 g3 g11 (g10.trans (by congr 1; omega)) g1 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by rw [e1N _ _ (by omega) (by omega) (by omega)]; exact hT)
        (fun a h1 h2 => by rw [e1r]; exact hr a (by omega) (by omega))
        (fun a h1 h2 => by rw [e1w]; exact hrs a h1 h2)
        (fun a h1 h2 => by rw [e1w]; exact hw a (by omega) (by omega))
    refine ⟨ω₂, μ₂, ?run, ?post⟩
    case run =>
      refine hrun.trans' ?_
      rw [show ω₁ = regsNF ω₁ [] from rfl]
      apply FreeStepsH.step_decode (d_69027 (p := p) (P := P))
      · pvm_simp [g8, g10]
      exact run₂
    case post =>
      have e2 : ∀ a, a < 4294967296 → (a < d + 8 ∨ d + 8 + 8 * (k + 1) ≤ a) → (a < sp + 8 ∨ sp + 16 ≤ a) →
          μ₂.read a = μ₁.read a := krd
      refine ⟨?_, ⟨pw₂, k4, k4lt, ?_⟩, ?_, k3, ?_, k1', ?_, fun j hj => (kfr j hj).trans (gfr j hj),
        fun a ha0 ha1 ha2 => ?_, fun a => by rw [krr, e1r], fun a => by rw [krw, e1w]⟩
      · have s1 := Memory.readN_split μ₂ d 8 (8 * (k + 1))
        have s2 := Memory.readN_split μ (A + m) 8 (8 * (k + 1))
        rw [show 8 + 8 * (k + 1) = 8 * (k + 1 + 1) by omega] at s1 s2
        rw [s1, s2, k1, e1N _ _ (by omega) (by omega) (by omega), show A + 8 + m = A + m + 8 by omega]
        congr 1
        rw [Memory.readN_congr (μ := μ₁) (fun j hj => e2 (d + j) (by omega) (by omega) (by omega)), ← hμ₁,
          Memory.readN_writeN_same _ _ _ _ (Memory.length_readN _ _ _) (by simp [two32])]
      · rw [k4d, e1N _ _ (by omega) (by omega) (by omega)]; congr 1; omega
      · rw [k6]; congr 1; omega
      · rw [k11]; congr 1; omega
      · rw [k10]; exact g10.trans h10.symm
      · rw [e2 a ha0 (by omega) ha2, e1 a ha0 (by omega) ha2]

/-- **The misaligned path's head**, m = 7: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_7 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 7)) (h2 : ω[2] = UInt64.ofNat 7)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 7 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 30 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 7 = μ.readN (A0 + 7) (8 - 7) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 7) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 7) ∧
      ω'[2] = UInt64.ofNat 7 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 7) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's head**, m = 1: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_1 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 1)) (h2 : ω[2] = UInt64.ofNat 1)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 1 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 40 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 1 = μ.readN (A0 + 1) (8 - 1) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 1) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 1) ∧
      ω'[2] = UInt64.ofNat 1 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 1) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's head**, m = 2: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_2 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 2)) (h2 : ω[2] = UInt64.ofNat 2)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 2 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 40 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 2 = μ.readN (A0 + 2) (8 - 2) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 2) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 2) ∧
      ω'[2] = UInt64.ofNat 2 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 2) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's head**, m = 3: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_3 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 3)) (h2 : ω[2] = UInt64.ofNat 3)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 3 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 40 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 3 = μ.readN (A0 + 3) (8 - 3) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 3) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 3) ∧
      ω'[2] = UInt64.ofNat 3 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 3) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's head**, m = 4: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_4 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 4)) (h2 : ω[2] = UInt64.ofNat 4)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 4 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 40 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 4 = μ.readN (A0 + 4) (8 - 4) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 4) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 4) ∧
      ω'[2] = UInt64.ofNat 4 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 4) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's head**, m = 5: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_5 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 5)) (h2 : ω[2] = UInt64.ofNat 5)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 5 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 40 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 5 = μ.readN (A0 + 5) (8 - 5) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 5) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 5) ∧
      ω'[2] = UInt64.ofNat 5 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 5) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's head**, m = 6: 68872 … 68988 assemble the source's first 8 − m octets
    into the temporary word at sp + 16 and store the splice shift 64 − 8m at sp, then enter the loop. -/
theorem memcpy_mis_head_6 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (A0 d W sp : Nat) (h0 : ω[0] = UInt64.ofNat (A0 + 6)) (h2 : ω[2] = UInt64.ofNat 6)
    (h10 : ω[10] = UInt64.ofNat (d + W)) (h11 : ω[11] = UInt64.ofNat d) (h12 : ω[12] = UInt64.ofNat W)
    (h1 : ω[1] = UInt64.ofNat sp) (hW : 16 ≤ W) (hsp : sp % 8 = 0)
    (hb : A0 + 16 < 4294967296) (hd : d + W < 4294967296) (hs : sp + 24 < 4294967296)
    (hsA : sp + 24 ≤ A0 ∨ A0 + 16 ≤ sp)
    (hr : ∀ a, A0 + 6 ≤ a → a < A0 + 8 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true) :
    ∃ ω' μ' pw, FreeStepsH p R 68872 ω μ x 68989 ω' μ' x 40 ∧
      ω'[4] = UInt64.ofNat pw ∧ pw < 18446744073709551616 ∧
      (Num.encodeLE 8 pw).drop 6 = μ.readN (A0 + 6) (8 - 6) ∧
      ω'[6] = UInt64.ofNat A0 ∧ ω'[3] = UInt64.ofNat (8 * 6) ∧ ω'[11] = UInt64.ofNat d ∧
      ω'[10] = UInt64.ofNat (d + W) ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[0] = UInt64.ofNat (A0 + 6) ∧
      ω'[2] = UInt64.ofNat 6 ∧ ω'[12] = UInt64.ofNat W ∧
      (∀ j : Fin 13, j.val ∉ [3, 4, 5, 6, 8] → ω'[j] = ω[j]) ∧
      μ'.readN sp 8 = Num.encodeLE 8 (64 - 8 * 6) ∧
      (∀ a, a < 4294967296 → (a < sp ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?pw, ?run, ?post⟩
  case run =>
    pvm_go [h0, h2, h10, h11, h12, h1, hrs, hrs', hr, bitwise_or_low8, ↓rdN_fold, ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64]
  case post =>
    refine ⟨?e4, ?rest⟩
    case e4 =>
      simp only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte, PVM.getD_some']
      rfl
    refine ⟨rdN_lt64 _ _, ?drop, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, ?T, fun a ha0 ha1 => ?mf,
      fun a => ?rd, fun a => ?wr⟩
    case drop =>
      rw [encodeLE_rdN, readN_drop]
      copy_bytes
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g1, g2, g3, g4, g5⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g1, g2, g3, g4, g5]
    all_goals simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h10, h11, h12,
      PVM.Memory.readN_writeN_same, PVM.Memory.read_writeN_disjoint,
      PVM.Memory.readable_writeN, PVM.Memory.writable_writeN, PVM.Num.length_encodeLE, List.length_cons,
      List.length_nil, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals rfl

/-- **The misaligned path's end**, m = 7: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_7 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 7 = μ.readN (A + 7) (8 - 7))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 7)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 7) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 7) (hA : A + 7 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 7 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 7 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 7) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 2 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 1 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 7 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 7) (8 - 7) 7
      rw [show 8 - 7 + 7 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

/-- **The misaligned path's end**, m = 1: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_1 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 1 = μ.readN (A + 1) (8 - 1))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 1)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 1) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 1) (hA : A + 1 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 1 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 1 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 1) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 0 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 1 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 1 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 1) (8 - 1) 1
      rw [show 8 - 1 + 1 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

/-- **The misaligned path's end**, m = 2: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_2 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 2 = μ.readN (A + 2) (8 - 2))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 2)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 2) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 2) (hA : A + 2 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 2 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 2 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 2) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 2 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 0 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 2 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 2) (8 - 2) 2
      rw [show 8 - 2 + 2 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

/-- **The misaligned path's end**, m = 3: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_3 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 3 = μ.readN (A + 3) (8 - 3))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 3)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 3) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 3) (hA : A + 3 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 3 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 3 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 3) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 2 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 1 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 3 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 3) (8 - 3) 3
      rw [show 8 - 3 + 3 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

/-- **The misaligned path's end**, m = 4: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_4 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 4 = μ.readN (A + 4) (8 - 4))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 4)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 4) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 4) (hA : A + 4 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 4 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 4 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 4) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 0 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 0 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 4 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 4) (8 - 4) 4
      rw [show 8 - 4 + 4 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

/-- **The misaligned path's end**, m = 5: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_5 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 5 = μ.readN (A + 5) (8 - 5))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 5)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 5) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 5) (hA : A + 5 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 5 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 5 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 5) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 0 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 1 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 5 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 5) (8 - 5) 5
      rw [show 8 - 5 + 5 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

/-- **The misaligned path's end**, m = 6: 69030 … 69129 load the source's last m octets into the
    temporary word, splice them onto the carried word's high 8 − m, store the last destination word,
    and set up the tail (ω₈ = s' + W, ω₉ = n' mod 8, ω₁₁ = d_E + n' mod 8) for the branch at 69132. -/
theorem memcpy_mis_end_6 {p : ByteArray} {P : Program} [HasCode p P] (ω : Regs) (μ : Memory) (x : X)
    (pw A dl s' W n' sp : Nat) (h4 : ω[4] = UInt64.ofNat pw) (hpw : pw < 18446744073709551616)
    (hdrop : (Num.encodeLE 8 pw).drop 6 = μ.readN (A + 6) (8 - 6))
    (h6 : ω[6] = UInt64.ofNat A) (h3 : ω[3] = UInt64.ofNat (8 * 6)) (h11 : ω[11] = UInt64.ofNat dl)
    (h0 : ω[0] = UInt64.ofNat s') (h2 : ω[2] = UInt64.ofNat 6) (h12 : ω[12] = UInt64.ofNat W)
    (h9 : ω[9] = UInt64.ofNat n') (h10 : ω[10] = UInt64.ofNat (dl + 8)) (h1 : ω[1] = UInt64.ofNat sp)
    (hs' : s' % 8 = 6) (hA : A + 6 + 8 = s' + W) (hsp : sp % 8 = 0)
    (hb : s' + W < 4294967296) (hd : dl + 16 < 4294967296) (hs : sp + 24 < 4294967296) (hn' : n' < 4294967296)
    (hsA : sp + 24 ≤ A ∨ A + 16 ≤ sp) (hsd : sp + 24 ≤ dl ∨ dl + 8 ≤ sp) (hdA : dl + 8 ≤ A + 6 ∨ A + 16 ≤ dl)
    (hr : ∀ a, A + 8 ≤ a → a < A + 8 + 6 → μ.readable a = true)
    (hrs : ∀ a, sp ≤ a → a < sp + 24 → μ.writable a = true)
    (hw : ∀ a, dl ≤ a → a < dl + 8 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 69030 ω μ x 69132 ω' μ' x 40 ∧
      μ'.readN dl 8 = μ.readN (A + 6) 8 ∧
      ω'[8] = UInt64.ofNat (s' + W) ∧ ω'[9] = UInt64.ofNat (n' % 8) ∧ ω'[10] = UInt64.ofNat (dl + 8) ∧
      ω'[11] = UInt64.ofNat (dl + 8 + n' % 8) ∧ ω'[1] = UInt64.ofNat sp ∧
      (∀ j : Fin 13, j.val ∉ [0, 2, 3, 4, 5, 6, 8, 9, 10, 11] → ω'[j] = ω[j]) ∧
      (∀ a, a < 4294967296 → (a < dl ∨ dl + 8 ≤ a) → (a < sp + 16 ∨ sp + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs' : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hrs a h1 h2)
  have hsb2 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 2 = 2 := by
    rw [bitwise_and_pow2 _ 2 1 (by decide) (by decide)]; split <;> omega
  have hsb1 : Exec.bitwise (fun x1 x2 => x1 && x2) s' 1 = 0 := by
    rw [bitwise_and_pow2 _ 1 0 (by decide) (by decide)]; split <;> omega
  have hn7 : Exec.bitwise (fun x1 x2 => x1 && x2) n' 7 = n' % 8 := by
    rw [bitwise_and_low _ 7 3 (by decide) (by decide)]
  have hspl := fun T (hT : T < 18446744073709551616) =>
    (congrArg (Num.encodeLE 8) (bitwise_or_comm _ _)).symm.trans (encodeLE_splice' pw T 6 (by decide) hpw hT)
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hspl
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run =>
    pvm_go [h4, h6, h3, h11, h0, h2, h12, h9, h10, h1, hrs, hrs', hr, hw, bitwise_or_low8, ↓rdN_fold,
      ↓loadI_fold, store_rd1, store_rd2, store_rd4, rdN_lt64, rdN_mod64, hsb2, hsb1, hspl, bitwise_mod64, hpw]
  case post =>
    refine ⟨?w, ?_, ?_, ?_, ?_, ?_, fun j hj => ?fr, fun a ha0 ha1 ha2 => ?mf, fun a => ?rd, fun a => ?wr⟩
    case w =>
      rw [Memory.readN_writeN_same _ _ _ _ (by simp [Num.length_encodeLE]) (by simp [two32]), hdrop,
        encodeLE_rdN, readN_take _ _ _ _ (by omega)]
      have s1 := Memory.readN_split μ (A + 6) (8 - 6) 6
      rw [show 8 - 6 + 6 = 8 by rfl] at s1
      rw [s1]
      congr 1
      copy_bytes
    case mf =>
      rw [Memory.read_writeN_disjoint _ _ _ _ (by simp [Num.length_encodeLE]; omega)
        (by simp [Num.length_encodeLE, two32]; omega) (by simp [two32]; omega)]
      simp (disch := pvm_arith) only [PVM.Memory.read_writeN_disjoint, List.length_cons, List.length_nil,
        PVM.two32]
    case fr =>
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      obtain ⟨g0, g2, g3, g4, g5, g6, g8, g9, g10, g11⟩ := hj
      simp only [Fin.getElem_fin]
      rw [PVM.getElem_regsNF _ _ _ j.isLt, PVM.getElem_regsNF _ _ _ j.isLt]
      simp [PVM.lookup_cons_nat, g0, g2, g3, g4, g5, g6, g8, g9, g10, g11]
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h0, h1, h2, h9, h10, h11, h12, hn7,
      PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
      PVM.Num.length_encodeLE, List.length_cons, List.length_nil, List.length_append, List.length_drop,
      List.length_take, PVM.two32, Nat.reduceMul, Nat.reduceSub]
    all_goals (try rfl)

end Services.Bootstrap
