import PVM.Logic.Steps
import PVM.Logic.Bits
import PVM.Logic.Chase

/-!
# Words, octets and folded loads for summaries

Service-independent facts for summarizing compiled code: little-endian words as octet lists
(`encodeLE_decodeLE`, splits, `encodeLE_splice` for misaligned word copies), bitwise facts the
compiler's idioms need, loads folded so `pvm_simp` keeps them whole (`rdN`, `sxw`, `sx8`), and
octet reads through writes. ℰ (GP (C)) on each width range is `encodeNat_of_lt`.
-/

namespace PVM

theorem Memory.readN_split (μ : Memory) (a m l : Nat) :
    μ.readN a (m + l) = μ.readN a m ++ μ.readN (a + m) l := by
  simp only [Memory.readN, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, Nat.add_assoc]

theorem Num.encodeLE_split (m l v : Nat) :
    Num.encodeLE (m + l) v = Num.encodeLE m v ++ Num.encodeLE l (v / 256 ^ m) := by
  induction m generalizing v with
  | zero => simp [Num.encodeLE]
  | succ m ih =>
    rw [show m + 1 + l = (m + l) + 1 by omega]
    simp only [Num.encodeLE, ih, List.cons_append, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

end PVM

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
  have hs := Num.encodeLE_split (8 - m) m (Num.decodeLE (a.drop m) + Num.decodeLE (b.take m) * 2 ^ (64 - 8 * m))
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

/-- `a & ~7`: `a` rounded down to a multiple of 8. -/
theorem bitwise_and_not7 (a : Nat) (ha : a < 18446744073709551616) :
    Exec.bitwise (· && ·) a 18446744073709551608 = a / 8 * 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e : a / 8 * 8 = 2 ^ 3 * (a / 2 ^ 3) + 0 := by rw [Nat.mul_comm]; rfl
  rw [e, Nat.testBit_two_pow_mul_add _ (Nat.two_pow_pos 3)]
  simp only [Exec.bitwise, Num.testBit_ofBits, Num.bit_eq_testBit]
  have hm : (18446744073709551608 : Nat) = 2 ^ 64 - (2 ^ 3 - 1 + 1) := by rfl
  rw [hm, Nat.testBit_two_pow_sub_succ (by decide), Nat.testBit_two_pow_sub_one]
  by_cases h3 : i < 3
  · simp [h3, show i < 64 by omega]
  · by_cases h64 : i < 64
    · have h8 : (a / 8).testBit (i - 3) = a.testBit i := by
        rw [show (8 : Nat) = 2 ^ 3 by rfl, Nat.testBit_div_two_pow, show i - 3 + 3 = i by omega]
      simp [h3, h64, h8]
    · have hp : (18446744073709551616 : Nat) ≤ 2 ^ i := by
        have := Nat.pow_le_pow_right (by decide : 2 > 0) (show 64 ≤ i by omega)
        simpa using this
      have : a.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hp)
      have h2 : (a / 2 ^ 3).testBit (i - 3) = false := by
        rw [Nat.testBit_div_two_pow, show i - 3 + 3 = i by omega, this]
      simp [h3, h64, h2]

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

namespace PVM

open Num Exec

/-- `load_ind_i8`'s sign extension, folded as `sx8` . -/
theorem loadI8_sx8 (b : UInt8) :
    ((if b.toNat < 128 then (b.toNat : Int) else (b.toNat : Int) - 256) % 18446744073709551616).toNat =
      sx8 b.toNat := by
  have hb := b.toNat_lt
  unfold sx8
  split <;> omega

/-- `load_ind_i8` of the octet at `a`, folded as `sx8` before simp splits the sign. -/
theorem loadI8_read_sx8 (μ : Memory) (a : Nat) :
    Exec.u64 (Num.signed 1 (Num.decodeLE (μ.readN a 1))) = sx8 (μ.read a).toNat := by
  have hb := (μ.read a).toNat_lt
  simp only [Memory.readN, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    Nat.add_zero, Num.decodeLE, Exec.u64, Num.unsigned, Num.signed, sx8, Nat.reducePow, Nat.reduceMul,
    Nat.reduceSub]
  split <;> (try split) <;> omega

theorem writeN_append (μ : Memory) (d : Nat) (l₁ l₂ : List UInt8) :
    μ.writeN d (l₁ ++ l₂) = (μ.writeN d l₁).writeN (d + l₁.length) l₂ := by
  induction l₁ generalizing μ d with
  | nil => simp [Memory.writeN]
  | cons b l ih =>
    simp only [List.cons_append, Memory.writeN, ih, List.length_cons]
    congr 1; omega

/-- The spliced word is the source's 8 octets from A + m. -/
theorem splice_readN (μ : Memory) (pw A m : Nat) (hm : 0 < m ∧ m < 8)
    (hdrop : (Num.encodeLE 8 pw).drop m = μ.readN (A + m) (8 - m)) :
    (Num.encodeLE 8 pw).drop m ++ (μ.readN (A + 8) 8).take m = μ.readN (A + m) 8 := by
  rw [hdrop, readN_take _ _ _ _ (by omega)]
  have := Memory.readN_split μ (A + m) (8 - m) m
  rw [show 8 - m + m = 8 by omega, show A + m + (8 - m) = A + 8 by omega] at this
  exact this.symm

/-- ℰ(x) for 2^(7l) ≤ x < 2^(7(l+1)), l < 5 (GP (C)): the prefix octet 2^8 − 2^(8−l) + ⌊x / 2^(8l)⌋, then
    ℰ_l(x mod 2^(8l)). -/
theorem encodeNat_of_lt (x l : Nat) (hl : l < 5) (hx : 0 < x) (h1 : 2 ^ (7 * l) ≤ x)
    (h2 : x < 2 ^ (7 * (l + 1))) :
    Blob.encodeNat x = UInt8.ofNat (2 ^ 8 - 2 ^ (8 - l) + x / 2 ^ (8 * l)) :: Num.encodeLE l (x % 2 ^ (8 * l)) := by
  have hx' : x ≠ 0 := by omega
  have : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at h1 h2 <;>
  simp (disch := omega) only [Blob.encodeNat, hx', ite_false, List.range_succ, List.range_zero, List.nil_append,
    List.find?_append, List.find?_cons, List.find?_nil, Nat.reduceMul, Nat.reducePow, Nat.reduceAdd,
    decide_eq_true, decide_eq_false, Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and,
    Option.some_or, Option.none_or, Nat.reduceSub, Nat.reduceDiv, Nat.div_one, Nat.mod_one, Nat.zero_add]


end PVM
