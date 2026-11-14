import Services.Bootstrap.Encode.EncM
import Services.Bootstrap.Encode.Prefix
import Services.Bootstrap.CodeAAll

/-!
# The length prefix (30977) for 2^7 ≤ n < 2^32 elements, and the encoder for any n

The sequence codec (GP v0.8.0 Appendix C.1) prefixes a sequence with ℰ(n), the general natural
encoding: for 2^(7l) ≤ n < 2^(7(l+1)) (l < 8) it is the octet 2^8 − 2^(8−l) + ⌊n / 2^(8l)⌋ followed by
ℰ_l(n mod 2^(8l)) (`Blob.encodeNat`). The function at 30977 reads the count as a 32-bit word, so
l ≤ 4 here. Past the comparison with 2^7 (`Prefix.pa`), for n ≥ 2^7 it finds l by comparing n with
2^(7l) and 2^(7(l+1)) in turn (31143 for l = 1, 31362, 31442, 31522 for l = 2, 3, 4; each power by a
square-and-multiply loop of fixed length) and then, at 31041 with ω₅ = l:

* computes 2^(8−l), parks v, l at sp + 16, sp + 8, then (31225) 2^(8l), parks n at sp, and appends the
  octet ⌊n / 2^(8l)⌋ − 2^(8−l) (mod 2^8) from sp + 24 (`Vec<u8>::extend_from_slice`, return address
  1470 → 31291) (`pg`);
* computes 2^(8l) again, stores the word n mod 2^(8l) at sp + 24 and appends its l low octets (return
  address 1472 → 31348) (`ph`); then the function returns (`Prefix.pt`).

`prefix_big` composes these: the octets appended are `Blob.encodeNat n`. `prefix_pos` joins it with
`Prefix.prefix_small`, and `encode_okM_big` is `EncM.encode_okM` for any 0 < n < 2^32, the buffer's
capacity holding |ℰ(n)| + off + 2 octets (no reallocation). The paths for 2^(7l) ≤ n with l ≥ 2 run
through code in `CodeA`, hence `[HasCodeA p P]`.
-/

namespace Services.Bootstrap.Encode.PrefixBig

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- ℰ(n) for 2^(7l) ≤ n < 2^(7(l+1)), 1 ≤ l ≤ 4 (GP v0.8.0 Appendix C, the general natural encoding). -/
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

/-- ℰ(n) = [n] for 0 < n < 2^7 (GP v0.8.0 Appendix C). -/
theorem encodeNat_small (n : Nat) (hn : 0 < n ∧ n < 128) : Blob.encodeNat n = [UInt8.ofNat n] := by
  unfold Blob.encodeNat
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show n ≠ 0 by omega)),
    show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp [show 1 ≤ n by omega, hn.2]
  rfl

/-- Octets equal modulo 2^8. -/
theorem u8_eq {a b : Nat} (h : a % 256 = b % 256) : UInt8.ofNat a = UInt8.ofNat b :=
  UInt8.toNat_inj.1 (by simpa [UInt8.toNat_ofNat] using h)

/-- A memory goal of `pg`/`ph`, through the writes. -/
macro "pg_mem" : tactic => `(tactic| (
  simp (disch := pvm_arith) only [PVM.Memory.readN_writeN_same, PVM.Memory.readN_writeN_disjoint,
    PVM.Memory.read_writeN_disjoint, PVM.Memory.readable_writeN, PVM.Memory.writable_writeN,
    PVM.Num.length_encodeLE, List.length_cons, List.length_nil, PVM.two32]
  try decide))

set_option hygiene false in
/-- A register goal of `pg`. -/
macro "pg_reg" : tactic => `(tactic| (
  simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff, ↓reduceIte,
    List.lookup_nil, Option.getD_none, PVM.getD_some', h1, r16]))

set_option hygiene false in
/-- The goals `pvm_go` leaves for `pg`: the octet first (its arithmetic by `u8_eq`, never unfolded),
    then the memory goals, then the registers. -/
macro "pg_post" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
  rotate_left 6
  · refine (PVM.Memory.readN_writeN_same _ _ _ _ rfl (by simp [PVM.two32])).trans ?_
    exact congrArg (fun b => [b]) (u8_eq (by omega))
  · pg_mem
  · pg_mem
  · pg_mem
  · pg_mem
  · pg_mem
  · pg_mem
  · pg_reg
  · pg_reg
  · pg_reg
  · pg_reg
  · pg_reg
  · pg_reg))

set_option maxHeartbeats 40000000 in
/-- 31029 … 31285, for 2^(7l) ≤ n < 2^(7(l+1)), 1 ≤ l ≤ 4 (after `Prefix.pa`, ω₆ = n, ω₈ = 2^7): the
    function finds l, parks n, l and the writer v at sp, sp + 8, sp + 16, puts the first octet of ℰ(n),
    2^8 − 2^(8−l) + ⌊n / 2^(8l)⌋, at sp + 24 and calls `Vec<u8>::extend_from_slice` for it (return
    address 1470 → 31291), with 8l in ω₅. -/
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

set_option hygiene false in
/-- The goals `pvm_go` leaves for `ph`. -/
macro "ph_post" : tactic => `(tactic| (
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
  · simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
    ↓reduceIte, List.lookup_nil, Option.getD_none, PVM.getD_some', h1, Nat.mod_eq_of_lt hv]
    rw [PVM.rdN_writeN_disjoint _ _ _ _ _ (by simp) (by simp [PVM.two32]; omega) (by simp [PVM.two32]; omega), r8]
  · exact PVM.Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [PVM.two32])
  · exact PVM.Memory.read_writeN_disjoint _ _ _ _ (by simp; omega) (by simp [PVM.two32]; omega) (by simp [PVM.two32]; omega)
  · rw [PVM.Memory.readable_writeN]
  · rw [PVM.Memory.writable_writeN]))

set_option maxHeartbeats 40000000 in
/-- 31291 … 31342: back from the first octet (ω₅ = 8l), the function computes 2^(8l), stores the word
    n mod 2^(8l) at sp + 24 and calls `Vec<u8>::extend_from_slice` for its l low octets (l from sp + 8;
    return address 1472 → 31348). -/
theorem ph {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (sp v n l : Nat) (hl : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4)
    (hsp : sp + 32 ≤ 4294967296) (hv : v < 18446744073709551616) (hn : n < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat (8 * l))
    (s0 : μ.readN sp 8 = Num.encodeLE 8 n) (s8 : μ.readN (sp + 8) 8 = Num.encodeLE 8 l)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 v)
    (hw : ∀ a, sp ≤ a → a < sp + 32 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 31291 ω μ x 58508 ω' μ' x 200 ∧
      ω'[0] = UInt64.ofNat 1472 ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[7] = UInt64.ofNat v ∧
      ω'[8] = UInt64.ofNat (sp + 24) ∧ ω'[9] = UInt64.ofNat l ∧
      μ'.readN (sp + 24) 8 = Num.encodeLE 8 (n % 2 ^ (8 * l)) ∧
      (∀ a, a < 4294967296 → (a < sp + 24 ∨ sp + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp ≤ a → a < sp + 32 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r0 := rd8 hn s0
  have r16 := rd8 hv s16
  rw [show ω = regsNF ω [] from rfl]
  rcases hl with rfl | rfl | rfl | rfl <;>
    have r8 := rd8 (by decide) s8 <;>
    simp only [Nat.reducePow, Nat.reduceMul] at h5 ⊢ <;>
  · refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 2
    · pvm_go [h1, h5, hsp, hw, hr, r0, r8, r16, Nat.mod_eq_of_lt hn, ↓rdN_fold]
    · ph_post

/-- The l low octets of ℰ_8(x) are ℰ_l(x). -/
theorem enc_take (l x : Nat) (hl : l ≤ 8) : (Num.encodeLE 8 x).take l = Num.encodeLE l x := by
  rw [show (8 : Nat) = l + (8 - l) by omega, Num.encodeLE_split, List.take_left' (Num.length_encodeLE _ _)]

/-- **The length prefix of 2^7 ≤ n < 2^32 elements** (30977): called with ω₁ = F, the 32-bit count n
    at c (ω₇) and the writer `{cap, ptr, len}` at v (ω₈) with room for ℰ(n), the function appends ℰ(n)
    (`Blob.encodeNat n`, GP v0.8.0 Appendix C) and stores `len + |ℰ(n)|`, and returns to `ret` with ω₁ = F
    and ω₅, ω₆ as they were. Memory changes only in [F − 136, F), the octets appended and the writer's
    length. -/
theorem prefix_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (ω : Regs) (μ : Memory)
    (F c v cap ptr len ret t r5 r6 n : Nat) (hF : 65536 + 256 ≤ F ∧ F < 4294967296 ∧ F % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 136 ∨ F ≤ c) (hn : rdN μ c 4 = n) (hn1 : 128 ≤ n)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len) (hroom : len + (Blob.encodeNat n).length ≤ cap)
    (hcap : cap < 18446744073709551616)
    (hv : v + 24 ≤ 4294967296) (hvF : v + 24 ≤ F - 136 ∨ F ≤ v)
    (hd : 65536 ≤ ptr + len ∧ ptr + len + (Blob.encodeNat n).length + 16 < 4294967296)
    (hdF : F ≤ ptr + len ∨ ptr + len + (Blob.encodeNat n).length + 16 ≤ F - 136)
    (hdv : v + 24 ≤ ptr + len ∨ ptr + len + (Blob.encodeNat n).length ≤ v)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true)
    (hwd : ∀ a, ptr + len ≤ a → a < ptr + len + (Blob.encodeNat n).length → μ.writable a = true)
    (hwF : ∀ a, F - 136 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x t ω' μ' x 2000 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN (ptr + len) (Blob.encodeNat n).length = Blob.encodeNat n ∧
      μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + (Blob.encodeNat n).length) ∧
      (∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) →
        (a < ptr + len ∨ ptr + len + (Blob.encodeNat n).length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hF0, hF1, hF8⟩ := hF
  have hret' : ret < 18446744073709551616 := by omega
  have hn4 : n < 4294967296 := by rw [← hn]; exact rdN_lt μ c 4
  -- the octet count l of ℰ(n) beyond its first
  obtain ⟨l, hl, hnl⟩ : ∃ l, (l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4) ∧ 2 ^ (7 * l) ≤ n ∧ n < 2 ^ (7 * (l + 1)) := by
    by_cases h2 : n < 16384
    · exact ⟨1, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
    by_cases h3 : n < 2097152
    · exact ⟨2, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
    by_cases h4 : n < 268435456
    · exact ⟨3, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
    · exact ⟨4, by omega, by simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]; omega⟩
  have henc := encodeNat_big n l hl hnl
  have hw : (Blob.encodeNat n).length = 1 + l := by rw [henc]; simp; omega
  rw [hw] at hroom hd hdF hdv hwd ⊢
  have hl4 : 1 ≤ l ∧ l ≤ 4 := by omega
  -- the frame, n, 2^7
  obtain ⟨ω1, μ1, run1, a1, a2, a6, a8, a0', a5', a6', afr, ard, awr⟩ := Prefix.pa (p := p) (P := P) (R := R)
    x ω μ F c v ret r5 r6 n ⟨by omega, hF1⟩ h0 h1 h5 h6 h7 h8 hret' hr5 hr6 (by omega) hc (by omega) hn
    (by omega) hrc (fun a h1 h2 => hwF a (by omega) h2)
  -- l, the first octet, and the call for it
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b7, b8, b9, bo, bn, bl, bv, bfr, brd, bwr⟩ := pg (p := p) (P := P) (R := R)
    x ω1 μ1 (F - 56) v n l hl hnl (by omega) (by omega) a1 a2 a6 a8
    (fun a h1 h2 => by rw [awr]; exact hwF a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < F - 56 ∨ F ≤ a) → μ2.read a = μ.read a := fun a h0 h1 => by
    rw [bfr a h0 (by omega), afr a h0 h1]
  have k2v : ∀ a, v ≤ a → a < v + 24 → μ2.read a = μ.read a := fun a h1 h2 => k2 a (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, cd, cl, cfr, crd, cwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω2 μ2
    (F - 56) v (F - 56 + 24) 1 cap ptr len 1470 31291 ⟨by omega, by omega, by omega⟩ b0 b1 b7 b8 b9
    (by omega) hcap
    (by rw [Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vc)
    (by rw [Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vp)
    (by rw [Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vl)
    hv (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_734 bs_31291
    (fun a h1 h2 => by rw [brd, ard]; exact hrv a h1 h2)
    (fun a h1 h2 => by rw [bwr, awr]; exact hwv a h1 h2)
    (fun a h1 h2 => by rw [brd, ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
    (fun a h1 h2 => by rw [bwr, awr]; exact hwd a h1 (by omega))
    (fun a h1 h2 => by rw [bwr, awr]; exact hwF a (by omega) (by omega))
  -- the function's frame [F − 56, F) is kept by the call
  have k3 : ∀ a, F - 56 ≤ a → a < F → μ3.read a = μ2.read a := fun a h1 h2 =>
    cfr a (by omega) (by omega) (by omega) (by omega)
  -- the l further octets, and the call for them
  obtain ⟨ω4, μ4, run4, d0, d1, d7, d8, d9, dw, dfr, drd, dwr⟩ := ph (p := p) (P := P) (R := R) x ω3 μ3 (F - 56)
    v n l hl (by omega) (by omega) (by omega) c1 (c5.trans b5)
    (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; exact bn)
    (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; exact bl)
    (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; exact bv)
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact hwF a (by omega) (by omega))
  have k4v : ∀ a, v ≤ a → a < v + 24 → μ4.read a = μ3.read a := fun a h1 h2 => dfr a (by omega) (by omega)
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, ed, el, efr, erd, ewr⟩ := extend_ok (p := p) (P := P) (R := R) x ω4 μ4
    (F - 56) v (F - 56 + 24) l cap ptr (len + 1) 1472 31348 ⟨by omega, by omega, by omega⟩ d0 d1 d7 d8 d9
    (by omega) hcap
    (by rw [Memory.readN_congr (fun j hj => k4v _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vc)
    (by rw [Memory.readN_congr (fun j hj => k4v _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k2v _ (by omega) (by omega))]; exact vp)
    (by rw [Memory.readN_congr (fun j hj => k4v _ (by omega) (by omega))]; exact cl)
    hv (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_735 bs_31348
    (fun a h1 h2 => by rw [drd, crd, brd, ard]; exact hrv a h1 h2)
    (fun a h1 h2 => by rw [dwr, cwr, bwr, awr]; exact hwv a h1 h2)
    (fun a h1 h2 => by rw [drd, crd, brd, ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
    (fun a h1 h2 => by rw [dwr, cwr, bwr, awr]; exact hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [dwr, cwr, bwr, awr]; exact hwF a (by omega) (by omega))
  -- the saved words, through everything
  have k5 : ∀ a, F - 24 ≤ a → a < F → μ5.read a = μ1.read a := fun a h1 h2 => by
    rw [efr a (by omega) (by omega) (by omega) (by omega), dfr a (by omega) (by omega), k3 a (by omega) h2,
      bfr a (by omega) (by omega)]
  obtain ⟨ω6, run6, f0, f1, f5, f6⟩ := Prefix.pt (p := p) (P := P) (R := R) x ω5 μ5 31348 (F - 56) ret t r5 r6
    (Or.inr rfl) (by omega) e1
    (by rw [show F - 56 + 48 = F - 8 by omega, Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))]
        exact a0')
    (by rw [show F - 56 + 40 = F - 16 by omega, Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))]
        exact a5')
    (by rw [show F - 56 + 32 = F - 24 by omega, Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega))]
        exact a6')
    hr5 hr6 hret hjt hbt
    (fun a h1 h2 => by rw [erd, drd, crd, brd, ard]; exact Memory.readable_of_writable (hwF a (by omega) (by omega)))
  refine ⟨ω6, μ5, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    f0, by rw [f1]; congr 1; omega, f5, f6, ?_, by rw [el, Nat.add_assoc], fun a h0' h1' h2' h3' => ?_,
    fun a => by rw [erd, drd, crd, brd, ard], fun a => by rw [ewr, dwr, cwr, bwr, awr]⟩
  · have o1 : μ5.readN (ptr + len) 1 = [UInt8.ofNat (2 ^ 8 - 2 ^ (8 - l) + n / 2 ^ (8 * l))] := by
      rw [Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)),
        Memory.readN_congr (fun j hj => dfr _ (by omega) (by omega)), cd]
      exact bo
    rw [henc, Enc.readN_add', show ptr + len + 1 = ptr + (len + 1) by omega, ed,
      ← readN_take _ _ 8 l (by omega), dw, enc_take l _ (by omega), o1]
    rfl
  · rw [efr a h0' (by omega) (by omega) h3', dfr a h0' (by omega), cfr a h0' (by omega) (by omega) h3',
      k2 a h0' (by omega)]

/-- **The length prefix of n > 0 elements** (30977): `prefix_small` (n < 2^7) or `prefix_big`, appending
    ℰ(n) (GP v0.8.0 Appendix C). -/
theorem prefix_pos {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (ω : Regs) (μ : Memory)
    (F c v cap ptr len ret t r5 r6 n : Nat) (hF : 65536 + 256 ≤ F ∧ F < 4294967296 ∧ F % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 136 ∨ F ≤ c) (hn : rdN μ c 4 = n) (hn1 : 0 < n)
    (hrc : ∀ a, c ≤ a → a < c + 4 → μ.readable a = true)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len) (hroom : len + (Blob.encodeNat n).length ≤ cap)
    (hcap : cap < 18446744073709551616)
    (hv : v + 24 ≤ 4294967296) (hvF : v + 24 ≤ F - 136 ∨ F ≤ v)
    (hd : 65536 ≤ ptr + len ∧ ptr + len + (Blob.encodeNat n).length + 16 < 4294967296)
    (hdF : F ≤ ptr + len ∨ ptr + len + (Blob.encodeNat n).length + 16 ≤ F - 136)
    (hdv : v + 24 ≤ ptr + len ∨ ptr + len + (Blob.encodeNat n).length ≤ v)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true)
    (hwd : ∀ a, ptr + len ≤ a → a < ptr + len + (Blob.encodeNat n).length → μ.writable a = true)
    (hwF : ∀ a, F - 136 ≤ a → a < F → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x t ω' μ' x 2000 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN (ptr + len) (Blob.encodeNat n).length = Blob.encodeNat n ∧
      μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + (Blob.encodeNat n).length) ∧
      (∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) →
        (a < ptr + len ∨ ptr + len + (Blob.encodeNat n).length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rcases Nat.lt_or_ge n 128 with hs | hs
  · rw [encodeNat_small n ⟨hn1, hs⟩] at *
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at *
    obtain ⟨ω', μ', run, rest⟩ := Prefix.prefix_small (p := p) (P := P) (R := R) x ω μ F c v cap ptr len ret t
      r5 r6 n hF h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn ⟨hn1, hs⟩ hrc vc vp vl hroom hcap hv hvF hd hdF hdv hret
      hjt hbt hrv hwv hwd hwF
    exact ⟨ω', μ', run.mono (by omega), rest⟩
  · exact prefix_big x ω μ F c v cap ptr len ret t r5 r6 n hF h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn hs hrc vc vp
      vl hroom hcap hv hvF hd hdF hdv hret hjt hbt hrv hwv hwd hwF

/-- **Refine's output encoder, for any number of `EncOkM` elements** (30073): `EncM.encode_okM` without
    the bound n < 128. For 0 < n < 2^32 instructions at E, each encoding to `enc j` by `EncOkM`, with the
    buffer's capacity holding everything (`|ℰ(n)| + off + 2 ≤ cap`), the encoder writes ℰ(n) (GP v0.8.0
    Appendix C), the n encodings and the work item's 2-octet `work_item_index` into the buffer, stores the
    result `{cap, buf, |output|}` at O and returns to `ret`. Memory changes only in the stack
    [M − 136, M + 80), the result and the buffer. -/
theorem encode_okM_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (ω : Regs) (μ : Memory)
    {M E n buf cap S0 : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Memory → Prop}
    {src : Nat → Nat → Prop}
    (L : EncM.LayLM P p M E n buf cap enc rep src μ) (O ret t r5 r6 : Nat) (hn : 0 < n ∧ n < 4294967296)
    (hcapw : (Blob.encodeNat n).length + Loop.off enc n + 2 ≤ cap)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cap) (h6 : ω[6] = UInt64.ofNat (232 * n))
    (h7 : ω[7] = UInt64.ofNat buf)
    (s0 : μ.readN M 8 = Num.encodeLE 8 O) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n) (sE : μ.readN (S0 + 8) 8 = Num.encodeLE 8 E)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS0 : S0 + 26 ≤ M - 136 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296)
    (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 8)
    (rS0 : ∀ a, S0 + 8 ≤ a → a < S0 + 26 → μ.readable a = true)
    (hO : O + 24 ≤ 4294967296) (hOM : O + 24 ≤ M - 136 ∨ M + 80 ≤ O) (hOb : O + 24 ≤ buf ∨ buf + cap ≤ O)
    (wO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30073 ω μ x t ω' μ' x (4100 * n + 2000 * Loop.off enc n + 2500) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 ((Blob.encodeNat n).length + Loop.off enc n + 2) ∧
      μ'.readN buf ((Blob.encodeNat n).length + Loop.off enc n + 2) =
        Blob.encodeNat n ++ Loop.out enc n ++ μ.readN (S0 + 24) 2 ∧
      (∀ a, a < 4294967296 → (a < M - 136 ∨ M + 80 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        (a < buf ∨ buf + cap ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hcap := L.hcap
  -- the prologue and the count
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, ac, ap, al, a52, afr, ard, awr⟩ := Top.t1 (p := p) (P := P)
    (R := R) x ω μ M buf cap S0 E n (by omega) ⟨by omega, by omega⟩ (by omega) hn.2 h1 h5 h7 s8 s16 (by omega)
    (by omega) sE (by omega) (fun a h1 h2 => L.rM a h1 h2) (fun a h1 h2 => rS0 a h1 (by omega))
    (fun a h1 h2 => L.wM a (by omega) (by omega))
  -- the length prefix ℰ(n)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bo, bl, bfr, brd, bwr⟩ := prefix_pos (p := p) (P := P) (R := R)
    x ω1 μ1 M (M + 52) (M + 24) cap buf 0 1416 30122 E (232 * n) n ⟨by omega, by omega, hM8⟩ a0 a1 a5
    (by rw [a6, h6]) a7 a8 (by omega) (by omega) (by omega) (by omega) a52 hn.1
    (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega)) ac (by simpa using ap) (by simpa using al)
    (by omega) hcap.2 (by omega) (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_707 bs_30122
    (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) →
      (a < buf ∨ buf + (Blob.encodeNat n).length ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 => by
    rw [bfr a h0 (by omega) (by simpa using h2) (by omega), afr a h0 (by omega)]
  have k1w : ∀ a, M + 24 ≤ a → a < M + 40 → μ2.read a = μ1.read a := fun a h1 h2 =>
    bfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, rest⟩ := EncM.rest (R := R) x ω2 μ μ2 (pre := Blob.encodeNat n) L hcapw O ret t r5 r6
    hn b1 b5 b6
    (by rw [Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ac)
    (by rw [Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ap)
    (by simpa using bl) (by simpa using bo) k2
    (fun a => by rw [brd, ard]) (fun a => by rw [bwr, awr])
    s0 s8 s16 sr s5 s6 hr5 hr6 hret hjt hbt hS0 hS0' hS0b rS0 hO hOM hOb wO
  exact ⟨ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), rest⟩

end Services.Bootstrap.Encode.PrefixBig
