import Services.Bootstrap.Decode.VecHash
import Services.Bootstrap.Decode.U32Hash

/-!
# `Instruction::decode`: `Assign { core: u16, queue: [Hash; 𝖰], assigner: u32 }`

`Assign` (tag 12) is decoded by a helper with an 88-octet frame at H = A − 88 (the return address 952,
O and the reader at H + 80, H + 72, H + 64). It reads the `u16` core into H + 40, parks it at H + 24,
reads the queue's length 𝖰 from the word at 196680 (the global the service's start-up copied from its
protocol parameters, GP v0.8.0 §B: 𝖰 = 80), and decodes 𝖰 hashes with the hash-`Vec` decoder at 1764
(`vec_hash`) into H + 40. It copies that `Vec` to H + 16, H + 8, H + 0, reads the `u32` assigner into
H + 40 and stores the variant into the slot O: the discriminant word 2^63 + 11 at O, the `Vec`'s
capacity and pointer at O + 8 and O + 16, its length capped by the global (`min len (𝖰 mod 2^32)`) at
O + 24, the assigner at O + 32 and the core at O + 36.
-/

namespace Services.Bootstrap.Decode.Assign

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 20971 … 21010: `Assign`'s decoder enters the helper: an 88-octet frame at H = A − 88 saving the
    return address 952, O and the reader at H + 80, H + 72, H + 64, a zeroed `u16` at H + 40, and the
    call of the reader for 2 octets into H + 40 (return address 1152). -/
theorem as1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 88 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 88 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 20971 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1152 ∧ ω'[1] = UInt64.ofNat (A - 88) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 48) ∧
      ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 952 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 88 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 88 + 80 = A - 8 by omega, show A - 88 + 72 = A - 16 by omega,
      show A - 88 + 64 = A - 24 by omega]; post_simp)

/-- A word shifted left and then right by 32 keeps its low 32 bits. -/
theorem shl_shr32 (G : Nat) :
    G % 18446744073709551616 * 4294967296 % 18446744073709551616 / 4294967296 = G % 4294967296 := by
  rw [show (18446744073709551616 : Nat) = 4294967296 * 4294967296 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by decide), Nat.mod_mul_right_mod]

/-- The low 32 bits by a mask on the left: `0xffffffff & G = G mod 2^32`. -/
theorem mask32 (G : Nat) : Exec.bitwise (fun x1 x2 => x1 && x2) 4294967295 G = G % 4294967296 := by
  have : Exec.bitwise (fun x1 x2 => x1 && x2) 4294967295 G = Exec.bitwise (· && ·) G 4294967295 := by
    unfold Exec.bitwise; congr 1; funext i; exact Bool.and_comm _ _
  rw [this, bitwise_and_low _ 4294967295 32 (by decide) (by decide)]

/-- 24765 … 24820: the `u16` read succeeded (ω₇ = 0): the helper saves O at H + 32, parks the core
    at H + 24, takes the queue's length from the word G at 196680 (its low 32 bits) and calls the
    hash-`Vec` decoder at 1764 for it, into H + 40 (return address 1154). -/
theorem as2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H O rd c G : Nat)
    (hH : 196688 ≤ H ∧ H + 88 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hc : c < 65536) (cv : μ.readN (H + 40) 2 = Num.encodeLE 2 c)
    (hG : G < 18446744073709551616) (gv : μ.readN 196680 8 = Num.encodeLE 8 G)
    (hgr : ∀ a, 196680 ≤ a → a < 196688 → μ.readable a = true)
    (hw : ∀ a, H + 24 ≤ a → a < H + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 24765 ω μ x 1764 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1154 ∧ ω'[1] = UInt64.ofNat H ∧ ω'[5] = UInt64.ofNat 196680 ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat (H + 40) ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat (G % 4294967296) ∧
      μ'.readN (H + 32) 8 = Num.encodeLE 8 O ∧ μ'.readN (H + 24) 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < H + 24 ∨ H + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc : rdN μ (H + 40) 2 = c := by
    show Num.decodeLE _ = _
    rw [cv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hc)]
  have rG : rdN μ 196680 8 = G := by
    show Num.decodeLE _ = _
    rw [gv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hG)]
  have hr : ∀ a, H + 24 ≤ a → a < H + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hH, hw, hr, hgr, rc, rG, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (simp (disch := pvm_arith) only [rdN_writeN_disjoint, rc, rG, Nat.mod_eq_of_lt (show c < 18446744073709551616 by omega),
      shl_shr32])

/-- 24826 … 24860: the hash-`Vec` decoder returned a `Vec` (capacity K ≠ 2^64 − 1, pointer q, length
    m at H + 40): the helper copies it to H + 16, H + 8, H + 0, reloads the global G' at 196680 (ω₅),
    zeroes a `u32` at H + 40 and calls the reader for 4 octets into H + 40 (return address 1156). -/
theorem as3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (H rd K q m G' : Nat)
    (hH : 196688 ≤ H ∧ H + 88 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat H)
    (h5 : ω[5] = UInt64.ofNat 196680) (h6 : ω[6] = UInt64.ofNat rd) (hrd : rd < 18446744073709551616)
    (hK : K < 18446744073709551615) (hq : q < 18446744073709551616) (hm : m < 18446744073709551616)
    (kv : μ.readN (H + 40) 8 = Num.encodeLE 8 K) (qv : μ.readN (H + 48) 8 = Num.encodeLE 8 q)
    (mv : μ.readN (H + 56) 8 = Num.encodeLE 8 m)
    (hG : G' < 18446744073709551616) (gv : μ.readN 196680 8 = Num.encodeLE 8 G')
    (hgr : ∀ a, 196680 ≤ a → a < 196688 → μ.readable a = true)
    (hw : ∀ a, H ≤ a → a < H + 64 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 24826 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1156 ∧ ω'[1] = UInt64.ofNat H ∧ ω'[5] = UInt64.ofNat G' ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (H + 40) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (H + 16) 8 = Num.encodeLE 8 K ∧ μ'.readN (H + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN H 8 = Num.encodeLE 8 m ∧
      (∀ a, a < 4294967296 → (a < H ∨ H + 24 ≤ a) → (a < H + 40 ∨ H + 44 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd8 : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rK := rd8 _ K (by omega) kv
  have rq := rd8 _ q hq qv
  have rm := rd8 _ m hm mv
  have rG := rd8 _ G' hG gv
  have hr : ∀ a, H ≤ a → a < H + 64 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hH, hw, hr, hgr, rK, rq, rm, rG, hK, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (simp (disch := pvm_arith) only [rdN_writeN_disjoint, rK, rq, rm, rG,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hG, Nat.mod_eq_of_lt hrd,
      Nat.mod_eq_of_lt (show K < 18446744073709551616 by omega)])

/-- 24867 … 25010 then 21014 … 21026: the `u32` read succeeded (ω₇ = 0): the helper stores `Assign`'s
    discriminant word 2^63 + 11 at O, the `Vec`'s capacity K and pointer q at O + 8 and O + 16, its length
    m capped by the global G' (`min m (G' mod 2^32)`) at O + 24, the assigner (H + 40) at O + 32 and
    the core (H + 24) at O + 36, pops its frame and returns to 21014, and the decoder returns through its
    frame at A = H + 88. -/
theorem as4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (H O ret t v5 v6 rd K q m G' w c : Nat) (hA : H + 88 + 56 < 4294967296) (hO : O + 38 ≤ 4294967296)
    (hOS : O + 38 ≤ H ∨ H + 144 ≤ O)
    (h1 : ω[1] = UInt64.ofNat H) (h5 : ω[5] = UInt64.ofNat G') (h7 : ω[7] = UInt64.ofNat 0)
    (hG : G' < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616) (hOv : O < 18446744073709551616)
    (hK : K < 18446744073709551616) (hq : q < 18446744073709551616) (hm : m < 18446744073709551616)
    (hw4 : w < 4294967296) (hc : c < 65536)
    (sm : μ.readN H 8 = Num.encodeLE 8 m) (sq : μ.readN (H + 8) 8 = Num.encodeLE 8 q)
    (sK : μ.readN (H + 16) 8 = Num.encodeLE 8 K) (sc : μ.readN (H + 24) 8 = Num.encodeLE 8 c)
    (sO : μ.readN (H + 32) 8 = Num.encodeLE 8 O) (sw : μ.readN (H + 40) 4 = Num.encodeLE 4 w)
    (sr : μ.readN (H + 80) 8 = Num.encodeLE 8 952) (sO' : μ.readN (H + 72) 8 = Num.encodeLE 8 O)
    (srd : μ.readN (H + 64) 8 = Num.encodeLE 8 rd)
    (s0 : μ.readN (H + 136) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (H + 128) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (H + 120) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 38 → μ.writable a = true)
    (hr : ∀ a, H ≤ a → a < H + 144 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 24867 ω μ x t ω' μ' x 28 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (H + 144) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775819 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 K ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 24) 8 = Num.encodeLE 8 (min m (G' % 4294967296)) ∧
      μ'.readN (O + 32) 4 = Num.encodeLE 4 w ∧ μ'.readN (O + 36) 2 = Num.encodeLE 2 c ∧
      (∀ a, a < 4294967296 → (a < O ∨ O + 38 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd8 : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rm := rd8 _ m hm sm
  have rq := rd8 _ q hq sq
  have rK := rd8 _ K hK sK
  have rc := rd8 _ c (by omega) sc
  have rO := rd8 _ O hOv sO
  have rO' := rd8 _ O hOv sO'
  have rr := rd8 _ 952 (by decide) sr
  have rrd := rd8 _ rd hrd srd
  have rw4 : rdN μ (H + 40) 4 = w := by
    show Num.decodeLE _ = _
    rw [sw, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hw4)]
  have r0 : rdN μ (H + 88 + 48) 8 = ret := by rw [show H + 88 + 48 = H + 136 by omega]; exact rd8 _ ret (by omega) s0
  have r5 : rdN μ (H + 88 + 40) 8 = v5 := by rw [show H + 88 + 40 = H + 128 by omega]; exact rd8 _ v5 hv5 s5
  have r6 : rdN μ (H + 88 + 32) 8 = v6 := by rw [show H + 88 + 32 = H + 120 by omega]; exact rd8 _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rm, rq, rK, rc, rO, rO', rr, rrd, rw4, r0, r5, r6, hret, hjt, hbt,
      jte_475, bs_21014, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try exact (encodeLE_mod 4 _).trans (encodeLE4_sxw w hw4)
    all_goals try (simp only [mask32, Nat.mod_eq_of_lt (show G' % 4294967296 < 18446744073709551616 by omega)]; congr 1; rw [Nat.min_def]; split <;> split <;> omega)

open Picoalloc JAM Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

/-- **`Assign`'s slot**: the discriminant word 2^63 + 11; the queue, a `Vec` of capacity and length n
    at some q, whose n hashes are the 32-octet pieces of `hb` (in the heap μ); the assigner's four
    octets `w4` at 32 and the core's two `c2` at 36. -/
def AssignRep (n : Nat) (c2 hb w4 : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775819 ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ (bs.drop 32).take 4 = w4 ∧ (bs.drop 36).take 2 = c2 ∧
    ∀ k, k < n → μ.readN (q + 32 * k) 32 = (hb.drop (32 * k)).take 32

/-- The globals' octets at 196680 … 196688 read as the word G in every memory that holds `gl`
    there. -/
theorem glob_word {gl : Nat → UInt8} {G : Nat}
    (gv : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 G) {μ : Memory}
    (hg : ∀ a, Glob a → μ.read a = gl a) : μ.readN 196680 8 = Num.encodeLE 8 G := by
  rw [← gv]
  unfold Memory.readN
  apply List.map_congr_left
  intro k hk
  simp only [List.mem_range] at hk
  exact hg _ ⟨by omega, by omega⟩

/-- The globals lie on the heap's first page, which is writable. -/
theorem glob_writable {env : RefineHost.Env} {pb : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {a : Nat} (ha : 196608 ≤ a ∧ a < 196792) : μ.writable a = true := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hq := hp (a / 4096) (by omega) (by omega)
  unfold Memory.writable
  rw [show pageSize = 4096 from rfl, hq]
  simp only [decide_eq_true_eq]; omega
