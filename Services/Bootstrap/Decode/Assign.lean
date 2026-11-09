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
  Services.Bootstrap.Decode.Loop

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

/-- **`Assign`, as an element of the decode loop** (tag 12; GP v0.8.0 B.7, Ω_A): with the globals
    `gl` holding at 196680 a word G whose low 32 bits n (the queue's length 𝖰) are 1 … 512, the
    encoding [12] ++ c2 ++ hb ++ w4 (the core's two octets, n hashes, the assigner's four) decodes to
    `Assign`'s slot (`AssignRep`), its queue a fresh `Vec` in the heap; or an allocation fails. -/
theorem assign_elemF {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (F RD : Nat) (hL : Lay F RD)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (G : Nat)
    (hG : G < 18446744073709551616)
    (gv : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 G)
    (hn : 1 ≤ G % 4294967296 ∧ G % 4294967296 ≤ 512)
    (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * (G % 4294967296))
    (hw4 : w4.length = 4) :
    ElemOkAF env cap pb gl p P F RD (1000 + 550 * (G % 4294967296)) (12 :: (c2 ++ hb ++ w4))
      (AssignRep (G % 4294967296) c2 hb w4) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hg
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  have hL : (12 :: (c2 ++ hb ++ w4)).length = 7 + 32 * (G % 4294967296) := by
    simp [hc2, hhb, hw4]; omega
  simp only [hL, show 7 + 32 * (G % 4294967296) - 1 = 2 + 32 * (G % 4294967296) + 4 by omega,
    List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  obtain ⟨n, hnG⟩ : ∃ n, n = G % 4294967296 := ⟨_, rfl⟩
  rw [← hnG] at hn hhb hl hp' pay rpay hcph ⊢
  have hst : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.writable a = true := H.st
  have ht0 := H.wf.2.2.2.1
  unfold TilesOk at ht0
  have htop0 : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcpm' := ht0.mem_lt cp hcp
  have hT0 := H.hbT
  have hb00 := H.hb0
  have hp31 : ptr + (2 + 32 * n + 4) < 2147483648 := by omega
  -- the payload's parts
  have hlist : c2 ++ hb ++ w4 = c2 ++ (hb ++ w4) := List.append_assoc _ _ _
  have pc2 : μ.readN ptr 2 = c2 := by
    have := readN_sub μ ptr (2 + 32 * n + 4) 0 2 _ pay (by omega)
    simp only [Nat.add_zero] at this
    rw [this]; simp [List.take_append, hc2]
  have phb : ∀ k, k < n → μ.readN (ptr + 2 + 32 * k) 32 = (hb.drop (32 * k)).take 32 := by
    intro k hk
    have := readN_sub μ ptr (2 + 32 * n + 4) (2 + 32 * k) 32 _ pay (by omega)
    rw [show ptr + 2 + 32 * k = ptr + (2 + 32 * k) by omega, this]
    simp [List.drop_append, List.take_append, hc2, hhb, List.drop_eq_nil_of_le]
    omega
  have pw4 : μ.readN (ptr + 2 + 32 * n) 4 = w4 := by
    have := readN_sub μ ptr (2 + 32 * n + 4) (2 + 32 * n) 4 _ pay (by omega)
    rw [show ptr + 2 + 32 * n = ptr + (2 + 32 * n) by omega, this]
    simp [List.drop_append, List.take_append, hc2, hhb, hw4, List.drop_eq_nil_of_le]
    exact List.take_of_length_le (by omega)
  have hc2v : Num.decodeLE c2 < 65536 := by have := decodeLE_lt c2; rw [hc2] at this; simpa using this
  have ec2 : Num.encodeLE 2 (Num.decodeLE c2) = c2 := by have := encodeLE_decodeLE c2; rwa [hc2] at this
  have hw4v : Num.decodeLE w4 < 4294967296 := by have := decodeLE_lt w4; rw [hw4] at this; simpa using this
  have ew4 : Num.encodeLE 4 (Num.decodeLE w4) = w4 := by have := encodeLE_decodeLE w4; rwa [hw4] at this
  -- the dispatch and the helper's entry
  obtain ⟨ω1, run1, d0, d1, d5, d6⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ
    F 12 (by omega) (by omega) h1 h7 (by simpa using tag) tab
    (Memory.readable_of_writable (hst _ (by omega) (by omega))) rt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f80, f72, f64, ffr, frd, fwr⟩ :=
    as1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ F (F + 120) RD
      ⟨by omega, by omega⟩ (d1.trans h1) (d5.trans h5) (d6.trans h6) (by omega) (by omega)
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- the core, into H + 40
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1152 24765 (F - 88) RD
      (F - 48) ptr len 2 f0 f1 f7 f8 f9 (by omega) jte_575 bs_24765 ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) hl'
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [fwr]; exact wr a h1 h2)
      (fun a h1 h2 => by rw [fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [frd]; exact rpay a h1 (by omega))
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rP)
      (by rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega))]; exact rL)
  have low3 : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha =>
    (gfr a (by omega) (by omega) (by omega) (by omega)).trans (ffr a (by omega) (by omega))
  have hg3 : ∀ a, Glob a → μ3.read a = gl a := fun a ha => by
    have h' := ha; unfold Glob at h'; rw [low3 a (by omega)]; exact hg a ha
  have H3 : HeapCtx env pb S0 S1 μ3 s := heap_of_high H low3 (fun a => by rw [gwr, fwr])
  -- the global, and the call of the hash-Vec decoder
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k8, k9, k32, k24, kfr, krd, kwr⟩ :=
    as2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (F - 88) (F + 120) RD
      (Num.decodeLE c2) G ⟨by omega, by omega⟩ (g1.trans f1) (g5.trans f5) (g6.trans f6) g7 (by omega)
      (by omega) hc2v (by rw [gbuf, Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), pc2, ec2])
      hG (glob_word gv hg3)
      (fun a h1 h2 => Memory.readable_of_writable (glob_writable H3 ⟨by omega, by omega⟩))
      (fun a h1 h2 => by rw [gwr, fwr]; exact hst a (by omega) (by omega))
  have low4 : ∀ a, a < 2147483648 → μ4.read a = μ.read a := fun a ha =>
    (kfr a (by omega) (Or.inl (by omega))).trans (low3 a ha)
  have H4 : HeapCtx env pb S0 S1 μ4 s := heap_of_high H3 (fun a ha => (kfr a (by omega) (Or.inl (by omega))))
    (fun a => by rw [kwr])
  have hcpm := hcp
  -- the queue: n hashes, into a fresh Vec at H + 40
  rcases VecHash.vec_hash (p := p) (P := P) env cap pb hcap1 hcap x ω4 μ4 s cp (F - 240) n RD (ptr + 2)
      (len - 2) (F - 48) 1154 24826 196680 RD (fun k => (hb.drop (32 * k)).take 32) H4 k0 k1 k5 k6 k7 k8
      (by rw [hnG]; exact k9) hn ⟨by omega, by omega, by omega⟩ (by omega) ⟨by omega, by omega⟩
      (Or.inr (by omega)) ⟨hcp, hcpu⟩
      (fun a h1 h2 => by unfold InData; omega)
      (fun k hk => by
        rw [Memory.readN_congr (fun j hj => low4 _ (by omega)), show ptr + 2 + 32 * k = ptr + 2 + 32 * k from rfl]
        exact phb k hk)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR8)
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ jte_576 bs_24826 with
    ⟨q, s', ω5, μ5, ha, run5, v0, v1, v5', v6', vO, vO8, vO16, vel, vR0, vR8, H5, hnew, hfresh, keepU, keepD, vfr,
      vlow, vglob, vwr⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre (run1.trans (run2.trans (run3.trans run4))) ex).mono (by omega))
  -- the new chunk's place
  have ht5 := H5.wf.2.2.2.1
  unfold TilesOk at ht5
  have htop5 : s'.top = s'.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hqm := ht5.mem_lt _ hnew
  simp only at hqm
  have hT5 := H5.hbT
  have hb05 := H5.hb0
  have hq31 : 206896 ≤ q ∧ q + 32 * n < 2147483648 := by omega
  have hg4 : ∀ a, Glob a → μ4.read a = gl a := fun a ha => by
    have h' := ha; unfold Glob at h'; rw [low4 a (by omega)]; exact hg a ha
  have hg5 : ∀ a, Glob a → μ5.read a = gl a := fun a ha => (vglob a ha).trans (hg4 a ha)
  have hst5 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ5.writable a = true := H5.st
  -- the Vec copied, the global reloaded, and the assigner's call
  obtain ⟨ω6, μ6, run6, m0, m1, m5, m6, m7, m8, m9, m16, m8', m0', mfr, mrd, mwr⟩ :=
    as3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (F - 88) RD n q n G
      ⟨by omega, by omega⟩ v1 v5' v6' (by omega) (by omega) (by omega) (by omega) vO vO8 vO16 hG
      (glob_word gv hg5) (fun a h1 h2 => Memory.readable_of_writable (glob_writable H5 ⟨by omega, by omega⟩))
      (fun a h1 h2 => hst5 a (by omega) (by omega))
  have pw46 : μ6.readN (ptr + 2 + 32 * n) 4 = w4 := by
    rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((keepD cp hcp hcpu _ ⟨by omega, by omega⟩).trans (low4 _ (by omega))))]
    exact pw4
  obtain ⟨ω7, μ7, run7, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω6 μ6 1156 24867 (F - 88) RD
      (F - 48) (ptr + 2 + 32 * n) (len - 2 - 32 * n) 4 m0 m1 m7 m8 m9 (by omega) jte_577 bs_24867
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst5 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst5 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst5 a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [mrd]; exact Memory.readable_of_writable
          (heap_writable_data H5 (keepU cp hcp hcpu) hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR0)
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR8)
  -- the frame above H, from the start to before the store
  have up7 : ∀ a, (F - 24) ≤ a → a < 4294967296 →
      (a < RD ∨ (RD + 16) ≤ a) → μ7.read a = μ2.read a := fun a h0 h1 h3 =>
    (nfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))).trans ((mfr a h1 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((vfr a (by omega) h1 h3 (Or.inr (by omega))).trans ((kfr a h1 (Or.inr (by omega))).trans
        (gfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))))))
  have up2 : ∀ a, F ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h0 h1 =>
    ffr a h1 (Or.inr h0)
  have sv : ∀ a v, a + 8 ≤ RD → F ≤ a → μ.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (up7 _ (by omega) (by omega) (by omega)).trans
      (up2 _ (by omega) (by omega)))]; exact h
  have sH : ∀ a v, (F - 88) ≤ a → a + 8 ≤ (F - 48) → μ6.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))]
    exact h
  have sK4 : ∀ a v, (F - 88) + 24 ≤ a → a + 8 ≤ (F - 48) → μ4.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((mfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans (vfr _ (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega)))))]
    exact h
  have sA : ∀ a v, (F - 88) + 64 ≤ a → a + 8 ≤ F → μ2.readN a 8 = Num.encodeLE 8 v →
      μ7.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => up7 _ (by omega) (by omega) (by omega))]; exact h
  have hst7 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ7.writable a = true := fun a h1 h2 => by
    rw [nwr, mwr]; exact hst5 a h1 h2
  -- the variant, into the slot O, and the returns
  obtain ⟨ω8, μ8, run8, o0, o1, o5, o6, oO, oO8, oO16, oO24, oO32, oO36, ofr, ord, owr⟩ :=
    as4 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (F - 88) (F + 120) 18 723 v5 v6 RD
      n q n G (Num.decodeLE w4) (Num.decodeLE c2) (by omega) (by omega) (Or.inr (by omega)) (n1.trans m1)
      (n5.trans m5) n7 hG hv5 hv6 (by omega) (by omega) (by omega) (by omega) (by omega) hw4v hc2v
      (sH _ _ (by omega) (by omega) m0') (sH _ _ (by omega) (by omega) m8') (sH _ _ (by omega) (by omega) m16)
      (sK4 _ _ (by omega) (by omega) k24) (sK4 _ _ (by omega) (by omega) k32)
      (by rw [nbuf, pw46, ew4])
      (sA _ _ (by omega) (by omega) f80) (sA _ _ (by omega) (by omega) f72) (sA _ _ (by omega) (by omega) f64)
      (sv _ _ (by omega) (by omega) s0) (sv _ _ (by omega) (by omega) s5) (sv _ _ (by omega) (by omega) s6)
      ⟨by omega, by omega, by omega⟩ jte_8 bs_723
      (fun a h1 h2 => hst7 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst7 a (by omega) (by omega)))
  have low85 : ∀ a, a < 2147483648 → μ8.read a = μ5.read a := fun a ha =>
    (ofr a (by omega) (Or.inl (by omega))).trans ((nfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (mfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))))
  refine Or.inl ⟨ω8, μ8, s', (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    (run7.trans run8))))))).mono (by omega), o1, o5, o6, ?_, ?_,
    ⟨9223372036854775819, by omega, oO, by omega⟩,
    heap_of_high H5 low85 (fun a => by rw [owr, nwr, mwr]), keepU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR0]; congr 1; omega
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR8]; congr 1; omega
  · intro c hc hu a ha
    have hcm := ht0.mem_lt c hc
    have hd := ha
    unfold InData at hd
    rw [low85 a (by omega), keepD c hc hu a ha, low4 a (by omega)]
  · refine ⟨[⟨q - 32, n + 1, true⟩], fun c hc => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc
      subst hc
      exact ⟨hnew, rfl, hfresh⟩
    · refine ⟨by rw [readN_take _ _ 232 8 (by omega)]; exact oO, q, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_⟩
      · rw [← readN_sub μ8 (F + 120) 232 8 8 _ rfl (by omega)]; exact oO8
      · rw [← readN_sub μ8 (F + 120) 232 16 8 _ rfl (by omega)]; exact oO16
      · rw [← readN_sub μ8 (F + 120) 232 24 8 _ rfl (by omega)]; rw [oO24, ← hnG, Nat.min_self]
      · rw [← readN_sub μ8 (F + 120) 232 32 4 _ rfl (by omega)]; rw [oO32, ew4]
      · rw [← readN_sub μ8 (F + 120) 232 36 2 _ rfl (by omega)]; rw [oO36, ec2]
      · rw [Memory.readN_congr (fun j hj => (hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩).trans (low85 _ (by omega)))]
        exact vel k hk
  · intro a h0 h1 h2 h3
    rw [ofr a h1 (by omega), up7 a (by omega) h1 h2]; exact up2 a (by omega) h1
  · intro a ha
    rw [low85 a (by omega), (vlow a ha).1, low4 a (by omega)]
  · intro a ha
    rw [ord, nrd, mrd, (vlow a ha).2, krd, grd, frd]
  · intro a ha
    have h' := ha; unfold Glob at h'
    rw [low85 a (by omega), vglob a ha, low4 a (by omega)]
  · intro a ha
    rw [owr, nwr, mwr, vwr a ha, kwr, gwr, fwr]


/-- `assign_elemF` in refine's frame. -/
/-- **`Assign`, as an element of the decode loop** (tag 12; GP v0.8.0 B.7, Ω_A): with the globals
    `gl` holding at 196680 a word G whose low 32 bits n (the queue's length 𝖰) are 1 … 512, the
    encoding [12] ++ c2 ++ hb ++ w4 (the core's two octets, n hashes, the assigner's four) decodes to
    `Assign`'s slot (`AssignRep`), its queue a fresh `Vec` in the heap; or an allocation fails. -/
theorem assign_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8) (G : Nat)
    (hG : G < 18446744073709551616)
    (gv : (List.range 8).map (fun k => gl (196680 + k)) = Num.encodeLE 8 G)
    (hn : 1 ≤ G % 4294967296 ∧ G % 4294967296 ≤ 512)
    (c2 hb w4 : List UInt8) (hc2 : c2.length = 2) (hhb : hb.length = 32 * (G % 4294967296))
    (hw4 : w4.length = 4) :
    ElemOkA env cap pb gl p P (1000 + 550 * (G % 4294967296)) (12 :: (c2 ++ hb ++ w4))
      (AssignRep (G % 4294967296) c2 hb w4) :=
  assign_elemF env cap pb 4278057632 4278058648 lay_refine hcap1 hcap gl G hG gv hn c2 hb w4 hc2 hhb hw4

end Services.Bootstrap.Decode.Assign
