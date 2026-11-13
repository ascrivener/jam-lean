import Services.Bootstrap.Decode.Assign
import Services.Bootstrap.DecodeU32

/-!
# `Instruction::decode`: `AssignForGasCost { core: u16, queue: Vec<Hash>, assigner: u32 }`

Tag 24 (GP v0.8.0 B.7, the bootstrap service's instruction list) is decoded by the handler at 21075,
with an 80-octet frame at S = A − 80 (A the decode loop's frame): it saves the return address 960, O
and the reader at S + 72, S + 64, S + 56, reads the `u16` core into S + 32 (parked at S + 24), decodes
the queue's length n (`decodeU32`, its low 32 bits), decodes n hashes with the hash-`Vec` decoder at
1764 (`VecHash.vec_hash`) into S + 32, copies that `Vec` to S + 16, S + 8, S + 0, reads the `u32`
assigner into S + 32 and stores the variant into the slot O: the discriminant word 2^63 + 23 at O, the
`Vec`'s capacity, pointer and length at O + 8, O + 16, O + 24, the assigner at O + 32 and the core at
O + 36. It returns through 960 to 21118, which pops the decode loop's frame.

Unlike `Assign` (tag 12, `Assign.lean`), the hash count is read from the stream rather than from the
global 𝖰, and the length is stored as is.
-/

namespace Services.Bootstrap.Decode.AssignGas

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Decode.Tag
  Services.Bootstrap.Decode.Hash Services.Bootstrap.Decode.HashU64 Services.Bootstrap.Decode.U32Hash
  Services.Bootstrap.Decode.Assign

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 21075 … 21114: tag 24's handler opens an 80-octet frame at S = A − 80 saving the return address
    960, O and the reader at S + 72, S + 64, S + 56, zeroes a `u16` at S + 32 and calls the reader for
    2 octets into S + 32 (return address 1174). -/
theorem ag1 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (A O rd : Nat)
    (hA : 65536 + 80 ≤ A ∧ A < 4294967296) (h1 : ω[1] = UInt64.ofNat A) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (hO : O < 18446744073709551616) (hrd : rd < 18446744073709551616)
    (hw : ∀ a, A - 80 ≤ a → a < A → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 21075 ω μ x 58434 ω' μ' x 15 ∧
      ω'[0] = UInt64.ofNat 1174 ∧ ω'[1] = UInt64.ofNat (A - 80) ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (A - 48) ∧
      ω'[9] = UInt64.ofNat 2 ∧
      μ'.readN (A - 8) 8 = Num.encodeLE 8 960 ∧ μ'.readN (A - 16) 8 = Num.encodeLE 8 O ∧
      μ'.readN (A - 24) 8 = Num.encodeLE 8 rd ∧
      (∀ a, a < 4294967296 → (a < A - 80 ∨ A ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hA, hw]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (simp only [show A - 80 + 72 = A - 8 by omega, show A - 80 + 64 = A - 16 by omega,
      show A - 80 + 56 = A - 24 by omega]; post_simp)

/-- 25390 … 25402: the `u16` read succeeded (ω₇ = 0): the handler parks the core c at S + 24 and calls
    `decodeU32` on the reader (return address 1176). -/
theorem ag2 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O rd c : Nat)
    (hS : 65536 ≤ S ∧ S + 80 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0)
    (hrd : rd < 18446744073709551616)
    (hc : c < 65536) (cv : μ.readN (S + 32) 2 = Num.encodeLE 2 c)
    (hw : ∀ a, S + 24 ≤ a → a < S + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 25390 ω μ x 31894 ω' μ' x 8 ∧
      ω'[0] = UInt64.ofNat 1176 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < S + 24 ∨ S + 32 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc : rdN μ (S + 32) 2 = c := by
    show Num.decodeLE _ = _
    rw [cv, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hc)]
  have hr : ∀ a, S + 24 ≤ a → a < S + 40 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hS, hw, hr, rc, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (simp (disch := pvm_arith) only [rdN_writeN_disjoint, rc,
      Nat.mod_eq_of_lt (show c < 18446744073709551616 by omega)])

/-- 25408 … 25425: `decodeU32` returned the length n (ω₇ = 0, ω₈ = n): the handler checks the result's
    flag (ω₇ & 1 = 0), takes n's low 32 bits and calls the hash-`Vec` decoder at 1764 for n hashes into
    S + 32 (ω₇ = S + 32, ω₈ = the reader; return address 1178). -/
theorem ag3 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O rd n : Nat)
    (hS : S + 80 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O)
    (h6 : ω[6] = UInt64.ofNat rd) (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n)
    (hn : n < 4294967296) (hrd : rd < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 25408 ω μ x 1764 ω' μ x 9 ∧
      ω'[0] = UInt64.ofNat 1178 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat (S + 32) ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat n := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  · pvm_go [h1, h5, h6, h7, h8, hS]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (simp only [shl_shr32, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hrd])

/-- 25431 … 25463: the hash-`Vec` decoder returned a `Vec` (capacity K ≠ 2^64 − 1, pointer q, length
    m at S + 32): the handler copies it to S + 16, S + 8, S + 0, zeroes a `u32` at S + 32 and calls the
    reader for 4 octets into S + 32 (return address 1180). -/
theorem ag4 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory) (S O rd K q m : Nat)
    (hS : 65536 ≤ S ∧ S + 80 ≤ 4294967296) (h1 : ω[1] = UInt64.ofNat S)
    (h5 : ω[5] = UInt64.ofNat O) (h6 : ω[6] = UInt64.ofNat rd)
    (hrd : rd < 18446744073709551616)
    (hK : K < 18446744073709551615) (hq : q < 18446744073709551616) (hm : m < 18446744073709551616)
    (kv : μ.readN (S + 32) 8 = Num.encodeLE 8 K) (qv : μ.readN (S + 40) 8 = Num.encodeLE 8 q)
    (mv : μ.readN (S + 48) 8 = Num.encodeLE 8 m)
    (hw : ∀ a, S ≤ a → a < S + 56 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 25431 ω μ x 58434 ω' μ' x 13 ∧
      ω'[0] = UInt64.ofNat 1180 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat O ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧ ω'[8] = UInt64.ofNat (S + 32) ∧
      ω'[9] = UInt64.ofNat 4 ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 K ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN S 8 = Num.encodeLE 8 m ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 24 ≤ a) → (a < S + 32 ∨ S + 36 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rd8 : ∀ a w, w < 2 ^ 64 → μ.readN a 8 = Num.encodeLE 8 w → rdN μ a 8 = w := by
    intro a w hw h
    show Num.decodeLE _ = _
    rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hw]
  have rK := rd8 _ K (by omega) kv
  have rq := rd8 _ q hq qv
  have rm := rd8 _ m hm mv
  have hr : ∀ a, S ≤ a → a < S + 56 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, rK, rq, rm, hK, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (simp (disch := pvm_arith) only [rdN_writeN_disjoint, rK, rq, rm,
      Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hrd,
      Nat.mod_eq_of_lt (show K < 18446744073709551616 by omega)])

/-- 25470, 25532 … 25586 then 21118 … 21130: the `u32` read succeeded (ω₇ = 0): the handler stores
    `AssignForGasCost`'s discriminant word 2^63 + 23 at O (ω₅), the `Vec`'s capacity K, pointer q and
    length m at O + 8, O + 16, O + 24, the assigner (S + 32, loaded sign-extended and stored as 32 bits)
    at O + 32 and the core (S + 24) at O + 36, pops its frame and returns through 960 to 21118, which
    returns through the decode loop's frame at A = S + 80. -/
theorem ag5 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S O ret t v5 v6 rd K q m w c : Nat) (hA : S + 80 + 56 < 4294967296) (hO : O + 38 ≤ 4294967296)
    (hOS : O + 38 ≤ S ∨ S + 136 ≤ O)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat O) (h7 : ω[7] = UInt64.ofNat 0)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : rd < 18446744073709551616) (hOv : O < 18446744073709551616)
    (hK : K < 18446744073709551616) (hq : q < 18446744073709551616) (hm : m < 18446744073709551616)
    (hw4 : w < 4294967296) (hc : c < 65536)
    (sm : μ.readN S 8 = Num.encodeLE 8 m) (sq : μ.readN (S + 8) 8 = Num.encodeLE 8 q)
    (sK : μ.readN (S + 16) 8 = Num.encodeLE 8 K) (sc : μ.readN (S + 24) 8 = Num.encodeLE 8 c)
    (sw : μ.readN (S + 32) 4 = Num.encodeLE 4 w)
    (sr : μ.readN (S + 72) 8 = Num.encodeLE 8 960) (sO' : μ.readN (S + 64) 8 = Num.encodeLE 8 O)
    (srd : μ.readN (S + 56) 8 = Num.encodeLE 8 rd)
    (s0 : μ.readN (S + 128) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (S + 120) 8 = Num.encodeLE 8 v5)
    (s6 : μ.readN (S + 112) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hw : ∀ a, O ≤ a → a < O + 38 → μ.writable a = true)
    (hr : ∀ a, S ≤ a → a < S + 136 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 25470 ω μ x t ω' μ' x 28 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 136) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 9223372036854775831 ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 K ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 q ∧ μ'.readN (O + 24) 8 = Num.encodeLE 8 m ∧
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
  have rO' := rd8 _ O hOv sO'
  have rr := rd8 _ 960 (by decide) sr
  have rrd := rd8 _ rd hrd srd
  have rw4 : rdN μ (S + 32) 4 = w := by
    show Num.decodeLE _ = _
    rw [sw, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt (by simpa using hw4)]
  have r0 : rdN μ (S + 80 + 48) 8 = ret := by rw [show S + 80 + 48 = S + 128 by omega]; exact rd8 _ ret (by omega) s0
  have r5 : rdN μ (S + 80 + 40) 8 = v5 := by rw [show S + 80 + 40 = S + 120 by omega]; exact rd8 _ v5 hv5 s5
  have r6 : rdN μ (S + 80 + 32) 8 = v6 := by rw [show S + 80 + 32 = S + 112 by omega]; exact rd8 _ v6 hv6 s6
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h7, hA, hO, hOS, hw, hr, rm, rq, rK, rc, rO', rr, rrd, rw4, r0, r5, r6, hret, hjt, hbt,
      jte_479, bs_21118, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try exact (encodeLE_mod 4 _).trans (encodeLE4_sxw w hw4)

/-- n consecutive 32-octet pieces equal one by one make the whole 32·n octets equal. -/
theorem readN_of_pieces (μ μ' : Memory) (q ptr : Nat) :
    ∀ n, (∀ k, k < n → μ'.readN (q + 32 * k) 32 = μ.readN (ptr + 32 * k) 32) →
      μ'.readN q (32 * n) = μ.readN ptr (32 * n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [Nat.mul_succ, Memory.readN_split, Memory.readN_split, ih (fun k hk => h k (by omega)), h n (by omega)]

open Picoalloc JAM Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.Loop

/-- **`AssignForGasCost`'s slot** (GP v0.8.0 B.7, tag 24): the discriminant word 2^63 + 23; the
    assigner's four octets `g` at 32 and the core's two `c` at 36; the queue, a `Vec` of capacity and
    length n at some q, whose 32n octets (in the heap μ) are the n hashes `hs`. -/
def AssignGasRep (c : List UInt8) (n : Nat) (hs g : List UInt8) (bs : List UInt8) (μ : Memory) : Prop :=
  bs.take 8 = Num.encodeLE 8 9223372036854775831 ∧ (bs.drop 32).take 4 = g ∧ (bs.drop 36).take 2 = c ∧
  ∃ q, (bs.drop 8).take 8 = Num.encodeLE 8 n ∧ (bs.drop 16).take 8 = Num.encodeLE 8 q ∧
    (bs.drop 24).take 8 = Num.encodeLE 8 n ∧ μ.readN q (32 * n) = hs

/-- **`AssignForGasCost`, as an element of the decode loop** (tag 24; GP v0.8.0 B.7): for 1 ≤ n ≤ 512
    hashes, the encoding 24 :: (c ++ ℰ(n) ++ hs ++ g) (the core's two octets, the queue's length, the
    32n octets of the n hashes, the assigner's four octets) decodes to `AssignForGasCost`'s slot
    (`AssignGasRep`), its queue a fresh `Vec` in the heap; or an allocation fails. -/
theorem assign_gas_elemF {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (F RD : Nat) (hL : Lay F RD)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 512)
    (c hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n) (hg : g.length = 4) :
    ElemOkAF env cap pb gl p P F RD (1500 + 550 * n) (24 :: (c ++ Blob.encodeNat n ++ hs ++ g))
      (AssignGasRep c n hs g) := by
  have hL' := hL
  obtain ⟨l1, l2, l3, l4⟩ := hL'
  intro x ω μ ptr len v5 v6 s h1 h5 h6 h7 tag rP rL hl hl' hp hp' pay rpay s0 s5 s6 hv5 hv6 tab rt ws wr H hgl
    ⟨cp, hcp, hcpu, hcpl, hcph⟩
  obtain ⟨w, hW⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  have hw15 := encodeNat_len_le5 n (by omega)
  rw [hW] at hw15
  have hLen : (24 :: (c ++ Blob.encodeNat n ++ hs ++ g)).length = 7 + w + 32 * n := by
    simp [hc, hW, hh, hg]; omega
  simp only [hLen, show 7 + w + 32 * n - 1 = 2 + w + 32 * n + 4 by omega,
    List.tail_cons, List.headD_cons] at hl hp' pay rpay hcph tag ⊢
  have hst : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ.writable a = true := H.st
  have ht0 := H.wf.2.2.2.1
  unfold TilesOk at ht0
  have htop0 : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hcpm' := ht0.mem_lt cp hcp
  have hT0 := H.hbT
  have hb00 := H.hb0
  have hp31 : ptr + (2 + w + 32 * n + 4) < 2147483648 := by omega
  -- the payload's parts
  have hsplit : μ.readN ptr (2 + w + 32 * n + 4) = μ.readN ptr 2 ++ (μ.readN (ptr + 2) w ++
      (μ.readN (ptr + 2 + w) (32 * n) ++ μ.readN (ptr + 2 + w + 32 * n) 4)) := by
    rw [Memory.readN_split, Memory.readN_split, Memory.readN_split]
    simp only [Nat.add_assoc, List.append_assoc]
  rw [hsplit] at pay
  simp only [List.append_assoc] at pay
  obtain ⟨pc, pay1⟩ := List.append_inj pay (by simp [hc])
  obtain ⟨pe, pay2⟩ := List.append_inj pay1 (by simp [hW])
  obtain ⟨phs, pg⟩ := List.append_inj pay2 (by simp [hh])
  have hcv : Num.decodeLE c < 65536 := by have := decodeLE_lt c; rw [hc] at this; simpa using this
  have ec : Num.encodeLE 2 (Num.decodeLE c) = c := by have := encodeLE_decodeLE c; rwa [hc] at this
  have hgv : Num.decodeLE g < 4294967296 := by have := decodeLE_lt g; rw [hg] at this; simpa using this
  have eg : Num.encodeLE 4 (Num.decodeLE g) = g := by have := encodeLE_decodeLE g; rwa [hg] at this
  -- the dispatch and the handler's frame
  obtain ⟨ω1, run1, d0, d1, d5, d6⟩ := dispatch (p := p) (P := P) (R := refineContractK cap env) x ω μ
    F 24 (by omega) (by omega) h1 h7 (by simpa using tag) tab
    (Memory.readable_of_writable (hst _ (by omega) (by omega))) rt
  obtain ⟨ω2, μ2, run2, f0, f1, f5, f6, f7, f8, f9, f72, f64, f56, ffr, frd, fwr⟩ :=
    ag1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ F (F + 120) RD
      ⟨by omega, by omega⟩ (d1.trans h1) (d5.trans h5) (d6.trans h6) (by omega) (by omega)
      (fun a h1 h2 => hst a (by omega) (by omega))
  -- the core, into S + 32
  obtain ⟨ω3, μ3, run3, g0, g1, g2, g3, g4, g5, g6, g12, g7, gR0, gR8, gbuf, gfr, grd, gwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω2 μ2 1174 25390 (F - 80) RD
      (F - 48) ptr len 2 f0 f1 f7 f8 f9 (by omega) jte_586 bs_25390 ⟨by omega, by omega⟩
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
  -- the core parked, and the call of decodeU32
  obtain ⟨ω4, μ4, run4, k0, k1, k5, k6, k7, k24, kfr, krd, kwr⟩ :=
    ag2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (F - 80) (F + 120) RD
      (Num.decodeLE c) ⟨by omega, by omega⟩ (g1.trans f1) (g5.trans f5) (g6.trans f6) g7
      (by omega) hcv
      (by rw [show F - 80 + 32 = F - 48 by omega, gbuf,
        Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), pc, ec])
      (fun a h1 h2 => by rw [gwr, fwr]; exact hst a (by omega) (by omega))
  have low4 : ∀ a, a < 2147483648 → μ4.read a = μ.read a := fun a ha =>
    (kfr a (by omega) (Or.inl (by omega))).trans (low3 a ha)
  -- the length ℰ(n)
  obtain ⟨ω5, μ5, run5, ⟨e0, e1, -, -, -, e5, e6, -, e7, e8, eR0, eR8, efr, erd, ewr⟩⟩ :=
    decodeU32 (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 1176 25408 (F - 80) RD (ptr + 2)
      (len - 2) k0 k1 k7 (by decide) jte_587 bs_25408 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [kwr, gwr, fwr]; exact wr a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR0)
      (by rw [Memory.readN_congr (fun j hj => kfr _ (by omega) (Or.inr (by omega)))]; exact gR8)
      n (by omega) (by rw [hW]; omega)
      (fun a h1 h2 => by rw [hW] at h2; rw [krd, grd, frd]; exact rpay a (by omega) (by omega))
      (by rw [hW, Memory.readN_congr (fun j hj => low4 _ (by omega))]; exact pe)
  rw [hW] at eR0 eR8
  have low5 : ∀ a, a < 2147483648 → μ5.read a = μ.read a := fun a ha =>
    (efr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (low4 a ha)
  have H5 : HeapCtx env pb S0 S1 μ5 s := heap_of_high H low5 (fun a => by rw [ewr, kwr, gwr, fwr])
  -- the call of the hash-Vec decoder
  obtain ⟨ω6, run6, a0, a1, a5, a6, a7, a8, a9⟩ :=
    ag3 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (F - 80) (F + 120) RD n (by omega)
      (by rw [e1, k1]) (by rw [e5, k5]) (by rw [e6, k6]) e7 e8 (by omega) (by omega)
  -- the queue: n hashes, into a fresh Vec at S + 32
  rcases VecHash.vec_hash (p := p) (P := P) env cap pb hcap1 hcap x ω6 μ5 s cp (F - 232) n RD (ptr + 2 + w)
      (len - 2 - w) (F - 48) 1178 25431 (F + 120) RD (fun k => μ.readN (ptr + 2 + w + 32 * k) 32) H5 a0
      (by rw [a1]; congr 1; omega) a5 a6 (by rw [a7]; congr 1; omega) a8 a9 hn
      ⟨by simp only [LoopA.S0]; omega, by omega, by omega⟩ (by simp only [LoopA.S1]; omega)
      ⟨by omega, by simp only [LoopA.S1]; omega⟩
      (Or.inr (by omega)) ⟨hcp, hcpu⟩
      (fun a h1 h2 => by unfold InData; omega)
      (fun k hk => Memory.readN_congr (fun j hj => low5 _ (by omega)))
      (by rw [show ptr + 2 + w = ptr + 2 + w from rfl]; exact eR0)
      (by rw [show len - 2 - w = len - 2 - w from rfl]; exact eR8)
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) ⟨by omega, by omega, by omega⟩ jte_588 bs_25431 with
    ⟨q, s', ω7, μ7, ha, run7, v0, v1, v5', v6', vO, vO8, vO16, vel, vR0, vR8, H7, hnew, hfresh, keepU, keepD, vfr,
      vlow, vglob, vwr⟩ | ex
  rotate_left
  · exact Or.inr ((Exhausts.pre (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))) ex).mono
      (by omega))
  -- the new chunk's place
  have ht7 := H7.wf.2.2.2.1
  unfold TilesOk at ht7
  have htop7 : s'.top = s'.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have hqm := ht7.mem_lt _ hnew
  simp only at hqm
  have hT7 := H7.hbT
  have hb07 := H7.hb0
  have hq31 : 206896 ≤ q ∧ q + 32 * n < 2147483648 := by omega
  have hst7 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ7.writable a = true := H7.st
  -- the Vec copied, and the assigner's call
  obtain ⟨ω8, μ8, run8, m0, m1, m5, m6, m7, m8, m9, m16, m8', m0', mfr, mrd, mwr⟩ :=
    ag4 (p := p) (P := P) (R := refineContractK cap env) x ω7 μ7 (F - 80) (F + 120) RD n q n
      ⟨by omega, by omega⟩ (by rw [v1]; congr 1; omega) v5' v6' (by omega) (by omega) (by omega)
      (by omega) (by rw [show F - 80 + 32 = F - 48 by omega]; exact vO)
      (by rw [show F - 80 + 40 = F - 48 + 8 by omega]; exact vO8)
      (by rw [show F - 80 + 48 = F - 48 + 16 by omega]; exact vO16)
      (fun a h1 h2 => hst7 a (by omega) (by omega))
  have pg8 : μ8.readN (ptr + 2 + w + 32 * n) 4 = g := by
    rw [Memory.readN_congr (fun j hj => (mfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((keepD cp hcp hcpu _ ⟨by omega, by omega⟩).trans (low5 _ (by omega))))]
    exact pg
  obtain ⟨ω9, μ9, run9, n0, n1, n2, n3, n4, n5, n6, n12, n7, nR0, nR8, nbuf, nfr, nrd, nwr⟩ :=
    read_ok (p := p) (P := P) (R := refineContractK cap env) x ω8 μ8 1180 25470 (F - 80) RD
      (F - 48) (ptr + 2 + w + 32 * n) (len - 2 - w - 32 * n) 4 m0 m1 m7 (by rw [m8]; congr 1; omega) m9
      (by omega) jte_589 bs_25470
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by rw [mwr]; exact hst7 a (by omega) (by omega))
      (fun a h1 h2 => by
        rw [mrd]; exact Memory.readable_of_writable
          (heap_writable_data H7 (keepU cp hcp hcpu) hcpu ⟨by omega, by omega⟩))
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR0)
      (by rw [Memory.readN_congr (fun j hj => mfr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))]; exact vR8)
  -- the frame above S, from the start to before the store
  have up9 : ∀ a, (F - 24) ≤ a → a < 4294967296 →
      (a < RD ∨ (RD + 16) ≤ a) → μ9.read a = μ2.read a := fun a h0 h1 h3 =>
    (nfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega))).trans
      ((mfr a h1 (Or.inr (by omega)) (Or.inr (by omega))).trans
      ((vfr a (by omega) h1 h3 (Or.inr (by omega))).trans
      ((efr a h1 (Or.inr (by omega)) h3).trans ((kfr a h1 (Or.inr (by omega))).trans
        (gfr a h1 (Or.inr (by omega)) h3 (Or.inr (by omega)))))))
  have up2 : ∀ a, F ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h0 h1 =>
    ffr a h1 (Or.inr h0)
  have sv : ∀ a v, a + 8 ≤ RD → F ≤ a → μ.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (up9 _ (by omega) (by omega) (by omega)).trans
      (up2 _ (by omega) (by omega)))]; exact h
  have sH : ∀ a v, (F - 80) ≤ a → a + 8 ≤ (F - 56) → μ8.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega)))]
    exact h
  have sK4 : ∀ a v, (F - 56) ≤ a → a + 8 ≤ (F - 48) → μ4.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => (nfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
      ((mfr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))).trans ((vfr _ (by omega) (by omega) (Or.inl (by omega))
        (Or.inl (by omega))).trans (efr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))))))]
    exact h
  have sA : ∀ a v, (F - 24) ≤ a → a + 8 ≤ F → μ2.readN a 8 = Num.encodeLE 8 v →
      μ9.readN a 8 = Num.encodeLE 8 v := fun a v h1 h2 h => by
    rw [Memory.readN_congr (fun j hj => up9 _ (by omega) (by omega) (by omega))]; exact h
  have hst9 : ∀ a, 4278050816 ≤ a → a < 4278059008 → μ9.writable a = true := fun a h1 h2 => by
    rw [nwr, mwr]; exact hst7 a h1 h2
  -- the variant, into the slot O, and the returns
  obtain ⟨ω10, μ10, run10, o0, o1, o5, o6, oO, oO8, oO16, oO24, oO32, oO36, ofr, ord, owr⟩ :=
    ag5 (p := p) (P := P) (R := refineContractK cap env) x ω9 μ9 (F - 80) (F + 120) 18 723 v5 v6 RD
      n q n (Num.decodeLE g) (Num.decodeLE c) (by omega) (by omega) (Or.inr (by omega)) (n1.trans m1)
      (n5.trans m5) n7 hv5 hv6 (by omega) (by omega) (by omega) (by omega) (by omega) hgv hcv
      (sH _ _ (by omega) (by omega) m0') (sH _ _ (by omega) (by omega) m8') (sH _ _ (by omega) (by omega) m16)
      (sK4 _ _ (by omega) (by omega) k24)
      (by rw [show F - 80 + 32 = F - 48 by omega, nbuf, pg8, eg])
      (by rw [show F - 80 + 72 = F - 8 by omega]; exact sA _ _ (by omega) (by omega) f72)
      (by rw [show F - 80 + 64 = F - 16 by omega]; exact sA _ _ (by omega) (by omega) f64)
      (by rw [show F - 80 + 56 = F - 24 by omega]; exact sA _ _ (by omega) (by omega) f56)
      (by rw [show F - 80 + 128 = F + 48 by omega]; exact sv _ _ (by omega) (by omega) s0)
      (by rw [show F - 80 + 120 = F + 40 by omega]; exact sv _ _ (by omega) (by omega) s5)
      (by rw [show F - 80 + 112 = F + 32 by omega]; exact sv _ _ (by omega) (by omega) s6)
      ⟨by omega, by omega, by omega⟩ jte_8 bs_723
      (fun a h1 h2 => hst9 a (by omega) (by omega))
      (fun a h1 h2 => Memory.readable_of_writable (hst9 a (by omega) (by omega)))
  have low10 : ∀ a, a < 2147483648 → μ10.read a = μ7.read a := fun a ha =>
    (ofr a (by omega) (Or.inl (by omega))).trans ((nfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega))).trans (mfr a (by omega) (Or.inl (by omega)) (Or.inl (by omega))))
  refine Or.inl ⟨ω10, μ10, s', (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans
    (run7.trans (run8.trans (run9.trans run10))))))))).mono (by omega), (by rw [o1]; congr 1; omega), o5, o6, ?_, ?_,
    ⟨9223372036854775831, by omega, oO, by omega⟩,
    heap_of_high H7 low10 (fun a => by rw [owr, nwr, mwr]), keepU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR0]; congr 1; omega
  · rw [Memory.readN_congr (fun j hj => ofr _ (by omega) (Or.inr (by omega)))]
    rw [nR8]; congr 1; omega
  · intro c' hc' hu a ha
    have hcm := ht0.mem_lt c' hc'
    have hd := ha
    unfold InData at hd
    rw [low10 a (by omega), keepD c' hc' hu a ha, low5 a (by omega)]
  · refine ⟨[⟨q - 32, n + 1, true⟩], fun c' hc' => ?_, fun μ'' hag => ?_⟩
    · simp only [List.mem_singleton] at hc'
      subst hc'
      exact ⟨hnew, rfl, hfresh⟩
    · refine ⟨by rw [readN_take _ _ 232 8 (by omega)]; exact oO, ?_, ?_, q, ?_, ?_, ?_, ?_⟩
      · rw [← readN_sub μ10 (F + 120) 232 32 4 _ rfl (by omega)]; rw [oO32, eg]
      · rw [← readN_sub μ10 (F + 120) 232 36 2 _ rfl (by omega)]; rw [oO36, ec]
      · rw [← readN_sub μ10 (F + 120) 232 8 8 _ rfl (by omega)]; exact oO8
      · rw [← readN_sub μ10 (F + 120) 232 16 8 _ rfl (by omega)]; exact oO16
      · rw [← readN_sub μ10 (F + 120) 232 24 8 _ rfl (by omega)]; exact oO24
      · rw [Memory.readN_congr (fun j hj => (hag _ (List.mem_singleton.mpr rfl) _
          ⟨by simp only; omega, by simp only; omega⟩).trans (low10 _ (by omega))),
          readN_of_pieces μ μ7 q (ptr + 2 + w) n (fun k hk => vel k hk)]
        exact phs
  · intro a h0 h1 h2 h3
    rw [ofr a h1 (by omega), up9 a (by omega) h1 h2]; exact up2 a (by omega) h1
  · intro a ha
    rw [low10 a (by omega), (vlow a ha).1, low5 a (by omega)]
  · intro a ha
    rw [ord, nrd, mrd, (vlow a ha).2, erd, krd, grd, frd]
  · intro a ha
    have h' := ha; unfold Glob at h'
    rw [low10 a (by omega), vglob a ha, low5 a (by omega)]
  · intro a ha
    rw [owr, nwr, mwr, vwr a ha, ewr, kwr, gwr, fwr]

/-- **`AssignForGasCost`, as an element of the decode loop**, in refine's frame (`assign_gas_elemF`)
    (tag 24; GP v0.8.0 B.7): for 1 ≤ n ≤ 512 hashes, the encoding 24 :: (c ++ ℰ(n) ++ hs ++ g) (the
    core's two octets, the queue's length, the n hashes, the assigner's four octets) decodes to
    `AssignForGasCost`'s slot (`AssignGasRep`), its queue a fresh `Vec` in the heap; or an allocation
    fails. -/
theorem assign_gas_elem {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap pb : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (gl : Nat → UInt8)
    (n : Nat) (hn : 1 ≤ n ∧ n ≤ 512)
    (c hs g : List UInt8) (hc : c.length = 2) (hh : hs.length = 32 * n) (hg : g.length = 4) :
    ElemOkA env cap pb gl p P (1500 + 550 * n) (24 :: (c ++ Blob.encodeNat n ++ hs ++ g))
      (AssignGasRep c n hs g) :=
  assign_gas_elemF env cap pb 4278057632 4278058648 lay_refine hcap1 hcap gl n hn c hs g hc hh hg

end Services.Bootstrap.Decode.AssignGas
