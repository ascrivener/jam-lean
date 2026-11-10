import Services.Bootstrap.Decode.VecPairs
import Services.Bootstrap.Decode.VecU8HeapBig

/-!
# `Vec<(u64, u64)>` of more than 1024 pairs, the payload in the heap

`vec_pairs_heap_big` is `VecPairs.vec_pairs_heap` (the pair reader at 3100, `Import`'s items) for
n > 1024 elements. The reader's outer loop reserves c = min(left, B) elements per batch, `left` the
elements still to read and B a bound that is 1024 for the first batch and the length read so far
for every later one (3179: ω₁₀ ← ω₇, the length), so the buffer doubles: L ↦ L + min(left, L). Each
reservation calls `finish_grow` (32989, alignment 8, element size 16) for the capacity L + c (the
capacity is always the length at the loop's head, so the reservation always grows): for the first
batch with no old buffer (`alloc`, `HeapCtx.alloc_call`), for every later one with the old buffer q
of L elements (`realloc`, `ReallocCall.realloc_call`). Then the inner loop (3277) reads the batch's c
pairs as in `VecPairs.loop`.

The outer loop's invariant (`bloop_heap`), at the batch end 3169: L elements read into the buffer q,
the data of an allocated chunk of ⌈16L/32⌉ + 1 units, holding the payload's first 16L octets; a set
`K` of protected chunks (allocated, not q's, one of them holding the payload); `HeapCtx`. As in
`VecU8.loop_heap`, `realloc` keeps the protected chunks with their data and its block is never one
of them (`VecU8.realloc_fresh`).

Either the reader returns, or the run reaches a failed allocator call (`LoopA.Exhausts`).

Not stated (unlike `vec_pairs_heap`): the globals below the allocator (`Glob`) are kept;
`realloc_call` does not record it.

GP v0.8.0: the octets are read from the service's memory by the PVM (Appendix A); the
`Vec<(u64, u64)>` is the bootstrap service's own decoding of an argument blob.
-/

namespace Services.Bootstrap.Decode.VecPairs

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Decode.VecU8

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 32989 … 33049: `finish_grow` with an old buffer q of capacity L ≥ 1 (ω₈ = L, ω₉ = q), the new
    capacity N ≥ 1 (ω₁₀), alignment `al` (ω₁₁) and element size E (ω₁₂): as `VecU8.g3`, it calls
    `realloc` (40701) for q to E·N octets at alignment `al` (ω₇ = q, ω₉ = al, ω₁₀ = E·N, return
    address 1524), E·N also at F + 8. -/
theorem g3e {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (F res L q N al E r0 v5 v6 : Nat) (hF : 65536 ≤ F ∧ F + 40 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat (F + 40)) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat res) (h8 : ω[8] = UInt64.ofNat L)
    (h9 : ω[9] = UInt64.ofNat q) (h10 : ω[10] = UInt64.ofNat N) (h11 : ω[11] = UInt64.ofNat al)
    (h12 : ω[12] = UInt64.ofNat E)
    (hr0 : r0 < 18446744073709551616) (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hres : res < 18446744073709551616) (hL : 1 ≤ L ∧ L < 4294967296) (hN : 1 ≤ N ∧ N < 4294967296)
    (hal : 1 ≤ al ∧ al ≤ 32) (hE : 1 ≤ E ∧ E ≤ 64) (hq : q < 18446744073709551616)
    (hw : ∀ a, F ≤ a → a < F + 40 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 32989 ω μ x 40701 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 1524 ∧ ω'[1] = UInt64.ofNat F ∧ ω'[6] = UInt64.ofNat res ∧
      ω'[7] = UInt64.ofNat q ∧ ω'[9] = UInt64.ofNat al ∧ ω'[10] = UInt64.ofNat (E * N) ∧
      μ'.readN (F + 32) 8 = Num.encodeLE 8 r0 ∧ μ'.readN (F + 24) 8 = Num.encodeLE 8 v5 ∧
      μ'.readN (F + 16) 8 = Num.encodeLE 8 v6 ∧ μ'.readN (F + 8) 8 = Num.encodeLE 8 (E * N) ∧
      (∀ a, a < 4294967296 → (a < F ∨ F + 40 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, F ≤ a → a < F + 40 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hEn : E * N < 274877906944 := by
    have : E * N ≤ 64 * N := Nat.mul_le_mul_right N hE.2
    omega
  have hEn0 : ¬ E * N = 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos (by omega) (by omega))
  have hL0 : ¬ L = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, h10, h11, h12, hF, hw, hr, hL, hL0, hN, hal, hE, hEn, hEn0,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals (try simp only [show F + 40 - 40 = F by omega]); post_simp
    all_goals try (congr 1; omega)

/-- 3169 … 3208, the batch end with more to read: the batch of c elements is read (ω₇ = L, the
    length; S + 16 holds c + left, S + 8 holds c, left ≥ 1), and the buffer is full (S + 48, the
    capacity, holds L): the reader goes back to its reserve loop (3143) with the bound L, and calls
    `finish_grow` for the capacity L + c', c' = min(left, L) (ω₆ = c', ω₈ = L the old capacity, ω₉ = q
    from S + 56, ω₁₀ = L + c', alignment 8, element size 16, result slot S + 72, return address 76),
    L + c' at S + 24 and L at S + 40. -/
theorem bk {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q L c left : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L) (hL : 1 ≤ L ∧ L < 4294967296)
    (hl : 1 ≤ left ∧ c + left < 4294967296) (hq : q < 18446744073709551616)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 (c + left)) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 c)
    (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 L) (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3169 ω μ x 32989 ω' μ' x 25 ∧
      ω'[0] = UInt64.ofNat 76 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat left ∧
      ω'[6] = UInt64.ofNat (min left L) ∧ ω'[7] = UInt64.ofNat (S + 72) ∧ ω'[8] = UInt64.ofNat L ∧
      ω'[9] = UInt64.ofNat q ∧ ω'[10] = UInt64.ofNat (L + min left L) ∧ ω'[11] = UInt64.ofNat 8 ∧
      ω'[12] = UInt64.ofNat 16 ∧
      μ'.readN (S + 24) 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 40) 8 = Num.encodeLE 8 L ∧
      (∀ a, a < 4294967296 → (a < S + 24 ∨ S + 32 ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r16 := rd8'' (by omega) s16
  have r8 := rd8'' (by omega) s8
  have r48 := rd8'' (by omega) s48
  have r56 := rd8'' hq s56
  have hpos : 0 < (if left ≤ L then left else L) % 18446744073709551616 := by split <;> omega
  have hle : c ≤ c + left := Nat.le_add_right c left
  have hne : ¬ c + left - c = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h7, hS, hw, hr, hL, hl, r16, r8, r48, r56, hle, hne, Nat.sub_self, hpos, Nat.add_sub_cancel_left,
      rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try (congr 1; split <;> omega)
    all_goals try (congr 1; omega)

/-- 3213 … 3242, as `p4` for any batch: `finish_grow` returned `Ok` with the buffer q (S + 72 holds 0,
    S + 80 holds q), the capacity N at S + 24, the batch c in ω₆ and the bound M ≠ 0 at S + 40: the
    reader records the `Vec` `{cap N, ptr q}` at S + 48, left (ω₅) at S + 16 and c at S + 8, and
    enters its read loop (3277). -/
theorem p4g {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q left c N M : Nat) (hS : 65536 ≤ S ∧ S + 120 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat left) (h6 : ω[6] = UInt64.ofNat c)
    (hq : q < 18446744073709551616) (hc : c < 18446744073709551616) (hl : left < 18446744073709551616)
    (hN : N < 18446744073709551616) (hM : 0 < M ∧ M < 18446744073709551616)
    (s72 : μ.readN (S + 72) 8 = Num.encodeLE 8 0) (s80 : μ.readN (S + 80) 8 = Num.encodeLE 8 q)
    (s24 : μ.readN (S + 24) 8 = Num.encodeLE 8 N) (s40 : μ.readN (S + 40) 8 = Num.encodeLE 8 M)
    (hw : ∀ a, S ≤ a → a < S + 120 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 3213 ω μ x 3277 ω' μ' x 15 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat c ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 N ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 q ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 left ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 c ∧
      (∀ a, a < 4294967296 → (a < S + 8 ∨ S + 24 ≤ a) → (a < S + 48 ∨ S + 64 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, S ≤ a → a < S + 120 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have r72 := rd8' (by decide) s72
  have r80 := rd8' hq s80
  have r24 := rd8' hN s24
  have r40 := rd8' hM.2 s40
  have hM0 : ¬ M = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hw, hr, r72, r80, r24, r40, hM0, rdN_writeN_disjoint, ↓rdN_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 ha2 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try decide
    all_goals assumption

/-- `VecPairs.pass`, also stating ω₇ = k + 1 (the new length) after the chunk's last element.
    **One pass of the read loop** (3277 … 3277, or 3169 after the last element of the chunk): with
    k < n elements pushed into q (S + 56; cap n at S + 48, len k at S + 64), r = n − k left in the
    chunk (ω₆), and the reader rd (S + 32) at ptr₀ + 16k, the reader reads the next 16 octets as a
    pair and pushes it as element k. The payload and the buffer lie below the reader's frames. -/
theorem pass7 {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (S q n k r rd ptr0 len0 : Nat) (hS : 65536 + 88 ≤ S ∧ S + 120 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h6 : ω[6] = UInt64.ofNat r) (hr : 1 ≤ r ∧ k + r = n)
    (hn : n < 4294967296)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 n)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q) (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 k)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * k))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * k))
    (hlen : 16 * n ≤ len0 ∧ len0 < 4294967296) (hrd : S + 120 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 16 * n + 16 ≤ S - 88) (hq : 65536 ≤ q ∧ q + 16 * n + 16 ≤ S - 88)
    (hpq : q + 16 * n ≤ ptr0 ∨ ptr0 + 16 * n ≤ q)
    (hws : ∀ a, S - 88 ≤ a → a < S + 120 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true)
    (hwq : ∀ a, q ≤ a → a < q + 16 * n → μ.writable a = true)
    (hra : ∀ a, ptr0 ≤ a → a < ptr0 + 16 * n → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 3277 ω μ x (if r = 1 then 3169 else 3277) ω' μ' x 260 ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ (r = 1 → ω'[7] = UInt64.ofNat (k + 1)) ∧
      μ'.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) ∧
      μ'.readN (q + 16 * k) 16 = μ.readN (ptr0 + 16 * k) 16 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * (k + 1)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * (k + 1)) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrd64 : rd < 18446744073709551616 := by omega
  -- the first u64
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, fr1, rd1, wr1⟩ :=
    b1 (p := p) (P := P) (R := R) x ω μ S rd ⟨by omega, by omega⟩ h1 hrd64 s32
      (fun a h1 h2 => hws a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, ⟨c0, c1, -, -, -, c5, c6, -, c7, cR0, cR8, cbuf, cfr, crd, cwr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω1 μ1 78 3297 S rd (S + 72) (ptr0 + 16 * k) (len0 - 16 * k) 8 a0 a1
      a7 a8 a9 (by decide) jte_38 bs_3297 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd1]; exact hra a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => fr1 _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => fr1 _ (by omega) (by omega))]; exact hR8)
  have hA : μ2.readN (S + 72) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k) 8) := by
    rw [cbuf, encodeLE_rdN]
    exact Memory.readN_congr (fun j hj => fr1 _ (by omega) (by omega))
  -- the second u64
  obtain ⟨ω3, μ3, run3, d0, d1, d5, d6, d7, d8, d9, d40, fr3, rd3, wr3⟩ :=
    b2 (p := p) (P := P) (R := R) x ω2 μ2 S rd (rdN μ (ptr0 + 16 * k) 8) ⟨by omega, by omega⟩
      (by rw [c1, a1]) (by rw [c5, a5]) c7 (rdN_lt64 _ _) hrd64 hA
      (fun a h1 h2 => by rw [cwr, wr1]; exact hws a (by omega) (by omega))
  obtain ⟨ω4, μ4, run4, ⟨e0, e1, -, -, -, e5, e6, -, e7, eR0, eR8, ebuf, efr, erd, ewr⟩⟩ :=
    read_ok (p := p) (P := P) (R := R) x ω3 μ3 80 3324 S rd (S + 72) (ptr0 + 16 * k + 8) (len0 - 16 * k - 8) 8
      d0 d1 d7 d8 d9 (by decide) jte_39 bs_3324 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by decide) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
      (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega))
      (fun a h1 h2 => by rw [wr3, cwr, wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, cwr, wr1]; exact hwr a h1 h2)
      (fun a h1 h2 => by rw [wr3, cwr, wr1]; exact hws a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd3, crd, rd1]; exact hra a (by omega) (by omega))
      (by rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (by omega) (by omega))]; exact cR0)
      (by rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (by omega) (by omega)),
            show len0 - 16 * k - 8 = len0 - 16 * k - 8 from rfl]; exact cR8)
  have hB : μ4.readN (S + 72) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k + 8) 8) := by
    rw [ebuf, encodeLE_rdN]
    exact Memory.readN_congr (fun j hj => (fr3 _ (by omega) (by omega) (by omega)).trans
      ((cfr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans
        (fr1 _ (by omega) (by omega))))
  -- the stack slots the reads keep
  have k4 : ∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 72 ∨ S + 80 ≤ a) →
      (a < rd ∨ rd + 16 ≤ a) → μ4.read a = μ.read a := fun a h0 h1 h2 h3 h4 =>
    (efr a h0 h1 h4 h3).trans ((fr3 a h0 h2 h3).trans ((cfr a h0 h1 h4 h3).trans (fr1 a h0 h3)))
  have w4 : ∀ a, μ4.writable a = μ.writable a := fun a => by rw [ewr, wr3, cwr, wr1]
  have r4 : ∀ a, μ4.readable a = μ.readable a := fun a => by rw [erd, rd3, crd, rd1]
  have h40 : μ4.readN (S + 40) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k) 8) := by
    rw [Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega))]; exact d40
  have run14 := run1.trans (run2.trans (run3.trans run4))
  have fin : ∀ (ω5 : Regs) (μ5 : Memory) (pc : Nat), FreeStepsH p R 3324 ω4 μ4 x pc ω5 μ5 x 20 →
      ω5[1] = UInt64.ofNat S → ω5[6] = UInt64.ofNat (r - 1) → (r = 1 → ω5[7] = UInt64.ofNat (k + 1)) →
      μ5.readN (q + 16 * k) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k) 8) →
      μ5.readN (q + 16 * k + 8) 8 = Num.encodeLE 8 (rdN μ (ptr0 + 16 * k + 8) 8) →
      μ5.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) →
      (∀ a, a < 4294967296 → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → (a < S + 64 ∨ S + 72 ≤ a) →
        μ5.read a = μ4.read a) →
      (∀ a, μ5.readable a = μ4.readable a) → (∀ a, μ5.writable a = μ4.writable a) →
      ∃ ω' μ', FreeStepsH p R 3277 ω μ x pc ω' μ' x 260 ∧
        ω'[1] = UInt64.ofNat S ∧ ω'[6] = UInt64.ofNat (r - 1) ∧ (r = 1 → ω'[7] = UInt64.ofNat (k + 1)) ∧
        μ'.readN (S + 64) 8 = Num.encodeLE 8 (k + 1) ∧
        μ'.readN (q + 16 * k) 16 = μ.readN (ptr0 + 16 * k) 16 ∧
        μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * (k + 1)) ∧
        μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * (k + 1)) ∧
        (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
          (a < rd ∨ rd + 16 ≤ a) → (a < q + 16 * k ∨ q + 16 * k + 16 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
    intro ω5 μ5 pc run5 f1 f6 f7 fa fb f64 ffr frd fwr
    refine ⟨ω5, μ5, (run14.trans run5).mono (by omega), f1, f6, f7, f64, ?_, ?_, ?_,
      fun a h0 h1 h2 h3 h4 h5 => (ffr a h0 h5 (by omega)).trans (k4 a h0 h1 h2 (by omega) h4),
      fun a => by rw [frd, r4], fun a => by rw [fwr, w4]⟩
    · rw [show (16 : Nat) = 8 + 8 from rfl, readN_split, readN_split, fa, encodeLE_rdN,
        show q + 16 * k + 8 = q + 16 * k + 8 from rfl]
      rw [fb, encodeLE_rdN]
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))), eR0,
        show ptr0 + 16 * k + 8 + 8 = ptr0 + 16 * (k + 1) by omega]
    · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))), eR8,
        show len0 - 16 * k - 8 - 8 = len0 - 16 * (k + 1) by omega]
  by_cases hr1 : r = 1
  · subst hr1
    rw [if_pos rfl]
    obtain ⟨ω5, μ5, run5, f1, f6, f7, fa, fb, f64, ffr, frd, fwr⟩ :=
      b3l (p := p) (P := P) (R := R) x ω4 μ4 S q n k 1 (rdN μ (ptr0 + 16 * k) 8) (rdN μ (ptr0 + 16 * k + 8) 8)
        ⟨by omega, by omega⟩ (by rw [e1, d1]) (by rw [e6, d6, c6, a6, h6]) e7 rfl ⟨by omega, hn⟩
        (by omega) (rdN_lt64 _ _) (rdN_lt64 _ _)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s48)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s64)
        hB
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s56)
        h40 (by omega)
        (fun a h1 h2 => by rw [w4]; exact hws a (by omega) (by omega))
        (fun a h1 h2 => by rw [w4]; exact hwq a (by omega) (by omega))
    exact fin ω5 μ5 3169 run5 f1 f6 (fun _ => f7) fa fb f64 ffr frd fwr
  · rw [if_neg hr1]
    obtain ⟨ω5, μ5, run5, f1, f6, fa, fb, f64, ffr, frd, fwr⟩ :=
      b3c (p := p) (P := P) (R := R) x ω4 μ4 S q n k r (rdN μ (ptr0 + 16 * k) 8) (rdN μ (ptr0 + 16 * k + 8) 8)
        ⟨by omega, by omega⟩ (by rw [e1, d1]) (by rw [e6, d6, c6, a6, h6]) e7 (by omega) (by omega)
        ⟨by omega, hn⟩ (by omega) (rdN_lt64 _ _) (rdN_lt64 _ _)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s48)
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s64)
        hB
        (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact s56)
        h40 (by omega)
        (fun a h1 h2 => by rw [w4]; exact hws a (by omega) (by omega))
        (fun a h1 h2 => by rw [w4]; exact hwq a (by omega) (by omega))
    exact fin ω5 μ5 3277 run5 f1 f6 (fun h => absurd h hr1) fa fb f64 ffr frd fwr

/-- `VecPairs.loop`, also stating ω₇ = n (the length) at the exit 3169, which the batch end reads.
    **The read loop** (3277 … 3169): from k < n elements pushed, r = n − k left, as `pass`, the reader
    pushes the remaining pairs: the buffer q then holds the payload's first 16n octets and the reader
    is advanced to ptr₀ + 16n. -/
theorem loop7 {p : ByteArray} {P : Program} [HasCode p P] (x : X)
    (S q n rd ptr0 len0 : Nat) (hS : 65536 + 88 ≤ S ∧ S + 120 < 4294967296) (hn : n < 4294967296)
    (hlen : 16 * n ≤ len0 ∧ len0 < 4294967296) (hrd : S + 120 ≤ rd ∧ rd + 16 < 4294967296)
    (hptr : 65536 ≤ ptr0 ∧ ptr0 + 16 * n + 16 ≤ S - 88) (hq : 65536 ≤ q ∧ q + 16 * n + 16 ≤ S - 88)
    (hpq : q + 16 * n ≤ ptr0 ∨ ptr0 + 16 * n ≤ q) :
    ∀ r k (ω : Regs) (μ : Memory), ω[1] = UInt64.ofNat S → ω[6] = UInt64.ofNat r → 1 ≤ r → k + r = n →
    μ.readN (S + 32) 8 = Num.encodeLE 8 rd → μ.readN (S + 48) 8 = Num.encodeLE 8 n →
    μ.readN (S + 56) 8 = Num.encodeLE 8 q → μ.readN (S + 64) 8 = Num.encodeLE 8 k →
    μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * k) → μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * k) →
    μ.readN q (16 * k) = μ.readN ptr0 (16 * k) →
    (∀ a, S - 88 ≤ a → a < S + 120 → μ.writable a = true) →
    (∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) →
    (∀ a, q ≤ a → a < q + 16 * n → μ.writable a = true) →
    (∀ a, ptr0 ≤ a → a < ptr0 + 16 * n → μ.readable a = true) →
    ∃ ω' μ', FreeStepsH p R 3277 ω μ x 3169 ω' μ' x (260 * r) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat n ∧ μ'.readN (S + 64) 8 = Num.encodeLE 8 n ∧
      μ'.readN q (16 * n) = μ.readN ptr0 (16 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * n) ∧
      (∀ a, a < 4294967296 → (a < S - 88 ∨ S ≤ a) → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → (a < q + 16 * k ∨ q + 16 * n ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  intro r
  induction r with
  | zero => intro k ω μ _ _ h; exact absurd h (by decide)
  | succ r ih =>
  intro k ω μ h1 h6 hr1 hkr s32 s48 s56 s64 hR0 hR8 hdat hws hwr hwq hra
  obtain ⟨ω1, μ1, run1, a1, a6, a7, a64, adat, aR0, aR8, afr, ard, awr⟩ :=
    pass7 (p := p) (P := P) (R := R) x ω μ S q n k (r + 1) rd ptr0 len0 hS h1 h6 ⟨hr1, hkr⟩ hn s32 s48 s56 s64
      hR0 hR8 hlen hrd hptr hq hpq hws hwr hwq hra
  have hpay : ∀ a, ptr0 ≤ a → a < ptr0 + 16 * n → μ1.read a = μ.read a := fun a h1 h2 =>
    afr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by rcases hpq with h | h <;> omega)
  have hdat1 : μ1.readN q (16 * (k + 1)) = μ1.readN ptr0 (16 * (k + 1)) := by
    rw [show 16 * (k + 1) = 16 * k + 16 by omega, readN_split, readN_split, adat,
      Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega))), hdat,
      Memory.readN_congr (μ' := μ1) (a := ptr0) (n := 16 * k) (fun j hj => hpay _ (by omega) (by omega)),
      Memory.readN_congr (μ' := μ1) (a := ptr0 + 16 * k) (n := 16) (fun j hj => hpay _ (by omega) (by omega))]
  by_cases hr0 : r = 0
  · subst hr0
    rw [if_pos rfl] at run1
    have hk : k + 1 = n := by omega
    refine ⟨ω1, μ1, run1.mono (by omega), a1, by rw [a7 rfl, hk], by rw [a64, hk], ?_, by rw [aR0, hk], by rw [aR8, hk],
      fun a h0 h1 h2 h3 h4 h5 => afr a h0 h1 h2 h3 h4 (by omega), ard, awr⟩
    rw [← hk, hdat1]
    exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))
  · rw [if_neg (by omega)] at run1
    obtain ⟨ω', μ', run', e1, e7, e64, edat, eR0, eR8, efr, erd, ewr⟩ :=
      ih (k + 1) ω1 μ1 a1 (by rw [a6]; congr 1) (by omega) (by omega)
        (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)))]; exact s32)
        (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)))]; exact s48)
        (by rw [Memory.readN_congr (fun j hj => afr _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (by omega)))]; exact s56)
        a64 aR0 aR8 hdat1
        (fun a h1 h2 => by rw [awr]; exact hws a h1 h2) (fun a h1 h2 => by rw [awr]; exact hwr a h1 h2)
        (fun a h1 h2 => by rw [awr]; exact hwq a h1 h2) (fun a h1 h2 => by rw [ard]; exact hra a h1 h2)
    refine ⟨ω', μ', (run1.trans run').mono (by rw [Nat.mul_succ]; omega), e1, e7, e64, ?_, eR0, eR8,
      fun a h0 h1 h2 h3 h4 h5 => (efr a h0 h1 h2 h3 h4 (by omega)).trans (afr a h0 h1 h2 h3 h4 (by omega)),
      fun a => by rw [erd, ard], fun a => by rw [ewr, awr]⟩
    rw [edat]; exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.Decode.ReallocCall Services.Bootstrap.Decode.ReallocKeepAll in
/-- **One later batch, the payload in the heap** (3169 … 3169): at the batch end with L ≥ 1 elements
    read (ω₇ = L, the buffer q of capacity L at S + 56, S + 48, S + 64; S + 16, S + 8 holding c + left,
    c) and left ≥ 1 to go, q the data of an allocated chunk of ⌈16L/32⌉ + 1 units holding the
    payload's first 16L octets, the payload ptr0 … ptr0 + 16(L + left) inside a protected chunk (`K`:
    allocated, not q's): either the model's `realloc` of q to ⌈16(L + c')/32⌉ units (c' = min(left, L))
    gives a block r and state `s'`, and the reader reads the batch's c' pairs into r, reaching the
    batch end again with ω₇ = L + c', the `Vec` `{cap L + c', ptr r, len L + c'}`, r holding the
    payload's first 16(L + c') octets and the data of an allocated chunk of ⌈16(L + c')/32⌉ + 1 units,
    the context kept for `s'`, every protected chunk still allocated, not r's, with its data; or the
    run reaches a failed `realloc` (`Exhausts`). -/
theorem batch_heap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop) (S rd q L c left ptr0 len0 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (16 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + 16 * (L + left) ≤ d.addr + 32 * d.size)
    (hS : S0 + 360 ≤ S ∧ S + 120 ≤ S1) (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L)
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hn : 16 * (L + left) < 1073741760)
    (hlen : 16 * (L + left) ≤ len0 ∧ len0 < 4294967296)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 (c + left)) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 c)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 L)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q) (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 L)
    (hrd : S + 120 ≤ rd ∧ rd + 16 ≤ S1)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * L))
    (hdat : μ.readN q (16 * L) = μ.readN ptr0 (16 * L)) :
    (∃ ω' μ' s' r, FreeStepsH p (refineContractK cap env) 3169 ω μ x 3169 ω' μ' x
        (64 * ((16 * L + 31) / 32) + 260 * min left L + 1400) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[7] = UInt64.ofNat (L + min left L) ∧
      μ'.readN (S + 16) 8 = Num.encodeLE 8 left ∧ μ'.readN (S + 8) 8 = Num.encodeLE 8 (min left L) ∧
      μ'.readN (S + 48) 8 = Num.encodeLE 8 (L + min left L) ∧ μ'.readN (S + 56) 8 = Num.encodeLE 8 r ∧
      μ'.readN (S + 64) 8 = Num.encodeLE 8 (L + min left L) ∧
      (∀ a, a < 4294967296 → (S ≤ a ∧ a < S + 8 ∨ S + 32 ≤ a ∧ a < S + 40 ∨ S + 96 ≤ a) →
        (a < rd ∨ rd + 16 ≤ a) → μ'.read a = μ.read a) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * (L + min left L)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * (L + min left L)) ∧
      μ'.readN r (16 * (L + min left L)) = μ.readN ptr0 (16 * (L + min left L)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = r ∧ d.used = true ∧ d.size = (16 * (L + min left L) + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ r ∧
        ∀ a, InData d a → μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 3169 ω μ x (64 * ((16 * L + 31) / 32) + 1400) := by
  obtain ⟨cq, hcqm, hcqa, hcqu, hcqs⟩ := hcq
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpm, hcpu, hcpq⟩ := hK cp hcpK
  have hu : usable s q = (16 * L + 31) / 32 := by rw [← hcqa, usable_of_chunk hcqm, hcqs]; rfl
  obtain ⟨hq0, -, hqT⟩ := chunk_in H.wf hcqm hcqu
  obtain ⟨hp0, -, hpT⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  have hba : s.base % 8 = 0 := by have := H.wf.2.1; omega
  -- the batch end, and finish_grow to realloc
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m24, m40, fr1, rd1, wr1⟩ :=
    bk (p := p) (P := P) (R := refineContractK cap env) x ω μ S q L c left ⟨by omega, by omega⟩ h1 h7
      ⟨hL, by omega⟩ ⟨hl1, by omega⟩ (by omega) s16 s8 s48 s56 (fun a h1 h2 => hst a (by omega) (by omega))
  generalize hcdef : min left L = c' at *
  have hc1 : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L := by omega
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b9, b10, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g3e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (S - 40) (S + 72) L q (L + c') 8 16 76 left c'
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a9 a10 a11 a12
      (by decide) (by omega) (by omega) (by omega) ⟨hL, by omega⟩ ⟨by omega, by omega⟩ (by decide) (by decide)
      (by omega) (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < S - 40 ∨ S + 48 ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega) (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcqm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- realloc
  rcases realloc_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω2 μ2 s (S - 40) q 8 (16 * (L + c')) pb
      S0 S1 H2 ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) (by omega) hba b1 b7 b9 b10 (by decide) (by decide)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ with
    ⟨r, s', b, ω3, μ3, hR, run3, e7, H3, dat3, keep3, ⟨cr, hcrm, hcra, hcru, hcrs⟩, kp3, stk3, -, -, e0, e1,
      e5, e6⟩ |
    ⟨hR, ω3, μ3, run3, e7, -, -, e0, -, -, -⟩
  rotate_left
  · rw [hu] at run3
    have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
    exact Or.inr (Exhausts.of_realloc ((run1.trans (run2.trans (run3.trans run4))).mono (by omega)) e7 hR)
  have hR1 : realloc (growTo pb) hb s q 1 ((16 * (L + c') + 31) / 32) = some (r, s', b) := hR
  have hfr := realloc_fresh H.wf ⟨cq, hcqm, hcqa, hcqu⟩ (by omega) hR1
  rw [hu, Nat.min_eq_left (by omega)] at dat3
  rw [hu] at run3
  obtain ⟨hr0, -, hrT⟩ := chunk_in H3.wf hcrm hcru
  rw [hcrs] at hrT
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have hcp' := keep3 cp hcpm hcpu hcpq
  have hcpr : cp.addr + 32 ≠ r := hfr cp hcpm hcpu hcpq
  have hcpne : cp ≠ cr := fun e => hcpr (by rw [e]; exact hcra)
  have run4 := realloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  -- back in finish_grow
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2r (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (S - 40) (S + 72) (16 * (L + c')) r 76 3213
      left c' ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => stk3 _ (by omega) (by omega))]; exact n8)
      (by decide) jte_37 bs_3213
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS51 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 72 ∨ S + 96 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 h3).trans ((stk3 a h2 (by omega)).trans (fr2 a h2 (Or.inr (by omega))))
  obtain ⟨ω6, μ6, run6, d1, d6, d48, d56, d16, d8, fr6, rd6, wr6⟩ :=
    p4g (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 S r left c' (L + c') L ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩
      cres (by rw [show S + 80 = S + 72 + 8 by omega]; exact cres8)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m24)
      (by rw [Memory.readN_congr (fun j hj => hS51 _ (by omega) (by omega) (by omega))]; exact m40)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  -- the frame S in μ6: off the slots written since μ
  have hS60 : ∀ a, S ≤ a → a < 4294967296 → (a < S + 8 ∨ S + 32 ≤ a ∧ a < S + 40 ∨ S + 64 ≤ a ∧ a < S + 72 ∨ S + 96 ≤ a) →
      μ6.read a = μ.read a := fun a h1 h2 h3 =>
    (fr6 a h2 (by omega) (by omega)).trans ((hS51 a h1 h2 (by omega)).trans (fr1 a h2 (by omega) (by omega)))
  have hhigh : ∀ a, a < 4294967296 → S + 96 ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    hS60 a (by omega) h0 (by omega)
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha => by
    have hca := ha
    unfold InData at hca
    rw [h63 a (by omega), kp3 a ⟨cp, hcpm, hcpu, hcpq, ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hdq : r + 16 * (L + c') ≤ ptr0 ∨ ptr0 + 16 * (L + c') ≤ r := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' cr hcrm hcpne with h' | h' <;> omega
  -- the batch's reads
  obtain ⟨ω7, μ7, run7, f1, f7, f64, fdat, fR0, fR8, ffr, frd, fwr⟩ :=
    loop7 (p := p) (P := P) (R := refineContractK cap env) x S r (L + c') rd ptr0 len0 ⟨by omega, by omega⟩
      (by omega) ⟨by omega, hlen.2⟩ ⟨hrd.1, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hdq c' L ω6 μ6
      d1 d6 hc1.1 rfl
      (by rw [Memory.readN_congr (fun j hj => hS60 _ (by omega) (by omega) (by omega))]; exact s32)
      d48 d56
      (by rw [Memory.readN_congr (fun j hj => hS60 _ (by omega) (by omega) (by omega))]; exact s64)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      (by
        rw [Memory.readN_congr (fun j hj => h63 _ (by omega)), readN_prefix (by omega) dat3,
          Memory.readN_congr (fun j hj => hlow _ (by omega) (Or.inl (by omega))), hdat]
        exact (Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)).symm)
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hcrm hcru ⟨by omega, by rw [hcrs]; omega⟩)
      (fun a h1 h2 => Memory.readable_of_writable
        (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  -- the results
  have h76 : ∀ a, S ≤ a → a < S + 120 → (a < S + 40 ∨ S + 48 ≤ a) → (a < S + 64 ∨ S + 80 ≤ a) →
      μ7.read a = μ6.read a := fun a h1 h2 h3 h4 =>
    ffr a (by omega) (Or.inr h1) h3 h4 (Or.inl (by omega)) (Or.inr (by omega))
  have hlowh : ∀ a, a < 2147483648 → (a < r + 16 * L ∨ r + 16 * (L + c') ≤ a) → μ7.read a = μ3.read a :=
    fun a h2 h3 => (ffr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (Or.inl (by omega)) h3).trans (h63 a h2)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [fwr, wr36]
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  refine Or.inl ⟨ω7, μ7, s', r, run17.mono (by omega), f1, f7, ?_, ?_, ?_, ?_, f64, ?_, fR0, fR8, ?_,
    ctx_congr_data H3 hcrm (fun a h1 h2 => hlowh a h1 (by rw [hcrs] at h2; omega)) wr73,
    ⟨cr, hcrm, hcra, hcru, hcrs⟩, ?_⟩
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d16
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d8
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d48
  · rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d56
  · intro a h0 h1 h2
    exact (ffr a h0 (Or.inr (by omega)) (by omega) (by omega) h2 (Or.inr (by omega))).trans
      (hS60 a (by omega) h0 (by omega))
  · rw [fdat]; exact Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩)
  · intro d hd
    obtain ⟨hdm, hdu, hdq'⟩ := hK d hd
    have hdm' := keep3 d hdm hdu hdq'
    have hdr : d.addr + 32 ≠ r := hfr d hdm hdu hdq'
    have hdne : d ≠ cr := fun e => hdr (by rw [e]; exact hcra)
    refine ⟨hdm', hdu, hdr, fun a ha => ?_⟩
    have hdis := data_disj H3.wf hdm' hcrm hdne ha
    rw [hcrs] at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hdm hdu).2.2
    rw [hlowh a (by omega) (by omega), kp3 a ⟨d, hdm, hdu, hdq', ha⟩]
    exact hlow a (by omega) (Or.inl (by omega))

/-- A step bound for the batches from L elements read with `left` to go. -/
def pairSteps (L left : Nat) : Nat := 34 * L + 330 * left + 2000 * (left / L) + 2000

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA in
/-- **The reader's batches, the payload in the heap** (from the batch end 3169 to the reader's
    return t): as `batch_heap`, with the reader's frame (O at S, ret, v5, v6 at S + 112, S + 104,
    S + 96) and left ≥ 1 to go. Either the reader returns to t with the `Vec` `{cap L + left, ptr q',
    len L + left}` at O, q' holding the payload's first 16(L + left) octets and being the data of an
    allocated chunk of exactly ⌈16(L + left)/32⌉ + 1 units, the context kept for the final state, every
    protected chunk still allocated, not q''s, with its data, and memory from S + 120 up kept off the
    reader and O; or the run reaches a failed `realloc` (`Exhausts`). -/
theorem bloop_heap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (hb : Nat) (s : State) (K : Chunk → Prop)
    (S O rd q L c left ptr0 len0 ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hcq : ∃ d ∈ chunks s, d.addr + 32 = q ∧ d.used = true ∧ d.size = (16 * L + 31) / 32 + 1)
    (hK : ∀ d, K d → d ∈ chunks s ∧ d.used = true ∧ d.addr + 32 ≠ q)
    (hpay : ∃ d, K d ∧ d.addr + 32 ≤ ptr0 ∧ ptr0 + 16 * (L + left) ≤ d.addr + 32 * d.size)
    (hS : S0 + 360 ≤ S ∧ S + 120 ≤ S1) (hsp : 2147484008 ≤ S ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat L)
    (hL : 1 ≤ L) (hc : c ≤ L) (hl1 : 1 ≤ left) (hn : 16 * (L + left) < 1073741760)
    (hlen : 16 * (L + left) ≤ len0 ∧ len0 < 4294967296)
    (s0 : μ.readN S 8 = Num.encodeLE 8 O)
    (s16 : μ.readN (S + 16) 8 = Num.encodeLE 8 (c + left)) (s8 : μ.readN (S + 8) 8 = Num.encodeLE 8 c)
    (s32 : μ.readN (S + 32) 8 = Num.encodeLE 8 rd) (s48 : μ.readN (S + 48) 8 = Num.encodeLE 8 L)
    (s56 : μ.readN (S + 56) 8 = Num.encodeLE 8 q) (s64 : μ.readN (S + 64) 8 = Num.encodeLE 8 L)
    (s112 : μ.readN (S + 112) 8 = Num.encodeLE 8 ret) (s104 : μ.readN (S + 104) 8 = Num.encodeLE 8 v5)
    (s96 : μ.readN (S + 96) 8 = Num.encodeLE 8 v6)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hrd : S + 120 ≤ rd ∧ rd + 16 ≤ S1) (hO : S + 120 ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * L))
    (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * L))
    (hdat : μ.readN q (16 * L) = μ.readN ptr0 (16 * L)) :
    (∃ ω' μ' s' q', FreeStepsH p (refineContractK cap env) 3169 ω μ x t ω' μ' x (pairSteps L left) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 120) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 (L + left) ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q' ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (L + left) ∧
      μ'.readN q' (16 * (L + left)) = μ.readN ptr0 (16 * (L + left)) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr0 + 16 * (L + left)) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len0 - 16 * (L + left)) ∧
      HeapCtx env pb S0 S1 μ' s' ∧
      (∃ d ∈ chunks s', d.addr + 32 = q' ∧ d.used = true ∧ d.size = (16 * (L + left) + 31) / 32 + 1) ∧
      (∀ d, K d → d ∈ chunks s' ∧ d.used = true ∧ d.addr + 32 ≠ q' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∀ a, a < 4294967296 → S + 120 ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        μ'.read a = μ.read a)) ∨
    Exhausts env cap pb p P 3169 ω μ x (pairSteps L left) := by
  induction left using Nat.strongRecOn generalizing ω μ s q L c with
  | _ left ih =>
  have hS1 := H.hS1
  rcases batch_heap (p := p) (P := P) env cap hcap1 hcap x ω μ hb s K S rd q L c left ptr0 len0 pb S0 S1 H hcq hK
      hpay hS hsp h1 h7 hL hc hl1 hn hlen s16 s8 s32 s48 s56 s64 hrd hR0 hR8 hdat with
    ⟨ω1, μ1, s', r, run1, a1, a7, m16, m8, m48, m56, m64, fr1, rR0, rR8, dat1, H1, hc1, hK1⟩ | hex
  rotate_left
  · exact Or.inr (hex.mono (by unfold pairSteps; omega))
  obtain ⟨cp, hcpK, hcp1, hcp2⟩ := hpay
  generalize hcdef : min left L = c' at *
  have hcc : 1 ≤ c' ∧ c' ≤ left ∧ c' ≤ L ∧ (c' < left → c' = L) := by omega
  have hS1r : ∀ a, S ≤ a → a < S + 120 → (S ≤ a ∧ a < S + 8 ∨ S + 32 ≤ a ∧ a < S + 40 ∨ S + 96 ≤ a) →
      μ1.read a = μ.read a := fun a h1 h2 h3 => fr1 a (by omega) h3 (Or.inl (by omega))
  have hpay1 : ∀ a, ptr0 ≤ a → a < ptr0 + 16 * (L + left) → μ1.read a = μ.read a := fun a h1 h2 =>
    (hK1 cp hcpK).2.2.2 a ⟨by omega, by omega⟩
  have hX : 64 * ((16 * L + 31) / 32) ≤ 32 * L + 62 := by omega
  rcases Classical.em (c' < left) with hlt | hlt
  · -- the next batches
    have hcL : c' = L := hcc.2.2.2 hlt
    have hrec := ih (left - c') (by omega) ω1 μ1 s' r (L + c') c' H1 hc1
      (fun d hd => ⟨(hK1 d hd).1, (hK1 d hd).2.1, (hK1 d hd).2.2.1⟩) ⟨cp, hcpK, hcp1, by omega⟩
      a1 a7 (by omega) (by omega) (by omega) (by omega) ⟨by omega, hlen.2⟩
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s0)
      (by rw [show c' + (left - c') = left by omega]; exact m16) m8
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s32)
      m48 m56 m64
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s112)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s104)
      (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s96)
      rR0 rR8
      (by rw [dat1]; exact (Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))).symm)
    have hY : left / L = (left - L) / L + 1 := Nat.div_eq_sub_div (by omega) (by omega)
    have hX2 : (left - L) / (L + L) ≤ (left - L) / L := Nat.div_le_div_left (by omega) (by omega)
    have hsteps : 64 * ((16 * L + 31) / 32) + 260 * c' + 1400 + pairSteps (L + c') (left - c') ≤
        pairSteps L left := by
      subst hcL; unfold pairSteps; omega
    rcases hrec with ⟨ω', μ', s'', q', run', z0, z1, z5, z6, zO, zO8, zO16, zdat, zR0, zR8, zH, zc, zK, zfr⟩ | hex
    · have e : L + c' + (left - c') = L + left := by omega
      rw [e] at zO zO16 zdat zR0 zR8 zc
      refine Or.inl ⟨ω', μ', s'', q', (run1.trans run').mono hsteps, z0, z1, z5, z6, zO, zO8, zO16, ?_,
        zR0, zR8, zH, zc, fun d hd => ?_,
        fun a h0 h1 h2 h3 => (zfr a h0 h1 h2 h3).trans (fr1 a h0 (Or.inr (Or.inr (by omega))) h2)⟩
      · rw [zdat]
        exact Memory.readN_congr (fun j hj => hpay1 _ (by omega) (by omega))
      · obtain ⟨z1', z2', z3', z4'⟩ := zK d hd
        exact ⟨z1', z2', z3', fun a ha => (z4' a ha).trans ((hK1 d hd).2.2.2 a ha)⟩
    · exact Or.inr ((Exhausts.pre run1 hex).mono hsteps)
  · -- the last batch: the exit
    have hcl : c' = left := by omega
    subst hcl
    obtain ⟨cr, hcrm, hcra, hcru, hcrs⟩ := hc1
    obtain ⟨hr0, -, hrT⟩ := chunk_in H1.wf hcrm hcru
    have hb1 := H1.hb0
    have hbT1 := H1.hbT
    have hrd1 : ∀ a, S ≤ a → a < S + 120 → μ1.readable a = true := fun a h1 h2 =>
      Memory.readable_of_writable (H1.st a (by omega) (by omega))
    obtain ⟨ω2, run2, g1⟩ :=
      ex1 (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 S c' ⟨by omega, by omega⟩ a1 (by omega)
        m16 m8 hrd1
    obtain ⟨ω3, μ3, run3, z0, z1, z5, z6, zO, zO8, zO16, fr3, rd3, wr3⟩ :=
      ex2 (p := p) (P := P) (R := refineContractK cap env) x ω2 μ1 S O (L + c') r (L + c') ret t v5 v6
        ⟨by omega, by omega⟩ (by omega) (Or.inr hO.1) g1 (by omega) (by omega) (by omega) hv5 hv6 m48 m56 m64
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s0)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s112)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s104)
        (by rw [Memory.readN_congr (fun j hj => hS1r _ (by omega) (by omega) (by omega))]; exact s96)
        hret hjt hbt (fun a h1 h2 => H1.st a (by omega) (by omega)) (fun a h1 h2 => H1.st a (by omega) (by omega))
    have hlowh : ∀ a, a < 2147483648 → μ3.read a = μ1.read a := fun a h2 =>
      fr3 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    have run13 := run1.trans (run2.trans run3)
    refine Or.inl ⟨ω3, μ3, s', r, run13.mono (by unfold pairSteps; omega), z0, z1, z5, z6, zO, zO8, zO16,
      ?_, ?_, ?_, ctx_congr_data H1 hcrm (fun a h1 _ => hlowh a h1) wr3, ⟨cr, hcrm, hcra, hcru, hcrs⟩,
      fun d hd => ?_, ?_⟩
    · rw [Memory.readN_congr (fun j hj => hlowh _ (by omega))]; exact dat1
    · rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (by omega))]; exact rR0
    · rw [Memory.readN_congr (fun j hj => fr3 _ (by omega) (Or.inr (by omega)) (by omega))]; exact rR8
    · obtain ⟨k1, k2, k3, k4⟩ := hK1 d hd
      refine ⟨k1, k2, k3, fun a ha => ?_⟩
      have hca := ha
      unfold InData at hca
      have := (chunk_in H1.wf k1 k2).2.2
      exact (hlowh a (by omega)).trans (k4 a ha)
    · intro a h0 h1 h2 h3
      exact (fr3 a h0 (Or.inr (by omega)) h3).trans (fr1 a h0 (Or.inr (Or.inr (by omega))) h2)

open Picoalloc Services.Bootstrap.Alloc JAM Services.Bootstrap.Decode.AllocOk Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA in
/-- **Reading more than 1024 pairs into a fresh `Vec<(u64, u64)>`, the payload in the heap** (3100):
    as `vec_pairs_heap`, for 1024 < n with 16n < 2³⁰ − 64, with the stack pointer at least S0 + 480
    (the `realloc` wrapper's frames below the reader's). The first 1024 pairs go into the block of the
    model's `alloc` of 512 units; then the reader's batches (`bloop_heap`) grow the buffer with
    `realloc` to exactly L + min(left, L) elements per batch until all n are read. Either the reader
    returns to t with the `Vec` `{cap n, ptr q, len n}` at O (the capacity is exactly n: each
    reservation asks for the length so far plus the next batch), q holding the payload's 16n octets
    (the n pairs, each two little-endian `u64`s) and being the data of an allocated chunk of
    ⌈16n/32⌉ + 1 units that is no allocated chunk of `s`, the context kept for the final state `s'`,
    every allocated chunk of `s` kept with its data, the reader advanced by 16n, the stack from sp up
    kept off the reader and O, memory below 196608 and the access of everything from S0 up kept; or
    the run reaches a failed allocator call (`Exhausts`): the first batch's `alloc` or one of the
    `realloc`s fails.

    *Not stated:* that the globals below the allocator (`Glob`) are kept, as `vec_pairs_heap` states;
    `ReallocCall.realloc_call` does not record it. -/
theorem vec_pairs_heap_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (s : State) (sp O rd ptr len n ret t v5 v6 pb S0 S1 : Nat)
    (H : HeapCtx env pb S0 S1 μ s)
    (hpay : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ptr ∧ ptr + 16 * n ≤ c.addr + 32 * c.size)
    (hS : S0 + 480 ≤ sp ∧ sp ≤ S1) (hsp : 2147484128 ≤ sp ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat O) (h8 : ω[8] = UInt64.ofNat rd)
    (h9 : ω[9] = UInt64.ofNat n)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hn : 1024 < n ∧ 16 * n < 1073741760) (hnl : 16 * n ≤ len) (hlen : len < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 ≤ S1) (hO : sp ≤ O ∧ O + 24 ≤ S1) (hOr : O + 24 ≤ rd ∨ rd + 16 ≤ O)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ptr) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 len) :
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap env) 3100 ω μ x t ω' μ' x
        (267000 + pairSteps 1024 (n - 1024)) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 n ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 n ∧ μ'.readN q (16 * n) = μ.readN ptr (16 * n) ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ptr + 16 * n) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (len - 16 * n) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨q - 32, (16 * n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨q - 32, (16 * n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InData c a → μ'.read a = μ.read a) ∧
      PagesOut 48 pb μ μ' ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → (a < O ∨ O + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, S0 ≤ a → μ'.writable a = μ.writable a)) ∨
    Exhausts env cap pb p P 3100 ω μ x (267000 + pairSteps 1024 (n - 1024)) := by
  obtain ⟨cp, hcpm, hcpu, hcp1, hcp2⟩ := hpay
  obtain ⟨hcpb, hcpT, hcpT'⟩ := chunk_in H.wf hcpm hcpu
  have hb0 := H.hb0
  have hbT := H.hbT
  have hS1 := H.hS1
  have hSb := H.hSb
  have hst := H.st
  -- the frame and the call of finish_grow for the first batch
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11, a12, m8, m16, m24, m88, m120, m96, m80, m56, fr1,
      rd1, wr1⟩ := p1 (p := p) (P := P) (R := refineContractK cap env) x ω μ sp O rd n ret v5 v6
    ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h8 h9 (by omega) hv5 hv6 (by omega) (by omega) ⟨by omega, by omega⟩
    (fun a h1 h2 => hst a (by omega) (by omega))
  rw [show min n 1024 = 1024 by omega] at a6 a10 m96
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, n32, n24, n16, n8, fr2, rd2, wr2⟩ :=
    g1e (p := p) (P := P) (R := refineContractK cap env) x ω1 μ1 (sp - 160) (sp - 120 + 72) 1024 8 16 76 n 1024
      ⟨by omega, by omega⟩ a0 (by rw [a1]; congr 1; omega) a5 a6 a7 a8 a10 a11 a12 (by decide) (by omega)
      (by omega) (by omega) ⟨by omega, by omega⟩ (by decide) (by decide)
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
  have hlow : ∀ a, a < 4294967296 → (a < sp - 160 ∨ sp ≤ a) → μ2.read a = μ.read a := fun a h0 h1 =>
    (fr2 a h0 (by omega)).trans (fr1 a h0 (by omega))
  have wr12 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [wr2, wr1]
  have H2 : HeapCtx env pb S0 S1 μ2 s :=
    ctx_congr_data H hcpm (fun a h1 _ => hlow a (by omega) (Or.inl (by omega))) wr12
  -- alloc
  rcases alloc_call (p := p) (P := P) (hb := 0) env cap hcap1 hcap x ω2 μ2 s (sp - 160) (16 * 1024) 8 pb S0 S1 H2
      b1 b7 b8 (by decide) (by decide) (by omega) (by omega) ⟨by omega, by omega⟩ with
    ⟨q, s1, ω3, μ3, ha, run3, H3, keep, hnew, hfresh, hk, e7, stk3, e0, e1, e5, e6⟩ |
    ⟨hna, ω3, μ3, run3, e7, -, -, -, -, -⟩
  rotate_left
  · exact Or.inr ((Exhausts.of_alloc (run1.trans (run2.trans run3)) e7 hna).mono (by omega))
  have hcp' := keep cp hcpm hcpu
  have hcpne : cp ≠ ⟨q - 32, (16 * 1024 + 31) / 32 + 1, true⟩ := hfresh cp hcpm hcpu
  obtain ⟨hqb, hqT, hqT'⟩ := chunk_in H3.wf hnew rfl
  simp only at hqb hqT hqT'
  have hb3 := H3.hb0
  have hbT3 := H3.hbT
  have kd : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ3.read a = μ2.read a := fun d hd hu a ha =>
    hk.hkeep a (off_hdr_data H3.wf H3.hb0 H3.hbT (keep d hd hu) ha.1 ha.2)
  have run4 := alloc_ret (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (by rw [e0, b0])
  have hF : ∀ a, sp - 160 ≤ a → a < 4294967296 → μ3.read a = μ2.read a := fun a h1 h2 => stk3 a h2 h1
  obtain ⟨ω5, μ5, run5, c0, c1, c5, c6, cres, cres8, cres16, fr5, rd5, wr5⟩ :=
    g2 (p := p) (P := P) (R := refineContractK cap env) x ω3 μ3 (sp - 160) (sp - 120 + 72) (16 * 1024) q 76 3213
      n 1024 ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) (by rw [e1, b1]) (by rw [e6, b6]) e7
      ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n32)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n24)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n16)
      (by rw [Memory.readN_congr (fun j hj => hF _ (by omega) (by omega))]; exact n8)
      (by decide) jte_37 bs_3213
      (fun a h1 h2 => Memory.readable_of_writable (H3.st a (by omega) (by omega)))
      (fun a h1 h2 => H3.st a (by omega) (by omega))
  have hS5 : ∀ a, sp - 120 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → μ5.read a = μ1.read a :=
    fun a h1 h2 h3 => (fr5 a h2 (by omega)).trans ((hF a (by omega) h2).trans (fr2 a h2 (by omega)))
  obtain ⟨ω6, μ6, run6, d1, d6, d48, d56, d16, d8, fr6, rd6, wr6⟩ :=
    p4 (p := p) (P := P) (R := refineContractK cap env) x ω5 μ5 (sp - 120) q n 1024 ⟨by omega, by omega⟩
      (by rw [c1]; congr 1; omega) c5 c6 (by omega) (by omega) (by omega)
      (by rw [show sp - 120 + 72 = sp - 120 + 72 from rfl]; exact cres)
      (by rw [show sp - 120 + 80 = sp - 120 + 72 + 8 by omega]; exact cres8)
      (by rw [show sp - 120 + 24 = sp - 96 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m96)
      (by rw [show sp - 120 + 40 = sp - 80 by omega, Memory.readN_congr (fun j hj => hS5 _ (by omega) (by omega) (by omega))]; exact m80)
      (fun a h1 h2 => by rw [wr5]; exact H3.st a (by omega) (by omega))
  have hS6 : ∀ a, sp - 120 ≤ a → a < 4294967296 → (a < sp - 48 ∨ sp - 24 ≤ a) → (a < sp - 112 ∨ sp - 96 ≤ a) →
      (a < sp - 72 ∨ sp - 56 ≤ a) → μ6.read a = μ1.read a := fun a h1 h2 h3 h4 h5 =>
    (fr6 a h2 (by omega) (by omega)).trans (hS5 a h1 h2 h3)
  have hhigh : ∀ a, a < 4294967296 → sp ≤ a → μ6.read a = μ.read a := fun a h0 h1 =>
    (fr6 a h0 (by omega) (by omega)).trans ((fr5 a h0 (by omega)).trans ((hF a (by omega) h0).trans (hlow a h0 (Or.inr h1))))
  have h63 : ∀ a, a < 2147483648 → μ6.read a = μ3.read a := fun a h0 =>
    (fr6 a (by omega) (by omega) (by omega)).trans (fr5 a (by omega) (Or.inl (by omega)))
  have hpay6 : ∀ a, InData cp a → μ6.read a = μ.read a := fun a ha =>
    (h63 a (by unfold InData at ha; omega)).trans ((kd cp hcpm hcpu a ha).trans
      (hlow a (by unfold InData at ha; omega) (Or.inl (by unfold InData at ha; omega))))
  have wr36 : ∀ a, μ6.writable a = μ3.writable a := fun a => by rw [wr6, wr5]
  have hdq : q + 16 * 1024 ≤ ptr ∨ ptr + 16 * 1024 ≤ q := by
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    rcases HeapFrame.Tiles.disjoint ht cp hcp' _ hnew hcpne with h' | h' <;> simp only at h' <;> omega
  -- the first batch's reads
  obtain ⟨ω7, μ7, run7, f1, f7, f64, fdat, fR0, fR8, ffr, frd, fwr⟩ :=
    loop7 (p := p) (P := P) (R := refineContractK cap env) x (sp - 120) q 1024 rd ptr len ⟨by omega, by omega⟩
      (by omega) ⟨by omega, hlen⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hdq 1024 0 ω6 μ6
      d1 d6 (by omega) (by omega)
      (by rw [show sp - 120 + 32 = sp - 88 by omega, Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
      d48 d56
      (by rw [show sp - 120 + 64 = sp - 56 by omega, Memory.readN_congr (fun j hj => hS6 _ (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m56)
      (by rw [show ptr + 16 * 0 = ptr by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR0)
      (by rw [show len - 16 * 0 = len by omega, Memory.readN_congr (fun j hj => hhigh _ (by omega) (by omega))]; exact hR8)
      rfl
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact H3.st a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr36]; exact heap_writable H3 hnew rfl ⟨by simp only; omega, by simp only; omega⟩)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [wr36]; exact heap_writable H3 hcp' hcpu ⟨by omega, by omega⟩))
  have h76 : ∀ a, sp - 120 ≤ a → a < sp → (a < sp - 80 ∨ sp - 72 ≤ a) → (a < sp - 56 ∨ sp - 40 ≤ a) →
      μ7.read a = μ6.read a := fun a h1 h2 h3 h4 =>
    ffr a (by omega) (Or.inr (by omega)) (by omega) (by omega) (Or.inl (by omega)) (Or.inr (by omega))
  have h7S : ∀ a, sp - 120 ≤ a → a < sp → (a < sp - 80 ∨ sp - 72 ≤ a) → (a < sp - 56 ∨ sp - 40 ≤ a) →
      (a < sp - 48 ∨ sp - 24 ≤ a) → (a < sp - 112 ∨ sp - 96 ≤ a) → (a < sp - 72 ∨ sp - 56 ≤ a) →
      μ7.read a = μ1.read a := fun a h1 h2 h3 h4 h5 h6 h7 =>
    (h76 a h1 h2 h3 h4).trans (hS6 a h1 (by omega) h5 h6 h7)
  have h7hi : ∀ a, a < 4294967296 → sp ≤ a → (a < rd ∨ rd + 16 ≤ a) → μ7.read a = μ.read a :=
    fun a h0 h1 h2 => (ffr a h0 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) h2
      (Or.inr (by omega))).trans (hhigh a h0 h1)
  have hlowh : ∀ a, a < 2147483648 → (a < q ∨ q + 16 * 1024 ≤ a) → μ7.read a = μ3.read a := fun a h1 h3 =>
    (ffr a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (by omega)).trans (h63 a h1)
  have wr73 : ∀ a, μ7.writable a = μ3.writable a := fun a => by rw [fwr, wr36]
  have H7 : HeapCtx env pb S0 S1 μ7 s1 :=
    ctx_congr_data H3 hnew (fun a h1 h2 => hlowh a h1 (by simp only at h2; omega)) wr73
  have kd7 : ∀ d ∈ chunks s, d.used = true → ∀ a, InData d a → μ7.read a = μ.read a := by
    intro d hd hu a ha
    have hdis := data_disj H3.wf (keep d hd hu) hnew (hfresh d hd hu) ha
    simp only at hdis
    have hca := ha
    unfold InData at hca
    have := (chunk_in H.wf hd hu).2.2
    rw [hlowh a (by omega) (by omega), kd d hd hu a ha]
    exact hlow a (by omega) (Or.inl (by omega))
  have run17 := run1.trans (run2.trans (run3.trans (run4.trans (run5.trans (run6.trans run7)))))
  -- the later batches
  have hK : ∀ d, (d ∈ chunks s ∧ d.used = true) → d ∈ chunks s1 ∧ d.used = true ∧ d.addr + 32 ≠ q := by
    intro d ⟨hd, hu⟩
    refine ⟨keep d hd hu, hu, fun e => hfresh d hd hu ?_⟩
    have ht := H3.wf.2.2.2.1; unfold TilesOk at ht
    exact Tiles.addr_inj ht d (keep d hd hu) _ hnew (by simp only; omega)
  have hrest := bloop_heap (p := p) (P := P) env cap hcap1 hcap x ω7 μ7 0 s1
    (fun d => d ∈ chunks s ∧ d.used = true) (sp - 120) O rd q 1024 1024 (n - 1024) ptr len ret t v5 v6 pb S0 S1 H7
    ⟨_, hnew, by simp only; omega, rfl, rfl⟩ hK ⟨cp, ⟨hcpm, hcpu⟩, hcp1, by omega⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ f1 f7 (by omega) (by omega) (by omega) (by omega) ⟨by omega, hlen⟩
    (by rw [Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m120)
    (by rw [show 1024 + (n - 1024) = n by omega, Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d16)
    (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d8)
    (by rw [show sp - 120 + 32 = sp - 88 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m88)
    (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d48)
    (by rw [Memory.readN_congr (fun j hj => h76 _ (by omega) (by omega) (by omega) (by omega))]; exact d56)
    f64
    (by rw [show sp - 120 + 112 = sp - 8 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m8)
    (by rw [show sp - 120 + 104 = sp - 16 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m16)
    (by rw [show sp - 120 + 96 = sp - 24 by omega, Memory.readN_congr (fun j hj => h7S _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))]; exact m24)
    hret hjt hbt hv5 hv6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hOr fR0 fR8
    (by rw [fdat, Memory.readN_congr (fun j hj => hpay6 _ ⟨by omega, by omega⟩),
          Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)])
  rcases hrest with ⟨ω', μ', s', q', run', y0, y1, y5, y6, yO, yO8, yO16, ydat, yR0, yR8, yH,
      ⟨cf, hcfm, hcfa, hcfu, hcfs⟩, yK, yfr⟩ | hex
  · have hn' : 1024 + (n - 1024) = n := by omega
    rw [hn'] at yO yO16 ydat yR0 yR8 hcfs
    have runAll := run17.trans run'
    obtain ⟨hfb, -, -⟩ := chunk_in yH.wf hcfm hcfu
    have hyb := yH.hb0
    have hcf : cf = ⟨q' - 32, (16 * n + 31) / 32 + 1, true⟩ := by
      obtain ⟨ca, cs, cu⟩ := cf
      simp only at hcfa hcfu hcfs
      rw [hcfu, hcfs]; congr 1; omega
    refine Or.inl ⟨q', s', ω', μ', runAll.mono (by omega), y0, by rw [y1]; congr 1; omega, y5, y6, yO, yO8,
      yO16, ?_, yR0, yR8, yH,
      fun c hc hu => (yK c ⟨hc, hu⟩).1, hcf ▸ hcfm, ?_, ?_, FreeStepsH.pagesOut H.bd runAll, ?_, ?_, ?_⟩
    · rw [ydat]; exact Memory.readN_congr (fun j hj => kd7 cp hcpm hcpu _ ⟨by omega, by omega⟩)
    · intro d hd hu e
      have := (yK d ⟨hd, hu⟩).2.2.1
      rw [e] at this; simp only at this; omega
    · intro c hc hu a ha
      exact ((yK c ⟨hc, hu⟩).2.2.2 a ha).trans (kd7 c hc hu a ha)
    · intro a h0 h1 h2 h3
      exact (yfr a h0 (by omega) h2 h3).trans (h7hi a h0 h1 h2)
    · intro a ha'
      obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd runAll
      refine ⟨kr a (by unfold two32; omega) (Or.inl (by unfold pageSize; omega)) (H.ro a ha'), ?_⟩
      unfold Memory.readable
      rw [kp _ (Or.inl (by unfold pageSize; omega))]
    · intro a ha'
      obtain ⟨kp, -⟩ := FreeStepsH.keepRO H.bd runAll
      unfold Memory.writable
      rw [kp _ (Or.inr (by unfold pageSize; omega))]
  · exact Or.inr ((Exhausts.pre run17 hex).mono (by omega))

end Services.Bootstrap.Decode.VecPairs
