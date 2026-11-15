import Services.Bootstrap.Refine.ArgsTail
import Services.Bootstrap.Refine.ArgsTailBig
import Services.Bootstrap.Refine.ArgsCtx

/-!
# Refine's argument parse, from pc 0 to 4680

`refine_args`: from Y's state (`StartMem`, `StartMemZ`) with the argument blob
ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ℰ(|y|) ⌢ y ⌢ h at 4278124544 (1 ≤ |y| = Y < 2^24), under refine's host
contract `refineContractK cap env` (2^27 ≤ cap < 2^64): `ArgsCtx.args_ctx` (0 → 35130, lifted from
`refineContract`) composed with `args_tail` (Y ≤ 16384) or `args_tail_big_one` (Y > 16384), here
re-run as `args_tail_hi` / `args_tail_big_hi` with one more clause, the frame above the result struct
(from O + 66 up, so refine's saved words at M + 608 … M + 632) kept from 35130. Either refine's
arguments are parsed into the struct at O = M + 168 (M = 4278058376) with the payload's chunk at the
heap's base, or the run reaches a failed allocator call (`ExhaustsX`).
-/

namespace Services.Bootstrap.Refine.ArgsAll

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Refine.ArgsGlue
  Services.Bootstrap.Alloc.AfterStart Services.Bootstrap.Refine.ArgsTail Services.Bootstrap.Prefix

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `ArgsTail.tail_core` with the frame from O + 66 up. -/
theorem tail_core_hi {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs)
    (μ : Memory) (sp O Y q ptr' I S C v5 v6 S0 S1 : Nat)
    (hS : S0 + 88 ≤ sp ∧ sp + 112 ≤ O ∧ O + 66 ≤ S1 ∧ S1 ≤ ptr' ∧ ptr' + 56 < 4294967296)
    (hsp : 65536 + 88 ≤ sp ∧ sp % 8 = 0)
    (hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true)
    (hY : Y < 4294967296) (hq : q < 4294967296)
    (hI : I < 4294967296) (hS' : S < 4294967296) (hC : C < 65536)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat O)
    (s56 : μ.readN (sp + 56) 8 = Num.encodeLE 8 Y) (s64 : μ.readN (sp + 64) 8 = Num.encodeLE 8 q)
    (s72 : μ.readN (sp + 72) 8 = Num.encodeLE 8 Y)
    (s40 : μ.readN (sp + 40) 8 = Num.encodeLE 8 ptr') (s48 : μ.readN (sp + 48) 8 = Num.encodeLE 8 32)
    (s16 : μ.readN (sp + 16) 8 = Num.encodeLE 8 S) (s24 : μ.readN (sp + 24) 8 = Num.encodeLE 8 I)
    (s32 : μ.readN (sp + 32) 8 = Num.encodeLE 8 C)
    (s88 : μ.readN (sp + 88) 8 = Num.encodeLE 8 v6) (s96 : μ.readN (sp + 96) 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN (sp + 104) 8 = Num.encodeLE 8 152)
    (hra : ∀ a, ptr' ≤ a → a < ptr' + 32 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 35155 ω μ x 4680 ω' μ' x 505 ∧
      ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat (sp + 112) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN O 8 = Num.encodeLE 8 Y ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 q ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 Y ∧ μ'.readN (O + 24) 32 = μ.readN ptr' 32 ∧
      μ'.readN (O + 56) 4 = Num.encodeLE 4 I ∧ μ'.readN (O + 60) 4 = Num.encodeLE 4 S ∧
      μ'.readN (O + 64) 2 = Num.encodeLE 2 C ∧
      (∀ a, a < sp - 88 → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      (∀ a, O + 66 ≤ a → a < 4294967296 → μ'.read a = μ.read a) := by
  obtain ⟨hS0, hSO, hOS, hSp, hp⟩ := hS
  have hrd : ∀ a, S0 ≤ a → a < S1 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a h1 h2)
  obtain ⟨ω2, μ2, run2, b0, b1, b6, b7, b8, b9, -, -, -, b5, -, -, -, m0, m8, -, -, -, -, fr2, rd2, wr2⟩ :=
    glue_post_vec (P := P) (R := R) x ω μ sp Y q Y (by omega) (by omega) (by omega) (by omega) h1 s56 s64 s72
      (fun a h1 h2 => hrd a (by omega) (by omega)) (fun a h1 h2 => hst a (by omega) (by omega))
      (fun a h1 h2 => hst a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < sp ∨ sp + 16 ≤ a) → (a < sp + 56 ∨ sp + 88 ≤ a) →
      μ2.read a = μ.read a := fr2
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, -, -, cbuf, fr3, rd3, wr3⟩ :=
    read_big (P := P) (R := R) x ω2 μ2 1644 35202 sp (sp + 40) (sp + 56) ptr' 32 32 b0 b1 b7 b8 b9 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_821]) bs_35202 ⟨by omega, by omega, hsp.2⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega)
      (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [wr2]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr2]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr2]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [rd2]; exact hra a h1 h2)
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; exact s40)
      (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))]; exact s48)
  have k3 : ∀ a, a < 4294967296 → (a < sp - 88 ∨ sp ≤ a) → (a < sp + 40 ∨ sp + 40 + 16 ≤ a) →
      (a < sp + 56 ∨ sp + 56 + 32 ≤ a) → μ3.read a = μ2.read a := fr3
  have k31 : ∀ a, sp + 16 ≤ a → a < sp + 40 ∨ sp + 88 ≤ a → a < 4294967296 → μ3.read a = μ.read a :=
    fun a h1 h2 h3 => (k3 a h3 (Or.inr (by omega)) (by omega) (by omega)).trans (k2 a h3 (Or.inr h1) (by omega))
  obtain ⟨ω4, μ4, run4, d0, d1, d5, d6, dc, dq, dl, dh, dI, dS, dC, fr4, rd4, wr4⟩ :=
    glue_tail_4680 (P := P) (R := R) x ω3 μ3 sp O Y q Y I S C v5 v6 hSO (by omega) (by omega) (by omega)
      (by omega) hI hS' hC hv5 hv6 (c1.trans b1) (c5.trans (b5.trans h5)) (c6.trans b6) c7
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (Or.inr (by omega)) (by omega) (by omega))]; exact m0)
      (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (Or.inr (by omega)) (by omega) (by omega))]; exact m8)
      (by rw [Memory.readN_congr (fun j hj => k31 _ (by omega) (by omega) (by omega))]; exact s16)
      (by rw [Memory.readN_congr (fun j hj => k31 _ (by omega) (by omega) (by omega))]; exact s24)
      (by rw [Memory.readN_congr (fun j hj => k31 _ (by omega) (by omega) (by omega))]; exact s32)
      (by rw [Memory.readN_congr (fun j hj => k31 _ (by omega) (by omega) (by omega))]; exact s88)
      (by rw [Memory.readN_congr (fun j hj => k31 _ (by omega) (by omega) (by omega))]; exact s96)
      (by rw [Memory.readN_congr (fun j hj => k31 _ (by omega) (by omega) (by omega))]; exact s104)
      (fun a h1 h2 => by rw [rd3, rd2]; exact hrd a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr3, wr2]; exact hst a (by omega) (by omega))
  refine ⟨ω4, μ4, (run2.trans (run3.trans run4)).mono (by omega), d0, d1, d5, d6, dc, dq, dl, ?_, dI, dS, dC,
    fun a ha => ?_, fun a => by rw [rd4, rd3, rd2], fun a => by rw [wr4, wr3, wr2], fun a h1 h2 => ?_⟩
  · rw [dh, cbuf]
    exact Memory.readN_congr (fun j hj => k2 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
  · rw [fr4 a (by omega) (Or.inl (by omega)), k3 a (by omega) (Or.inl ha) (Or.inl (by omega)) (Or.inl (by omega))]
    exact k2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  · rw [fr4 a h2 (Or.inr h1), k3 a h2 (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))]
    exact k2 a h2 (Or.inr (by omega)) (Or.inr (by omega))

/-- **The success of the parse from 35130**, from the state (μ0) at 35130: `args_tail`'s success form
    plus the frame from O + 66 = 4278058610 up kept. -/
def TailOut (env : RefineHost.Env) (μ0 : Memory) (Y C I S v5 v6 : Nat) (y h : List UInt8) (q : Nat) (s' : State)
    (ω' : Regs) (μ' : Memory) : Prop :=
  ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat 4278058376 ∧ ω'[5] = UInt64.ofNat v5 ∧
  ω'[6] = UInt64.ofNat v6 ∧
  μ'.readN 4278058544 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058552 8 = Num.encodeLE 8 q ∧
  μ'.readN 4278058560 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058568 32 = h ∧
  μ'.readN 4278058600 4 = Num.encodeLE 4 I ∧ μ'.readN 4278058604 4 = Num.encodeLE 4 S ∧
  μ'.readN 4278058608 2 = Num.encodeLE 2 C ∧
  μ'.readN q Y = y ∧ HeapCtx env 1044430 4278050816 4278059008 μ' s' ∧
  q = 206912 ∧ s'.base = 206880 ∧
  (∃ cp ∈ chunks s', cp.used = true ∧ cp.addr = s'.base ∧ cp.addr + 32 = q ∧
    ∀ a, q ≤ a → a < q + Y → InData cp a) ∧
  TablesKept μ0 μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true) ∧
  (∀ a, 4278058610 ≤ a → a < 4294967296 → μ'.read a = μ0.read a)

/-- `ArgsTail.from_vec` through `tail_core_hi`, with the payload's chunk at the base given, ending in
    `TailOut`. -/
theorem from_vec_hi {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (x : RefineCtx) (ω : Regs) (μ μ2 : Memory) (ω2 : Regs) (s' : State) (Y q ptr C I S v5 v6 n2 : Nat)
    (y h : List UInt8)
    (H2 : HeapCtx env 1044430 4278050816 4278059008 μ2 s')
    (hY : 1 ≤ Y ∧ Y < 4294967296) (hptr : 4278059008 ≤ ptr ∧ ptr + Y + 56 < 4294967296)
    (hC : C < 65536) (hI : I < 4294967296) (hS : S < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hra : ∀ a, ptr ≤ a → a < ptr + Y + 32 → μ.readable a = true)
    (hy : μ.readN ptr Y = y) (hh : μ.readN (ptr + Y) 32 = h)
    (s16 : μ.readN 4278058280 8 = Num.encodeLE 8 S) (s24 : μ.readN 4278058288 8 = Num.encodeLE 8 I)
    (s32 : μ.readN 4278058296 8 = Num.encodeLE 8 C)
    (s88 : μ.readN 4278058352 8 = Num.encodeLE 8 v6) (s96 : μ.readN 4278058360 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN 4278058368 8 = Num.encodeLE 8 152)
    (run2 : FreeStepsH p (refineContractK cap env) 35130 ω μ x 35155 ω2 μ2 x n2)
    (H : HeapCtx env 1044430 4278050816 4278059008 μ sStart)
    (b1 : ω2[1] = UInt64.ofNat 4278058264) (b5 : ω2[5] = UInt64.ofNat 4278058544)
    (bO : μ2.readN 4278058320 8 = Num.encodeLE 8 Y) (bO8 : μ2.readN (4278058320 + 8) 8 = Num.encodeLE 8 q)
    (bO16 : μ2.readN (4278058320 + 16) 8 = Num.encodeLE 8 Y) (bdat : μ2.readN q Y = μ.readN ptr Y)
    (bR0 : μ2.readN 4278058304 8 = Num.encodeLE 8 (ptr + Y))
    (bR8 : μ2.readN (4278058304 + 8) 8 = Num.encodeLE 8 (Y + 32 - Y))
    (hnew : (⟨q - 32, (Y + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s')
    (hq : q = 206912) (hbase : s'.base = 206880)
    (bfr : ∀ a, a < 4294967296 → 4278058264 ≤ a → (a < 4278058304 ∨ 4278058304 + 16 ≤ a) →
      (a < 4278058320 ∨ 4278058320 + 24 ≤ a) → μ2.read a = μ.read a) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 35130 ω μ x 4680 ω' μ' x (n2 + 505) ∧
      TailOut env μ Y C I S v5 v6 y h q s' ω' μ' := by
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H2.wf hnew rfl
  simp only at hq0 hqT
  have hb0 := H2.hb0
  have hbT := H2.hbT
  have hSb := H.hSb
  have hpay : ∀ a, 4278059008 ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h1 h2 =>
    bfr a h2 (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  have kf : ∀ a, 4278058264 ≤ a → a < 4278058304 ∨ 4278058344 ≤ a → a < 4278059008 → μ2.read a = μ.read a :=
    fun a h1 h2 h3 => bfr a (by omega) h1 (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, d0, d1, d5, d6, dc, dq, dl, dh, dI, dS, dC, fr3, rd3, wr3, hi3⟩ :=
    tail_core_hi (P := P) (R := refineContractK cap env) x ω2 μ2 4278058264 4278058544 Y q (ptr + Y) I S C v5 v6
      4278050816 4278059008 ⟨by omega, by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega⟩ H2.st
      (by omega) (by omega) hI hS hC hv5 hv6 b1 b5 bO bO8 bO16 bR0
      (by rw [show Y + 32 - Y = 32 by omega] at bR8; exact bR8)
      (by rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega) (by omega))]; exact s16)
      (by rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega) (by omega))]; exact s24)
      (by rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega) (by omega))]; exact s32)
      (by rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega) (by omega))]; exact s88)
      (by rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega) (by omega))]; exact s96)
      (by rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega) (by omega))]; exact s104)
      (fun a h1 h2 => by
        rw [Decode.VecU8.readable_hi H.bd run2 (by omega)]; exact hra a (by omega) (by omega))
  have runAll := run2.trans run3
  have H3 : HeapCtx env 1044430 4278050816 4278059008 μ3 s' :=
    Decode.VecU8.ctx_congr_hi H2 (fun a ha => fr3 a (by omega)) wr3
  refine ⟨ω3, μ3, runAll, d0, d1, d5, d6, dc, dq, dl, ?_, dI, dS, dC, ?_, H3, hq, hbase,
    ⟨_, hnew, rfl, by simp only; omega, by simp only; omega, fun a h1 h2 => ⟨by simp only; omega, by simp only; omega⟩⟩,
    tables_kept H runAll, fun a h1 h2 => H3.st a h1 h2, fun a h1 h2 => ?_⟩
  · rw [dh, ← hh]
    exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))
  · rw [← hy, ← bdat]
    exact Memory.readN_congr (fun j hj => fr3 _ (by omega))
  · rw [hi3 a (by omega) h2]
    exact bfr a h2 (by omega) (Or.inr (by omega)) (Or.inr (by omega))

/-- **`args_tail` with the frame from O + 66 up** (1 ≤ Y ≤ 16384). -/
theorem args_tail_hi {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
    (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs) (μ : Memory)
    (Y ptr C I S v5 v6 : Nat) (y h : List UInt8)
    (H : HeapCtx env 1044430 4278050816 4278059008 μ sStart)
    (hY : 1 ≤ Y ∧ Y ≤ 16384) (hptr : 4278059008 ≤ ptr ∧ ptr + Y + 56 < 4294967296)
    (hC : C < 65536) (hI : I < 4294967296) (hS : S < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hra : ∀ a, ptr ≤ a → a < ptr + Y + 32 → μ.readable a = true)
    (hy : μ.readN ptr Y = y) (hh : μ.readN (ptr + Y) 32 = h)
    (h1 : ω[1] = UInt64.ofNat 4278058264) (h5 : ω[5] = UInt64.ofNat 4278058544)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat Y)
    (s40 : μ.readN 4278058304 8 = Num.encodeLE 8 ptr) (s48 : μ.readN 4278058312 8 = Num.encodeLE 8 (Y + 32))
    (s16 : μ.readN 4278058280 8 = Num.encodeLE 8 S) (s24 : μ.readN 4278058288 8 = Num.encodeLE 8 I)
    (s32 : μ.readN 4278058296 8 = Num.encodeLE 8 C)
    (s88 : μ.readN 4278058352 8 = Num.encodeLE 8 v6) (s96 : μ.readN 4278058360 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN 4278058368 8 = Num.encodeLE 8 152) :
    (∃ q s' ω' μ' N, FreeStepsH p (refineContractK cap env) 35130 ω μ x 4680 ω' μ' x N ∧
      TailOut env μ Y C I S v5 v6 y h q s' ω' μ') ∨
    ∃ N, PassLoop.ExhaustsX env cap 1044430 p 35130 ω μ x N := by
  obtain ⟨ω1, run1, a0, a1, a7, a8, a9, -, -, -, a5, a6, -, -, -⟩ :=
    glue_pre_vec (P := P) (R := refineContractK cap env) x ω μ 4278058264 Y (by omega) (by omega) h1 h7 h8
  have hv6' : (ω[6]).toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  rcases Decode.VecU8.vec_u8_args (P := P) (hb := 0) env cap hcap1 hcap x ω1 μ sStart 4278058264 4278058320
      4278058304 ptr (Y + 32) Y 1642 35155 4278058544 (ω[6]).toNat 1044430 4278050816 4278059008 H
      ⟨hptr.1, by omega⟩ (fun a h1 h2 => hra a h1 (by omega)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      a0 a1 (a5.trans h5) (by rw [a6, UInt64.ofNat_toNat]) a7 a8 a9 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_820]) bs_35155 (by omega) hv6' hY (by omega)
      (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) s40 s48 with
    ⟨q, s', ω2, μ2, ha, run2, -, b1, b5, -, bO, bO8, bO16, bdat, bR0, bR8, H2, -, hnew, -, -, -, bfr, -, -, -⟩ |
    ⟨hna, ω2, μ2, run2, e7⟩
  · obtain ⟨hq, -, -, -, -, hbase⟩ := alloc_sStart ha
    obtain ⟨ω', μ', run, out⟩ :=
      from_vec_hi (P := P) env cap x ω μ μ2 ω2 s' Y q ptr C I S v5 v6 _ y h H2 ⟨hY.1, by omega⟩ hptr hC hI hS hv5
        hv6 hra hy hh s16 s24 s32 s88 s96 s104 (run1.trans run2) H b1 (b5.trans (by rfl)) bO bO8 bO16 bdat bR0
        bR8 hnew hq hbase bfr
    exact Or.inl ⟨q, s', ω', μ', _, run, out⟩
  · exact Or.inr ⟨_, PassLoop.ExhaustsX.ofFmt ⟨ω2, μ2, x, 40611, run1.trans run2, e7, Or.inl rfl⟩⟩

/-- **`args_tail_big_one` with the frame from O + 66 up** (16384 < Y < 2^30 − 64). -/
theorem args_tail_big_hi {p : ByteArray} {P : Program} [HasCode p P] [CodeX.HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616) (x : RefineCtx) (ω : Regs)
    (μ : Memory) (Y ptr C I S v5 v6 : Nat) (y h : List UInt8)
    (H : HeapCtx env 1044430 4278050816 4278059008 μ sStart)
    (hY : 16384 < Y ∧ Y < 1073741760) (hptr : 4278059008 ≤ ptr ∧ ptr + Y + 56 < 4294967296)
    (hC : C < 65536) (hI : I < 4294967296) (hS : S < 4294967296)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hra : ∀ a, ptr ≤ a → a < ptr + Y + 32 → μ.readable a = true)
    (hy : μ.readN ptr Y = y) (hh : μ.readN (ptr + Y) 32 = h)
    (h1 : ω[1] = UInt64.ofNat 4278058264) (h5 : ω[5] = UInt64.ofNat 4278058544)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat Y)
    (s40 : μ.readN 4278058304 8 = Num.encodeLE 8 ptr) (s48 : μ.readN 4278058312 8 = Num.encodeLE 8 (Y + 32))
    (s16 : μ.readN 4278058280 8 = Num.encodeLE 8 S) (s24 : μ.readN 4278058288 8 = Num.encodeLE 8 I)
    (s32 : μ.readN 4278058296 8 = Num.encodeLE 8 C)
    (s88 : μ.readN 4278058352 8 = Num.encodeLE 8 v6) (s96 : μ.readN 4278058360 8 = Num.encodeLE 8 v5)
    (s104 : μ.readN 4278058368 8 = Num.encodeLE 8 152) :
    (∃ q s' ω' μ' N, FreeStepsH p (refineContractK cap env) 35130 ω μ x 4680 ω' μ' x N ∧
      TailOut env μ Y C I S v5 v6 y h q s' ω' μ') ∨
    ∃ N, PassLoop.ExhaustsX env cap 1044430 p 35130 ω μ x N := by
  obtain ⟨ω1, run1, a0, a1, a7, a8, a9, -, -, -, a5, a6, -, -, -⟩ :=
    glue_pre_vec (P := P) (R := refineContractK cap env) x ω μ 4278058264 Y (by omega) (by omega) h1 h7 h8
  have hv6' : (ω[6]).toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  rcases Decode.VecU8.vec_u8_args_big_one (P := P) env cap hcap1 hcap x ω1 μ 4278058264 4278058320
      4278058304 ptr (Y + 32) Y 1642 35155 4278058544 (ω[6]).toNat 1044430 4278050816 4278059008 H
      ⟨hptr.1, by omega⟩ (fun a h1 h2 => hra a h1 (by omega)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      a0 a1 (a5.trans h5) (by rw [a6, UInt64.ofNat_toNat]) a7 a8 a9 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_820]) bs_35155 (by omega) hv6' hY (by omega)
      (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) s40 s48 with
    ⟨q, s', ω2, μ2, run2, -, b1, b5, -, bO, bO8, bO16, bdat, bR0, bR8, H2, -, hnew, -, -, -, bfr, -, -, -, hq,
      hbase, -⟩ | hex
  · obtain ⟨ω', μ', run, out⟩ :=
      from_vec_hi (P := P) env cap x ω μ μ2 ω2 s' Y q ptr C I S v5 v6 _ y h H2 ⟨by omega, by omega⟩ hptr hC hI hS
        hv5 hv6 hra hy hh s16 s24 s32 s88 s96 s104 (run1.trans run2) H b1 (b5.trans (by rfl))
        bO bO8 bO16 bdat bR0 bR8 hnew hq hbase bfr
    exact Or.inl ⟨q, s', ω', μ', _, run, out⟩
  · exact Or.inr ⟨_, PassLoop.ExhaustsX.pre run1 (PassLoop.ExhaustsX.of hex)⟩

/-- The read-only tables of the initial memory survive a refine run to a state with the allocator's
    context (whose read-only region, below 196608, is not writable). -/
theorem tables_kept0 {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory}
    {s : State} {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} (H : HeapCtx env pb S0 S1 μ' s)
    (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n) : TablesKept μ μ' := by
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
  have hro : ∀ b, b < 196608 → μ.writable b = false := fun b hb => by
    have := H.ro b hb
    unfold Memory.writable at this ⊢
    rw [← kp _ (Or.inl (by unfold pageSize; omega))]; exact this
  have key : ∀ a l, a + l ≤ 196608 →
      μ'.readN a l = μ.readN a l ∧ ∀ b, a ≤ b → b < a + l → μ'.readable b = μ.readable b := fun a l hal =>
    ⟨Memory.readN_congr (fun j hj => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
      (hro _ (by omega))), fun b h1 h2 => by unfold Memory.readable; rw [kp _ (Or.inl (by unfold pageSize; omega))]⟩
  obtain ⟨a1, a2⟩ := key 67476 100 (by omega)
  obtain ⟨b1, b2⟩ := key 67376 100 (by omega)
  obtain ⟨c1, c2⟩ := key 67760 96 (by omega)
  exact ⟨a1, a2, b1, b2, c1, c2⟩

theorem TablesKept.trans {μ μ' μ'' : Memory} (h1 : TablesKept μ μ') (h2 : TablesKept μ' μ'') : TablesKept μ μ'' := by
  obtain ⟨a1, a2, b1, b2, c1, c2⟩ := h1
  obtain ⟨d1, d2, e1, e2, f1, f2⟩ := h2
  exact ⟨d1.trans a1, fun b x y => (d2 b x y).trans (a2 b x y), e1.trans b1, fun b x y => (e2 b x y).trans (b2 b x y),
    f1.trans c1, fun b x y => (f2 b x y).trans (c2 b x y)⟩

/-- **Refine's argument parse, pc 0 → 4680**, under `refineContractK cap env` (2^27 ≤ cap < 2^64), from
    Y's state with the argument blob ℰ(c) ⌢ ℰ(i) ⌢ ℰ(s) ⌢ ℰ(|y|) ⌢ y ⌢ h at 4278124544, 1 ≤ |y| = Y < 2^24.
    Either the run reaches 4680 with sp = M = 4278058376, ω₀ = 152, ω₅ = L and ω₆ = 4278124544 (the
    values the arguments' code restores), the result struct at O = M + 168 = 4278058544
    {cap Y, ptr q = 206912, len Y, h, i, s, c}, y at q, the allocator's context for s' (base 206880) whose
    chunk at the base holds [q, q + Y), the read-only tables and the stack's access kept, and refine's
    saved words at M + 624 (the return address 2^32 − 2^16 = initial ω₀), M + 616 and M + 608 (the
    initial ω₅ and ω₆, both 0); or it reaches a failed allocator call (`ExhaustsX`). -/
theorem refine_args (p : ByteArray) (P : Program) [HasCode p P] [CodeX.HasCodeX p P] (env : RefineHost.Env)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (henv : heapBounds env.code = (48, 1044430)) (hpar : env.fetch.params = Params.full) (μ : Memory)
    (hμ : StartMem μ) (hz : StartMemZ μ) (C I S : Nat) (h : List UInt8) (hC : C < 65536) (hI : I < 65536)
    (hS : S < 4294967296) (Y : Nat) (hY1 : 1 ≤ Y) (hY : Y < 16777216) (y : List UInt8) (hy : y.length = Y)
    (hh : h.length = 32) (L : Nat)
    (hLdef : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
      (Blob.encodeNat Y).length + Y + 32 = L) (hL : L < 16777217)
    (hmem : μ.readN 4278124544 L = Blob.encodeNat C ++ Blob.encodeNat I ++ Blob.encodeNat S ++
      Blob.encodeNat Y ++ y ++ h)
    (hrd : ∀ j, 4278124544 ≤ j → j < 4278124544 + L → μ.readable j = true) :
    (∃ q s' ω' μ' N, FreeStepsH p (refineContractK cap env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 4680 ω' μ'
        ((∅, []) : RefineCtx) N ∧
      ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat 4278058376 ∧ ω'[5] = UInt64.ofNat L ∧
      ω'[6] = UInt64.ofNat 4278124544 ∧
      μ'.readN 4278058544 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058552 8 = Num.encodeLE 8 q ∧
      μ'.readN 4278058560 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058568 32 = h ∧
      μ'.readN 4278058600 4 = Num.encodeLE 4 I ∧ μ'.readN 4278058604 4 = Num.encodeLE 4 S ∧
      μ'.readN 4278058608 2 = Num.encodeLE 2 C ∧
      μ'.readN q Y = y ∧ HeapCtx env 1044430 4278050816 4278059008 μ' s' ∧
      q = 206912 ∧ s'.base = 206880 ∧
      (∃ cp ∈ chunks s', cp.used = true ∧ cp.addr = s'.base ∧ cp.addr + 32 = q ∧
        ∀ a, q ≤ a → a < q + Y → InData cp a) ∧
      TablesKept μ μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true) ∧
      μ'.readN (4278058376 + 624) 8 = Num.encodeLE 8 4294901760 ∧
      μ'.readN (4278058376 + 616) 8 = Num.encodeLE 8 0 ∧ μ'.readN (4278058376 + 608) 8 = Num.encodeLE 8 0 ∧
      (initRegs L)[0] = UInt64.ofNat 4294901760 ∧ (initRegs L)[5] = UInt64.ofNat 0 ∧
      (initRegs L)[6] = UInt64.ofNat 0) ∨
    ∃ N, PassLoop.ExhaustsX env cap 1044430 p 0 (initRegs L) μ ((∅, []) : RefineCtx) N := by
  obtain ⟨ω1, μ1, run0, post, H1⟩ := ArgsCtx.args_ctx p P env henv hpar μ hμ C I S h hC hI hS Y hY1 hY y hy hh L
    hLdef hL hmem hrd hz
  have run0' : FreeStepsH p (refineContractK cap env) 0 (initRegs L) μ ((∅, []) : RefineCtx) 35130 ω1 μ1
      ((∅, []) : RefineCtx) 6000 :=
    run0.weaken (fun _ _ _ _ _ _ _ hr => refineContract_le (by unfold hostCostMax; omega)
      (by simp only [Nat.reducePow]; omega) env hr)
  unfold ArgsCtx.ArgsPost at post
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, c128, c129, c130, c131⟩ := post
  have q0 : ω1[1] = UInt64.ofNat 4278058264 := by assumption
  have q2 : ω1[5] = UInt64.ofNat 4278058544 := by assumption
  have q4 : ω1[7] = UInt64.ofNat 0 := by assumption
  have q5 : ω1[8] = UInt64.ofNat Y := by assumption
  have q14 : μ1.readN 4278058312 8 = Num.encodeLE 8 (Y + 32) := by assumption
  have q40 : μ1.readN 4278058352 8 = [0, 0, 255, 254, 0, 0, 0, 0] := by assumption
  have q41 : μ1.readN 4278058368 8 = [152, 0, 0, 0, 0, 0, 0, 0] := by assumption
  have q42 : μ1.readN 4278058360 8 = Num.encodeLE 8 L := by assumption
  have q89 : μ1.readN 4278058280 8 = Num.encodeLE 8 S := by assumption
  have q90 : μ1.readN 4278058288 8 = Num.encodeLE 8 I := by assumption
  have q91 : μ1.readN 4278058296 8 = Num.encodeLE 8 C := by assumption
  have q92 : μ1.readN 4278058304 8 = Num.encodeLE 8 (4278124544 + (Blob.encodeNat C).length +
    (Blob.encodeNat I).length + (Blob.encodeNat S).length + (Blob.encodeNat Y).length) := by assumption
  have q93 : μ1.readN (4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length +
    (Blob.encodeNat S).length + (Blob.encodeNat Y).length) Y = y := by assumption
  have q94 : ∀ a, 4278124544 ≤ a → a < 4278124544 + L → μ1.readable a = true := by assumption
  have q106 : μ1.readN 4278058984 8 = [0, 0, 0, 0, 0, 0, 0, 0] := by assumption
  have q107 : μ1.readN 4278058992 8 = [0, 0, 0, 0, 0, 0, 0, 0] := by assumption
  have q108 : μ1.readN 4278059000 8 = [0, 0, 255, 255, 0, 0, 0, 0] := by assumption
  have q130 : ∀ a, 4278059008 ≤ a → a < 4294967296 → μ1.read a = μ.read a := by assumption
  clear c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61 c62 c63 c64 c65 c66 c67 c68 c69 c70 c71 c72 c73 c74 c75 c76 c77 c78 c79 c80 c81 c82 c83 c84 c85 c86 c87 c88 c89 c90 c91 c92 c93 c94 c95 c96 c97 c98 c99 c100 c101 c102 c103 c104 c105 c106 c107 c108 c109 c110 c111 c112 c113 c114 c115 c116 c117 c118 c119 c120 c121 c122 c123 c124 c125 c126 c127 c128 c129 c130 c131
  -- the payload's pointer and the hash
  generalize hk : (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
    (Blob.encodeNat Y).length = k at hLdef
  have ep : 4278124544 + (Blob.encodeNat C).length + (Blob.encodeNat I).length + (Blob.encodeNat S).length +
      (Blob.encodeNat Y).length = 4278124544 + k := by omega
  rw [ep] at q92 q93
  have hh1 : μ1.readN (4278124544 + k + Y) 32 = h := by
    rw [Memory.readN_congr (fun j hj => q130 _ (by omega) (by omega))]
    have e := Memory.readN_split μ 4278124544 (k + Y) 32
    rw [show k + Y + 32 = L by omega, hmem] at e
    have := (List.append_inj' e (by simp only [Memory.length_readN, hh])).2
    rw [Nat.add_assoc, ← this]
  have s88 : μ1.readN 4278058352 8 = Num.encodeLE 8 4278124544 := by rw [q40]; decide
  have s104 : μ1.readN 4278058368 8 = Num.encodeLE 8 152 := by rw [q41]; decide
  have hi0 : (initRegs L)[0] = UInt64.ofNat 4294901760 := by simp [initRegs]
  have hi5 : (initRegs L)[5] = UInt64.ofNat 0 := by simp [initRegs]
  have hi6 : (initRegs L)[6] = UInt64.ofNat 0 := by simp [initRegs]
  have hfin : ∀ ω' μ' q s', TailOut env μ1 Y C I S L 4278124544 y h q s' ω' μ' →
      ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat 4278058376 ∧ ω'[5] = UInt64.ofNat L ∧
      ω'[6] = UInt64.ofNat 4278124544 ∧
      μ'.readN 4278058544 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058552 8 = Num.encodeLE 8 q ∧
      μ'.readN 4278058560 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058568 32 = h ∧
      μ'.readN 4278058600 4 = Num.encodeLE 4 I ∧ μ'.readN 4278058604 4 = Num.encodeLE 4 S ∧
      μ'.readN 4278058608 2 = Num.encodeLE 2 C ∧
      μ'.readN q Y = y ∧ HeapCtx env 1044430 4278050816 4278059008 μ' s' ∧
      q = 206912 ∧ s'.base = 206880 ∧
      (∃ cp ∈ chunks s', cp.used = true ∧ cp.addr = s'.base ∧ cp.addr + 32 = q ∧
        ∀ a, q ≤ a → a < q + Y → InData cp a) ∧
      TablesKept μ μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true) ∧
      μ'.readN (4278058376 + 624) 8 = Num.encodeLE 8 4294901760 ∧
      μ'.readN (4278058376 + 616) 8 = Num.encodeLE 8 0 ∧ μ'.readN (4278058376 + 608) 8 = Num.encodeLE 8 0 ∧
      (initRegs L)[0] = UInt64.ofNat 4294901760 ∧ (initRegs L)[5] = UInt64.ofNat 0 ∧
      (initRegs L)[6] = UInt64.ofNat 0 := by
    intro ω' μ' q s' o
    obtain ⟨o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hq, hb, hcp, tk, wst, fr⟩ := o
    refine ⟨o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hq, hb, hcp,
      TablesKept.trans (tables_kept0 H1 run0') tk, wst, ?_, ?_, ?_, hi0, hi5, hi6⟩
    · rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega)), q108]; decide
    · rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega)), q107]; decide
    · rw [Memory.readN_congr (fun j hj => fr _ (by omega) (by omega)), q106]; decide
  by_cases hsm : Y ≤ 16384
  · rcases args_tail_hi (P := P) env cap hcap1 hcap ((∅, []) : RefineCtx) ω1 μ1 Y (4278124544 + k) C I S L
        4278124544 y h H1 ⟨hY1, hsm⟩ ⟨by omega, by omega⟩ hC (by omega) hS (by omega) (by omega)
        (fun a h1 h2 => q94 a (by omega) (by omega)) q93 hh1 q0 q2 q4 q5 q92 q14 q89 q90 q91 s88 q42 s104 with
      ⟨q, s', ω', μ', N, run, out⟩ | ⟨N, hex⟩
    · exact Or.inl ⟨q, s', ω', μ', _, run0'.trans run, hfin ω' μ' q s' out⟩
    · exact Or.inr ⟨_, PassLoop.ExhaustsX.pre run0' hex⟩
  · rcases args_tail_big_hi (P := P) env cap hcap1 hcap ((∅, []) : RefineCtx) ω1 μ1 Y (4278124544 + k) C I S L
        4278124544 y h H1 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hC (by omega) hS (by omega) (by omega)
        (fun a h1 h2 => q94 a (by omega) (by omega)) q93 hh1 q0 q2 q4 q5 q92 q14 q89 q90 q91 s88 q42 s104 with
      ⟨q, s', ω', μ', N, run, out⟩ | ⟨N, hex⟩
    · exact Or.inl ⟨q, s', ω', μ', _, run0'.trans run, hfin ω' μ' q s' out⟩
    · exact Or.inr ⟨_, PassLoop.ExhaustsX.pre run0' hex⟩

end Services.Bootstrap.Refine.ArgsAll
