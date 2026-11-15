import Services.Bootstrap.Refine.ArgsGlue
import Services.Bootstrap.Refine.PassLoop
import Services.Bootstrap.Decode.VecU8ArgsBig
import Services.Bootstrap.Alloc.AfterStart
import Services.Bootstrap.ReaderBig

/-!
# Refine's argument parse from 35130 to 4680

From `run_args_gen`'s state at 35130 (the decodes of c, i, s and |y| = Y done, the reader at
sp + 40 pointing at the payload y, followed by the 32-octet hash h, in the argument zone), the rest of
refine's argument decode: `glue_pre_vec` (35130 → 3473), `read_vec` of the payload into a fresh
`Vec<u8>` (`vec_u8_args`, 1 ≤ Y ≤ 16384, or `vec_u8_args_big`, Y > 16384; 3473 → 35155),
`glue_post_vec` (35155 → 58434), `read_big` of the hash (58434 → 35202) and `glue_tail_4680`
(35202 → 4680). The frame: sp = 4278058264, M = sp + 112 = 4278058376, the result struct at
O = M + 168 = 4278058544.

* `tail_core`: 35155 → 4680, from `read_vec`'s return, under any host relation.
* `args_tail`: 35130 → 4680 for 1 ≤ Y ≤ 16384, from the allocator's start-up state `sStart`: the
  payload's chunk is the first allocation, at the heap's base 206880 (q = 206912).
* `args_tail_big`: 35130 → 4680 for 16384 < Y < 2^30 − 64. `vec_u8_args_big` exposes no equation
  of the model's `alloc` / `realloc` calls (only an allocated chunk of ⌈Y/32⌉ + 1 units with data at
  q), so the chunk's address is not tied to the base here.
-/

namespace Services.Bootstrap.Refine.ArgsTail

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Refine.ArgsGlue
  Services.Bootstrap.Alloc.AfterStart

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **35155 → 4680**: from `read_vec`'s return with the `Vec` {Y, q, Y} at sp + 56 and the reader at
    sp + 40 now at the hash (ptr', 32 octets left): `glue_post_vec`, `read_big` of the hash into
    sp + 56 and `glue_tail_4680`. Memory below sp − 88 is kept, as are all pages' access. -/
theorem tail_core {p : ByteArray} {P : Program} [HasCode p P] {X : Type} {R : HostRel X} (x : X) (ω : Regs)
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
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
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
    fun a ha => ?_, fun a => by rw [rd4, rd3, rd2], fun a => by rw [wr4, wr3, wr2]⟩
  · rw [dh, cbuf]
    exact Memory.readN_congr (fun j hj => k2 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
  · rw [fr4 a (by omega) (Or.inl (by omega)), k3 a (by omega) (Or.inl ha) (Or.inl (by omega)) (Or.inl (by omega))]
    exact k2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))

/-- A refine run keeps the read-only data (below 196608), values and access (as `ExitRun.ro_keep`). -/
theorem ro_keep' {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} (H : HeapCtx env pb S0 S1 μ s)
    (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n) {a l : Nat} (hal : a + l ≤ 196608) :
    μ'.readN a l = μ.readN a l ∧ ∀ b, a ≤ b → b < a + l → μ'.readable b = μ.readable b := by
  obtain ⟨kp, kr⟩ := FreeStepsH.keepRO H.bd run
  refine ⟨Memory.readN_congr (fun j hj => kr _ (by unfold two32; omega) (Or.inl (by unfold pageSize; omega))
    (H.ro _ (by omega))), fun b h1 h2 => ?_⟩
  unfold Memory.readable; rw [kp _ (Or.inl (by unfold pageSize; omega))]

/-- The three read-only tables refine's later code reads (67476: the decoders' jump table, 67376: the
    exit encoder's, 67760: the drops'), kept by a refine run. -/
def TablesKept (μ μ' : Memory) : Prop :=
  μ'.readN 67476 100 = μ.readN 67476 100 ∧ (∀ b, 67476 ≤ b → b < 67576 → μ'.readable b = μ.readable b) ∧
  μ'.readN 67376 100 = μ.readN 67376 100 ∧ (∀ b, 67376 ≤ b → b < 67476 → μ'.readable b = μ.readable b) ∧
  μ'.readN 67760 96 = μ.readN 67760 96 ∧ (∀ b, 67760 ≤ b → b < 67856 → μ'.readable b = μ.readable b)

theorem tables_kept {p : ByteArray} {cap0 : Nat} {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory}
    {s : State} {i i' n : Nat} {ω ω' : Regs} {x x' : RefineCtx} (H : HeapCtx env pb S0 S1 μ s)
    (run : FreeStepsH p (refineContractK cap0 env) i ω μ x i' ω' μ' x' n) : TablesKept μ μ' := by
  obtain ⟨a1, a2⟩ := ro_keep' H run (a := 67476) (l := 100) (by omega)
  obtain ⟨b1, b2⟩ := ro_keep' H run (a := 67376) (l := 100) (by omega)
  obtain ⟨c1, c2⟩ := ro_keep' H run (a := 67760) (l := 96) (by omega)
  exact ⟨a1, a2, b1, b2, c1, c2⟩

/-- **From `read_vec`'s return to 4680, at refine's frame**: `tail_core` at sp = 4278058264, from the
    post of `vec_u8_args` / `vec_u8_args_big` (the `Vec` {Y, q, Y} at sp + 56, the reader at the hash,
    the heap context for s' with q the data of an allocated chunk of ⌈Y/32⌉ + 1 units). -/
theorem from_vec {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat) (x : RefineCtx)
    (ω : Regs) (μ μ2 : Memory) (ω2 : Regs) (s' : State) (Y q ptr C I S v5 v6 n2 : Nat) (y h : List UInt8)
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
    (bfr : ∀ a, a < 4294967296 → 4278058264 ≤ a → (a < 4278058304 ∨ 4278058304 + 16 ≤ a) →
      (a < 4278058320 ∨ 4278058320 + 24 ≤ a) → μ2.read a = μ.read a) :
    ∃ ω' μ', FreeStepsH p (refineContractK cap env) 35130 ω μ x 4680 ω' μ' x (n2 + 505) ∧
      ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat 4278058376 ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN 4278058544 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058552 8 = Num.encodeLE 8 q ∧
      μ'.readN 4278058560 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058568 32 = h ∧
      μ'.readN 4278058600 4 = Num.encodeLE 4 I ∧ μ'.readN 4278058604 4 = Num.encodeLE 4 S ∧
      μ'.readN 4278058608 2 = Num.encodeLE 2 C ∧
      μ'.readN q Y = y ∧ HeapCtx env 1044430 4278050816 4278059008 μ' s' ∧
      (⟨q - 32, (Y + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧ 32 ≤ q ∧
      (∀ a, q ≤ a → a < q + Y → InData ⟨q - 32, (Y + 31) / 32 + 1, true⟩ a) ∧
      TablesKept μ μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true) := by
  obtain ⟨hq0, -, hqT⟩ := Decode.VecU8.chunk_in H2.wf hnew rfl
  simp only at hq0 hqT
  have hb0 := H2.hb0
  have hbT := H2.hbT
  have hSb := H.hSb
  have hpay : ∀ a, 4278059008 ≤ a → a < 4294967296 → μ2.read a = μ.read a := fun a h1 h2 =>
    bfr a h2 (by omega) (Or.inr (by omega)) (Or.inr (by omega))
  have kf : ∀ a, 4278058264 ≤ a → a < 4278058304 ∨ 4278058344 ≤ a → a < 4278059008 → μ2.read a = μ.read a :=
    fun a h1 h2 h3 => bfr a (by omega) h1 (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, d0, d1, d5, d6, dc, dq, dl, dh, dI, dS, dC, fr3, rd3, wr3⟩ :=
    tail_core (P := P) (R := refineContractK cap env) x ω2 μ2 4278058264 4278058544 Y q (ptr + Y) I S C v5 v6
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
  refine ⟨ω3, μ3, runAll, d0, d1, d5, d6, dc, dq, dl, ?_, dI, dS, dC, ?_, H3, hnew, by omega,
    fun a h1 h2 => ⟨by simp only; omega, by simp only; omega⟩, tables_kept H runAll, fun a h1 h2 => H3.st a h1 h2⟩
  · rw [dh, ← hh]
    exact Memory.readN_congr (fun j hj => hpay _ (by omega) (by omega))
  · rw [← hy, ← bdat]
    exact Memory.readN_congr (fun j hj => fr3 _ (by omega))

/-- **Refine's argument parse from 35130 to 4680, 1 ≤ Y ≤ 16384** (see the module doc). At 35130:
    sp = 4278058264 (ω₁), O = 4278058544 (ω₅), the decoder's error flag ω₇ = 0, Y in ω₈; the reader at
    sp + 40 = {ptr, Y + 32}, c, i, s at sp + 32, sp + 24, sp + 16, the saved ω₆, ω₅ and the return
    address 152 at sp + 88, sp + 96, sp + 104; the payload y and the hash h at ptr, at or above the
    stack's top S1 = 4278059008, readable; the allocator's context for its start-up state `sStart`.
    Either the run reaches 4680 with the result struct {cap Y, q, len Y, h, i, s, c} at O, y at q,
    the context for s' in which q is the data of the allocated chunk at the base 206880 (q = 206912),
    ω₁ = M = sp + 112, ω₀ = 152, ω₅, ω₆ restored, the read-only tables and the stack's access kept;
    or it reaches a failed `alloc` (`ExhaustsX`). -/
theorem args_tail {p : ByteArray} {P : Program} [HasCode p P] (env : RefineHost.Env) (cap : Nat)
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
    (∃ q s' ω' μ', FreeStepsH p (refineContractK cap env) 35130 ω μ x 4680 ω' μ' x (2 * Y + 1712) ∧
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
      TablesKept μ μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true)) ∨
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
    obtain ⟨ω', μ', run, o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hmem, -, hin, tk, wst⟩ :=
      from_vec (P := P) env cap x ω μ μ2 ω2 s' Y q ptr C I S v5 v6 _ y h H2 ⟨hY.1, by omega⟩ hptr hC hI hS hv5 hv6
        hra hy hh s16 s24 s32 s88 s96 s104 (run1.trans run2) H b1 (b5.trans (by rfl)) bO bO8 bO16 bdat bR0 bR8
        hnew bfr
    refine Or.inl ⟨q, s', ω', μ', run.mono (by omega), o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hq, hbase,
      ⟨_, hmem, rfl, by simp only; omega, by simp only; omega, hin⟩, tk, wst⟩
  · exact Or.inr ⟨_, PassLoop.ExhaustsX.ofFmt ⟨ω2, μ2, x, 40611, run1.trans run2, e7, Or.inl rfl⟩⟩

/-- **Refine's argument parse from 35130 to 4680, 16384 < Y < 2^30 − 64**: as `args_tail`, through
    `vec_u8_args_big`, except that the payload's chunk is only an allocated chunk of ⌈Y/32⌉ + 1 units
    whose data starts at q (`vec_u8_args_big` exposes no equation of the model's `alloc`/`realloc`
    calls, so its address is not tied to the heap's base), and the failure is a failed `alloc` or
    `realloc` (`ExhaustsX`). -/
theorem args_tail_big {p : ByteArray} {P : Program} [HasCode p P] [CodeX.HasCodeX p P] (env : RefineHost.Env)
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
      ω'[0] = UInt64.ofNat 152 ∧ ω'[1] = UInt64.ofNat 4278058376 ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧
      μ'.readN 4278058544 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058552 8 = Num.encodeLE 8 q ∧
      μ'.readN 4278058560 8 = Num.encodeLE 8 Y ∧ μ'.readN 4278058568 32 = h ∧
      μ'.readN 4278058600 4 = Num.encodeLE 4 I ∧ μ'.readN 4278058604 4 = Num.encodeLE 4 S ∧
      μ'.readN 4278058608 2 = Num.encodeLE 2 C ∧
      μ'.readN q Y = y ∧ HeapCtx env 1044430 4278050816 4278059008 μ' s' ∧
      (∃ cp ∈ chunks s', cp.used = true ∧ cp.addr + 32 = q ∧ ∀ a, q ≤ a → a < q + Y → InData cp a) ∧
      TablesKept μ μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true)) ∨
    ∃ N, PassLoop.ExhaustsX env cap 1044430 p 35130 ω μ x N := by
  obtain ⟨ω1, run1, a0, a1, a7, a8, a9, -, -, -, a5, a6, -, -, -⟩ :=
    glue_pre_vec (P := P) (R := refineContractK cap env) x ω μ 4278058264 Y (by omega) (by omega) h1 h7 h8
  have hv6' : (ω[6]).toNat < 18446744073709551616 := UInt64.toNat_lt_size _
  rcases Decode.VecU8.vec_u8_args_big (P := P) env cap hcap1 hcap x ω1 μ sStart 4278058264 4278058320
      4278058304 ptr (Y + 32) Y 1642 35155 4278058544 (ω[6]).toNat 1044430 4278050816 4278059008 H
      ⟨hptr.1, by omega⟩ (fun a h1 h2 => hra a h1 (by omega)) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      a0 a1 (a5.trans h5) (by rw [a6, UInt64.ofNat_toNat]) a7 a8 a9 (by decide)
      (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_820]) bs_35155 (by omega) hv6' hY (by omega)
      (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Or.inr (by omega)) s40 s48 with
    ⟨q, s', ω2, μ2, run2, -, b1, b5, -, bO, bO8, bO16, bdat, bR0, bR8, H2, -, hnew, -, -, -, bfr, -, -, -⟩ | hex
  · obtain ⟨ω', μ', run, o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hmem, hq32, hin, tk, wst⟩ :=
      from_vec (P := P) env cap x ω μ μ2 ω2 s' Y q ptr C I S v5 v6 _ y h H2 ⟨by omega, by omega⟩ hptr hC hI hS hv5
        hv6 hra hy hh s16 s24 s32 s88 s96 s104 (run1.trans run2) H b1 (b5.trans (by rfl))
        bO bO8 bO16 bdat bR0 bR8 hnew bfr
    exact Or.inl ⟨q, s', ω', μ', _, run, o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H',
      ⟨_, hmem, rfl, by simp only; omega, hin⟩, tk, wst⟩
  · exact Or.inr ⟨_, PassLoop.ExhaustsX.pre run1 (PassLoop.ExhaustsX.of hex)⟩

end Services.Bootstrap.Refine.ArgsTail
