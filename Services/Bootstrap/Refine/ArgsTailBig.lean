import Services.Bootstrap.Refine.ArgsTail
import Services.Bootstrap.Decode.VecU8ArgsBigOne

/-!
# Refine's argument parse from 35130 to 4680, Y > 16384, the payload at the heap's base

`args_tail_big_one`: `args_tail_big` through `vec_u8_args_big_one`, whose success case ties the
payload's buffer to the allocator's base (the first `alloc` from `sStart` takes the chunk at 206880,
and each `realloc` grows it in place). Its success conclusion has `args_tail`'s form: q = 206912,
s'.base = 206880 and the payload's chunk at s'.base.
-/

namespace Services.Bootstrap.Refine.ArgsTail

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Refine.ArgsGlue
  Services.Bootstrap.Alloc.AfterStart

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **Refine's argument parse from 35130 to 4680, 16384 < Y < 2^30 − 64, the payload at the heap's
    base**: `args_tail_big` through `vec_u8_args_big_one`, with `args_tail`'s success form: the
    payload's chunk is the allocated chunk at the base 206880 (q = 206912, s'.base = 206880,
    cp.addr = s'.base), its data holding y. The step count is existential and the failure is a
    failed `alloc` or `realloc` (`ExhaustsX`), as in `args_tail_big`. -/
theorem args_tail_big_one {p : ByteArray} {P : Program} [HasCode p P] [CodeX.HasCodeX p P] (env : RefineHost.Env)
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
      q = 206912 ∧ s'.base = 206880 ∧
      (∃ cp ∈ chunks s', cp.used = true ∧ cp.addr = s'.base ∧ cp.addr + 32 = q ∧
        ∀ a, q ≤ a → a < q + Y → InData cp a) ∧
      TablesKept μ μ' ∧ (∀ a, 4278050816 ≤ a → a < 4278059008 → μ'.writable a = true)) ∨
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
    ⟨q, s', ω2, μ2, run2, -, b1, b5, -, bO, bO8, bO16, bdat, bR0, bR8, H2, -, hnew, -, -, -, bfr, -, -, -, hq, hbase, -⟩ | hex
  · obtain ⟨ω', μ', run, o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hmem, hq32, hin, tk, wst⟩ :=
      from_vec (P := P) env cap x ω μ μ2 ω2 s' Y q ptr C I S v5 v6 _ y h H2 ⟨by omega, by omega⟩ hptr hC hI hS hv5
        hv6 hra hy hh s16 s24 s32 s88 s96 s104 (run1.trans run2) H b1 (b5.trans (by rfl))
        bO bO8 bO16 bdat bR0 bR8 hnew bfr
    exact Or.inl ⟨q, s', ω', μ', _, run, o0, o1, o5, o6, oc, oq, ol, oh, oI, oS, oC, odat, H', hq, hbase,
      ⟨_, hmem, rfl, by simp only; omega, by simp only; omega, hin⟩, tk, wst⟩
  · exact Or.inr ⟨_, PassLoop.ExhaustsX.pre run1 (PassLoop.ExhaustsX.of hex)⟩

end Services.Bootstrap.Refine.ArgsTail
