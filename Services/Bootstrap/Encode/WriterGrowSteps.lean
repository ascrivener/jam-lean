import Services.Bootstrap.Encode.Writer
import Services.Bootstrap.CodeAAll
import Services.Bootstrap.CodeX

/-!
# `Vec<u8>::extend_from_slice` (58508), the grow path: the straight-line pieces

When `cap − len < n`, `extend_from_slice` (58508) does not copy at once: it calls
`RawVec<u8>::reserve` (58251), which asks `finish_grow` (58327) for the capacity

  nc = max(max(len + n, 8), 2 · cap)

and `finish_grow` calls picoalloc's `realloc` wrapper (40701) for the old buffer (cap ≠ 0). The pieces
between the calls, each its own theorem to keep elaboration small:
- `g1`: 58508 … 58532, the room test failing, then 58578 … 58586: src parked at the frame base S = sp − 32
  and `reserve` called (return address 2554, entry 1276 = 58592);
- `g2`: 58251 … 58292 (`reserve`'s 48-octet frame at S − 48, nc computed), then 58327 … 58357
  (`finish_grow`'s 24-octet frame at S − 72, the `realloc` call, return address 2546, entry 1272 = 58363);
- `rret`: the `realloc` wrapper's return (40821) to 58363;
- `g3`: 58363 … 58432, `realloc` returned r ≠ 0: `finish_grow` writes `Ok`, r and nc to its result slot
  S − 48 and returns to `reserve` (2544, entry 1271 = 58297);
- `g4`: 58297 … 58323, `reserve` finds `Ok`, stores nc and r into the vector and returns (2554);
- `g5`: 58592 … 58597, then 58538 … 58548: src and len reloaded, `memcpy` (68729) called for the n octets
  at src to r + len, return address 2552 (as on the path without growth).

When `realloc` returns null, `finish_grow` returns `Err` and `reserve` traps (58326,
`handle_alloc_error`); the run is not followed past 58363.
-/

namespace Services.Bootstrap.Encode.WriterGrow

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The capacity `reserve` asks for: max(max(len + n, 8), 2 · cap). -/
def newCap (cap len n : Nat) : Nat := max (max (len + n) 8) (2 * cap)

theorem newCap_ge (cap len n : Nat) : len + n ≤ newCap cap len n ∧ 8 ≤ newCap cap len n ∧
    2 * cap ≤ newCap cap len n := by
  unfold newCap; omega

theorem newCap_le (cap len n B : Nat) (h1 : len + n ≤ B) (h2 : 8 ≤ B) (h3 : 2 * cap ≤ B) :
    newCap cap len n ≤ B := by
  unfold newCap; omega

/-- 58508 … 58532, the room test failing (cap − len < n), then 58578 … 58586: the function's frame
    at S = sp − 32 (ω₀, ω₅, ω₆ at S + 24, S + 16, S + 8), src parked at S, and `reserve` (58251)
    called with the vector v (ω₇), len (ω₈) and n (ω₉), return address 2554. -/
theorem g1 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v src n cap len r0 r5 r6 : Nat) (hsp : 65536 + 32 ≤ sp ∧ sp < 4294967296)
    (h0 : ω[0] = UInt64.ofNat r0) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hv : v + 24 ≤ 4294967296)
    (hr0 : r0 < 18446744073709551616) (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hsrc : src < 18446744073709551616) (hn : n < 18446744073709551616)
    (hlc : len ≤ cap) (hgrow : cap < len + n) (hcap : cap < 18446744073709551616)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hvs : v + 24 ≤ sp - 32 ∨ sp ≤ v)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hw : ∀ a, sp - 32 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x 58251 ω' μ' x 16 ∧
      ω'[0] = UInt64.ofNat 2554 ∧ ω'[1] = UInt64.ofNat (sp - 32) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat v ∧ ω'[7] = UInt64.ofNat v ∧ ω'[8] = UInt64.ofNat len ∧
      ω'[9] = UInt64.ofNat n ∧
      μ'.readN (sp - 32) 8 = Num.encodeLE 8 src ∧ μ'.readN (sp - 8) 8 = Num.encodeLE 8 r0 ∧
      μ'.readN (sp - 16) 8 = Num.encodeLE 8 r5 ∧ μ'.readN (sp - 24) 8 = Num.encodeLE 8 r6 ∧
      (∀ a, a < 4294967296 → (a < sp - 32 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 hcap vc
  have rl := rd8 (by omega) vl
  have hr : ∀ a, sp - 32 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hsp, hw, hr, hrv, rc, rl, hv, hvs, rdN_writeN_disjoint, ↓rdN_fold,
      ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show sp - 32 + 24 = sp - 8 by omega, show sp - 32 + 16 = sp - 16 by omega,
      show sp - 32 + 8 = sp - 24 by omega]
    post_simp
    all_goals try assumption

/-- 58251 … 58292, then 58327 … 58357: `reserve` opens its frame at S − 48 (ω₀ = 2554, ω₅ = n, ω₆ = v at
    S − 8, S − 16, S − 24), reads cap and ptr from the vector, computes nc = `newCap cap len n` and calls
    `finish_grow` (58327, result slot S − 48, return address 2544), which opens its frame at S − 72
    (2544, v, nc at S − 56, S − 64, S − 72) and, the capacity being nonzero, calls the `realloc` wrapper
    (40701) for ptr, alignment 1 and size nc, return address 2546. -/
theorem g2 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (S v n cap ptr len : Nat) (hS : 65536 + 72 ≤ S ∧ S < 4294967296)
    (h0 : ω[0] = UInt64.ofNat 2554) (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n)
    (h6 : ω[6] = UInt64.ofNat v) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat len)
    (h9 : ω[9] = UInt64.ofNat n) (hv : v + 24 ≤ 4294967296) (hvs : v + 16 ≤ S - 72 ∨ S ≤ v)
    (hcap : 0 < cap ∧ cap < 4611686018427387904) (hln : len + n < 4611686018427387904)
    (hptr : ptr < 18446744073709551616)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr)
    (hrv : ∀ a, v ≤ a → a < v + 16 → μ.readable a = true)
    (hw : ∀ a, S - 72 ≤ a → a < S → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58251 ω μ x 40701 ω' μ' x 40 ∧
      ω'[0] = UInt64.ofNat 2546 ∧ ω'[1] = UInt64.ofNat (S - 72) ∧ ω'[5] = UInt64.ofNat (S - 48) ∧
      ω'[6] = UInt64.ofNat (newCap cap len n) ∧ ω'[7] = UInt64.ofNat ptr ∧ ω'[9] = UInt64.ofNat 1 ∧
      ω'[10] = UInt64.ofNat (newCap cap len n) ∧
      μ'.readN (S - 8) 8 = Num.encodeLE 8 2554 ∧ μ'.readN (S - 16) 8 = Num.encodeLE 8 n ∧
      μ'.readN (S - 24) 8 = Num.encodeLE 8 v ∧ μ'.readN (S - 56) 8 = Num.encodeLE 8 2544 ∧
      μ'.readN (S - 64) 8 = Num.encodeLE 8 v ∧ μ'.readN (S - 72) 8 = Num.encodeLE 8 (newCap cap len n) ∧
      (∀ a, a < 4294967296 → (a < S - 72 ∨ S ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rc := rd8 (by omega) vc
  have rp := rd8 hptr vp
  have hr : ∀ a, S - 72 ≤ a → a < S → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hcap0 : ¬ cap = 0 := by omega
  have hm1 : (if n + len ≤ 8 then 8 else n + len) % 18446744073709551616 = (if n + len ≤ 8 then 8 else n + len) :=
    Nat.mod_eq_of_lt (by split <;> omega)
  have hm2 : (if (if n + len ≤ 8 then 8 else n + len) ≤ cap * 2 then cap * 2 else
      (if n + len ≤ 8 then 8 else n + len)) % 18446744073709551616 =
      (if (if n + len ≤ 8 then 8 else n + len) ≤ cap * 2 then cap * 2 else (if n + len ≤ 8 then 8 else n + len)) :=
    Nat.mod_eq_of_lt (by split <;> split <;> omega)
  have hm3 : (if (if n + len ≤ 8 then 8 else n + len) ≤ cap * 2 then cap * 2 else
      (if n + len ≤ 8 then 8 else n + len)) < 9223372036854775808 := by split <;> split <;> omega
  have hm4 : newCap cap len n = (if (if n + len ≤ 8 then 8 else n + len) ≤ cap * 2 then cap * 2 else
      (if n + len ≤ 8 then 8 else n + len)) := by unfold newCap; split <;> split <;> omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h0, h1, h5, h6, h7, h8, h9, hS, hw, hr, hrv, rc, rp, hv, hvs, hcap, hcap0, hln, hm1, hm2, hm3,
      rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try rw [hm4]
    all_goals try simp only [show S - 48 + 40 = S - 8 by omega, show S - 48 + 32 = S - 16 by omega,
      show S - 48 + 24 = S - 24 by omega, show S - 72 + 16 = S - 56 by omega, show S - 72 + 8 = S - 64 by omega]
    post_simp
    all_goals try assumption

/-- 40821: the `realloc` wrapper's return to `finish_grow` (2546, entry 1272 = 58363). -/
theorem rret {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (h0 : ω[0] = UInt64.ofNat 2546) : FreeStepsH p R 40821 ω μ x 58363 ω μ x 1 := by
  rw [show ω = regsNF ω [] from rfl]
  pvm_go [h0]

/-- 58363 … 58432: `realloc` returned r ≠ 0. `finish_grow` writes `Ok` (0), r and nc to its result slot
    T + 24 (ω₅), restores ω₀, ω₅, ω₆ from its frame at T and returns to `reserve` (2544). -/
theorem g3 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (T r nc v : Nat) (hT : 65536 ≤ T ∧ T + 72 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat T) (h5 : ω[5] = UInt64.ofNat (T + 24)) (h6 : ω[6] = UInt64.ofNat nc)
    (h7 : ω[7] = UInt64.ofNat r) (hr : 0 < r ∧ r < 18446744073709551616) (hnc : nc < 18446744073709551616)
    (hv : v < 18446744073709551616)
    (s16 : μ.readN (T + 16) 8 = Num.encodeLE 8 2544) (s8 : μ.readN (T + 8) 8 = Num.encodeLE 8 v)
    (s0 : μ.readN T 8 = Num.encodeLE 8 nc)
    (hw : ∀ a, T ≤ a → a < T + 48 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58363 ω μ x 58297 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 2544 ∧ ω'[1] = UInt64.ofNat (T + 24) ∧ ω'[5] = UInt64.ofNat v ∧
      ω'[6] = UInt64.ofNat nc ∧
      μ'.readN (T + 24) 8 = Num.encodeLE 8 0 ∧ μ'.readN (T + 32) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (a < T + 24 ∨ T + 48 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r16 := rd8 (by omega) s16
  have r8 := rd8 hv s8
  have r0 := rd8 hnc s0
  have hrd : ∀ a, T ≤ a → a < T + 48 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hw a h1 h2)
  have hr0 : ¬ r = 0 := by omega
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, h7, hT, hw, hrd, hr, hr0, r16, r8, r0, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp only [show T + 24 + 8 = T + 32 by omega, show T + 24 + 16 = T + 40 by omega]
    post_simp
    all_goals try assumption

/-- 58297 … 58323: `reserve` finds `Ok` (0) at its result slot U, stores nc (ω₆) and the block r (U + 8)
    into the vector v (ω₅), restores ω₀, ω₅, ω₆ from U + 40, U + 32, U + 24, closes its frame and returns. -/
theorem g4 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] [HasCodeX p P] (x : X) (ω : Regs)
    (μ : Memory) (U v r nc n : Nat) (hU : 65536 ≤ U ∧ U + 48 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat U) (h5 : ω[5] = UInt64.ofNat v) (h6 : ω[6] = UInt64.ofNat nc)
    (hv : v + 16 ≤ 4294967296) (hvU : v + 16 ≤ U ∨ U + 48 ≤ v)
    (hr : r < 18446744073709551616) (hnc : nc < 18446744073709551616) (hn : n < 18446744073709551616)
    (hv' : v < 18446744073709551616)
    (s0 : μ.readN U 8 = Num.encodeLE 8 0) (s8 : μ.readN (U + 8) 8 = Num.encodeLE 8 r)
    (s40 : μ.readN (U + 40) 8 = Num.encodeLE 8 2554) (s32 : μ.readN (U + 32) 8 = Num.encodeLE 8 n)
    (s24 : μ.readN (U + 24) 8 = Num.encodeLE 8 v)
    (hrU : ∀ a, U ≤ a → a < U + 48 → μ.readable a = true)
    (hwv : ∀ a, v ≤ a → a < v + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58297 ω μ x 58592 ω' μ' x 14 ∧
      ω'[0] = UInt64.ofNat 2554 ∧ ω'[1] = UInt64.ofNat (U + 48) ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat v ∧
      μ'.readN v 8 = Num.encodeLE 8 nc ∧ μ'.readN (v + 8) 8 = Num.encodeLE 8 r ∧
      (∀ a, a < 4294967296 → (a < v ∨ v + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have r0 := rd8 (by decide) s0
  have r8 := rd8 hr s8
  have r40 := rd8 (by decide) s40
  have r32 := rd8 hn s32
  have r24 := rd8 hv' s24
  have hrv : ∀ a, v ≤ a → a < v + 16 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwv a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hU, hv, hvU, hrU, hwv, hrv, r0, r8, r40, r32, r24, rdN_writeN_disjoint, ↓rdN_fold,
      ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption

/-- 58592 … 58597, then 58538 … 58548: back from `reserve`, the function reloads src from its frame at S
    and len from v + 16, parks len at S, and calls `memcpy` (68729) of n octets from src to r + len (r the
    new block, from v + 8), return address 2552. -/
theorem g5 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (S v src len r n : Nat) (hS : 65536 ≤ S ∧ S + 8 ≤ 4294967296)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat v)
    (hv : v + 24 ≤ 4294967296) (hvS : v + 24 ≤ S ∨ S + 8 ≤ v)
    (hsrc : src < 18446744073709551616) (hl : len < 18446744073709551616) (hr : r < 18446744073709551616)
    (hrl : r + len < 18446744073709551616) (hn : n < 18446744073709551616)
    (sS : μ.readN S 8 = Num.encodeLE 8 src) (vp : μ.readN (v + 8) 8 = Num.encodeLE 8 r)
    (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hwS : ∀ a, S ≤ a → a < S + 8 → μ.writable a = true)
    (hrv : ∀ a, v + 8 ≤ a → a < v + 24 → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 58592 ω μ x 68729 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 2552 ∧ ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧
      ω'[6] = UInt64.ofNat v ∧ ω'[7] = UInt64.ofNat (r + len) ∧ ω'[8] = UInt64.ofNat src ∧
      ω'[9] = UInt64.ofNat n ∧ μ'.readN S 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have rs := rd8 hsrc sS
  have rp := rd8 hr vp
  have rl := rd8 hl vl
  have hrS : ∀ a, S ≤ a → a < S + 8 → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwS a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · pvm_go [h1, h5, h6, hS, hv, hvS, hwS, hrS, hrv, rs, rp, rl, hrl, rdN_writeN_disjoint, ↓rdN_fold,
      ↓loadI_fold]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha0 ha1 => ?_, fun a => ?_, fun a => ?_⟩
    post_simp
    all_goals try assumption
    all_goals try rw [Nat.mod_eq_of_lt hn]

end Services.Bootstrap.Encode.WriterGrow
