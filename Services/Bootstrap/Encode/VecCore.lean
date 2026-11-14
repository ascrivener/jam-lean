import Services.Bootstrap.Encode.VecSegs
import Services.Bootstrap.Encode.VecSegs2

/-!
# The arms holding a `Vec`: the state between calls, the length prefix and the heap octets

Inside `Instruction::encode_to` (frame at F − 56) the arms holding a `Vec` call the length-prefix
function (30977) and `Vec<u8>::extend_from_slice` (58508) from their frame; the former calls the latter
from its own, so the stack used reaches F − 192. `StD D pre` is `Fixed.St pre` with the stack
[F − D, F) in its frame clause, and also the writer v saved at F − 40 (by the dispatch). Its steps:

* `ext_stepD`: one call of `extend_from_slice` for n octets at `src`, under `Writer.extend_ok`'s
  conditions on `src` (`hs`, `hdj`, `hfs`); `ext_zeroD`: the call for no octets, with none
  (`extend_zero`, from `Writer.wz1` and `w3`: the source is not read);
* `prefixD`: one call of the length prefix for n < 2^32 at the scratch word F − 32, appending ℰ(n)
  (GP v0.8.0 Appendix C, the general natural encoding; `prefix_any`, from `Prefix.prefix_zero` and
  `PrefixBig.prefix_pos`);
* `heapD`: the reusable piece for a `Vec<u8>` / `&[u8]` field with its n octets in the heap at q: the
  `extend_from_slice` call for them, its conditions on q derived from the heap octets `Src` (taken as
  the padded stretch [q − 24, q + n + 24) when n > 0, see `HeapPad`) being apart from what one
  `encode_to` call writes; for n = 0 it reads nothing.

`startV` is the dispatch into `StD []` for the variants 18 and 19 (ω₅ = 2^64 − 1), and `closeD` the
function's end from any of its tails, giving `EncOkMD`'s conclusion.
-/

namespace Services.Bootstrap.Encode.Enc

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.EncMD

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **`Vec<u8>::extend_from_slice` for no octets** (58508, n = 0): as `extend_ok` with n = 0, without
    any condition on the source (it is not read). -/
theorem extend_zero {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (sp v cap len ret t : Nat) (hsp : 65536 + 128 ≤ sp ∧ sp < 4294967296 ∧ sp % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat v)
    (h9 : ω[9] = UInt64.ofNat 0) (hroom : len ≤ cap) (hcap : cap < 18446744073709551616)
    (vc : μ.readN v 8 = Num.encodeLE 8 cap) (vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len)
    (hv : v + 24 ≤ 4294967296) (hvs : v + 24 ≤ sp - 80 ∨ sp ≤ v)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true)
    (hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true)
    (hw : ∀ a, sp - 80 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x t ω' μ' x 20 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (v + 16) 8 = Num.encodeLE 8 len ∧
      (∀ a, a < 4294967296 → (a < sp - 80 ∨ sp ≤ a) → (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have h5' := UInt64.toNat_lt ω[5]
  have h6' := UInt64.toNat_lt ω[6]
  have hr0 : ret < 18446744073709551616 := by omega
  obtain ⟨ω1, μ1, run1, a1, a5, a6, a9, a0', a5', a6', afr, ard, awr⟩ := wz1 (p := p) (P := P) (R := R) x ω μ
    sp v cap len ret ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ h0 h1 h5 h6 h7 h9 hv (by omega) hr0 h5' h6'
    hroom hcap vc vl hrv (fun a h1 h2 => hw a (by omega) h2)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bl, bfr, brd, bwr⟩ := w3 (p := p) (P := P) (R := R) x ω1 μ1
    (sp - 32) v 0 len ret t ω[5].toNat ω[6].toNat ⟨by omega, by omega⟩ a1 a5 a6 a9 hv (by omega) (by omega)
    (by rw [show sp - 32 + 24 = sp - 8 by omega]; exact a0')
    (by rw [show sp - 32 + 16 = sp - 16 by omega]; exact a5')
    (by rw [show sp - 32 + 8 = sp - 24 by omega]; exact a6') h5' h6' hret hjt hbt
    (fun a h1 h2 => by rw [ard]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
    (fun a h1 h2 => by rw [awr]; exact hwv a h1 h2)
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), b0, by rw [b1]; congr 1; omega, by rw [b5, ← h5],
    by rw [b6, ← h6], by simpa using bl, fun a h0' h1' h3' => ?_, fun a => by rw [brd, ard],
    fun a => by rw [bwr, awr]⟩
  rw [bfr a h0' h3', afr a h0' (by omega)]

/-- **The state between calls, with the stack [F − D, F)**: `St` with D for 136, and the writer v
    saved at F − 40. -/
structure StD (D F v ptr len ret r5 r6 : Nat) (μ0 : Memory) (pre : List UInt8) (ω : Regs) (μ : Memory) :
    Prop where
  h1 : ω[1] = UInt64.ofNat (F - 56)
  s0 : μ.readN (F - 8) 8 = Num.encodeLE 8 ret
  s5 : μ.readN (F - 16) 8 = Num.encodeLE 8 r5
  s6 : μ.readN (F - 24) 8 = Num.encodeLE 8 r6
  sv : μ.readN (F - 40) 8 = Num.encodeLE 8 v
  vl : μ.readN (v + 16) 8 = Num.encodeLE 8 (len + pre.length)
  out : μ.readN (ptr + len) pre.length = pre
  keep : ∀ a, a < 4294967296 → (a < F - D ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + pre.length ≤ a) →
    (a < v + 16 ∨ v + 24 ≤ a) → μ.read a = μ0.read a
  rd : ∀ a, μ.readable a = μ0.readable a
  wr : ∀ a, μ.writable a = μ0.writable a

/-- `StD` for a list written differently. -/
theorem StD.cast {D F v ptr len ret r5 r6 : Nat} {μ0 : Memory} {pre pre' : List UInt8} {ω : Regs} {μ : Memory}
    (h : pre = pre') (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) : StD D F v ptr len ret r5 r6 μ0 pre' ω μ :=
  h ▸ st

/-- Writes to the frame's scratch [F − 56, F − 40) and [F − 32, F − 24) (with ω₁ kept) keep `StD`. -/
theorem StD.scratch {D F S v cap ptr len N ret t r5 r6 : Nat} {μ0 : Memory} {pre : List UInt8} {ω ω' : Regs}
    {μ μ' : Memory} {P : Program} (L : LayD P D F S v cap ptr len N ret t μ0) (hD : 136 ≤ D)
    (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ)
    (hpre : pre.length ≤ N) (h1 : ω'[1] = UInt64.ofNat (F - 56))
    (hk : ∀ a, a < 4294967296 → (a < F - 56 ∨ (F - 40 ≤ a ∧ a < F - 32) ∨ F - 24 ≤ a) → μ'.read a = μ.read a)
    (hrd : ∀ a, μ'.readable a = μ.readable a) (hwr : ∀ a, μ'.writable a = μ.writable a) :
    StD D F v ptr len ret r5 r6 μ0 pre ω' μ' := by
  have hF := L.hF; have hF' := L.hF'; have hvF := L.hvF; have hdF := L.hdF; have hv := L.hv
  have hd' := L.hd'
  refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 h3 => ?_, fun a => by rw [hrd, st.rd],
    fun a => by rw [hwr, st.wr]⟩
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.s0
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.s5
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.s6
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.sv
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.vl
  · rw [Memory.readN_congr (fun j hj => hk _ (by omega) (by omega))]; exact st.out
  · rw [hk a h0 (by omega)]; exact st.keep a h0 h1 h2 h3

/-- The value's octets are as at entry. -/
theorem StD.slot {D F S v cap ptr len N ret t r5 r6 : Nat} {μ0 : Memory} {pre : List UInt8} {ω : Regs}
    {μ : Memory} {P : Program} (L : LayD P D F S v cap ptr len N ret t μ0)
    (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ)
    (hpre : pre.length ≤ N) (i m : Nat) (him : i + m ≤ 232) : μ.readN (S + i) m = μ0.readN (S + i) m :=
  Memory.readN_congr (fun j hj => st.keep _ (by have := L.hS'; omega) (by have := L.hSF; omega)
    (by have := L.hdS; omega) (by have := L.hvS; omega))

/-- **One call of `Vec<u8>::extend_from_slice`** (58508, returning to e) for the n octets at `src`,
    under `Writer.extend_ok`'s conditions on `src`: `StD pre` becomes `StD (pre ++ μ.readN src n)`; the
    frame [F − 56, F) and ω₅, ω₆ are kept. -/
theorem ext_stepD {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (src n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hn : pre.length + n ≤ N)
    (hs : 65536 ≤ src ∧ src + n + 16 < 4294967296)
    (hdj : ptr + len + pre.length + n + 24 ≤ src ∨ src + n + 24 ≤ ptr + len + pre.length)
    (hfs : F - 56 ≤ src ∨ src + n + 16 ≤ F - 136)
    (hrs : ∀ a, src ≤ a → a < src + n → μ.readable a = true) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x e ω' μ' x (7 * n + 360) ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ μ.readN src n) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'; have hF8 := L.hF8; have hS := L.hS; have hS' := L.hS'
  have hSF := L.hSF; have hroom := L.hroom; have hv := L.hv; have hvF := L.hvF; have hvS := L.hvS
  have hd := L.hd; have hd' := L.hd'; have hdF := L.hdF; have hdS := L.hdS; have hdv := L.hdv
  have kv : ∀ a, v ≤ a → a < v + 16 → μ.read a = μ0.read a := fun a h1 h2 =>
    st.keep a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω', μ', run, c0, c1, c5, c6, cd, cl, cfr, crd, cwr⟩ := extend_ok (p := p) (P := P) (R := R) x ω μ
    (F - 56) v src n cap ptr (len + pre.length) r e ⟨by omega, by omega, by omega⟩ h0 st.h1 h7 h8 h9
    (by omega) L.hcap
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vc)
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vp)
    st.vl hv (by omega) ⟨by omega, by omega⟩ hs (by omega) (by omega) (by omega) (by omega) hr hje hbe
    (fun a h1 h2 => by rw [st.rd]; exact L.hrv a h1 h2)
    (fun a h1 h2 => by rw [st.wr]; exact L.hwv a h1 h2) hrs
    (fun a h1 h2 => by rw [st.wr]; exact L.hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have kF : ∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a := fun a h1 h2 =>
    cfr a (by omega) (by omega) (by omega) (by omega)
  have hlen : (μ.readN src n).length = n := by simp [Memory.readN]
  refine ⟨ω', μ', run, ⟨by rw [c1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => by rw [crd, st.rd],
    fun a => by rw [cwr, st.wr]⟩, c5, c6, kF⟩
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s0
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s5
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s6
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.sv
  · rw [List.length_append, hlen, ← Nat.add_assoc]; exact cl
  · rw [List.length_append, hlen, readN_add', show ptr + len + pre.length = ptr + (len + pre.length) by omega, cd,
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)), st.out]
  · intro a h0 h1 h2 h3
    rw [List.length_append, hlen] at h2
    rw [cfr a h0 (by omega) (by omega) h3, st.keep a h0 h1 (by omega) h3]

/-- **One call of `Vec<u8>::extend_from_slice` for no octets** (58508, returning to e): `StD pre` is
    kept, whatever ω₈ holds. -/
theorem ext_zeroD {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8} (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v)
    (h9 : ω[9] = UInt64.ofNat 0) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hn : pre.length ≤ N) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x e ω' μ' x 20 ∧
      StD D F v ptr len ret r5 r6 μ0 pre ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'; have hF8 := L.hF8
  have hroom := L.hroom; have hv := L.hv; have hvF := L.hvF
  have hd := L.hd; have hd' := L.hd'; have hdF := L.hdF; have hdv := L.hdv
  have kv : ∀ a, v ≤ a → a < v + 16 → μ.read a = μ0.read a := fun a h1 h2 =>
    st.keep a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω', μ', run, c0, c1, c5, c6, cl, cfr, crd, cwr⟩ := extend_zero (p := p) (P := P) (R := R) x ω μ
    (F - 56) v cap (len + pre.length) r e ⟨by omega, by omega, by omega⟩ h0 st.h1 h7 h9
    (by omega) L.hcap
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vc)
    st.vl hv (by omega) hr hje hbe
    (fun a h1 h2 => by rw [st.rd]; exact L.hrv a h1 h2)
    (fun a h1 h2 => by rw [st.wr]; exact L.hwv a h1 h2)
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have kF : ∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a := fun a h1 h2 =>
    cfr a (by omega) (by omega) (by omega)
  refine ⟨ω', μ', run, ⟨by rw [c1], ?_, ?_, ?_, ?_, cl, ?_, ?_, fun a => by rw [crd, st.rd],
    fun a => by rw [cwr, st.wr]⟩, c5, c6, kF⟩
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s0
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s5
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s6
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.sv
  · rw [Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega))]; exact st.out
  · intro a h0 h1 h2 h3
    rw [cfr a h0 (by omega) h3, st.keep a h0 h1 h2 h3]

/-- **The length prefix of any n < 2^32** (30977): ℰ(n) appended (GP v0.8.0 Appendix C), as
    `PrefixBig.prefix_pos`, with n = 0 (`Prefix.prefix_zero`, ℰ(0) = [0]). -/
theorem prefix_any {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (ω : Regs) (μ : Memory)
    (F c v cap ptr len ret t r5 r6 n : Nat) (hF : 65536 + 256 ≤ F ∧ F < 4294967296 ∧ F % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h5 : ω[5] = UInt64.ofNat r5)
    (h6 : ω[6] = UInt64.ofNat r6) (h7 : ω[7] = UInt64.ofNat c) (h8 : ω[8] = UInt64.ofNat v)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hc : c + 4 ≤ 4294967296) (hcF : c + 4 ≤ F - 136 ∨ F ≤ c) (hn : rdN μ c 4 = n)
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
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x t ω' μ' x (900 + 1100 * min (n / 128) 1) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN (ptr + len) (Blob.encodeNat n).length = Blob.encodeNat n ∧
      μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + (Blob.encodeNat n).length) ∧
      (∀ a, a < 4294967296 → (a < F - 136 ∨ F ≤ a) →
        (a < ptr + len ∨ ptr + len + (Blob.encodeNat n).length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · rw [show Blob.encodeNat 0 = [UInt8.ofNat 0] from rfl] at *
    simp only [List.length_cons, List.length_nil, Nat.zero_add] at *
    obtain ⟨ω', μ', run, rest⟩ := Prefix.prefix_zero (p := p) (P := P) (R := R) x ω μ F c v cap ptr len ret t
      r5 r6 hF h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn hrc vc vp vl hroom hcap hv hvF hd hdF hdv hret hjt hbt
      hrv hwv hwd hwF
    exact ⟨ω', μ', run.mono (by omega), rest⟩
  · rcases Nat.lt_or_ge n 128 with hs | hs
    · rw [PrefixBig.encodeNat_small n ⟨hn1, hs⟩] at *
      simp only [List.length_cons, List.length_nil, Nat.zero_add] at *
      obtain ⟨ω', μ', run, rest⟩ := Prefix.prefix_small (p := p) (P := P) (R := R) x ω μ F c v cap ptr len ret t
        r5 r6 n hF h0 h1 h5 h6 h7 h8 hr5 hr6 hc hcF hn ⟨hn1, hs⟩ hrc vc vp vl hroom hcap hv hvF hd hdF hdv hret
        hjt hbt hrv hwv hwd hwF
      exact ⟨ω', μ', run.mono (by omega), rest⟩
    · obtain ⟨ω', μ', run, rest⟩ := PrefixBig.prefix_big x ω μ F c v cap ptr len ret t r5 r6 n hF h0 h1 h5 h6 h7
        h8 hr5 hr6 hc hcF hn hs hrc vc vp vl hroom hcap hv hvF hd hdF hdv hret hjt hbt hrv hwv hwd hwF
      exact ⟨ω', μ', run.mono (by omega), rest⟩

/-- **One call of the length prefix** (30977, returning to e) for the count n < 2^32 in the scratch word
    F − 32: `StD pre` becomes `StD (pre ++ ℰ(n))` (GP v0.8.0 Appendix C); the frame [F − 56, F) and
    ω₅, ω₆ are kept. The callee frames reach F − 192. -/
theorem prefixD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X) (ω : Regs)
    (μ μ0 : Memory) {D F S v cap ptr len N ret t r5 r6 : Nat} {pre : List UInt8}
    (L : LayD P D F S v cap ptr len N ret t μ0)
    (hD : 192 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (n r e : Nat)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat (F - 32)) (h8 : ω[8] = UInt64.ofNat v)
    (hn : rdN μ (F - 32) 4 = n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0)
    (hje : P.jumpTable.getD (r / 2 - 1) 0 = e) (hbe : P.isBlockStart e = true)
    (hN : pre.length + (Blob.encodeNat n).length ≤ N) :
    ∃ ω' μ', FreeStepsH p R 30977 ω μ x e ω' μ' x (900 + 1100 * min (n / 128) 1) ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ Blob.encodeNat n) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'; have hF8 := L.hF8; have hS := L.hS; have hS' := L.hS'
  have hroom := L.hroom; have hv := L.hv; have hvF := L.hvF
  have hd := L.hd; have hd' := L.hd'; have hdF := L.hdF; have hdv := L.hdv
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have kv : ∀ a, v ≤ a → a < v + 16 → μ.read a = μ0.read a := fun a h1 h2 =>
    st.keep a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω', μ', run, c0, c1, c5, c6, cd, cl, cfr, crd, cwr⟩ := prefix_any (p := p) (P := P) (R := R) x ω μ
    (F - 56) (F - 32) v cap ptr (len + pre.length) r e ω[5].toNat ω[6].toNat n ⟨by omega, by omega, by omega⟩
    h0 st.h1 h5 h6 h7 h8 (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) hn
    (fun a h1 h2 => by rw [st.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega)))
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vc)
    (by rw [Memory.readN_congr (fun j hj => kv _ (by omega) (by omega))]; exact L.vp)
    st.vl (by omega) L.hcap hv (by omega) ⟨by omega, by omega⟩ (by omega) (by omega) hr hje hbe
    (fun a h1 h2 => by rw [st.rd]; exact L.hrv a h1 h2)
    (fun a h1 h2 => by rw [st.wr]; exact L.hwv a h1 h2)
    (fun a h1 h2 => by rw [st.wr]; exact L.hwd a (by omega) (by omega))
    (fun a h1 h2 => by rw [st.wr]; exact L.hwF a (by omega) (by omega))
  have kF : ∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a := fun a h1 h2 =>
    cfr a (by omega) (by omega) (by omega) (by omega)
  refine ⟨ω', μ', run, ⟨by rw [c1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => by rw [crd, st.rd],
    fun a => by rw [cwr, st.wr]⟩, by rw [c5, ← h5], by rw [c6, ← h6], kF⟩
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s0
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s5
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.s6
  · rw [Memory.readN_congr (fun j hj => kF _ (by omega) (by omega))]; exact st.sv
  · rw [List.length_append, ← Nat.add_assoc]; exact cl
  · rw [List.length_append, readN_add', show ptr + len + pre.length = ptr + (len + pre.length) by omega, cd,
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega) (by omega) (by omega)), st.out]
  · intro a h0 h1 h2 h3
    rw [List.length_append] at h2
    rw [cfr a h0 (by omega) (by omega) h3, st.keep a h0 h1 (by omega) h3]

/-- A stretch [lo, hi) all of whose addresses avoid [X, Y) (X < Y) lies on one side of it. -/
theorem side {lo hi X Y : Nat} (hXY : X < Y) (hlh : lo < hi)
    (h : ∀ a, lo ≤ a → a < hi → a < X ∨ Y ≤ a) : hi ≤ X ∨ Y ≤ lo := by
  by_cases hl : lo < X
  · left
    by_cases hX : X < hi
    · have := h X (by omega) hX; omega
    · omega
  · right; have := h lo (Nat.le_refl _) hlh; omega

/-- **The heap octets of a `Vec<u8>` field** (the reusable piece): one call of
    `Vec<u8>::extend_from_slice` (58508, returning to e) for the field's n octets at q in the heap, the
    output so far `pre` and the rest `post` of the element's encoding `enc = pre ++ bytes ++ post`. For
    n > 0 its conditions on q come from the padded stretch [q − 24, q + n + 24) being, as `EncOkMD` asks
    of the heap octets, below 2^32, readable and apart from the frame [F − D, F), the element's
    encoding and the writer (`hsrc`), with 65536 ≤ q. The octets are as at entry: `StD pre` becomes
    `StD (pre ++ bytes)`. -/
theorem heapD {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {D F S v cap ptr len ret t r5 r6 : Nat} {pre bytes post : List UInt8}
    (L : LayD P D F S v cap ptr len (pre ++ bytes ++ post).length ret t μ0)
    (hD : 136 ≤ D) (st : StD D F v ptr len ret r5 r6 μ0 pre ω μ) (q n r e : Nat) (hbn : bytes.length = n)
    (hb : μ0.readN q n = bytes)
    (h0 : ω[0] = UInt64.ofNat r) (h7 : ω[7] = UInt64.ofNat v) (h8 : ω[8] = UInt64.ofNat q)
    (h9 : ω[9] = UInt64.ofNat n) (hr : 0 < r ∧ r ≤ 2806 ∧ r % 2 = 0) (hje : P.jumpTable.getD (r / 2 - 1) 0 = e)
    (hbe : P.isBlockStart e = true) (hq : 0 < n → 65536 ≤ q)
    (hsrc : ∀ a, (0 < n ∧ q ≤ a + 24 ∧ a < q + n + 24) → a < 4294967296 ∧ μ0.readable a = true ∧
      (a < F - D ∨ F ≤ a) ∧ (a < ptr + len ∨ ptr + len + (pre ++ bytes ++ post).length ≤ a) ∧
      (a < v ∨ v + 24 ≤ a)) :
    ∃ ω' μ', FreeStepsH p R 58508 ω μ x e ω' μ' x (7 * n + 20 + 340 * min n 1) ∧
      StD D F v ptr len ret r5 r6 μ0 (pre ++ bytes) ω' μ' ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      (∀ a, F - 56 ≤ a → a < F → μ'.read a = μ.read a) := by
  have hF := L.hF; have hF' := L.hF'
  have hlen : (pre ++ bytes ++ post).length = pre.length + n + post.length := by
    rw [List.length_append, List.length_append, hbn]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hb0 : bytes = [] := List.eq_nil_of_length_eq_zero hbn
    subst hb0
    obtain ⟨ω', μ', run, st', c5, c6, kF⟩ := ext_zeroD (p := p) (P := P) (R := R) x ω μ μ0 L hD st r e h0 h7 h9
      hr hje hbe (by omega)
    exact ⟨ω', μ', run.mono (by omega), st'.cast (by simp), c5, c6, kF⟩
  · have hq' := hq hn
    have hs := fun a ha1 ha2 => hsrc a ⟨hn, ha1, ha2⟩
    have hlo : q - 24 < q + n + 24 := by omega
    have s1 := side (X := F - D) (Y := F) (by omega) hlo (fun a h1 h2 => (hs a (by omega) h2).2.2.1)
    have s2 := side (X := ptr + len) (Y := ptr + len + (pre ++ bytes ++ post).length) (by omega) hlo
      (fun a h1 h2 => (hs a (by omega) h2).2.2.2.1)
    have s3 := (hs (q + n + 23) (by omega) (by omega)).1
    have kq : ∀ a, q ≤ a → a < q + n → μ.read a = μ0.read a := fun a h1 h2 => by
      obtain ⟨a0, -, a2, a3, a4⟩ := hs a (by omega) (by omega)
      exact st.keep a a0 a2 (by omega) (by omega)
    obtain ⟨ω', μ', run, st', c5, c6, kF⟩ := ext_stepD (p := p) (P := P) (R := R) x ω μ μ0 L hD st q n r e
      h0 h7 h8 h9 hr hje hbe (by omega) ⟨hq', by omega⟩ (by omega) (by omega)
      (fun a h1 h2 => by rw [st.rd]; exact (hs a (by omega) (by omega)).2.1)
    rw [Memory.readN_congr (fun j hj => kq _ (by omega) (by omega)), hb] at st'
    exact ⟨ω', μ', run.mono (by omega), st', c5, c6, kF⟩

/-- From 30145 to the arm of `LookedUp` (18) or `Imported` (19), in `StD []`, with ω₅ = 2^64 − 1, the
    writer in ω₁₀ and the value in ω₁₁. -/
theorem startV {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {D F S v cap ptr len N ret t' : Nat} (L : LayD P D F S v cap ptr len N ret t' μ) (hD : 136 ≤ D)
    (t : Nat) (ht : t = 18 ∨ t = 19)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat F) (h7 : ω[7] = UInt64.ofNat S)
    (h8 : ω[8] = UInt64.ofNat v) (hD8 : μ.readN S 8 = Num.encodeLE 8 (9223372036854775807 + t))
    (tab : μ.readN 67376 100 = table) (hrt : ∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) :
    ∃ ω1 μ1, FreeStepsH p R 30145 ω μ x (arm t) ω1 μ1 x 24 ∧
      StD D F v ptr len ret ω[5].toNat ω[6].toNat μ [] ω1 μ1 ∧ ω1[5] = UInt64.ofNat 18446744073709551615 ∧
      ω1[10] = UInt64.ofNat v ∧ ω1[11] = UInt64.ofNat S := by
  have hF := L.hF; have hF' := L.hF'; have hS := L.hS; have hS' := L.hS'; have hSF := L.hSF
  have hv := L.hv; have hvF := L.hvF
  have h5 : ω[5] = UInt64.ofNat ω[5].toNat := UInt64.ofNat_toNat.symm
  have h6 : ω[6] = UInt64.ofNat ω[6].toNat := UInt64.ofNat_toNat.symm
  have hret := L.hret
  obtain ⟨ω1, μ1, run1, a1, a5, a10, a11, a0', a5', a6', av, afr, ard, awr⟩ := dispatchV (p := p) (P := P)
    (R := R) x ω μ F S v ret ω[5].toNat ω[6].toNat t ht ⟨by omega, hF'⟩ h0 h1 h5 h6 h7 h8 (by omega)
    (UInt64.toNat_lt _) (UInt64.toNat_lt _) (by omega) (by omega) (by omega) hD8 tab hrt
    (fun a h1 h2 => L.hrS a h1 (by omega)) (fun a h1 h2 => L.hwF a (by omega) h2)
  refine ⟨ω1, μ1, run1, ⟨a1, a0', a5', a6', av, ?_, by simp [Memory.readN],
    fun a h0 h1 _ _ => afr a h0 (by omega), ard, awr⟩, a5, a10, a11⟩
  rw [Memory.readN_congr (fun j hj => afr _ (by omega) (by omega))]; simpa using L.vl

/-- **Closing a variant**: from `StD enc` at one of the function's ends, after a run from 30145,
    `EncOkMD`'s conclusion. -/
theorem closeD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] {x : X} {ω ω5 : Regs}
    {μ μ5 : Memory} {D F S v cap ptr len ret t : Nat} {enc : List UInt8}
    (L : LayD P D F S v cap ptr len enc.length ret t μ) (hD : 56 ≤ D)
    (e k : Nat) (he : e = 20155 ∨ e = 20204 ∨ e = 20329 ∨ e = 20383 ∨ e = 19636 ∨ e = 20118)
    (hk : k + 7 ≤ 2000 * enc.length + 4000)
    (run : FreeStepsH p R 30145 ω μ x e ω5 μ5 x k)
    (st : StD D F v ptr len ret ω[5].toNat ω[6].toNat μ enc ω5 μ5) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x t ω' μ' x (2000 * enc.length + 4000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (ptr + len) enc.length = enc ∧ μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + enc.length) ∧
      (∀ a, a < 4294967296 → (a < F - D ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + enc.length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hF := L.hF; have hF' := L.hF'
  have hr : ∀ a, F - 56 + 32 ≤ a → a < F - 56 + 56 → μ5.readable a = true := fun a h1 h2 => by
    rw [st.rd]; exact Memory.readable_of_writable (L.hwF a (by omega) (by omega))
  have s0 : μ5.readN (F - 56 + 48) 8 = Num.encodeLE 8 ret := by rw [show F - 56 + 48 = F - 8 by omega]; exact st.s0
  have s5 : μ5.readN (F - 56 + 40) 8 = Num.encodeLE 8 ω[5].toNat := by
    rw [show F - 56 + 40 = F - 16 by omega]; exact st.s5
  have s6 : μ5.readN (F - 56 + 32) 8 = Num.encodeLE 8 ω[6].toNat := by
    rw [show F - 56 + 32 = F - 24 by omega]; exact st.s6
  have fin : ∃ ω6, FreeStepsH p R e ω5 μ5 x t ω6 μ5 x 7 ∧ ω6[0] = UInt64.ofNat ret ∧
      ω6[1] = UInt64.ofNat (F - 56 + 56) ∧ ω6[5] = UInt64.ofNat ω[5].toNat ∧ ω6[6] = UInt64.ofNat ω[6].toNat := by
    rcases he with he | he | he | he | he | he
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := R) x ω5 μ5 e (F - 56) ret t _ _ (Or.inl he)
        (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := R) x ω5 μ5 e (F - 56) ret t _ _
        (Or.inr (Or.inl he)) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt
        L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := R) x ω5 μ5 e (F - 56) ret t _ _
        (Or.inr (Or.inr (Or.inl he))) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        L.hret L.hjt L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · obtain ⟨ω6, r6, rest⟩ := tailAt (p := p) (P := P) (R := R) x ω5 μ5 e (F - 56) ret t _ _
        (Or.inr (Or.inr (Or.inr he))) (by omega) st.h1 s0 s5 s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        L.hret L.hjt L.hbt hr
      exact ⟨ω6, r6.mono (by omega), rest⟩
    · exact tailV (p := p) (P := P) (R := R) x ω5 μ5 e (F - 56) ret t _ _ (Or.inl he) (by omega) st.h1 s0 s5
        s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt L.hbt hr
    · exact tailV (p := p) (P := P) (R := R) x ω5 μ5 e (F - 56) ret t _ _ (Or.inr he) (by omega) st.h1 s0 s5
        s6 (UInt64.toNat_lt _) (UInt64.toNat_lt _) L.hret L.hjt L.hbt hr
  obtain ⟨ω6, run6, e0, e1, e5, e6⟩ := fin
  exact ⟨ω6, μ5, (run.trans run6).mono hk, e0, by rw [e1]; congr 1; omega,
    by rw [e5]; exact UInt64.ofNat_toNat, by rw [e6]; exact UInt64.ofNat_toNat, st.out, st.vl, st.keep, st.rd,
    st.wr⟩

end Services.Bootstrap.Encode.Enc
