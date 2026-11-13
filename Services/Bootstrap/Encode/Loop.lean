import Services.Bootstrap.Encode.Top

/-!
# Refine's output encoder: the element loop

`W k` is the encoder's state at 30145, about to encode element k of n (at E + 232 k): the writer at
M + 24 holds `[n] ++ enc 0 ++ … ++ enc (k − 1)` in its buffer, and memory outside the stack around M and
the octets written is as at entry. `step` is one element (`Instruction::encode_to`, by its `EncOk`),
then the step to the next element or, after the last, to the call that appends `work_item_index`.
-/

namespace Services.Bootstrap.Encode.Loop

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.Encode.Writer
  Services.Bootstrap.Encode.Enc Services.Bootstrap.Encode.Top

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The number of octets the first k elements encode to. -/
def off (enc : Nat → List UInt8) (k : Nat) : Nat := ((List.range k).map fun j => (enc j).length).sum

/-- The first k elements' encodings, in order. -/
def out (enc : Nat → List UInt8) (k : Nat) : List UInt8 := ((List.range k).map enc).flatten

theorem off_succ (enc : Nat → List UInt8) (k : Nat) : off enc (k + 1) = off enc k + (enc k).length := by
  simp [off, List.range_succ]

theorem out_succ (enc : Nat → List UInt8) (k : Nat) : out enc (k + 1) = out enc k ++ enc k := by
  simp [out, List.range_succ]

theorem off_le (enc : Nat → List UInt8) (k m : Nat) : off enc k ≤ off enc (k + m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [← Nat.add_assoc, off_succ]; omega

theorem length_out (enc : Nat → List UInt8) (k : Nat) : (out enc k).length = off enc k := by
  induction k with
  | zero => simp [out, off]
  | succ k ih => rw [out_succ, off_succ, List.length_append, ih]

/-- **The encoder's state at 30145, about to encode element k.** -/
structure W (M E n buf cap : Nat) (enc : Nat → List UInt8) (μ0 : Memory) (k : Nat) (ω : Regs) (μ : Memory) :
    Prop where
  h0 : ω[0] = UInt64.ofNat 1418
  h1 : ω[1] = UInt64.ofNat M
  h5 : ω[5] = UInt64.ofNat (E + 232 * k)
  h6 : ω[6] = UInt64.ofNat (232 * (n - k))
  h7 : ω[7] = UInt64.ofNat (E + 232 * k)
  h8 : ω[8] = UInt64.ofNat (M + 24)
  s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 (E + 232 * k + 232)
  vc : μ.readN (M + 24) 8 = Num.encodeLE 8 cap
  vp : μ.readN (M + 32) 8 = Num.encodeLE 8 buf
  vl : μ.readN (M + 40) 8 = Num.encodeLE 8 (1 + off enc k)
  wout : μ.readN buf (1 + off enc k) = UInt8.ofNat n :: out enc k
  keep : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
    (a < buf ∨ buf + 1 + off enc k ≤ a) → μ.read a = μ0.read a
  rd : ∀ a, μ.readable a = μ0.readable a
  wr : ∀ a, μ.writable a = μ0.writable a

/-- What the loop needs of its layout: the frame M (with [M − 136, M + 80) writable), the elements at E
    (n of them, 232 octets each, each satisfying its `rep` and encoding by `EncOk` to `enc`, the whole
    output fitting in `cap`), the buffer `buf` with room for everything, the dispatch table, all apart. -/
structure LayL (P : Program) (p : ByteArray) (M E n buf cap : Nat) (enc : Nat → List UInt8)
    (rep : Nat → List UInt8 → Prop) (μ0 : Memory) : Prop where
  hM : 67476 + 256 ≤ M ∧ M + 80 < 4294967296 ∧ M % 8 = 0
  hE : 65536 ≤ E ∧ E + 232 * n + 24 < 4294967296
  hEM : E + 232 * n + 24 ≤ M - 136 ∨ M + 80 ≤ E
  hbuf : 67476 ≤ buf ∧ buf + cap + 24 < 4294967296
  hbM : buf + cap + 16 ≤ M - 136 ∨ M + 80 ≤ buf
  hbE : buf + cap + 24 ≤ E ∨ E + 232 * n + 24 ≤ buf
  hcap : 1 + off enc n + 2 ≤ cap ∧ cap < 18446744073709551616
  ok : ∀ j, j < n → EncOk p P (enc j) (rep j)
  rep0 : ∀ j, j < n → rep j (μ0.readN (E + 232 * j) 232)
  tab : μ0.readN 67376 100 = table
  rtab : ∀ a, 67376 ≤ a → a < 67476 → μ0.readable a = true
  rE : ∀ a, E ≤ a → a < E + 232 * n → μ0.readable a = true
  rM : ∀ a, M ≤ a → a < M + 80 → μ0.readable a = true
  wM : ∀ a, M - 136 ≤ a → a < M + 80 → μ0.writable a = true
  wbuf : ∀ a, buf ≤ a → a < buf + cap → μ0.writable a = true

/-- **One element**: from `W k` (k < n) at 30145, element k is encoded, and the encoder is in `W (k + 1)`
    at 30145 again, or, after the last element, at the call appending `work_item_index` (as `tC`). -/
theorem step {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {M E n buf cap : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Prop}
    (L : LayL P p M E n buf cap enc rep μ0) (k : Nat) (hk : k < n)
    (st : W M E n buf cap enc μ0 k ω μ) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x 30215 ω' μ' x (7 * (enc k).length + 4000) ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[6] = UInt64.ofNat (232 * (n - k)) ∧
      μ'.readN (M + 16) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      μ'.readN (M + 24) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 32) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (M + 40) 8 = Num.encodeLE 8 (1 + off enc (k + 1)) ∧
      μ'.readN buf (1 + off enc (k + 1)) = UInt8.ofNat n :: out enc (k + 1) ∧
      (∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
        (a < buf ∨ buf + 1 + off enc (k + 1) ≤ a) → μ'.read a = μ0.read a) ∧
      (∀ a, μ'.readable a = μ0.readable a) ∧ (∀ a, μ'.writable a = μ0.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hbE := L.hbE
  have hcap := L.hcap
  have hon : off enc (k + 1) ≤ off enc n := by
    have h := off_le enc (k + 1) (n - (k + 1)); rwa [show k + 1 + (n - (k + 1)) = n by omega] at h
  rw [off_succ] at hon
  have hSk : E + 232 * k + 232 ≤ E + 232 * n := by omega
  -- the element's octets and the table are as at entry
  have hrep : rep k (μ.readN (E + 232 * k) 232) := by
    rw [Memory.readN_congr (fun j hj => st.keep _ (by omega) (by omega) (by omega))]; exact L.rep0 k hk
  have tab : μ.readN 67376 100 = table := by
    rw [Memory.readN_congr (fun j hj => st.keep _ (by omega) (by omega) (by omega))]; exact L.tab
  have La : Lay P M (E + 232 * k) (M + 24) cap buf (1 + off enc k) (enc k).length 1418 30215 μ :=
    { hF := hM0, hF' := by omega, hF8 := hM8, hS := by omega, hS' := by omega, hSF := by omega,
      vc := st.vc, vp := st.vp, vl := st.vl, hroom := by omega, hcap := hcap.2, hv := by omega,
      hvF := by omega, hvS := by omega, hd := by omega, hd' := by omega, hdF := by omega, hdS := by omega,
      hdv := by omega, hret := ⟨by decide, by decide, by decide⟩, hjt := jte_708, hbt := bs_30215,
      hrS := fun a h1 h2 => by rw [st.rd]; exact L.rE a (by omega) (by omega),
      hrv := fun a h1 h2 => by rw [st.rd]; exact L.rM a (by omega) (by omega),
      hwv := fun a h1 h2 => by rw [st.wr]; exact L.wM a (by omega) (by omega),
      hwd := fun a h1 h2 => by rw [st.wr]; exact L.wbuf a (by omega) (by omega),
      hwF := fun a h1 h2 => by rw [st.wr]; exact L.wM a (by omega) (by omega) }
  obtain ⟨ω1, μ1, run1, _, e1, _, e6, eo, el, efr, erd, ewr⟩ := L.ok k hk X R x ω μ M (E + 232 * k) (M + 24)
    cap buf (1 + off enc k) 1418 30215 st.h0 st.h1 st.h7 st.h8 hrep La tab
    (fun a h1 h2 => by rw [st.rd]; exact L.rtab a h1 h2)
  have kf : ∀ a, M + 16 ≤ a → a < M + 40 → μ1.read a = μ.read a := fun a h1 h2 =>
    efr a (by omega) (by omega) (by omega) (by omega)
  refine ⟨ω1, μ1, run1, e1, e6.trans st.h6, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 => ?_,
    fun a => by rw [erd, st.rd], fun a => by rw [ewr, st.wr]⟩
  · rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega))]; exact st.s16
  · rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega))]; exact st.vc
  · rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega))]; exact st.vp
  · rw [off_succ, ← Nat.add_assoc]; exact el
  · rw [off_succ, ← Nat.add_assoc, readN_add', out_succ,
      Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)), st.wout, eo]; rfl
  · rw [off_succ] at h2
    rw [efr a h0 (by omega) (by omega) (by omega), st.keep a h0 h1 (by omega)]

/-- **After the last element**, at the call appending `work_item_index` (58508, return address 1420):
    the writer holds `[n] ++ enc 0 ++ … ++ enc (n − 1)` and the index's 2 octets wait at M + 52. -/
structure Fin (M n buf cap S0 : Nat) (enc : Nat → List UInt8) (μ0 : Memory) (ω : Regs) (μ : Memory) : Prop where
  h0 : ω[0] = UInt64.ofNat 1420
  h1 : ω[1] = UInt64.ofNat M
  h7 : ω[7] = UInt64.ofNat (M + 24)
  h8 : ω[8] = UInt64.ofNat (M + 52)
  h9 : ω[9] = UInt64.ofNat 2
  vc : μ.readN (M + 24) 8 = Num.encodeLE 8 cap
  vp : μ.readN (M + 32) 8 = Num.encodeLE 8 buf
  vl : μ.readN (M + 40) 8 = Num.encodeLE 8 (1 + off enc n)
  wout : μ.readN buf (1 + off enc n) = UInt8.ofNat n :: out enc n
  w52 : μ.readN (M + 52) 2 = μ0.readN (S0 + 24) 2
  keep : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
    (a < buf ∨ buf + 1 + off enc n ≤ a) → μ.read a = μ0.read a
  rd : ∀ a, μ.readable a = μ0.readable a
  wr : ∀ a, μ.writable a = μ0.writable a

/-- **The element loop**: from `W k` with m = n − k > 0 elements left, the encoder encodes them all and
    reaches the call appending `work_item_index` (`Fin`). S0 (at M + 8) is the work item, its index at
    S0 + 24 apart from what the loop writes. -/
theorem loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X)
    {M E n buf cap S0 : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Prop} (μ0 : Memory)
    (L : LayL P p M E n buf cap enc rep μ0) (s8 : μ0.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (hS0 : S0 + 26 ≤ M - 136 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296) (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 24)
    (rS0 : ∀ a, S0 + 24 ≤ a → a < S0 + 26 → μ0.readable a = true) :
    ∀ m k (ω : Regs) (μ : Memory), k + m = n → 0 < m → W M E n buf cap enc μ0 k ω μ →
      ∃ ω' μ', FreeStepsH p R 30145 ω μ x 58508 ω' μ' x (4100 * m + 7 * (off enc n - off enc k)) ∧
        Fin M n buf cap S0 enc μ0 ω' μ' := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hbuf := L.hbuf; have hbM := L.hbM; have hcap := L.hcap; have hE := L.hE
  intro m
  induction m with
  | zero => intro k ω μ _ h; omega
  | succ m ih =>
    intro k ω μ hkm _ st
    have hk : k < n := by omega
    have hon : off enc (k + 1) ≤ off enc n := by
      have h := off_le enc (k + 1) (n - (k + 1)); rwa [show k + 1 + (n - (k + 1)) = n by omega] at h
    have hos := off_succ enc k
    obtain ⟨ω1, μ1, run1, a1, a6, a16, ac, ap, al, ao, akeep, ard, awr⟩ := step (R := R) x ω μ μ0 L k hk st
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- the last element: on to `work_item_index`
      have hkn : k + 1 = n := by omega
      have s8' : μ1.readN (M + 8) 8 = Num.encodeLE 8 S0 := by
        rw [Memory.readN_congr (fun j hj => akeep _ (by omega) (by omega) (by omega))]; exact s8
      obtain ⟨ω2, μ2, run2, b0, b1, b7, b8, b9, b52, bfr, brd, bwr⟩ := tC (p := p) (P := P) (R := R) x ω1 μ1
        30215 M S0 (Or.inl ⟨rfl, by rw [a6, show n - k = 1 by omega]⟩) (by omega) (by omega) (by omega) a1 s8'
        (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega))
        (fun a h1 h2 => by rw [ard]; exact rS0 a h1 h2)
        (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
      have k2 : ∀ a, M + 24 ≤ a → a < M + 48 → μ2.read a = μ1.read a := fun a h1 h2 =>
        bfr a (by omega) (by omega)
      rw [hkn] at al ao akeep
      refine ⟨ω2, μ2, (run1.trans run2).mono (by rw [← hkn, hos]; omega), ⟨b0, b1, b7, b8, b9, ?_, ?_, ?_, ?_, ?_,
        fun a h0 h1 h2 => ?_, fun a => by rw [brd, ard], fun a => by rw [bwr, awr]⟩⟩
      · rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact ac
      · rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact ap
      · rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact al
      · rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact ao
      · rw [b52, Memory.readN_congr (fun j hj => akeep _ (by omega) (by omega) (by omega))]
      · rw [bfr a h0 (by omega), akeep a h0 h1 h2]
    · -- more elements: on to the next one
      obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, b7, b8, b16, bfr, brd, bwr⟩ := tB (p := p) (P := P) (R := R) x ω1 μ1
        M (E + 232 * k + 232) (232 * (n - (k + 1))) (by omega) (by have := L.hE; omega)
        ⟨by omega, by omega⟩ a1 (by rw [a6]; congr 1; omega) a16
        (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega))
        (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
      have k2 : ∀ a, M + 24 ≤ a → a < M + 48 → μ2.read a = μ1.read a := fun a h1 h2 =>
        bfr a (by omega) (by omega)
      have st2 : W M E n buf cap enc μ0 (k + 1) ω2 μ2 :=
        { h0 := b0, h1 := b1, h5 := by rw [b5, show E + 232 * k + 232 = E + 232 * (k + 1) by omega], h6 := b6,
          h7 := by rw [b7, show E + 232 * k + 232 = E + 232 * (k + 1) by omega],
          h8 := b8, s16 := by rw [b16, show E + 232 * k + 232 + 232 = E + 232 * (k + 1) + 232 by omega],
          vc := by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact ac,
          vp := by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact ap,
          vl := by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega))]; exact al,
          wout := by rw [Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega))]; exact ao,
          keep := fun a h0 h1 h2 => by rw [bfr a h0 (by omega), akeep a h0 h1 h2],
          rd := fun a => by rw [brd, ard], wr := fun a => by rw [bwr, awr] }
      obtain ⟨ω3, μ3, run3, fin⟩ := ih (k + 1) ω2 μ2 (by omega) hm st2
      exact ⟨ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), fin⟩

/-- **Refine's output encoder** (30073, entered from refine's body with the buffer of 232 n + 6 octets):
    for 0 < n < 128 instructions at E (from the work item S0), each encoding to `enc j` by `EncOk`, the
    encoder writes ℰ(n) = [n], the n encodings and the work item's 2-octet `work_item_index` into the
    buffer, stores the result `{cap, buf, |output|}` at O and returns to `ret` (at M + 72), with ω₅, ω₆
    from M + 64, M + 56. Memory changes only in the stack [M − 136, M + 80), the result and the buffer. -/
theorem encode_ok {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {M E n buf cap S0 : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Prop}
    (L : LayL P p M E n buf cap enc rep μ) (O ret t r5 r6 : Nat) (hn : 0 < n ∧ n < 128)
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
    ∃ ω' μ', FreeStepsH p R 30073 ω μ x t ω' μ' x (4100 * n + 7 * off enc n + 1400) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (off enc n + 3) ∧
      μ'.readN buf (off enc n + 3) = UInt8.ofNat n :: (out enc n ++ μ.readN (S0 + 24) 2) ∧
      (∀ a, a < 4294967296 → (a < M - 136 ∨ M + 80 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        (a < buf ∨ buf + cap ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hcap := L.hcap
  have hon := off_le enc 0 n; simp only [Nat.zero_add] at hon
  -- the prologue and the count
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, ac, ap, al, a52, afr, ard, awr⟩ := t1 (p := p) (P := P) (R := R)
    x ω μ M buf cap S0 E n (by omega) ⟨by omega, by omega⟩ (by omega) (by omega) h1 h5 h7 s8 s16 (by omega)
    (by omega) sE (by omega) (fun a h1 h2 => L.rM a h1 h2) (fun a h1 h2 => rS0 a h1 (by omega))
    (fun a h1 h2 => L.wM a (by omega) (by omega))
  -- the length prefix
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bo, bl, bfr, brd, bwr⟩ := Prefix.prefix_small (p := p) (P := P) (R := R)
    x ω1 μ1 M (M + 52) (M + 24) cap buf 0 1416 30122 E (232 * n) n ⟨by omega, by omega, hM8⟩ a0 a1 a5
    (by rw [a6, h6]) a7 a8 (by omega) (by omega) (by omega) (by omega) a52 hn
    (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega)) ac (by simpa using ap) (by simpa using al)
    (by omega) hcap.2 (by omega) (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_707 bs_30122
    (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) → (a < buf ∨ buf + 1 ≤ a) →
      μ2.read a = μ.read a := fun a h0 h1 h2 => by
    rw [bfr a h0 (by omega) (by simpa using h2) (by omega), afr a h0 (by omega)]
  -- the first element
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c16, cfr, crd, cwr⟩ := tA (p := p) (P := P) (R := R) x ω2 μ2
    M E n (by omega) (by omega) ⟨hn.1, by omega⟩ b1 b5
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s16)
    (fun a h1 h2 => by rw [brd, ard]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [bwr, awr]; exact L.wM a (by omega) (by omega))
  have k3 : ∀ a, M + 24 ≤ a → a < M + 48 → μ3.read a = μ2.read a := fun a h1 h2 => cfr a (by omega) (by omega)
  have st0 : W M E n buf cap enc μ 0 ω3 μ3 :=
    { h0 := c0, h1 := c1, h5 := by rw [c5, b5]; simp, h6 := by rw [c6, b6]; simp,
      h7 := by simpa using c7, h8 := c8, s16 := by simpa using c16,
      vc := by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega))]; exact ac,
      vp := by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega)),
        Memory.readN_congr (fun j hj => bfr _ (by omega) (by omega) (by omega) (by omega))]; exact ap,
      vl := by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; simpa [off] using bl,
      wout := by
        rw [show 1 + off enc 0 = 1 by simp [off], Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega))]
        simpa [out] using bo,
      keep := fun a h0 h1 h2 => by
        rw [cfr a h0 (by omega), k2 a h0 (by omega) (by simp [off] at h2; omega)],
      rd := fun a => by rw [crd, brd, ard], wr := fun a => by rw [cwr, bwr, awr] }
  -- the elements
  obtain ⟨ω4, μ4, run4, fin⟩ := loop (R := R) x μ L s8 hS0 hS0' (by omega)
    (fun a h1 h2 => rS0 a (by omega) h2) n 0 ω3 μ3 (by omega) hn.1 st0
  -- `work_item_index`
  have k4v : ∀ a, M + 24 ≤ a → a < M + 48 → μ4.read a = μ4.read a := fun _ _ _ => rfl
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, ed, el, efr, erd, ewr⟩ := extend_ok (p := p) (P := P) (R := R) x ω4 μ4
    M (M + 24) (M + 52) 2 cap buf (1 + off enc n) 1420 30250 ⟨by omega, by omega, hM8⟩ fin.h0 fin.h1 fin.h7 fin.h8
    fin.h9 (by omega) hcap.2 fin.vc fin.vp fin.vl (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by omega) (by omega) (by omega) (by omega) ⟨by decide, by decide, by decide⟩ jte_709 bs_30250
    (fun a h1 h2 => by rw [fin.rd]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.wr]; exact L.wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.rd]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.wr]; exact L.wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.wr]; exact L.wM a (by omega) (by omega))
  have k5 : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
      (a < buf ∨ buf + (off enc n + 3) ≤ a) → μ5.read a = μ.read a := fun a h0 h1 h2 => by
    rw [efr a h0 (by omega) (by omega) (by omega), fin.keep a h0 h1 (by omega)]
  have k5w : ∀ a, M + 24 ≤ a → a < M + 40 → μ5.read a = μ4.read a := fun a h1 h2 =>
    efr a (by omega) (by omega) (by omega) (by omega)
  -- the result, and the return
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fc, fp, fl, ffr, frd, fwr⟩ := t5 (p := p) (P := P) (R := R) x ω5 μ5
    M O cap buf (1 + off enc n + 2) ret t r5 r6 (by omega) hO (by omega) e1
    (by rw [Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega) (by omega))]; exact s0)
    (by rw [Memory.readN_congr (fun j hj => k5w _ (by omega) (by omega))]; exact fin.vc)
    (by rw [Memory.readN_congr (fun j hj => k5w _ (by omega) (by omega))]; exact fin.vp)
    el
    (by rw [Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega) (by omega))]; exact sr)
    (by rw [Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega) (by omega))]; exact s5)
    (by rw [Memory.readN_congr (fun j hj => k5 _ (by omega) (by omega) (by omega))]; exact s6)
    hcap.2 (by omega) (by omega) hr5 hr6 hret hjt hbt
    (fun a h1 h2 => by rw [erd, fin.rd]; exact L.rM a h1 h2)
    (fun a h1 h2 => by rw [ewr, fin.wr]; exact wO a h1 h2)
  refine ⟨ω6, μ6, (run1.trans (run2.trans (run3.trans (run4.trans (run5.trans run6))))).mono (by omega),
    f0, f1, f5, f6, fc, fp, by rw [show off enc n + 3 = 1 + off enc n + 2 by omega]; exact fl, ?_,
    fun a h0 h1 h2 h3 => ?_, fun a => by rw [frd, erd, fin.rd], fun a => by rw [fwr, ewr, fin.wr]⟩
  · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), show off enc n + 3 = (1 + off enc n) + 2 by omega,
      readN_add', ed, Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)),
      fin.wout, fin.w52]
    rfl
  · rw [ffr a h0 h2, k5 a h0 (by omega) (by omega)]

/-- **Refine's output encoder, for no instructions** (30073, n = 0): the encoder writes ℰ(0) = [0] and the
    work item's 2-octet `work_item_index` into the buffer, stores the result `{cap, buf, 3}` at O and
    returns, as `encode_ok`. -/
theorem encode_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    (M buf cap S0 E O ret t r5 r6 : Nat)
    (hM : 67476 + 256 ≤ M ∧ M + 80 < 4294967296 ∧ M % 8 = 0)
    (hbuf : 67476 ≤ buf ∧ buf + cap + 24 < 4294967296) (hbM : buf + cap + 16 ≤ M - 136 ∨ M + 80 ≤ buf)
    (hcap : 3 ≤ cap ∧ cap < 18446744073709551616) (hE : E < 18446744073709551616)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cap) (h7 : ω[7] = UInt64.ofNat buf)
    (s0 : μ.readN M 8 = Num.encodeLE 8 O) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 0) (sE : μ.readN (S0 + 8) 8 = Num.encodeLE 8 E)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS0 : S0 + 26 ≤ M - 136 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296)
    (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 8)
    (rS0 : ∀ a, S0 + 8 ≤ a → a < S0 + 26 → μ.readable a = true)
    (hO : O + 24 ≤ 4294967296) (hOM : O + 24 ≤ M - 136 ∨ M + 80 ≤ O) (hOb : O + 24 ≤ buf ∨ buf + cap ≤ O)
    (rM : ∀ a, M ≤ a → a < M + 80 → μ.readable a = true)
    (wM : ∀ a, M - 136 ≤ a → a < M + 80 → μ.writable a = true)
    (wbuf : ∀ a, buf ≤ a → a < buf + cap → μ.writable a = true)
    (wO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30073 ω μ x t ω' μ' x 2000 ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 3 ∧
      μ'.readN buf 3 = UInt8.ofNat 0 :: μ.readN (S0 + 24) 2 ∧
      (∀ a, a < 4294967296 → (a < M - 136 ∨ M + 80 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        (a < buf ∨ buf + cap ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := hM
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, ac, ap, al, a52, afr, ard, awr⟩ := t1 (p := p) (P := P) (R := R)
    x ω μ M buf cap S0 E 0 (by omega) ⟨by omega, by omega⟩ (by omega) (by omega) h1 h5 h7 s8 s16 (by omega)
    (by omega) sE hE rM (fun a h1 h2 => rS0 a h1 (by omega)) (fun a h1 h2 => wM a (by omega) (by omega))
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bo, bl, bfr, brd, bwr⟩ := Prefix.prefix_zero (p := p) (P := P) (R := R)
    x ω1 μ1 M (M + 52) (M + 24) cap buf 0 1416 30122 E ω[6].toNat ⟨by omega, by omega, hM8⟩ a0 a1 a5
    (by rw [a6]; exact UInt64.ofNat_toNat.symm) a7 a8 hE (UInt64.toNat_lt _) (by omega) (by omega) a52
    (fun a h1 h2 => by rw [ard]; exact rM a (by omega) (by omega)) ac (by simpa using ap) (by simpa using al)
    (by omega) hcap.2 (by omega) (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_707 bs_30122
    (fun a h1 h2 => by rw [ard]; exact rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact wM a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) → (a < buf ∨ buf + 1 ≤ a) →
      μ2.read a = μ.read a := fun a h0 h1 h2 => by
    rw [bfr a h0 (by omega) (by simpa using h2) (by omega), afr a h0 (by omega)]
  obtain ⟨ω3, μ3, run3, c0, c1, c7, c8, c9, c52, cfr, crd, cwr⟩ := tC (p := p) (P := P) (R := R) x ω2 μ2 30122 M S0
    (Or.inr ⟨rfl, by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s16⟩)
    (by omega) hS0' (by omega) b1
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s8)
    (fun a h1 h2 => by rw [brd, ard]; exact rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [brd, ard]; exact rS0 a (by omega) h2)
    (fun a h1 h2 => by rw [bwr, awr]; exact wM a (by omega) (by omega))
  have k3 : ∀ a, M + 24 ≤ a → a < M + 48 → μ3.read a = μ2.read a := fun a h1 h2 => cfr a (by omega) (by omega)
  have k1w : ∀ a, M + 24 ≤ a → a < M + 40 → μ2.read a = μ1.read a := fun a h1 h2 =>
    bfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω4, μ4, run4, e0, e1, e5, e6, ed, el, efr, erd, ewr⟩ := extend_ok (p := p) (P := P) (R := R) x ω3 μ3
    M (M + 24) (M + 52) 2 cap buf 1 1420 30250 ⟨by omega, by omega, hM8⟩ c0 c1 c7 c8 c9 (by omega) hcap.2
    (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ac)
    (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega)),
      Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ap)
    (by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; simpa using bl)
    (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_709 bs_30250
    (fun a h1 h2 => by rw [crd, brd, ard]; exact rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [crd, brd, ard]; exact rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [cwr, bwr, awr]; exact wM a (by omega) (by omega))
  have k4 : ∀ a, a < 4294967296 → (a < M - 136 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) → (a < buf ∨ buf + 3 ≤ a) →
      μ4.read a = μ.read a := fun a h0 h1 h2 => by
    rw [efr a h0 (by omega) (by omega) (by omega), cfr a h0 (by omega), k2 a h0 h1 (by omega)]
  have k4w : ∀ a, M + 24 ≤ a → a < M + 40 → μ4.read a = μ1.read a := fun a h1 h2 => by
    rw [efr a (by omega) (by omega) (by omega) (by omega), k3 a h1 (by omega), k1w a h1 h2]
  obtain ⟨ω5, μ5, run5, f0, f1, f5, f6, fc, fp, fl, ffr, frd, fwr⟩ := t5 (p := p) (P := P) (R := R) x ω4 μ4
    M O cap buf 3 ret t r5 r6 (by omega) hO (by omega) e1
    (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega))]; exact s0)
    (by rw [Memory.readN_congr (fun j hj => k4w _ (by omega) (by omega))]; exact ac)
    (by rw [Memory.readN_congr (fun j hj => k4w _ (by omega) (by omega))]; exact ap)
    (by simpa using el)
    (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega))]; exact sr)
    (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega))]; exact s5)
    (by rw [Memory.readN_congr (fun j hj => k4 _ (by omega) (by omega) (by omega))]; exact s6)
    hcap.2 (by omega) (by omega) hr5 hr6 hret hjt hbt
    (fun a h1 h2 => by rw [erd, crd, brd, ard]; exact rM a h1 h2)
    (fun a h1 h2 => by rw [ewr, cwr, bwr, awr]; exact wO a h1 h2)
  refine ⟨ω5, μ5, (run1.trans (run2.trans (run3.trans (run4.trans run5)))).mono (by omega),
    f0, f1, f5, f6, fc, fp, fl, ?_, fun a h0 h1 h2 h3 => ?_, fun a => by rw [frd, erd, crd, brd, ard],
    fun a => by rw [fwr, ewr, cwr, bwr, awr]⟩
  · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), show (3 : Nat) = 1 + 2 from rfl,
      readN_add', ed, c52, Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)),
      Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega)), (show μ2.readN buf 1 = [UInt8.ofNat 0] by simpa using bo),
      Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]
    rfl
  · rw [ffr a h0 h2, k4 a h0 (by omega) (by omega)]

end Services.Bootstrap.Encode.Loop
