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

end Services.Bootstrap.Encode.Loop
