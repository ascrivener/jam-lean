import Services.Bootstrap.Encode.PrefixBig

/-!
# The element contract with a deeper stack, and the encoder over it

`EncOkM` (EncM.lean) lets one `Instruction::encode_to` call (frame base F) use the stack [F − 136, F):
its own 56-octet frame and one call of `Vec<u8>::extend_from_slice`. The variants that hold a `Vec`
encode its length ℰ(n) (GP v0.8.0 Appendix C, the sequence codec) by calling the length-prefix function
(30977) from their frame, and that function calls `extend_from_slice` from its own: they use the
stack down to F − 192 (or further, through a helper). `EncOkMD p P D enc Rep Src` is `EncOkM` with
[F − D, F) in place of [F − 136, F): in the layout (`LayD`, `Lay` with D), in the separation of the
heap octets `Src` and in the frame clause of the conclusion. `EncOkMD` is monotone in D
(`EncOkMD.mono`) and `EncOkM` is `EncOkMD 136` (`EncOkM.toMD`).

`LayLMD`, `loopMD`, `encode_okMD` and `encode_okMD_big` are `EncM.LayLM`, `loopM`, `encode_okM` and
`PrefixBig.encode_okM_big` for `EncOkMD 232` elements: the stack the encoder needs is [M − 232, M + 80).
-/

namespace Services.Bootstrap.Encode.EncMD

open PVM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeA
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.Enc Services.Bootstrap.Encode.Top
  Services.Bootstrap.Encode.Loop Services.Bootstrap.Encode.EncM Services.Bootstrap.Encode.PrefixBig

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **The layout of one `encode_to` call whose callees use [F − D, F)**: `Lay` with D for 136. -/
structure LayD (P : Program) (D F S v cap ptr len N ret t : Nat) (μ : Memory) : Prop where
  hF : 67476 + 256 ≤ F
  hF' : F < 4294967296
  hF8 : F % 8 = 0
  hS : 65536 ≤ S
  hS' : S + 256 < 4294967296
  hSF : S + 256 ≤ F - D ∨ F ≤ S
  vc : μ.readN v 8 = Num.encodeLE 8 cap
  vp : μ.readN (v + 8) 8 = Num.encodeLE 8 ptr
  vl : μ.readN (v + 16) 8 = Num.encodeLE 8 len
  hroom : len + N ≤ cap
  hcap : cap < 18446744073709551616
  hv : v + 24 ≤ 4294967296
  hvF : v + 24 ≤ F - D ∨ F ≤ v
  hvS : v + 24 ≤ S ∨ S + 232 ≤ v
  hd : 65536 ≤ ptr + len
  hd' : ptr + len + N + 16 < 4294967296
  hdF : F ≤ ptr + len ∨ ptr + len + N + 16 ≤ F - D
  hdS : ptr + len + N + 24 ≤ S ∨ S + 232 + 24 ≤ ptr + len
  hdv : v + 24 ≤ ptr + len ∨ ptr + len + N ≤ v
  hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0
  hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t
  hbt : P.isBlockStart t = true
  hrS : ∀ a, S ≤ a → a < S + 232 → μ.readable a = true
  hrv : ∀ a, v ≤ a → a < v + 24 → μ.readable a = true
  hwv : ∀ a, v + 16 ≤ a → a < v + 24 → μ.writable a = true
  hwd : ∀ a, ptr + len ≤ a → a < ptr + len + N → μ.writable a = true
  hwF : ∀ a, F - D ≤ a → a < F → μ.writable a = true

/-- A deeper layout is a shallower one. -/
theorem LayD.mono {P : Program} {D D' F S v cap ptr len N ret t : Nat} {μ : Memory}
    (L : LayD P D' F S v cap ptr len N ret t μ) (hD : D ≤ D') : LayD P D F S v cap ptr len N ret t μ :=
  { hF := L.hF, hF' := L.hF', hF8 := L.hF8, hS := L.hS, hS' := L.hS', hSF := by have := L.hSF; omega,
    vc := L.vc, vp := L.vp, vl := L.vl, hroom := L.hroom, hcap := L.hcap, hv := L.hv,
    hvF := by have := L.hvF; omega, hvS := L.hvS, hd := L.hd, hd' := L.hd', hdF := by have := L.hdF; omega,
    hdS := L.hdS, hdv := L.hdv, hret := L.hret, hjt := L.hjt, hbt := L.hbt, hrS := L.hrS, hrv := L.hrv,
    hwv := L.hwv, hwd := L.hwd, hwF := fun a h1 h2 => L.hwF a (by omega) h2 }

/-- `LayD` with D ≥ 136 is a `Lay`. -/
theorem LayD.toLay {P : Program} {D F S v cap ptr len N ret t : Nat} {μ : Memory}
    (L : LayD P D F S v cap ptr len N ret t μ) (hD : 136 ≤ D) : Lay P F S v cap ptr len N ret t μ :=
  have L' := L.mono hD
  { hF := L'.hF, hF' := L'.hF', hF8 := L'.hF8, hS := L'.hS, hS' := L'.hS', hSF := L'.hSF,
    vc := L'.vc, vp := L'.vp, vl := L'.vl, hroom := L'.hroom, hcap := L'.hcap, hv := L'.hv,
    hvF := L'.hvF, hvS := L'.hvS, hd := L'.hd, hd' := L'.hd', hdF := L'.hdF,
    hdS := L'.hdS, hdv := L'.hdv, hret := L'.hret, hjt := L'.hjt, hbt := L'.hbt, hrS := L'.hrS,
    hrv := L'.hrv, hwv := L'.hwv, hwd := L'.hwd, hwF := L'.hwF }

/-- **One element encodes, its callees using [F − D, F)** (`Instruction::encode_to`, 30145): `EncOkM`
    with the stack [F − D, F) for [F − 136, F) in the layout, in the separation of the heap octets
    `Src` and in the frame clause. Gas 2000 · |enc| + 4000. -/
def EncOkMD (p : ByteArray) (P : Program) (D : Nat) (enc : List UInt8) (Rep : List UInt8 → Memory → Prop)
    (Src : Nat → Prop) : Prop :=
  ∀ (X : Type) (R : HostRel X) (x : X) (ω : Regs) (μ : Memory) (F S v cap ptr len ret t : Nat),
    ω[0] = UInt64.ofNat ret → ω[1] = UInt64.ofNat F → ω[7] = UInt64.ofNat S → ω[8] = UInt64.ofNat v →
    Rep (μ.readN S 232) μ → LayD P D F S v cap ptr len enc.length ret t μ →
    μ.readN 67376 100 = table → (∀ a, 67376 ≤ a → a < 67476 → μ.readable a = true) →
    (∀ a, Src a → a < 4294967296 ∧ μ.readable a = true ∧ (a < F - D ∨ F ≤ a) ∧
      (a < ptr + len ∨ ptr + len + enc.length ≤ a) ∧ (a < v ∨ v + 24 ≤ a)) →
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x t ω' μ' x (2000 * enc.length + 4000) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat F ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      μ'.readN (ptr + len) enc.length = enc ∧ μ'.readN (v + 16) 8 = Num.encodeLE 8 (len + enc.length) ∧
      (∀ a, a < 4294967296 → (a < F - D ∨ F ≤ a) → (a < ptr + len ∨ ptr + len + enc.length ≤ a) →
        (a < v + 16 ∨ v + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a)

/-- **`EncOkMD` is monotone in the stack depth.** -/
theorem EncOkMD.mono {p : ByteArray} {P : Program} {D D' : Nat} {enc : List UInt8}
    {Rep : List UInt8 → Memory → Prop} {Src : Nat → Prop} (h : EncOkMD p P D enc Rep Src) (hD : D ≤ D') :
    EncOkMD p P D' enc Rep Src := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  have hF := L.hF
  obtain ⟨ω', μ', run, e0, e1, e5, e6, eo, el, efr, erd, ewr⟩ := h X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8
    rep (L.mono hD) tab hrt (fun a ha => by
      obtain ⟨a0, a1, a2, a3, a4⟩ := hsrc a ha; exact ⟨a0, a1, by omega, a3, a4⟩)
  exact ⟨ω', μ', run, e0, e1, e5, e6, eo, el, fun a h0 h1 h2 h3 => efr a h0 (by omega) h2 h3, erd, ewr⟩

/-- **An `EncOkM` element is an `EncOkMD 136` one.** -/
theorem EncOkM.toMD {p : ByteArray} {P : Program} {enc : List UInt8} {Rep : List UInt8 → Memory → Prop}
    {Src : Nat → Prop} (h : EncOkM p P enc Rep Src) : EncOkMD p P 136 enc Rep Src := by
  intro X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep L tab hrt hsrc
  exact h X R x ω μ F S v cap ptr len ret t h0 h1 h7 h8 rep (L.toLay (Nat.le_refl _)) tab hrt hsrc

/-- **An `EncOkM` element is an `EncOkMD 232` one.** -/
theorem EncOkM.toMD232 {p : ByteArray} {P : Program} {enc : List UInt8} {Rep : List UInt8 → Memory → Prop}
    {Src : Nat → Prop} (h : EncOkM p P enc Rep Src) : EncOkMD p P 232 enc Rep Src :=
  (EncOkM.toMD h).mono (by decide)

/-- What the loop needs of its layout, for `EncOkMD 232` elements: `LayL`, with each element's `rep` taking
    the memory, its heap octets `src j` readable and apart from the stack [M − 232, M + 80) and the
    buffer, and `rep j` holding in any memory that agrees with the entry memory on `src j` and on
    readability (`rcong`). -/
structure LayLMD (P : Program) (p : ByteArray) (M E n buf cap : Nat) (enc : Nat → List UInt8)
    (rep : Nat → List UInt8 → Memory → Prop) (src : Nat → Nat → Prop) (μ0 : Memory) : Prop where
  hM : 67476 + 256 ≤ M ∧ M + 80 < 4294967296 ∧ M % 8 = 0
  hE : 65536 ≤ E ∧ E + 232 * n + 24 < 4294967296
  hEM : E + 232 * n + 24 ≤ M - 232 ∨ M + 80 ≤ E
  hbuf : 67476 ≤ buf ∧ buf + cap + 24 < 4294967296
  hbM : buf + cap + 16 ≤ M - 232 ∨ M + 80 ≤ buf
  hbE : buf + cap + 24 ≤ E ∨ E + 232 * n + 24 ≤ buf
  hcap : 1 + off enc n + 2 ≤ cap ∧ cap < 18446744073709551616
  ok : ∀ j, j < n → EncOkMD p P 232 (enc j) (rep j) (src j)
  rep0 : ∀ j, j < n → rep j (μ0.readN (E + 232 * j) 232) μ0
  rcong : ∀ j, j < n → ∀ (bs : List UInt8) (μ : Memory), (∀ a, src j a → μ.read a = μ0.read a) →
    (∀ a, μ.readable a = μ0.readable a) → rep j bs μ0 → rep j bs μ
  hsrc : ∀ j, j < n → ∀ a, src j a → a < 4294967296 ∧ μ0.readable a = true ∧
    (a < M - 232 ∨ M + 80 ≤ a) ∧ (a < buf ∨ buf + cap ≤ a)
  tab : μ0.readN 67376 100 = table
  rtab : ∀ a, 67376 ≤ a → a < 67476 → μ0.readable a = true
  rE : ∀ a, E ≤ a → a < E + 232 * n → μ0.readable a = true
  rM : ∀ a, M ≤ a → a < M + 80 → μ0.readable a = true
  wM : ∀ a, M - 232 ≤ a → a < M + 80 → μ0.writable a = true
  wbuf : ∀ a, buf ≤ a → a < buf + cap → μ0.writable a = true

/-- **The encoder's state at 30145, about to encode element k**, after the prefix `pre`: `W` with the
    buffer holding `pre ++ enc 0 ++ … ++ enc (k − 1)`. -/
structure WMD (M E n buf cap : Nat) (pre : List UInt8) (enc : Nat → List UInt8) (μ0 : Memory) (k : Nat)
    (ω : Regs) (μ : Memory) : Prop where
  h0 : ω[0] = UInt64.ofNat 1418
  h1 : ω[1] = UInt64.ofNat M
  h5 : ω[5] = UInt64.ofNat (E + 232 * k)
  h6 : ω[6] = UInt64.ofNat (232 * (n - k))
  h7 : ω[7] = UInt64.ofNat (E + 232 * k)
  h8 : ω[8] = UInt64.ofNat (M + 24)
  s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 (E + 232 * k + 232)
  vc : μ.readN (M + 24) 8 = Num.encodeLE 8 cap
  vp : μ.readN (M + 32) 8 = Num.encodeLE 8 buf
  vl : μ.readN (M + 40) 8 = Num.encodeLE 8 (pre.length + off enc k)
  wout : μ.readN buf (pre.length + off enc k) = pre ++ out enc k
  keep : ∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
    (a < buf ∨ buf + pre.length + off enc k ≤ a) → μ.read a = μ0.read a
  rd : ∀ a, μ.readable a = μ0.readable a
  wr : ∀ a, μ.writable a = μ0.writable a

/-- **One element** (`EncOkMD 232`): from `WMD k` (k < n) at 30145, element k is encoded and the encoder is
    at 30215 with the buffer holding `pre ++ enc 0 ++ … ++ enc k`. -/
theorem stepMD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ0 : Memory)
    {M E n buf cap : Nat} {pre : List UInt8} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Memory → Prop}
    {src : Nat → Nat → Prop} (L : LayLMD P p M E n buf cap enc rep src μ0)
    (hw : pre.length + off enc n + 2 ≤ cap) (k : Nat) (hk : k < n)
    (st : WMD M E n buf cap pre enc μ0 k ω μ) :
    ∃ ω' μ', FreeStepsH p R 30145 ω μ x 30215 ω' μ' x (2000 * (enc k).length + 4000) ∧
      ω'[1] = UInt64.ofNat M ∧ ω'[6] = UInt64.ofNat (232 * (n - k)) ∧
      μ'.readN (M + 16) 8 = Num.encodeLE 8 (E + 232 * k + 232) ∧
      μ'.readN (M + 24) 8 = Num.encodeLE 8 cap ∧ μ'.readN (M + 32) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (M + 40) 8 = Num.encodeLE 8 (pre.length + off enc (k + 1)) ∧
      μ'.readN buf (pre.length + off enc (k + 1)) = pre ++ out enc (k + 1) ∧
      (∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
        (a < buf ∨ buf + pre.length + off enc (k + 1) ≤ a) → μ'.read a = μ0.read a) ∧
      (∀ a, μ'.readable a = μ0.readable a) ∧ (∀ a, μ'.writable a = μ0.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hbE := L.hbE
  have hcap := L.hcap
  have hon : off enc (k + 1) ≤ off enc n := by
    have h := off_le enc (k + 1) (n - (k + 1)); rwa [show k + 1 + (n - (k + 1)) = n by omega] at h
  rw [off_succ] at hon
  have hSk : E + 232 * k + 232 ≤ E + 232 * n := by omega
  -- the element's octets, its heap octets and the table are as at entry
  have hrep : rep k (μ.readN (E + 232 * k) 232) μ := by
    rw [Memory.readN_congr (fun j hj => st.keep _ (by omega) (by omega) (by omega))]
    refine L.rcong k hk _ μ (fun a ha => ?_) st.rd (L.rep0 k hk)
    obtain ⟨ha0, -, haM, hab⟩ := L.hsrc k hk a ha
    exact st.keep a ha0 (by omega) (by omega)
  have tab : μ.readN 67376 100 = table := by
    rw [Memory.readN_congr (fun j hj => st.keep _ (by omega) (by omega) (by omega))]; exact L.tab
  have La : LayD P 232 M (E + 232 * k) (M + 24) cap buf (pre.length + off enc k) (enc k).length 1418 30215 μ :=
    { hF := hM0, hF' := by omega, hF8 := hM8, hS := by omega, hS' := by omega, hSF := by omega,
      vc := st.vc, vp := st.vp, vl := st.vl, hroom := by omega, hcap := hcap.2, hv := by omega,
      hvF := by omega, hvS := by omega, hd := by omega, hd' := by omega, hdF := by omega, hdS := by omega,
      hdv := by omega, hret := ⟨by decide, by decide, by decide⟩, hjt := jte_708, hbt := bs_30215,
      hrS := fun a h1 h2 => by rw [st.rd]; exact L.rE a (by omega) (by omega),
      hrv := fun a h1 h2 => by rw [st.rd]; exact L.rM a (by omega) (by omega),
      hwv := fun a h1 h2 => by rw [st.wr]; exact L.wM a (by omega) (by omega),
      hwd := fun a h1 h2 => by rw [st.wr]; exact L.wbuf a (by omega) (by omega),
      hwF := fun a h1 h2 => by rw [st.wr]; exact L.wM a (by omega) (by omega) }
  have hsrc : ∀ a, src k a → a < 4294967296 ∧ μ.readable a = true ∧ (a < M - 232 ∨ M ≤ a) ∧
      (a < buf + (pre.length + off enc k) ∨ buf + (pre.length + off enc k) + (enc k).length ≤ a) ∧
      (a < M + 24 ∨ M + 24 + 24 ≤ a) := fun a ha => by
    obtain ⟨ha0, har, haM, hab⟩ := L.hsrc k hk a ha
    exact ⟨ha0, by rw [st.rd]; exact har, by omega, by omega, by omega⟩
  obtain ⟨ω1, μ1, run1, _, e1, _, e6, eo, el, efr, erd, ewr⟩ := L.ok k hk X R x ω μ M (E + 232 * k) (M + 24)
    cap buf (pre.length + off enc k) 1418 30215 st.h0 st.h1 st.h7 st.h8 hrep La tab
    (fun a h1 h2 => by rw [st.rd]; exact L.rtab a h1 h2) hsrc
  have kf : ∀ a, M + 16 ≤ a → a < M + 40 → μ1.read a = μ.read a := fun a h1 h2 =>
    efr a (by omega) (by omega) (by omega) (by omega)
  refine ⟨ω1, μ1, run1, e1, e6.trans st.h6, ?_, ?_, ?_, ?_, ?_, fun a h0 h1 h2 => ?_,
    fun a => by rw [erd, st.rd], fun a => by rw [ewr, st.wr]⟩
  · rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega))]; exact st.s16
  · rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega))]; exact st.vc
  · rw [Memory.readN_congr (fun j hj => kf _ (by omega) (by omega))]; exact st.vp
  · rw [off_succ, ← Nat.add_assoc]; exact el
  · rw [off_succ, ← Nat.add_assoc, readN_add', out_succ,
      Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)), st.wout, eo,
      List.append_assoc]
  · rw [off_succ] at h2
    rw [efr a h0 (by omega) (by omega) (by omega), st.keep a h0 h1 (by omega)]

/-- **After the last element**, at the call appending `work_item_index`: `Fin` after the prefix `pre`. -/
structure FinMD (M n buf cap S0 : Nat) (pre : List UInt8) (enc : Nat → List UInt8) (μ0 : Memory) (ω : Regs)
    (μ : Memory) : Prop where
  h0 : ω[0] = UInt64.ofNat 1420
  h1 : ω[1] = UInt64.ofNat M
  h7 : ω[7] = UInt64.ofNat (M + 24)
  h8 : ω[8] = UInt64.ofNat (M + 52)
  h9 : ω[9] = UInt64.ofNat 2
  vc : μ.readN (M + 24) 8 = Num.encodeLE 8 cap
  vp : μ.readN (M + 32) 8 = Num.encodeLE 8 buf
  vl : μ.readN (M + 40) 8 = Num.encodeLE 8 (pre.length + off enc n)
  wout : μ.readN buf (pre.length + off enc n) = pre ++ out enc n
  w52 : μ.readN (M + 52) 2 = μ0.readN (S0 + 24) 2
  keep : ∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
    (a < buf ∨ buf + pre.length + off enc n ≤ a) → μ.read a = μ0.read a
  rd : ∀ a, μ.readable a = μ0.readable a
  wr : ∀ a, μ.writable a = μ0.writable a

/-- **The element loop** (`EncOkMD 232` elements): from `WMD k` with m = n − k > 0 elements left, the encoder
    encodes them all and reaches the call appending `work_item_index` (`FinM`). -/
theorem loopMD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X)
    {M E n buf cap S0 : Nat} {pre : List UInt8} {enc : Nat → List UInt8}
    {rep : Nat → List UInt8 → Memory → Prop} {src : Nat → Nat → Prop} (μ0 : Memory)
    (L : LayLMD P p M E n buf cap enc rep src μ0) (hw : pre.length + off enc n + 2 ≤ cap)
    (s8 : μ0.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (hS0 : S0 + 26 ≤ M - 232 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296) (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 24)
    (rS0 : ∀ a, S0 + 24 ≤ a → a < S0 + 26 → μ0.readable a = true) :
    ∀ m k (ω : Regs) (μ : Memory), k + m = n → 0 < m → WMD M E n buf cap pre enc μ0 k ω μ →
      ∃ ω' μ', FreeStepsH p R 30145 ω μ x 58508 ω' μ' x (4100 * m + 2000 * (off enc n - off enc k)) ∧
        FinMD M n buf cap S0 pre enc μ0 ω' μ' := by
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
    obtain ⟨ω1, μ1, run1, a1, a6, a16, ac, ap, al, ao, akeep, ard, awr⟩ :=
      stepMD (R := R) x ω μ μ0 L hw k hk st
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
      have st2 : WMD M E n buf cap pre enc μ0 (k + 1) ω2 μ2 :=
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

/-- **The encoder after the length prefix** (30122, back from the prefix call): with the writer at
    M + 24 holding `{cap, buf, |pre|}`, `pre` in the buffer and memory otherwise as at entry (μ) outside
    the stack, the encoder encodes the n > 0 elements (`loopMD`), appends the work item's 2-octet
    `work_item_index`, stores the result `{cap, buf, |pre| + off + 2}` at O and returns to `ret`. -/
theorem restMD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ μ2 : Memory)
    {M E n buf cap S0 : Nat} {pre : List UInt8} {enc : Nat → List UInt8}
    {rep : Nat → List UInt8 → Memory → Prop} {src : Nat → Nat → Prop}
    (L : LayLMD P p M E n buf cap enc rep src μ) (hw : pre.length + off enc n + 2 ≤ cap)
    (O ret t r5 r6 : Nat) (hn : 0 < n ∧ n < 4294967296)
    (b1 : ω[1] = UInt64.ofNat M) (b5 : ω[5] = UInt64.ofNat E) (b6 : ω[6] = UInt64.ofNat (232 * n))
    (vc : μ2.readN (M + 24) 8 = Num.encodeLE 8 cap) (vp : μ2.readN (M + 32) 8 = Num.encodeLE 8 buf)
    (vl : μ2.readN (M + 40) 8 = Num.encodeLE 8 pre.length) (wpre : μ2.readN buf pre.length = pre)
    (k2 : ∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) →
      (a < buf ∨ buf + pre.length ≤ a) → μ2.read a = μ.read a)
    (rd2 : ∀ a, μ2.readable a = μ.readable a) (wr2 : ∀ a, μ2.writable a = μ.writable a)
    (s0 : μ.readN M 8 = Num.encodeLE 8 O) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS0 : S0 + 26 ≤ M - 232 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296)
    (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 8)
    (rS0 : ∀ a, S0 + 8 ≤ a → a < S0 + 26 → μ.readable a = true)
    (hO : O + 24 ≤ 4294967296) (hOM : O + 24 ≤ M - 232 ∨ M + 80 ≤ O) (hOb : O + 24 ≤ buf ∨ buf + cap ≤ O)
    (wO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30122 ω μ2 x t ω' μ' x (4100 * n + 2000 * off enc n + 400) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (pre.length + off enc n + 2) ∧
      μ'.readN buf (pre.length + off enc n + 2) = pre ++ out enc n ++ μ.readN (S0 + 24) 2 ∧
      (∀ a, a < 4294967296 → (a < M - 232 ∨ M + 80 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        (a < buf ∨ buf + cap ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hcap := L.hcap
  have hon := off_le enc 0 n; simp only [Nat.zero_add] at hon
  -- the first element
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c16, cfr, crd, cwr⟩ := tA (p := p) (P := P) (R := R) x ω μ2
    M E n (by omega) (by omega) ⟨hn.1, by omega⟩ b1 b5
    (by rw [Memory.readN_congr (fun j hj => k2 _ (by omega) (by omega) (by omega))]; exact s16)
    (fun a h1 h2 => by rw [rd2]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [wr2]; exact L.wM a (by omega) (by omega))
  have k3 : ∀ a, M + 24 ≤ a → a < M + 48 → μ3.read a = μ2.read a := fun a h1 h2 => cfr a (by omega) (by omega)
  have st0 : WMD M E n buf cap pre enc μ 0 ω3 μ3 :=
    { h0 := c0, h1 := c1, h5 := by rw [c5, b5]; simp, h6 := by rw [c6, b6]; simp,
      h7 := by simpa using c7, h8 := c8, s16 := by simpa using c16,
      vc := by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; exact vc,
      vp := by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; exact vp,
      vl := by rw [Memory.readN_congr (fun j hj => k3 _ (by omega) (by omega))]; simpa [off] using vl,
      wout := by
        rw [show pre.length + off enc 0 = pre.length by simp [off],
          Memory.readN_congr (fun j hj => cfr _ (by omega) (by omega))]
        simpa [out] using wpre,
      keep := fun a h0 h1 h2 => by
        rw [cfr a h0 (by omega), k2 a h0 (by omega) (by simp [off] at h2; omega)],
      rd := fun a => by rw [crd, rd2], wr := fun a => by rw [cwr, wr2] }
  -- the elements
  obtain ⟨ω4, μ4, run4, fin⟩ := loopMD (R := R) x μ L hw s8 hS0 hS0' (by omega)
    (fun a h1 h2 => rS0 a (by omega) h2) n 0 ω3 μ3 (by omega) hn.1 st0
  -- `work_item_index`
  obtain ⟨ω5, μ5, run5, e0, e1, e5, e6, ed, el, efr, erd, ewr⟩ := extend_ok (p := p) (P := P) (R := R) x ω4 μ4
    M (M + 24) (M + 52) 2 cap buf (pre.length + off enc n) 1420 30250 ⟨by omega, by omega, hM8⟩ fin.h0 fin.h1
    fin.h7 fin.h8 fin.h9 (by omega) hcap.2 fin.vc fin.vp fin.vl (by omega) (by omega) ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega) ⟨by decide, by decide, by decide⟩ jte_709
    bs_30250
    (fun a h1 h2 => by rw [fin.rd]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.wr]; exact L.wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.rd]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.wr]; exact L.wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [fin.wr]; exact L.wM a (by omega) (by omega))
  have k5 : ∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 16) ∨ M + 56 ≤ a) →
      (a < buf ∨ buf + (pre.length + off enc n + 2) ≤ a) → μ5.read a = μ.read a := fun a h0 h1 h2 => by
    rw [efr a h0 (by omega) (by omega) (by omega), fin.keep a h0 h1 (by omega)]
  have k5w : ∀ a, M + 24 ≤ a → a < M + 40 → μ5.read a = μ4.read a := fun a h1 h2 =>
    efr a (by omega) (by omega) (by omega) (by omega)
  -- the result, and the return
  obtain ⟨ω6, μ6, run6, f0, f1, f5, f6, fc, fp, fl, ffr, frd, fwr⟩ := t5 (p := p) (P := P) (R := R) x ω5 μ5
    M O cap buf (pre.length + off enc n + 2) ret t r5 r6 (by omega) hO (by omega) e1
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
  refine ⟨ω6, μ6, (run3.trans (run4.trans (run5.trans run6))).mono (by omega),
    f0, f1, f5, f6, fc, fp, fl, ?_,
    fun a h0 h1 h2 h3 => ?_, fun a => by rw [frd, erd, fin.rd], fun a => by rw [fwr, ewr, fin.wr]⟩
  · rw [Memory.readN_congr (fun j hj => ffr _ (by omega) (by omega)), readN_add', ed,
      Memory.readN_congr (fun j hj => efr _ (by omega) (by omega) (by omega) (by omega)), fin.wout, fin.w52]
  · rw [ffr a h0 h2, k5 a h0 (by omega) (by omega)]

/-- **Refine's output encoder, for `EncOkMD 232` elements** (30073): `encode_ok` over a `LayLMD` layout. For
    0 < n < 128 instructions at E, each encoding to `enc j` by `EncOkMD 232`, the encoder writes ℰ(n) = [n]
    (GP v0.8.0 Appendix C), the n encodings and the work item's 2-octet `work_item_index` into the
    buffer, stores the result `{cap, buf, |output|}` at O and returns to `ret`. Memory changes only in the
    stack [M − 232, M + 80), the result and the buffer. -/
theorem encode_okMD {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] (x : X) (ω : Regs) (μ : Memory)
    {M E n buf cap S0 : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Memory → Prop}
    {src : Nat → Nat → Prop}
    (L : LayLMD P p M E n buf cap enc rep src μ) (O ret t r5 r6 : Nat) (hn : 0 < n ∧ n < 128)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cap) (h6 : ω[6] = UInt64.ofNat (232 * n))
    (h7 : ω[7] = UInt64.ofNat buf)
    (s0 : μ.readN M 8 = Num.encodeLE 8 O) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n) (sE : μ.readN (S0 + 8) 8 = Num.encodeLE 8 E)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS0 : S0 + 26 ≤ M - 232 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296)
    (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 8)
    (rS0 : ∀ a, S0 + 8 ≤ a → a < S0 + 26 → μ.readable a = true)
    (hO : O + 24 ≤ 4294967296) (hOM : O + 24 ≤ M - 232 ∨ M + 80 ≤ O) (hOb : O + 24 ≤ buf ∨ buf + cap ≤ O)
    (wO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30073 ω μ x t ω' μ' x (4100 * n + 2000 * off enc n + 1400) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 (off enc n + 3) ∧
      μ'.readN buf (off enc n + 3) = UInt8.ofNat n :: (out enc n ++ μ.readN (S0 + 24) 2) ∧
      (∀ a, a < 4294967296 → (a < M - 232 ∨ M + 80 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        (a < buf ∨ buf + cap ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hcap := L.hcap
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
  have k2 : ∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) →
      (a < buf ∨ buf + [UInt8.ofNat n].length ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 => by
    rw [bfr a h0 (by omega) (by simpa using h2) (by omega), afr a h0 (by omega)]
  have k1w : ∀ a, M + 24 ≤ a → a < M + 40 → μ2.read a = μ1.read a := fun a h1 h2 =>
    bfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, cc, cp, cl, co, cfr, crd, cwr⟩ := restMD (R := R) x ω2 μ μ2
    (pre := [UInt8.ofNat n]) L (by simp; omega) O ret t r5 r6 ⟨hn.1, by omega⟩ b1 b5 b6
    (by rw [Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ac)
    (by rw [Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ap)
    (by simpa using bl) (by simpa using bo) k2
    (fun a => by rw [brd, ard]) (fun a => by rw [bwr, awr])
    s0 s8 s16 sr s5 s6 hr5 hr6 hret hjt hbt hS0 hS0' hS0b rS0 hO hOM hOb wO
  have e3 : [UInt8.ofNat n].length + off enc n + 2 = off enc n + 3 := by simp; omega
  rw [e3] at cl co
  refine ⟨ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), c0, c1, c5, c6, cc, cp, cl, ?_, cfr, crd, cwr⟩
  rw [co]; rfl


/-- **Refine's output encoder, for any number of `EncOkMD` elements** (30073): `EncM.encode_okM` without
    the bound n < 128. For 0 < n < 2^32 instructions at E, each encoding to `enc j` by `EncOkMD`, with the
    buffer's capacity holding everything (`|ℰ(n)| + off + 2 ≤ cap`), the encoder writes ℰ(n) (GP v0.8.0
    Appendix C), the n encodings and the work item's 2-octet `work_item_index` into the buffer, stores the
    result `{cap, buf, |output|}` at O and returns to `ret`. Memory changes only in the stack
    [M − 232, M + 80), the result and the buffer. -/
theorem encode_okMD_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (x : X)
    (ω : Regs) (μ : Memory)
    {M E n buf cap S0 : Nat} {enc : Nat → List UInt8} {rep : Nat → List UInt8 → Memory → Prop}
    {src : Nat → Nat → Prop}
    (L : LayLMD P p M E n buf cap enc rep src μ) (O ret t r5 r6 : Nat) (hn : 0 < n ∧ n < 4294967296)
    (hcapw : (Blob.encodeNat n).length + Loop.off enc n + 2 ≤ cap)
    (h1 : ω[1] = UInt64.ofNat M) (h5 : ω[5] = UInt64.ofNat cap) (h6 : ω[6] = UInt64.ofNat (232 * n))
    (h7 : ω[7] = UInt64.ofNat buf)
    (s0 : μ.readN M 8 = Num.encodeLE 8 O) (s8 : μ.readN (M + 8) 8 = Num.encodeLE 8 S0)
    (s16 : μ.readN (M + 16) 8 = Num.encodeLE 8 n) (sE : μ.readN (S0 + 8) 8 = Num.encodeLE 8 E)
    (sr : μ.readN (M + 72) 8 = Num.encodeLE 8 ret) (s5 : μ.readN (M + 64) 8 = Num.encodeLE 8 r5)
    (s6 : μ.readN (M + 56) 8 = Num.encodeLE 8 r6)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS0 : S0 + 26 ≤ M - 232 ∨ M + 80 ≤ S0) (hS0' : S0 + 26 ≤ 4294967296)
    (hS0b : S0 + 26 ≤ buf ∨ buf + cap ≤ S0 + 8)
    (rS0 : ∀ a, S0 + 8 ≤ a → a < S0 + 26 → μ.readable a = true)
    (hO : O + 24 ≤ 4294967296) (hOM : O + 24 ≤ M - 232 ∨ M + 80 ≤ O) (hOb : O + 24 ≤ buf ∨ buf + cap ≤ O)
    (wO : ∀ a, O ≤ a → a < O + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 30073 ω μ x t ω' μ' x (4100 * n + 2000 * Loop.off enc n + 2500) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (M + 80) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧
      μ'.readN O 8 = Num.encodeLE 8 cap ∧ μ'.readN (O + 8) 8 = Num.encodeLE 8 buf ∧
      μ'.readN (O + 16) 8 = Num.encodeLE 8 ((Blob.encodeNat n).length + Loop.off enc n + 2) ∧
      μ'.readN buf ((Blob.encodeNat n).length + Loop.off enc n + 2) =
        Blob.encodeNat n ++ Loop.out enc n ++ μ.readN (S0 + 24) 2 ∧
      (∀ a, a < 4294967296 → (a < M - 232 ∨ M + 80 ≤ a) → (a < O ∨ O + 24 ≤ a) →
        (a < buf ∨ buf + cap ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨hM0, hM1, hM8⟩ := L.hM
  have hE := L.hE; have hEM := L.hEM; have hbuf := L.hbuf; have hbM := L.hbM; have hcap := L.hcap
  -- the prologue and the count
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, ac, ap, al, a52, afr, ard, awr⟩ := t1 (p := p) (P := P)
    (R := R) x ω μ M buf cap S0 E n (by omega) ⟨by omega, by omega⟩ (by omega) hn.2 h1 h5 h7 s8 s16 (by omega)
    (by omega) sE (by omega) (fun a h1 h2 => L.rM a h1 h2) (fun a h1 h2 => rS0 a h1 (by omega))
    (fun a h1 h2 => L.wM a (by omega) (by omega))
  -- the length prefix ℰ(n)
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, bo, bl, bfr, brd, bwr⟩ := prefix_pos (p := p) (P := P) (R := R)
    x ω1 μ1 M (M + 52) (M + 24) cap buf 0 1416 30122 E (232 * n) n ⟨by omega, by omega, hM8⟩ a0 a1 a5
    (by rw [a6, h6]) a7 a8 (by omega) (by omega) (by omega) (by omega) a52 hn.1
    (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega)) ac (by simpa using ap) (by simpa using al)
    (by omega) hcap.2 (by omega) (by omega) ⟨by omega, by omega⟩ (by omega) (by omega)
    ⟨by decide, by decide, by decide⟩ jte_707 bs_30122
    (fun a h1 h2 => by rw [ard]; exact L.rM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wbuf a (by omega) (by omega))
    (fun a h1 h2 => by rw [awr]; exact L.wM a (by omega) (by omega))
  have k2 : ∀ a, a < 4294967296 → (a < M - 232 ∨ (M ≤ a ∧ a < M + 24) ∨ M + 56 ≤ a) →
      (a < buf ∨ buf + (Blob.encodeNat n).length ≤ a) → μ2.read a = μ.read a := fun a h0 h1 h2 => by
    rw [bfr a h0 (by omega) (by simpa using h2) (by omega), afr a h0 (by omega)]
  have k1w : ∀ a, M + 24 ≤ a → a < M + 40 → μ2.read a = μ1.read a := fun a h1 h2 =>
    bfr a (by omega) (by omega) (by omega) (by omega)
  obtain ⟨ω3, μ3, run3, rest⟩ := restMD (R := R) x ω2 μ μ2 (pre := Blob.encodeNat n) L hcapw O ret t r5 r6
    hn b1 b5 b6
    (by rw [Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ac)
    (by rw [Memory.readN_congr (fun j hj => k1w _ (by omega) (by omega))]; exact ap)
    (by simpa using bl) (by simpa using bo) k2
    (fun a => by rw [brd, ard]) (fun a => by rw [bwr, awr])
    s0 s8 s16 sr s5 s6 hr5 hr6 hret hjt hbt hS0 hS0' hS0b rS0 hO hOM hOb wO
  exact ⟨ω3, μ3, (run1.trans (run2.trans run3)).mono (by omega), rest⟩

end Services.Bootstrap.Encode.EncMD
