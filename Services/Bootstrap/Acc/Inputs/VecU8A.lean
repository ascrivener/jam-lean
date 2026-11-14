import Services.Bootstrap.Acc.Inputs.ReadVecCall
import Services.Bootstrap.Acc.DecodeU32A

/-!
# Accumulate's length-prefixed `Vec<u8>` decoder (39634)

39634 decodes ↕**v** (GP v0.8.0 (C)): the length n by the `u32` decoder (39710,
`decodeU32A`), then n octets by the `Vec<u8>` reader (45643, `rv_call` / `rv_empty`), into a
`Vec<u8>` at `out`; a failed length decode writes −1 at `out`. Here n ≤ 16384, one chunk: a
**temporary** bound, lifted once the realloc impl lemmas take any return address.
-/

namespace Services.Bootstrap.Acc

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.Alloc
  Services.Bootstrap.Decode.HeapCtx

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- **39634 … 39710**: the 24-octet frame (ω₀, ω₅, ω₆ at sp − 8, − 16, − 24), `out` kept in ω₅
    and the reader in ω₆, and the call of the `u32` decoder on the reader (return address 1958). -/
theorem vv_pre {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hsp : 65536 + 24 ≤ sp ∧ sp < 4294967296) (hout : out < 18446744073709551616)
    (hrd : rd < 18446744073709551616)
    (hwf : ∀ a, sp - 24 ≤ a → a < sp → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 39634 ω μ x 39710 ω' μ' x 10 ∧
      ω'[0] = UInt64.ofNat 1958 ∧ ω'[1] = UInt64.ofNat (sp - 24) ∧ ω'[5] = UInt64.ofNat out ∧
      ω'[6] = UInt64.ofNat rd ∧ ω'[7] = UInt64.ofNat rd ∧
      rdN μ' (sp - 8) 8 = ω[0].toNat ∧ rdN μ' (sp - 16) 8 = ω[5].toNat ∧ rdN μ' (sp - 24) 8 = ω[6].toNat ∧
      (∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hr : ∀ a, sp - 24 ≤ a → a < sp → μ.readable a = true :=
    fun a h1 h2 => Memory.readable_of_writable (hwf a h1 h2)
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?μ', ?run, ?post⟩
  case run => pvm_go [h1, h7, h8, hwf, hr, rdN_writeN_disjoint, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha h1 => ?_, fun a => ?_, fun a => ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1, h7, h8]
    all_goals try with_reducible rfl
    all_goals try simp only [show sp - 24 + 16 = sp - 8 from by omega, show sp - 24 + 8 = sp - 16 from by omega,
      show sp - 24 + 0 = sp - 24 from by omega]
    all_goals try first
      | (rd_simp []; done)
      | rd_simp []
    all_goals try first
      | with_reducible rfl
      | exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)
    all_goals first
      | (congr 1; omega)
      | rfl
      | rw [Nat.mod_eq_of_lt (by omega)]

/-- **39656 … 45643**, the length decoded (ω₇ = 0, ω₈ = n < 2³²): the call of the `Vec<u8>` reader
    with ω₇ = out, ω₈ = rd, ω₉ = n (return address 1960). -/
theorem vv_mid {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (out rd n : Nat) (h5 : ω[5] = UInt64.ofNat out) (h6 : ω[6] = UInt64.ofNat rd)
    (h7 : ω[7] = UInt64.ofNat 0) (h8 : ω[8] = UInt64.ofNat n) (hn : n < 4294967296)
    (hout : out < 18446744073709551616) (hrd : rd < 18446744073709551616) :
    ∃ ω', FreeStepsH p R 39656 ω μ x 45643 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat 1960 ∧ ω'[7] = UInt64.ofNat out ∧ ω'[8] = UInt64.ofNat rd ∧
      ω'[9] = UInt64.ofNat n ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h5, h6, h7, h8]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h5, h6, h8]
    all_goals try with_reducible rfl
    all_goals first
      | rfl
      | (congr 1; omega)
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega)])
      | (congr 1; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)])

/-- **45950 … 39708**: the reader's return through entry 979 (1960) to 39697, ω₀, ω₅, ω₆ restored
    from the 24-octet frame and the frame popped, at the return's `jumpInd`. -/
theorem vv_post {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp r0 r5 r6 : Nat) (h0 : ω[0] = UInt64.ofNat 1960) (h1 : ω[1] = UInt64.ofNat sp)
    (m0 : rdN μ sp 8 = r6) (m8 : rdN μ (sp + 8) 8 = r5) (m16 : rdN μ (sp + 16) 8 = r0)
    (hsp : 65536 ≤ sp ∧ sp + 24 < 4294967296) (hr0 : r0 < 18446744073709551616)
    (hr5 : r5 < 18446744073709551616) (hr6 : r6 < 18446744073709551616)
    (hrf : ∀ a, sp ≤ a → a < sp + 24 → μ.readable a = true) :
    ∃ ω', FreeStepsH p R 45950 ω μ x 39708 ω' μ x 10 ∧
      ω'[0] = UInt64.ofNat r0 ∧ ω'[1] = UInt64.ofNat (sp + 24) ∧ ω'[5] = UInt64.ofNat r5 ∧
      ω'[6] = UInt64.ofNat r6 ∧ ω'[7] = ω[7] := by
  rw [show ω = regsNF ω [] from rfl]
  refine ⟨?ω', ?run, ?post⟩
  case run => pvm_go [h0, h1, m0, m8, m16, hrf, ↓rdN_fold, ↓loadI_fold]
  case post =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp (disch := pvm_arith) only [PVM.getElem_regsNF, PVM.lookup_cons_nat, Nat.reduceEqDiff,
      ↓reduceIte, PVM.getD_some', List.lookup_nil, Option.getD_none, h1]
    all_goals first
      | with_reducible rfl
      | rfl
      | (congr 1; omega)


/-- **One call of the length-prefixed `Vec<u8>` decoder for 1 … 16384 octets** on `HeapCtxC`
    (39634 → 39708): the reader (`rd`, at ip with rlen octets left) holds ℰ(n) and then n octets, all
    inside an allocated chunk's data; n ≤ 16384 is the **temporary** one-chunk bound. Either the n
    octets are in a fresh block with `Vec { cap: n, ptr, len: n }` written at `out`, the context
    kept for the model's new state, every allocated chunk's data kept and the reader advanced past
    ℰ(n) and the octets; or the model's `alloc` fails and the run reaches the trap at 45975. -/
theorem vv_call {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (env : HeapHost X)
    (cap : Nat) (hcap1 : 134217728 ≤ cap) (hcap : cap < 18446744073709551616)
    (x : X) (ω : Regs) (μ : Memory) {hb : Nat} (s : State) (sp out rd ip rlen n pb S0 S1 : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s)
    (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out) (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hn : 0 < n ∧ n ≤ 16384) (hrl : (Blob.encodeNat n).length + n ≤ rlen) (hrl32 : rlen < 4294967296)
    (henc : μ.readN ip (Blob.encodeNat n).length = Blob.encodeNat n)
    (hsrc : ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 ≤ ip ∧
      ip + (Blob.encodeNat n).length + n ≤ c.addr + 32 * c.size)
    (hsp : 2147483960 ≤ sp ∧ sp % 8 = 0) (hSTk : S0 + 440 ≤ sp)
    (hout : sp ≤ out ∧ out + 24 ≤ S1) (hrd : sp ≤ rd ∧ rd + 16 ≤ S1)
    (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out) :
    (∃ ptr s' ω' μ', alloc (growTo pb) hb 1 ((n + 31) / 32) s = some (ptr, s') ∧
      FreeStepsH p (env.rel cap) 39634 ω μ x 39708 ω' μ' x (7 * n + 1800) ∧
      HeapCtxC env.code pb S0 S1 μ' s' ∧ (∀ c ∈ chunks s, c.used = true → c ∈ chunks s') ∧
      (⟨ptr - 32, (n + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ ⟨ptr - 32, (n + 31) / 32 + 1, true⟩) ∧
      (∀ c ∈ chunks s, c.used = true → ∀ a, InDataA c a → μ'.read a = μ.read a) ∧
      rdN μ' out 8 = n ∧ rdN μ' (out + 8) 8 = ptr ∧ rdN μ' (out + 16) 8 = n ∧
      μ'.readN ptr n = μ.readN (ip + (Blob.encodeNat n).length) n ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + (Blob.encodeNat n).length + n) ∧
      μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - (Blob.encodeNat n).length - n) ∧
      (∀ a, a < 4294967296 → sp ≤ a → (a < out ∨ out + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (alloc (growTo pb) hb 1 ((n + 31) / 32) s = none ∧ ∃ ω' μ',
      FreeStepsH p (env.rel cap) 39634 ω μ x 45975 ω' μ' x (7 * n + 1800)) := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  have hst := H.st
  obtain ⟨c, hcm, hcu, hci1, hci2⟩ := hsrc
  have hcs := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hcm hcu
  have hbT := H.hbT
  have hb0 := H.hb0
  obtain ⟨w, hw⟩ : ∃ w, (Blob.encodeNat n).length = w := ⟨_, rfl⟩
  rw [hw] at hrl hci2
  -- 1. the frame
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, s8, s16, s24, fr1, rd1, wr1⟩ :=
    vv_pre (p := p) (P := P) (R := env.rel cap) x ω μ sp out rd h1 h7 h8 ⟨by omega, by have := H.hS1; omega⟩
      (by have := H.hS1; omega) (by have := H.hS1; omega) (fun a h1 h2 => hst a (by omega) (by omega))
  have m1 : ∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  -- 2. the length
  obtain ⟨ω2, μ2, r2, d0, d1, -, -, -, d5, d6, -, d7, d8, q0, q8, dfr, drd, dwr⟩ :=
    decodeU32A (p := p) (P := P) (R := env.rel cap) x ω1 μ1 1958 39656 (sp - 24) rd ip rlen a0 a1 a7
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_978]) bs_39656
      ⟨by omega, by have := H.hS1; omega⟩ ⟨by omega, by have := H.hS1; omega⟩ ⟨by omega, by omega⟩
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hst a (by omega) (by omega))
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by have := H.hS1; omega) (by omega))]; exact hR0)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by have := H.hS1; omega) (by omega))]; exact hR8)
      n (by omega) ⟨by omega, hrl32⟩
      (fun a h1 h2 => Memory.readable_of_writable (by
        rw [wr1]; exact heapC_writable_data H hcm hcu ⟨by omega, by omega⟩))
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (Or.inl (by omega)))]; exact henc)
  rw [hw] at q0 q8
  have hS1 := H.hS1
  -- 3. on to the reader
  obtain ⟨ω3, r3, b0, b7, b8, b9, b1, b5, b6⟩ :=
    vv_mid (p := p) (P := P) (R := env.rel cap) x ω2 μ2 out rd n (by rw [d5, a5]) (by rw [d6, a6]) d7 d8
      (by omega) (by omega) (by omega)
  -- the context, carried over the frame and the reader's words (all on the stack)
  have m2 : ∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ2.read a = μ.read a :=
    fun a h1 h2 h3 => by rw [dfr a h1 (by omega) h3, m1 a h1 (by omega)]
  have ww2 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [dwr, wr1]
  have H2 : HeapCtxC env.code pb S0 S1 μ2 s :=
    ⟨H.wf, H.rep.congr_lock H.wf H.hb0 H.hbT fun a _ ha2 _ => m2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega)),
      H.fo, by rw [rdN_frame fun j hj => m2 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))]; exact H.lock,
      H.hb0, H.hbT, H.hA, H.bd, ⟨ph, h48, hhb, HeapPages.of_eq hp ww2, hHTs, hHT⟩, H.hSb, hS1,
      fun a h1 h2 => by rw [ww2]; exact hst a h1 h2, fun a ha => by rw [ww2]; exact H.ro a ha⟩
  -- 4. the reader
  rcases rv_call (p := p) (P := P) (hb := hb) env cap hcap1 hcap x ω3 μ2 s (sp - 24) out rd (ip + w) (rlen - w) n
      pb S0 S1 H2 (by rw [b1, d1, a1]) b7 b8 b9 q0 q8 hn (by omega) (by omega)
      ⟨c, hcm, hcu, by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) ⟨by omega, hout.2⟩ ⟨by omega, hrd.2⟩ dor with
    ⟨ptr, s', ω4, μ4, ha, r4, H4, keep, hnew, hfresh, keepd, g0, g8, g16, gd, gr0, gr8, gfr, e0, e1, e5, e6⟩ |
    ⟨ha, ω4, μ4, r4⟩
  · left
    -- the frame words, from μ1 to μ4
    have f41 : ∀ a, sp - 24 ≤ a → a < sp → μ4.read a = μ1.read a := fun a h1 h2 => by
      rw [gfr a (by omega) h1 (Or.inl (by omega)) (Or.inl (by omega)), dfr a (by omega) (Or.inr h1) (Or.inl (by omega))]
    have l : ∀ o v, sp - 24 ≤ o → o + 8 ≤ sp → rdN μ1 o 8 = v → rdN μ4 o 8 = v := fun o v h1 h2 hv => by
      rw [rdN_frame fun j hj => f41 _ (by omega) (by omega)]; exact hv
    obtain ⟨ω5, r5, f0, f1, f5, f6, -⟩ :=
      vv_post (p := p) (P := P) (R := env.rel cap) x ω4 μ4 (sp - 24) ω[0].toNat ω[5].toNat ω[6].toNat
        (by rw [e0, b0]) (by rw [e1, b1, d1, a1]) (l _ _ (by omega) (by omega) s24)
        (l _ _ (by omega) (by omega) (by rw [show sp - 24 + 8 = sp - 16 by omega]; exact s16))
        (l _ _ (by omega) (by omega) (by rw [show sp - 24 + 16 = sp - 8 by omega]; exact s8))
        ⟨by omega, by omega⟩ (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
        (fun a h1 h2 => Memory.readable_of_writable (by
          have := H4.st a (by omega) (by omega); exact this))
    have dec : ∀ v : UInt64, UInt64.ofNat v.toNat = v := fun v => UInt64.ofNat_toNat
    -- heap memory below 2³¹ is not touched by the frame and the length
    have m2h : ∀ a, a < 2147483648 → μ2.read a = μ.read a := fun a h =>
      m2 a (by omega) (Or.inl (by omega)) (Or.inl (by omega))
    refine ⟨ptr, s', ω5, μ4, ha, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), H4, keep, hnew,
      hfresh, fun c' hc' hu a ha' => ?_, g0, g8, g16, ?_, ?_, ?_, ?_, by rw [f0, dec], ?_, by rw [f5, dec],
      by rw [f6, dec]⟩
    · have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hc' hu
      unfold InDataA at ha'
      rw [keepd c' hc' hu a ⟨ha'.1, ha'.2⟩, m2h a (by omega)]
    · rw [gd, PVM.Memory.readN_congr (μ := μ) (fun j hj => m2h _ (by omega)), hw]
    · rw [gr0, hw]
    · rw [gr8, hw]
    · intro a h0 hs ho hr
      rw [gfr a h0 (by omega) ho hr, m2 a h0 (Or.inr hs) hr]
    · rw [f1, h1]; congr 1; omega
  · exact Or.inr ⟨ha, ω4, μ4, ((((r1.trans r2).trans r3).trans r4)).mono (by omega)⟩


/-- **The length-prefixed `Vec<u8>` decoder for an empty vector** (39634 → 39708): the reader holds
    ℰ(0) = [0]; `Vec { cap: 0, ptr: 1, len: 0 }` is written at `out` and the reader advanced by 1.
    Nothing is allocated: memory changes only below sp (the frames), at `out` and at the reader. -/
theorem vv_empty {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] (x : X) (ω : Regs) (μ : Memory)
    (sp out rd ip rlen : Nat) (h1 : ω[1] = UInt64.ofNat sp) (h7 : ω[7] = UInt64.ofNat out)
    (h8 : ω[8] = UInt64.ofNat rd)
    (hR0 : μ.readN rd 8 = Num.encodeLE 8 ip) (hR8 : μ.readN (rd + 8) 8 = Num.encodeLE 8 rlen)
    (hrl : 1 ≤ rlen) (hrl32 : rlen < 4294967296) (hb0 : μ.readN ip 1 = [0])
    (hip : 65536 ≤ ip ∧ ip < 2147483648) (hra : μ.readable ip = true)
    (hsp : 2147483960 ≤ sp ∧ sp < 4294967296) (hout : sp ≤ out ∧ out + 24 < 4294967296)
    (hrd : sp ≤ rd ∧ rd + 16 < 4294967296) (dor : out + 24 ≤ rd ∨ rd + 16 ≤ out)
    (hwf : ∀ a, sp - 160 ≤ a → a < sp → μ.writable a = true)
    (hwo : ∀ a, out ≤ a → a < out + 24 → μ.writable a = true)
    (hwr : ∀ a, rd ≤ a → a < rd + 16 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 39634 ω μ x 39708 ω' μ' x 600 ∧
      rdN μ' out 8 = 0 ∧ rdN μ' (out + 8) 8 = 1 ∧ rdN μ' (out + 16) 8 = 0 ∧
      μ'.readN rd 8 = Num.encodeLE 8 (ip + 1) ∧ μ'.readN (rd + 8) 8 = Num.encodeLE 8 (rlen - 1) ∧
      (∀ a, a < 4294967296 → (a < sp - 160 ∨ sp ≤ a) → (a < out ∨ out + 24 ≤ a) → (a < rd ∨ rd + 16 ≤ a) →
        μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) ∧
      ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have he : Blob.encodeNat 0 = [0] := by simp [Blob.encodeNat]
  obtain ⟨ω1, μ1, r1, a0, a1, a5, a6, a7, s8, s16, s24, fr1, rd1, wr1⟩ :=
    vv_pre (p := p) (P := P) (R := R) x ω μ sp out rd h1 h7 h8 ⟨by omega, hsp.2⟩ (by omega) (by omega)
      (fun a h1 h2 => hwf a (by omega) h2)
  have m1 : ∀ a, a < 4294967296 → (a < sp - 24 ∨ sp ≤ a) → μ1.read a = μ.read a := fr1
  obtain ⟨ω2, μ2, r2, d0, d1, -, -, -, d5, d6, -, d7, d8, q0, q8, dfr, drd, dwr⟩ :=
    decodeU32A (p := p) (P := P) (R := R) x ω1 μ1 1958 39656 (sp - 24) rd ip rlen a0 a1 a7
      (by decide) (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_978]) bs_39656
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [wr1]; exact hwr a h1 h2)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (by omega))]; exact hR0)
      (by rw [PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by omega) (by omega))]; exact hR8)
      0 (by omega) ⟨by rw [he]; simpa using hrl, hrl32⟩
      (fun a h1 h2 => by rw [he] at h2; simp at h2; rw [rd1, show a = ip by omega]; exact hra)
      (by rw [he, PVM.Memory.readN_congr (μ := μ) (fun j hj => m1 _ (by simp at hj; omega)
        (Or.inl (by simp at hj; omega)))]; exact hb0)
  rw [he] at q0 q8
  simp only [List.length_cons, List.length_nil, Nat.zero_add] at q0 q8
  obtain ⟨ω3, r3, b0, b7, b8, b9, b1, b5, b6⟩ :=
    vv_mid (p := p) (P := P) (R := R) x ω2 μ2 out rd 0 (by rw [d5, a5]) (by rw [d6, a6]) d7 d8
      (by omega) (by omega) (by omega)
  have m2 : ∀ a, a < 4294967296 → (a < sp - 152 ∨ sp ≤ a) → (a < rd ∨ rd + 16 ≤ a) → μ2.read a = μ.read a :=
    fun a h1 h2 h3 => by rw [dfr a h1 (by omega) h3, m1 a h1 (by omega)]
  have ww2 : ∀ a, μ2.writable a = μ.writable a := fun a => by rw [dwr, wr1]
  obtain ⟨ω4, μ4, r4, e0, e1, e5, e6, g0, g8, g16, gfr, grd, gwr⟩ :=
    rv_empty (p := p) (P := P) (R := R) x ω3 μ2 (sp - 24) out rd (by rw [b1, d1, a1]) b7 b8 b9
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [ww2]; exact hwr a h1 h2))
      (fun a h1 h2 => by rw [ww2]; exact hwf a (by omega) (by omega))
      (fun a h1 h2 => by rw [ww2]; exact hwo a h1 h2)
  have f41 : ∀ a, sp - 24 ≤ a → a < sp → μ4.read a = μ1.read a := fun a h1 h2 => by
    rw [gfr a (by omega) (Or.inr h1) (Or.inl (by omega)), dfr a (by omega) (Or.inr h1) (Or.inl (by omega))]
  have l : ∀ o v, sp - 24 ≤ o → o + 8 ≤ sp → rdN μ1 o 8 = v → rdN μ4 o 8 = v := fun o v h1 h2 hv => by
    rw [rdN_frame fun j hj => f41 _ (by omega) (by omega)]; exact hv
  obtain ⟨ω5, r5, f0, f1, f5, f6, -⟩ :=
    vv_post (p := p) (P := P) (R := R) x ω4 μ4 (sp - 24) ω[0].toNat ω[5].toNat ω[6].toNat
      (by rw [e0, b0]) (by rw [e1]) (l _ _ (by omega) (by omega) s24)
      (l _ _ (by omega) (by omega) (by rw [show sp - 24 + 8 = sp - 16 by omega]; exact s16))
      (l _ _ (by omega) (by omega) (by rw [show sp - 24 + 16 = sp - 8 by omega]; exact s8))
      ⟨by omega, by omega⟩ (UInt64.toNat_lt _) (UInt64.toNat_lt _) (UInt64.toNat_lt _)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [gwr, ww2]; exact hwf a (by omega) (by omega)))
  have dec : ∀ v : UInt64, UInt64.ofNat v.toNat = v := fun v => UInt64.ofNat_toNat
  refine ⟨ω5, μ4, ((((r1.trans r2).trans r3).trans r4).trans r5).mono (by omega), g0, g8, g16, ?_, ?_, ?_,
    fun a => by rw [grd, drd, rd1], fun a => by rw [gwr, ww2], by rw [f0, dec], ?_, by rw [f5, dec],
    by rw [f6, dec]⟩
  · rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => gfr _ (by omega) (Or.inr (by omega)) (by omega))]; exact q0
  · rw [PVM.Memory.readN_congr (μ := μ2) (fun j hj => gfr _ (by omega) (Or.inr (by omega)) (by omega))]; exact q8
  · intro a h0 hs ho hr
    rw [gfr a h0 (by omega) ho, m2 a h0 (by omega) hr]
  · rw [f1, h1]; congr 1; omega

end Services.Bootstrap.Acc
