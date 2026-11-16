import Services.Bootstrap.Refine.LookupWrap
import Services.Bootstrap.Refine.ExportSeg
import Services.Bootstrap.Decode.AllocZeroedCall
import Services.Bootstrap.Decode.AllocHuge
import Services.Bootstrap.Decode.VecU8Heap
import Services.Bootstrap.Acc.Handlers.HeapLock

/-!
# `foreign_historical_lookup` composed (5366 … 5372)

From refine's first Ω_H (host 7, GP v0.8.0 Appendix B.4) at 5366, with `foreign_historical_lookup`'s frame G set up
by `Lookup.la`, the run reaches 5372 with the result `Option<Vec<u8>>` at `out` (`ResAt`): `None` (the niche word
2^64 − 1) when Ω_H finds no preimage, else `Some(Vec)` {|d|, buf, |d|} with the preimage d in a fresh chunk (buf = 1
for d = []); or an allocation fails (`Bridge.AllocFails`: `alloc_impl` returns null at 49149, or the size check traps
at 49074 for |d| > 2^37 − 32). Preimages of 2^63 octets or more are excluded (`hlen`): the wrapper traps on them.
-/

namespace Services.Bootstrap.Refine.LookupRun

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeX Services.Bootstrap.CodeR
  Services.Bootstrap.Encode.Writer Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Decode.DeallocCall Services.Bootstrap.Refine.LookupHost
  Services.Bootstrap.Refine.LookupWrap

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The state at refine's first Ω_H (5366): the allocator's context; `foreign_historical_lookup`'s frame G (the
    service id, the hash's address hp, the output address `out`, the saved ω₆, ω₅ and the return address 170 at
    G … G + 48), on the stack with the hash (32 octets at hp) and `out` (24 octets) above it; the registers of the
    length query. -/
structure Pre (env : RefineHost.Env) (pb S0 S1 G svc hp out r5 r6 : Nat) (ω : Regs) (μ : Memory) (s : State) :
    Prop where
  H : HeapCtx env pb S0 S1 μ s
  hG : 2147483800 ≤ G ∧ S0 + 200 ≤ G ∧ G + 48 ≤ hp ∧ hp + 32 ≤ out ∧ out + 24 ≤ S1
  hsvc : svc < 4294967296
  hr5 : r5 < 18446744073709551616
  hr6 : r6 < 18446744073709551616
  h1 : ω[1] = UInt64.ofNat G
  h7 : ω[7] = UInt64.ofNat svc
  h8 : ω[8] = UInt64.ofNat hp
  h9 : ω[9] = UInt64.ofNat 0
  h10 : ω[10] = UInt64.ofNat 0
  h11 : ω[11] = UInt64.ofNat 0
  s0 : μ.readN G 8 = Num.encodeLE 8 svc
  s8 : μ.readN (G + 8) 8 = Num.encodeLE 8 hp
  s16 : μ.readN (G + 16) 8 = Num.encodeLE 8 out
  s24 : μ.readN (G + 24) 8 = Num.encodeLE 8 r6
  s32 : μ.readN (G + 32) 8 = Num.encodeLE 8 r5
  s40 : μ.readN (G + 40) 8 = Num.encodeLE 8 170

/-- The result `Option<Vec<u8>>` at `out` for the preimage v, the heap going from s to s': `None` is the niche word
    2^64 − 1; `Some d` is {|d|, buf, |d|} with buf = 1 for d = [], else buf the data of a fresh allocated chunk of
    ⌈|d|/32⌉ + 1 units of s' holding d. -/
def ResAt (μ : Memory) (out : Nat) (v : Option (List UInt8)) (s s' : State) : Prop :=
  match v with
  | none => μ.readN out 8 = Num.encodeLE 8 18446744073709551615
  | some d => μ.readN out 8 = Num.encodeLE 8 d.length ∧ μ.readN (out + 16) 8 = Num.encodeLE 8 d.length ∧
      ∃ buf, μ.readN (out + 8) 8 = Num.encodeLE 8 buf ∧
        ((d = [] ∧ buf = 1) ∨
         (∃ c ∈ chunks s', c.used = true ∧ c.addr + 32 = buf ∧ c.size = (d.length + 31) / 32 + 1 ∧
           (∀ e ∈ chunks s, e.used = true → e ≠ c) ∧ μ.readN buf d.length = d))

/-- What the wrapper reaches 5372 with: the frame popped (ω₁ = G + 48, ω₅, ω₆ restored), the allocator's context for
    s', every allocated chunk of s kept with its data, the stack from G up kept but for `out`, and the result. -/
def Done (env : RefineHost.Env) (pb S0 S1 G out r5 r6 : Nat) (v : Option (List UInt8)) (μ : Memory) (s : State)
    (ω' : Regs) (μ' : Memory) (s' : State) : Prop :=
  ω'[1] = UInt64.ofNat (G + 48) ∧ ω'[5] = UInt64.ofNat r5 ∧ ω'[6] = UInt64.ofNat r6 ∧
  HeapCtx env pb S0 S1 μ' s' ∧
  (∀ d ∈ chunks s, d.used = true → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
  (∀ a, a < 4294967296 → G ≤ a → (a < out ∨ out + 24 ≤ a) → μ'.read a = μ.read a) ∧
  ResAt μ' out v s s'

theorem reg_of {ω : Regs} {k : Fin 13} {n : Nat} (h : ω[k] = UInt64.ofNat n) (hn : n < 2 ^ 64) : reg ω k = n := by
  unfold reg; rw [show ω.get k = ω[k] from rfl, h, UInt64.toNat_ofNat_of_lt' hn]

/-- The hash is readable for Ω_H: it lies on the stack. -/
theorem Pre.hrd {env : RefineHost.Env} {pb S0 S1 G svc hp out r5 r6 : Nat} {ω : Regs} {μ : Memory} {s : State}
    (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s) : μ.rangeReadable (reg ω 8) 32 = true := by
  have hS := h.H.hS1
  obtain ⟨-, hG1, hG2, hG3, hG4⟩ := h.hG
  rw [reg_of h.h8 (by omega)]
  exact ExportSeg.rangeReadable_of (fun j h1 h2 => Memory.readable_of_writable (h.H.st j (by omega) (by omega)))
    (by omega)

/-- An allocated chunk's data lies below 2^31. -/
theorem data_lo {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State} (H : HeapCtx env pb S0 S1 μ s)
    {d : Chunk} (hd : d ∈ chunks s) (hu : d.used = true) {a : Nat} (ha : InData d a) : a < 2147483648 := by
  have := Decode.VecU8.chunk_in H.wf hd hu
  have := H.hbT
  unfold InData at ha
  omega

/-- **No preimage**: Ω_H returns NONE, and the wrapper stores `None`. -/
theorem lw_none {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : 134217728 ≤ cap ∧ cap < 18446744073709551616) (x : RefineCtx) {pb S0 S1 G svc hp out r5 r6 : Nat}
    {ω : Regs} {μ : Memory} {s : State} (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s)
    (hv : lookupVal env ω μ = none) :
    ∃ ω' μ' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω' μ' x N ∧
      Done env pb S0 S1 G out r5 r6 none μ s ω' μ' s := by
  obtain ⟨hG0, hG1, hG2, hG3, hG4⟩ := h.hG
  have hS := h.H.hS1
  have hsvc := h.hsvc
  have r11 := reg_of (k := 11) h.h11 (by decide)
  have hr7 : lookupR7 env ω μ = 18446744073709551615 := by unfold lookupR7; rw [hv]; rfl
  have hm : lookupMem env ω μ = μ := by unfold lookupMem; rw [hv]
  obtain ⟨ω1, μ1, run1, e1, e5, e6, eo, fr1, rd1, wr1⟩ :=
    wn (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω 18446744073709551615) μ G out r5 r6
      ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) h.hr5 h.hr6
      (by rw [ExportSeg.setR7_getElem ω _ 1 (by decide) (by decide)]; exact h.h1)
      (ExportSeg.setR7_getElem7 ω _) h.s16 h.s24 h.s32 h.s40
      (fun a h1 h2 => Memory.readable_of_writable (h.H.st a (by omega) (by omega)))
      (fun a h1 h2 => h.H.st a (by omega) (by omega))
  have run : FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω1 μ1 x _ :=
    FreeStepsH.lookupRef cap env (by simp [memGas, Constants.CgasHconst, r11]; omega)
      (d_5366 (p := p) (P := P)) (by rw [reg_of h.h7 (by omega)]; omega) h.hrd (fun v hv' => by rw [hv] at hv'; cases hv')
      (by rw [hr7, hm]; exact run1)
  have lo : ∀ a, a < 2147483648 → μ1.read a = μ.read a := fun a ha => fr1 a (by omega) (Or.inl (by omega))
  refine ⟨ω1, μ1, _, run, e1, e5, e6, Decode.GrowOne.ctx_high h.H lo wr1, fun d hd hu => ⟨hd, fun a ha =>
    lo a (data_lo h.H hd hu ha)⟩, fun a h0 _ ha => fr1 a h0 (by omega), eo⟩

/-- Ω_H's preimage depends only on ω₇, ω₈ and the hash's octets. -/
theorem lookupVal_congr {env : RefineHost.Env} {ω ω' : Regs} {μ μ' : Memory} (h7 : reg ω' 7 = reg ω 7)
    (h8 : reg ω' 8 = reg ω 8) (hh : μ'.readN (reg ω 8) 32 = μ.readN (reg ω 8) 32) :
    lookupVal env ω' μ' = lookupVal env ω μ := by
  unfold lookupVal; rw [h7, h8, hh]

/-- **The empty preimage**: Ω_H returns 0; the wrapper makes Ω_H again with the dangling buffer 1 and stores
    `Some(Vec)` {0, 1, 0}. -/
theorem lw_zero {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : 134217728 ≤ cap ∧ cap < 18446744073709551616) (x : RefineCtx) {pb S0 S1 G svc hp out r5 r6 : Nat}
    {ω : Regs} {μ : Memory} {s : State} (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s)
    (hv : lookupVal env ω μ = some []) :
    ∃ ω' μ' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω' μ' x N ∧
      Done env pb S0 S1 G out r5 r6 (some []) μ s ω' μ' s := by
  obtain ⟨hG0, hG1, hG2, hG3, hG4⟩ := h.hG
  have hS := h.H.hS1
  have hsvc := h.hsvc
  have r11 := reg_of (k := 11) h.h11 (by decide)
  have hr7 : lookupR7 env ω μ = 0 := by unfold lookupR7; rw [hv]; rfl
  have hm : lookupMem env ω μ = μ := by unfold lookupMem; rw [hv]; simp [Memory.writeN_nil]
  obtain ⟨ω2, run2, f1, f5, f6, f7, f8, f9, f10, f11⟩ :=
    wz (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω 0) μ G svc hp (by omega) (by omega) (by omega)
      (by rw [ExportSeg.setR7_getElem ω _ 1 (by decide) (by decide)]; exact h.h1)
      (ExportSeg.setR7_getElem7 ω _) h.s0 h.s8
      (fun a h1 h2 => Memory.readable_of_writable (h.H.st a (by omega) (by omega)))
  have hv2 : lookupVal env ω2 μ = some [] := by
    exact (lookupVal_congr (ω := ω) (ω' := ω2) ((reg_of f7 (by omega)).trans (reg_of h.h7 (by omega)).symm)
      ((reg_of f8 (by omega)).trans (reg_of h.h8 (by omega)).symm) rfl).trans hv
  have hr72 : lookupR7 env ω2 μ = 0 := by unfold lookupR7; rw [hv2]; rfl
  have hm2 : lookupMem env ω2 μ = μ := by unfold lookupMem; rw [hv2]; simp [Memory.writeN_nil]
  obtain ⟨ω3, μ3, run3, e1, e5, e6, o0, o8, o16, fr3, rd3, wr3⟩ :=
    wr (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω2 0) μ G out r5 r6 0 1 ⟨by omega, by omega⟩
      (by omega) (Or.inr (by omega)) h.hr5 h.hr6 (by decide) (by decide)
      (by rw [ExportSeg.setR7_getElem ω2 _ 1 (by decide) (by decide), f1,
        ExportSeg.setR7_getElem ω _ 1 (by decide) (by decide)]; exact h.h1)
      (by rw [ExportSeg.setR7_getElem ω2 _ 5 (by decide) (by decide)]; exact f5)
      (by rw [ExportSeg.setR7_getElem ω2 _ 6 (by decide) (by decide)]; exact f6)
      h.s16 h.s24 h.s32 h.s40
      (fun a h1 h2 => Memory.readable_of_writable (h.H.st a (by omega) (by omega)))
      (fun a h1 h2 => h.H.st a (by omega) (by omega))
  have rd2 : μ.rangeReadable (reg ω2 8) 32 = true := by
    rw [reg_of f8 (by omega)]; have := h.hrd; rwa [reg_of h.h8 (by omega)] at this
  have run : FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω3 μ3 x _ :=
    FreeStepsH.lookupRef cap env (by simp [memGas, Constants.CgasHconst, r11]; omega)
      (d_5366 (p := p) (P := P)) (by rw [reg_of h.h7 (by omega)]; omega) h.hrd
      (fun v hv' => by rw [hv] at hv'; cases hv'; simp [Memory.rangeWritable])
      (by rw [hr7, hm]; exact run2.trans (FreeStepsH.lookupRef cap env
        (by simp [memGas, Constants.CgasHconst, reg_of (k := 11) f11 (by decide)]; omega)
        (d_49174 (p := p) (P := P)) (by rw [reg_of f7 (by omega)]; omega) rd2
        (fun v hv' => by rw [hv2] at hv'; cases hv'; simp [Memory.rangeWritable])
        (by rw [hr72, hm2]; exact run3)))
  have lo : ∀ a, a < 2147483648 → μ3.read a = μ.read a := fun a ha => fr3 a (by omega) (Or.inl (by omega))
  refine ⟨ω3, μ3, _, run, e1, e5, e6, Decode.GrowOne.ctx_high h.H lo wr3, fun d hd hu => ⟨hd, fun a ha =>
    lo a (data_lo h.H hd hu ha)⟩, fun a h0 _ ha => fr3 a h0 ha, ?_⟩
  exact ⟨by simpa using o0, by simpa using o16, 1, o8, .inl ⟨rfl, rfl⟩⟩

/-- A range of writable octets passes `rangeWritable`'s page check (as `Fmt.rangeWritable_of`). -/
theorem rangeWritable_of {μ : Memory} {o n : Nat} (hn : o + n ≤ 2 ^ 32)
    (hw : ∀ a, o ≤ a → a < o + n → μ.writable a = true) : μ.rangeWritable o n = true := by
  unfold Memory.rangeWritable
  by_cases h0 : n = 0
  · simp [h0]
  simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true, decide_eq_true_eq, hn, true_and,
    List.all_eq_true, List.mem_range]
  intro k hk
  have hps : pageSize = 4096 := rfl
  have e : ((o / pageSize + k) * pageSize) / pageSize = (max o ((o / pageSize + k) * pageSize)) / pageSize := by
    rw [hps] at hk ⊢
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [Nat.add_zero]
      rw [Nat.max_def]; split <;> omega
    · rw [Nat.max_def]; split <;> omega
  have hw' := hw (max o ((o / pageSize + k) * pageSize)) (Nat.le_max_left _ _) (by
    rw [hps] at hk ⊢; rw [Nat.max_def]; split <;> omega)
  unfold Memory.writable at hw' ⊢
  rw [e]; exact hw'

/-- Memory read off the octets just written. -/
theorem read_writeN_off {μ : Memory} {o a : Nat} {bs : List UInt8} (ho : o + bs.length ≤ 4294967296)
    (ha : a < 4294967296) (hoa : a < o ∨ o + bs.length ≤ a) : (μ.writeN o bs).read a = μ.read a :=
  Memory.read_writeN_of_not_mem _ _ _ _ (fun k hk => by
    simp only [two32]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt ha]; omega)

/-- **A preimage too long for the size check** (2^37 − 32 < |d| < 2^63): the wrapper traps at 49074
    (`Bridge.sizeTrap`). -/
theorem lw_big {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : 134217728 ≤ cap ∧ cap < 18446744073709551616) (x : RefineCtx) {pb S0 S1 G svc hp out r5 r6 : Nat}
    {ω : Regs} {μ : Memory} {s : State} (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s) {d : List UInt8}
    (hv : lookupVal env ω μ = some d) (hd1 : 137438953440 < d.length) (hd2 : d.length < 9223372036854775808) :
    ∃ j ω' μ' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x j ω' μ' x N ∧ Bridge.AllocFails j ω' := by
  have hsvc := h.hsvc
  have r11 := reg_of (k := 11) h.h11 (by decide)
  have hr7 : lookupR7 env ω μ = d.length := by unfold lookupR7; rw [hv]
  obtain ⟨ω1, run1⟩ := wbig (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω d.length) (lookupMem env ω μ)
    d.length hd1 hd2 (ExportSeg.setR7_getElem7 ω _)
  refine ⟨49074, ω1, _, _, FreeStepsH.lookupRef cap env (by simp [memGas, Constants.CgasHconst, r11]; omega)
      (d_5366 (p := p) (P := P)) (by rw [reg_of h.h7 (by omega)]; omega) h.hrd
      (fun v hv' => by rw [hv] at hv'; cases hv'; simp [r11, Memory.rangeWritable])
      (by rw [hr7]; exact run1), .inr rfl⟩

/-- After the length query (ω₁₁ = 0) memory is unchanged. -/
theorem Pre.mem0 {env : RefineHost.Env} {pb S0 S1 G svc hp out r5 r6 : Nat} {ω : Regs} {μ : Memory} {s : State}
    (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s) : lookupMem env ω μ = μ := by
  have r11 := reg_of (k := 11) h.h11 (by decide)
  unfold lookupMem
  split <;> simp [r11]

/-- The heap's writable region for the allocator's lock steps. -/
theorem wrAt_of {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State} (H : HeapCtx env pb S0 S1 μ s) :
    ∃ HT, 206864 ≤ HT ∧ WrAt μ HT S0 S1 := by
  obtain ⟨ph, h48, hhb, hp, hHTs, hHT⟩ := H.pages
  exact ⟨4096 * ph, by omega, HeapPages.wrAt hp hhb H.st⟩

/-- **A preimage of ⌈|d|/32⌉ ≥ 2^31 units** (|d| ≤ 2^37 − 32): `alloc_impl` gets the sign-extended request and returns
    null (49149, `Bridge.allocRets`). -/
theorem lw_huge {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : 134217728 ≤ cap ∧ cap < 18446744073709551616) (x : RefineCtx) {pb S0 S1 G svc hp out r5 r6 : Nat}
    {ω : Regs} {μ : Memory} {s : State} (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s) {d : List UInt8}
    (hv : lookupVal env ω μ = some d) (hd1 : d.length ≤ 137438953440) (hu : 2147483648 ≤ (d.length + 31) / 32) :
    ∃ j ω' μ' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x j ω' μ' x N ∧ Bridge.AllocFails j ω' := by
  obtain ⟨hG0, hG1, hG2, hG3, hG4⟩ := h.hG
  have hS := h.H.hS1
  have hsvc := h.hsvc
  have r11 := reg_of (k := 11) h.h11 (by decide)
  have hr7 : lookupR7 env ω μ = d.length := by unfold lookupR7; rw [hv]
  obtain ⟨HT, hHT, hwr⟩ := wrAt_of h.H
  obtain ⟨ω2, μ2, run2, e1, e0, e5, e6, e7, e8, e9, e10, fr2, wr2⟩ :=
    wlh (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω d.length) μ d.length (by omega) hd1 hu
      (ExportSeg.setR7_getElem7 ω _) h.H.lock hHT hwr
  have HL : HeapCtxL env.code pb S0 S1 μ2 s := ⟨μ, h.H, fun a ha h1 h2 => fr2 a ha h1 h2, wr2⟩
  have e1' : ω2[1] = UInt64.ofNat G := by
    rw [e1, ExportSeg.setR7_getElem ω _ 1 (by decide) (by decide)]; exact h.h1
  obtain ⟨s3, ω3, μ3, run3, e7', -⟩ := Decode.AllocHuge.alloc_impl_huge_callG (p := p) (P := P) (refineHeap env)
    cap hcap.1 hcap.2 x ω2 μ2 s G _ 1 2184 49149 pb S0 S1 HL e1' e7 e8 e9 e10 (by decide) e0
    ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1091]) bs_49149
    (by omega) (by omega) (by omega) hG0 ⟨by omega, by omega⟩
  refine ⟨49149, ω3, μ3, _, FreeStepsH.lookupRef cap env (by simp [memGas, Constants.CgasHconst, r11]; omega)
      (d_5366 (p := p) (P := P)) (by rw [reg_of h.h7 (by omega)]; omega) h.hrd
      (fun v hv' => by rw [hv] at hv'; cases hv'; simp [r11, Memory.rangeWritable])
      (by rw [hr7, h.mem0]; exact run2.trans run3), .inl ⟨by decide, e7'⟩⟩

/-- **A preimage that fits the size check** (1 ≤ |d|, ⌈|d|/32⌉ < 2^31 units): the lock taken, `alloc_impl` for ⌈|d|/32⌉
    units; on a block, the lock cleared, Ω_H again into the block, and `Some(Vec)` {|d|, buf, |d|} stored; on null, an
    allocation failure at 49149. -/
theorem lw_alloc {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : 134217728 ≤ cap ∧ cap < 18446744073709551616) (x : RefineCtx) {pb S0 S1 G svc hp out r5 r6 : Nat}
    {ω : Regs} {μ : Memory} {s : State} (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s) {d : List UInt8}
    (hv : lookupVal env ω μ = some d) (hd0 : d ≠ []) (hu : (d.length + 31) / 32 < 2147483648)
    (hgas : Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap) :
    (∃ ω' μ' s' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω' μ' x N ∧
      Done env pb S0 S1 G out r5 r6 (some d) μ s ω' μ' s') ∨
    ∃ j ω' μ' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x j ω' μ' x N ∧ Bridge.AllocFails j ω' := by
  obtain ⟨hG0, hG1, hG2, hG3, hG4⟩ := h.hG
  have hS := h.H.hS1
  have hsvc := h.hsvc
  have r11 := reg_of (k := 11) h.h11 (by decide)
  have hL0 : d.length ≠ 0 := fun e => hd0 (List.eq_nil_of_length_eq_zero e)
  have hL1 : d.length ≤ 137438953440 := by omega
  have hr7 : lookupR7 env ω μ = d.length := by unfold lookupR7; rw [hv]
  obtain ⟨HT, hHT, hwr⟩ := wrAt_of h.H
  obtain ⟨ω2, μ2, run2, e1, e0, e5, e6, e7, e8, e9, e10, fr2, wr2⟩ :=
    wl (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω d.length) μ d.length hL0 hL1 hu
      (ExportSeg.setR7_getElem7 ω _) h.H.lock hHT hwr
  have HL : HeapCtxL env.code pb S0 S1 μ2 s := ⟨μ, h.H, fun a ha h1 h2 => fr2 a ha h1 h2, wr2⟩
  have e1' : ω2[1] = UInt64.ofNat G := by
    rw [e1, ExportSeg.setR7_getElem ω _ 1 (by decide) (by decide)]; exact h.h1
  have run1 : FreeStepsH p (refineContractK cap env) 5366 ω μ x 5368 (setR7 ω d.length) μ x 1 :=
    FreeStepsH.lookupRef cap env (by simp [memGas, Constants.CgasHconst, r11]; omega)
      (d_5366 (p := p) (P := P)) (by rw [reg_of h.h7 (by omega)]; omega) h.hrd
      (fun v hv' => by rw [hv] at hv'; cases hv'; simp [r11, Memory.rangeWritable])
      (by rw [hr7, h.mem0]; exact .refl)
  rcases Decode.AllocZeroedCall.alloc_implZ_callG (p := p) (P := P) (hb := 0) (refineHeap env) cap hcap.1 hcap.2 x ω2 μ2 s G
      ((d.length + 31) / 32) 1 2184 49149 pb S0 S1 HL e1' e7 e8 e9 e10 (by decide) e0
      ⟨by decide, by decide, by decide⟩ (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_1091]) bs_49149
      (by omega) hu hG0 ⟨by omega, by omega⟩ with
    ⟨ptr, s', ω4, μ4, -, run4, HL4, keep4, hnew, hfresh, -, keepd4, e7', stk4, f0, f1, f5, f6⟩ |
    ⟨-, ω4, μ4, run4, e7', -⟩
  rotate_left
  · exact .inr ⟨49149, ω4, μ4, _, run1.trans (run2.trans run4), .inl ⟨by decide, e7'⟩⟩
  left
  have HL4' := HL4
  obtain ⟨μ₀, H₀, hag, hwa⟩ := HL4'
  obtain ⟨Nb1, Nb2, Nb3⟩ := Decode.VecU8.chunk_in H₀.wf hnew rfl
  dsimp only at Nb1 Nb2 Nb3
  have hb0' := H₀.hb0
  have hbT' := H₀.hbT
  obtain ⟨ph', h48', hhb', hp', hHTs', hHT'⟩ := H₀.pages
  have hwl : μ4.writable 206848 = true := by
    rw [hwa]; exact HeapPages.wrAt hp' hhb' H₀.st 206848 (Or.inl ⟨by omega, by omega⟩)
  have hLu : d.length ≤ 32 * ((d.length + 31) / 32) := by omega
  -- μ4 against μ on the stack from G up
  have k4 : ∀ a, a < 4294967296 → G ≤ a → μ4.read a = μ.read a := fun a h0 ha => by
    rw [stk4 a h0 ha, fr2 a h0 (Or.inr (by omega)) (Or.inr (by omega))]
  have kr4 : ∀ o n, G ≤ o → o + n ≤ 4294967296 → μ4.readN o n = μ.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => k4 _ (by omega) (by omega)
  obtain ⟨ω5, μ5, run5, u1, u5, u6, u7, u8, u9, u10, u11, lock5, fr5, wr5⟩ :=
    wu (p := p) (P := P) (R := refineContractK cap env) x ω4 μ4 G svc hp ptr d.length ⟨by omega, by omega⟩
      (by omega) (by omega) (by omega) (by omega) (by omega) (f1.trans e1') (f5.trans e5) (f6.trans e6) e7'
      (by rw [kr4 G 8 (by omega) (by omega)]; exact h.s0) (by rw [kr4 (G + 8) 8 (by omega) (by omega)]; exact h.s8)
      (fun a h1 h2 => Memory.readable_of_writable (by rw [hwa]; exact H₀.st a (by omega) (by omega))) hwl
  have H5 : HeapCtx env pb S0 S1 μ5 s' :=
    Acc.Handlers.HeapLock.HeapCtxL.unlock HL4 (fun a ha h1 h2 => fr5 a ha (by omega)) wr5 lock5
  have k5 : ∀ a, a < 4294967296 → 206848 < a → μ5.read a = μ4.read a := fun a h0 ha => fr5 a h0 (by omega)
  -- the second Ω_H
  have hv5 : lookupVal env ω5 μ5 = some d := by
    refine (lookupVal_congr (ω := ω) (ω' := ω5) ((reg_of u7 (by omega)).trans (reg_of h.h7 (by omega)).symm)
      ((reg_of u8 (by omega)).trans (reg_of h.h8 (by omega)).symm) ?_).trans hv
    rw [reg_of h.h8 (by omega)]
    exact Memory.readN_congr fun j hj => by rw [k5 _ (by omega) (by omega), k4 _ (by omega) (by omega)]
  have q9 := reg_of (k := 9) u9 (show ptr < 2 ^ 64 by omega)
  have q10 := reg_of (k := 10) u10 (by decide)
  have q11 := reg_of (k := 11) u11 (show d.length < 2 ^ 64 by omega)
  have hr75 : lookupR7 env ω5 μ5 = d.length := by unfold lookupR7; rw [hv5]
  have hm5 : lookupMem env ω5 μ5 = μ5.writeN ptr d := by
    unfold lookupMem; rw [hv5]; simp [q9, q10, q11]
  have hwp : ∀ a, ptr ≤ a → a < ptr + d.length → μ5.writable a = true := fun a h1 h2 =>
    Decode.VecU8.heap_writable H5 hnew rfl ⟨by dsimp only; omega, by dsimp only; omega⟩
  have rd5 : μ5.rangeReadable (reg ω5 8) 32 = true := by
    rw [reg_of u8 (by omega)]
    exact ExportSeg.rangeReadable_of (fun j h1 h2 => Memory.readable_of_writable (H5.st j (by omega) (by omega)))
      (by omega)
  -- the store into the block
  have kW : ∀ a, a < 4294967296 → (a < ptr ∨ ptr + d.length ≤ a) → (μ5.writeN ptr d).read a = μ5.read a :=
    fun a h0 ha => read_writeN_off (by omega) h0 ha
  have H6 : HeapCtx env pb S0 S1 (μ5.writeN ptr d) s' :=
    Decode.VecU8.ctx_congr_data H5 hnew (fun a h0 ha => kW a (by omega) (by dsimp only at ha; omega))
      (fun a => Memory.writable_writeN _ _ _ _)
  have k6 : ∀ a, a < 4294967296 → G ≤ a → (μ5.writeN ptr d).read a = μ.read a := fun a h0 ha => by
    rw [kW a h0 (Or.inr (by omega)), k5 a h0 (by omega), k4 a h0 ha]
  have kr6 : ∀ o n, G ≤ o → o + n ≤ 4294967296 → (μ5.writeN ptr d).readN o n = μ.readN o n := fun o n h1 h2 =>
    Memory.readN_congr fun j hj => k6 _ (by omega) (by omega)
  obtain ⟨ω7, μ7, run7, g1, g5, g6, o0, o8, o16, fr7, rd7, wr7⟩ :=
    wr (p := p) (P := P) (R := refineContractK cap env) x (setR7 ω5 d.length) (μ5.writeN ptr d) G out r5 r6
      d.length ptr ⟨by omega, by omega⟩ (by omega) (Or.inr (by omega)) h.hr5 h.hr6 (by omega) (by omega)
      (by rw [ExportSeg.setR7_getElem ω5 _ 1 (by decide) (by decide), u1, f1]; exact e1')
      (by rw [ExportSeg.setR7_getElem ω5 _ 5 (by decide) (by decide), u5, f5]; exact e5)
      (by rw [ExportSeg.setR7_getElem ω5 _ 6 (by decide) (by decide)]; exact u6)
      (by rw [kr6 _ 8 (by omega) (by omega)]; exact h.s16) (by rw [kr6 _ 8 (by omega) (by omega)]; exact h.s24)
      (by rw [kr6 _ 8 (by omega) (by omega)]; exact h.s32) (by rw [kr6 _ 8 (by omega) (by omega)]; exact h.s40)
      (fun a h1 h2 => by rw [Memory.readable_writeN]; exact Memory.readable_of_writable (H5.st a (by omega) (by omega)))
      (fun a h1 h2 => by rw [Memory.writable_writeN]; exact H5.st a (by omega) (by omega))
  have run : FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω7 μ7 x _ :=
    run1.trans (run2.trans (run4.trans (run5.trans (FreeStepsH.lookupRef cap env
      (by rw [q11]; exact ⟨hgas, hcap.2⟩) (d_49174 (p := p) (P := P)) (by rw [reg_of u7 (by omega)]; omega) rd5
      (fun v hv' => by
        rw [hv5] at hv'; cases hv'
        rw [q9, q10, q11]; simp only [Nat.zero_min, Nat.sub_zero, Nat.min_self]
        exact rangeWritable_of (by omega) hwp)
      (by rw [hr75, hm5]; exact run7)))))
  have lo7 : ∀ a, a < 2147483648 → μ7.read a = (μ5.writeN ptr d).read a := fun a ha =>
    fr7 a (by omega) (Or.inl (by omega))
  refine ⟨ω7, μ7, s', _, run, g1, g5, g6, Decode.GrowOne.ctx_high H6 lo7 wr7, fun c hc hu => ⟨keep4 c hc hu,
    fun a ha => ?_⟩, fun a h0 ha hao => by rw [fr7 a h0 hao, k6 a h0 ha], ?_⟩
  · have hal := data_lo h.H hc hu ha
    have hne := hfresh c hc hu
    have hdj := Decode.VecU8.data_disj H5.wf (keep4 c hc hu) hnew hne ha
    have := Decode.VecU8.chunk_in h.H.wf hc hu
    have := h.H.hb0
    unfold InData at ha
    dsimp only at hdj
    rw [lo7 a hal, kW a (by omega) (by omega), k5 a (by omega) (by omega), keepd4 c hc hu a ha.1 ha.2,
      fr2 a (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
  · refine ⟨o0, o16, ptr, o8, .inr ⟨_, hnew, rfl, by dsimp only; omega, rfl, hfresh, ?_⟩⟩
    rw [Memory.readN_congr (μ := μ5.writeN ptr d) fun j hj => lo7 _ (by omega)]
    exact Memory.readN_writeN_same _ _ _ _ rfl (by simp only [two32]; omega)

/-- **`foreign_historical_lookup`, 5366 … 5372**: from refine's length query (`Pre`), for a preimage shorter than
    2^63 octets (`hlen`; the wrapper traps on longer ones) and a cap covering the second Ω_H's charge (`hgas`), the
    run reaches 5372 with the result at `out` (`Done`, `ResAt` of `lookupVal`), or an allocation fails
    (`Bridge.AllocFails`). -/
theorem lookup_wrap {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeR p P] (env : RefineHost.Env)
    (cap : Nat) (hcap : 134217728 ≤ cap ∧ cap < 18446744073709551616) (x : RefineCtx) {pb S0 S1 G svc hp out r5 r6 : Nat}
    {ω : Regs} {μ : Memory} {s : State} (h : Pre env pb S0 S1 G svc hp out r5 r6 ω μ s)
    (hlen : ∀ d, lookupVal env ω μ = some d → d.length < 9223372036854775808)
    (hgas : ∀ d, lookupVal env ω μ = some d → Constants.CgasHconst + memGas Constants.CgasHlinear d.length ≤ cap) :
    (∃ ω' μ' s' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x 5372 ω' μ' x N ∧
      Done env pb S0 S1 G out r5 r6 (lookupVal env ω μ) μ s ω' μ' s') ∨
    ∃ j ω' μ' N, FreeStepsH p (refineContractK cap env) 5366 ω μ x j ω' μ' x N ∧ Bridge.AllocFails j ω' := by
  cases hv : lookupVal env ω μ with
  | none =>
    obtain ⟨ω', μ', N, run, hd⟩ := lw_none (p := p) (P := P) env cap hcap x h hv
    exact .inl ⟨ω', μ', s, N, run, hd⟩
  | some d =>
    rcases d with _ | ⟨b, d'⟩
    · obtain ⟨ω', μ', N, run, hd⟩ := lw_zero (p := p) (P := P) env cap hcap x h hv
      exact .inl ⟨ω', μ', s, N, run, hd⟩
    · have h63 := hlen _ hv
      by_cases hbig : 137438953440 < (b :: d').length
      · exact .inr (lw_big (p := p) (P := P) env cap hcap x h hv hbig h63)
      by_cases hhu : 2147483648 ≤ ((b :: d').length + 31) / 32
      · exact .inr (lw_huge (p := p) (P := P) env cap hcap x h hv (by omega) hhu)
      exact lw_alloc (p := p) (P := P) env cap hcap x h hv (by simp) (by omega) (hgas _ hv)

end Services.Bootstrap.Refine.LookupRun
