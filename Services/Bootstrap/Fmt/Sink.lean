import Services.Bootstrap.Fmt.Frame
import Services.Bootstrap.Fmt.WriteStr
import Services.Bootstrap.Fmt.Reserve
import Services.Bootstrap.Fmt.Memcpy
import Services.Bootstrap.Decode.VecU8Heap

/-!
# The `String` sink: `write_str`, frame-only
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- 59989 … 60028, n > 0: the copy into the buffer and the return. From the `String` W's buffer ptr
    and length len (ω₉), `memcpy` puts the n octets at src at ptr + len, then the length len + n goes
    to W + 16 and `write_str` returns `Ok` to its caller. Memory changes only in S − 48 … S + 8 (the
    frames), the n octets at ptr + len and W + 16 … W + 24. -/
theorem ws_copytail {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (S W n len ptr src ret t v5 v6 : Nat) (hS : 65536 + 48 ≤ S ∧ S + 32 < 4294967296 ∧ S % 8 = 0)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat W)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat len) (hn : 0 < n)
    (hp : rdN μ (W + 8) 8 = ptr) (hb : 65536 ≤ ptr ∧ ptr + len + n + 16 < 4294967296)
    (hs : 65536 ≤ src ∧ src + n + 16 < 4294967296)
    (hW : S + 32 ≤ W ∧ W + 24 < 4294967296)
    (hdj : ptr + len + n + 24 ≤ src ∨ src + n + 24 ≤ ptr + len)
    (hfd : ptr + len + n ≤ S - 48) (hfs : S + 8 ≤ src ∨ src + n + 16 ≤ S - 48)
    (hsW : src + n ≤ W ∨ W + 24 ≤ src)
    (r0 : rdN μ (S + 24) 8 = ret) (r5 : rdN μ (S + 16) 8 = v5) (r6 : rdN μ (S + 8) 8 = v6)
    (hv5 : v5 < 18446744073709551616) (hv6 : v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0)
    (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t) (hbt : P.isBlockStart t = true)
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true)
    (hwb : ∀ a, ptr + len ≤ a → a < ptr + len + n → μ.writable a = true)
    (hws : ∀ a, S - 48 ≤ a → a < S + 32 → μ.writable a = true)
    (hWw : ∀ a, W ≤ a → a < W + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 59989 ω μ x t ω' μ' x (7 * n + 340) ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat (S + 32) ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧ rdN μ' (W + 16) 8 = n + len ∧
      (∀ a, a < 4294967296 → (a < S - 48 ∨ S + 8 ≤ a) → (a < ptr + len ∨ ptr + len + n ≤ a) →
        (a < W + 16 ∨ W + 24 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  have hrs : ∀ a, S - 48 ≤ a → a < S + 32 → μ.readable a = true := fun a h1 h2 => Memory.readable_of_writable (hws a h1 h2)
  -- the copy's set-up
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9⟩ := ws_copy (p := p) (P := P) (R := R) x ω μ S W n len ptr
    ⟨by omega, by omega⟩ h1 h5 h6 h9 (by omega) (by omega) hp (by omega) (by omega) (by omega)
    (fun a h1 h2 => Memory.readable_of_writable (hWw a h1 h2)) (fun a h1 h2 => hws a (by omega) (by omega))
  generalize hM1 : μ.writeN S (Num.encodeLE 8 len) = μ1 at run1
  have m1 : ∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ1.read a = μ.read a := fun a ha0 ha1 => by
    rw [← hM1, Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
      (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega)]
  have w1 : ∀ a, μ1.writable a = μ.writable a := fun a => by rw [← hM1, Memory.writable_writeN]
  have d1 : ∀ a, μ1.readable a = μ.readable a := fun a => by rw [← hM1, Memory.readable_writeN]
  -- `memcpy`
  obtain ⟨ω2, μ2, run2, b0, b1, b5, b6, fr2, rd2, wr2⟩ := memcpy_frame (p := p) (P := P) (R := R) x ω1 μ1
    2598 60005 S (ptr + len) src n a0 (a1.trans h1) a7 (a8.trans h8) a9 (by decide) jte_1298 bs_60005
    ⟨by omega, by omega, hS.2.2⟩ hs (by omega) (by omega) (Or.inr hfd) hfs
    (fun a h1 h2 => by rw [d1]; exact hr a h1 h2) (fun a h1 h2 => by rw [w1]; exact hwb a h1 h2)
    (fun a h1 h2 => by rw [w1]; exact hws a h1 (by omega))
  -- the length reloaded and stored, the return
  have rl2 : rdN μ2 S 8 = len := by
    rw [rdN_frame (fun j hj => fr2 _ (by omega) (by omega) (Or.inr (by omega)))]
    rw [← hM1]; unfold rdN
    rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega), Num.decodeLE_encodeLE,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨ω3, run3, c9, c1, c5, c6⟩ := ws_tail (p := p) (P := P) (R := R) x ω2 μ2 S len ⟨by omega, by omega⟩
    (b1.trans (a1.trans h1)) rl2 (fun a h1 h2 => by rw [rd2, d1]; exact hrs a (by omega) (by omega))
  have keep2 : ∀ a, S + 8 ≤ a → a < S + 32 → μ2.read a = μ.read a := fun a h1 h2 => by
    rw [fr2 _ (by omega) (by omega) (Or.inr (by omega)), m1 a (by omega) (Or.inr h1)]
  obtain ⟨ω4, run4, e0, e1, e5, e6, e7⟩ := ws_fin (p := p) (P := P) (R := R) x ω3 μ2 S W n len ret t v5 v6
    ⟨by omega, by omega⟩ (c1.trans (b1.trans (a1.trans h1))) (c5.trans (b5.trans (a5.trans h5)))
    (c6.trans (b6.trans (a6.trans h6))) c9 (by omega) (by omega) (Or.inr (by omega))
    (fun a h1 h2 => by rw [wr2, w1]; exact hWw a (by omega) h2)
    (by rw [rdN_frame (fun j hj => keep2 _ (by omega) (by omega))]; exact r0)
    (by rw [rdN_frame (fun j hj => keep2 _ (by omega) (by omega))]; exact r5)
    (by rw [rdN_frame (fun j hj => keep2 _ (by omega) (by omega))]; exact r6)
    hv5 hv6 hret hjt hbt (fun a h1 h2 => by rw [rd2, d1]; exact hrs a (by omega) h2)
  refine ⟨ω4, _, ((run1.trans run2).trans (run3.trans run4)).mono (by omega), e0, e1, e5, e6, e7, ?_,
    fun a ha0 ha1 ha2 ha3 => ?_, fun a => ?_, fun a => ?_⟩
  · unfold rdN
    rw [Memory.readN_writeN_same _ _ _ _ (by simp) (by simp [two32] <;> omega), Num.decodeLE_encodeLE,
      Nat.mod_eq_of_lt (by omega)]
  · rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
      (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega),
      fr2 a ha0 ha2 (by omega), m1 a ha0 (by omega)]
  · rw [Memory.readable_writeN, rd2, d1]
  · rw [Memory.writable_writeN, wr2, w1]

/-! ### The `String` and the allocator's context -/

/-- A chunk of a well-formed state lies in base … base + 2³⁰. -/
theorem chunk_bounds {s : State} (hwf : WF s) {c : Chunk} (hc : c ∈ chunks s) :
    s.base ≤ c.addr ∧ c.addr + 32 * c.size ≤ s.base + 1073741824 ∧ 0 < c.size := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  have := ht.mem_lt c hc
  omega

/-- A well-formed state has a chunk. -/
theorem chunks_ne {s : State} (hwf : WF s) : ∃ c, c ∈ chunks s := by
  have ht := hwf.2.2.2.1
  unfold TilesOk at ht
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  cases h : chunks s with
  | nil => rw [h] at ht; simp only [Tiles] at ht; omega
  | cons c cs => exact ⟨c, List.mem_cons_self⟩

/-- **The allocator's context is kept by writes at or above 2³¹** (the stack) that keep every
    octet's access. -/
theorem ctx_hi {env : RefineHost.Env} {pb S0 S1 : Nat} {μ μ' : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) (hk : ∀ a, a < 2147483648 → μ'.read a = μ.read a)
    (ww : ∀ a, μ'.writable a = μ.writable a) : HeapCtx env pb S0 S1 μ' s := by
  obtain ⟨c, hc⟩ := chunks_ne H.wf
  exact Decode.VecU8.ctx_congr_data H hc (fun a ha _ => hk a ha) ww

/-- **The `String` at W**, as the logging runs keep it, from the state s₀ a run started with to s:
    its capacity `cap` at W and its length `len` at W + 16, len ≤ cap < 2²⁹; every allocated
    chunk of s₀ still allocated in s; and, unless cap = 0, its buffer (at W + 8) the data of an
    allocated chunk c of s of exactly ⌈cap/32⌉ + 1 units, at an address no allocated chunk of s₀
    has (a fresh allocation of the run). -/
structure Str (s₀ s : State) (μ : Memory) (W cap len : Nat) : Prop where
  rc : rdN μ W 8 = cap
  rl : rdN μ (W + 16) 8 = len
  le : len ≤ cap
  lt : cap < 536870912
  base : ∀ d ∈ chunks s₀, d.used = true → d ∈ chunks s
  buf : cap = 0 ∨ ∃ c ∈ chunks s, c.used = true ∧ c.addr + 32 = rdN μ (W + 8) 8 ∧
    c.size = (cap + 31) / 32 + 1 ∧ ∀ d ∈ chunks s₀, d.used = true → d.addr ≠ c.addr

/-- A word written as 8 octets, read back. -/
theorem rdN_of_readN {μ : Memory} {a v : Nat} (h : μ.readN a 8 = Num.encodeLE 8 v) (hv : v < 18446744073709551616) :
    rdN μ a 8 = v := by
  unfold rdN; rw [h, Num.decodeLE_encodeLE, Nat.mod_eq_of_lt hv]

/-- 58848 … 59989: `finish_grow`'s success path, `do_reserve_and_handle`'s store of newcap m and
    the buffer q in the `String` W, and the way back into `write_str`'s copy (`rt`, `rt2`), with
    finish_grow's frame at F, do_reserve's at F + 40 and write_str's at F + 96. -/
theorem ws_back {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (x : X) (ω : Regs) (μ : Memory)
    (F W q m n src len : Nat) (hF : 65536 ≤ F ∧ F + 136 < 4294967296)
    (h1 : ω[1] = UInt64.ofNat F) (h6 : ω[6] = UInt64.ofNat (F + 48)) (h7 : ω[7] = UInt64.ofNat q)
    (h10 : ω[10] = UInt64.ofNat m) (hq : q < 4294967296) (hm : m < 4294967296) (hn : n < 4294967296)
    (hsrc : src < 4294967296) (hW : F + 128 ≤ W ∧ W + 24 < 4294967296)
    (r0 : rdN μ (F + 32) 8 = 2558) (r5 : rdN μ (F + 24) 8 = m) (r6 : rdN μ (F + 16) 8 = 8)
    (rW : rdN μ (F + 40) 8 = W) (r88 : rdN μ (F + 88) 8 = 2600) (r80 : rdN μ (F + 80) 8 = n)
    (r72 : rdN μ (F + 72) 8 = W) (r96 : rdN μ (F + 96) 8 = src) (rl : rdN μ (W + 16) 8 = len)
    (hw : ∀ a, F ≤ a → a < F + 104 → μ.writable a = true)
    (hWw : ∀ a, W ≤ a → a < W + 24 → μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 58848 ω μ x 59989 ω' μ' x 32 ∧
      ω'[1] = UInt64.ofNat (F + 96) ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat src ∧ ω'[9] = UInt64.ofNat len ∧
      rdN μ' W 8 = m ∧ rdN μ' (W + 8) 8 = q ∧ rdN μ' (W + 16) 8 = len ∧
      (∀ a, a < 4294967296 → (a < F + 48 ∨ F + 72 ≤ a) → (a < W ∨ W + 16 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, μ'.readable a = μ.readable a) ∧ (∀ a, μ'.writable a = μ.writable a) := by
  obtain ⟨ω1, μ1, run1, a1, a5, a6, z0, zq, fr1, rd1, wr1⟩ := rt (p := p) (P := P) (R := R) x ω μ F q m
    ⟨hF.1, by omega⟩ h1 h6 h7 h10 hq hm r0 r5 r6 (fun a h1 h2 => hw a h1 (by omega))
  have k : ∀ a, F + 72 ≤ a → a < 4294967296 → μ1.read a = μ.read a := fun a h1 h2 => fr1 a h2 (Or.inr h1)
  obtain ⟨ω2, μ2, run2, b0, bq, bl, fr2, rd2, wr2, -, e1, e5, e6, e8, e9⟩ := rt2 (p := p) (P := P) (R := R) x ω1 μ1
    (F + 40) W q m n src len ⟨by omega, by omega⟩ (by rw [a1]) a5 hq hm hn hsrc (by omega) (Or.inr (by omega))
    (by rw [show F + 40 + 8 = F + 48 by omega]; exact z0) (by rw [show F + 40 + 16 = F + 56 by omega]; exact zq)
    (by rw [rdN_frame (fun j hj => fr1 _ (by omega) (Or.inl (by omega)))]; exact rW)
    (by rw [show F + 40 + 48 = F + 88 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r88)
    (by rw [show F + 40 + 40 = F + 80 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r80)
    (by rw [show F + 40 + 32 = F + 72 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r72)
    (by rw [show F + 40 + 56 = F + 96 by omega, rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact r96)
    (by rw [rdN_frame (fun j hj => k _ (by omega) (by omega))]; exact rl)
    (fun a h1 h2 => by rw [rd1]; exact Memory.readable_of_writable (hw a (by omega) (by omega)))
    (fun a h1 h2 => by rw [wr1]; exact hWw a h1 h2)
  refine ⟨ω2, μ2, (run1.trans run2).mono (by omega), by rw [e1, show F + 40 + 56 = F + 96 by omega], e5, e6, e8, e9, b0, bq, bl,
    fun a h0 h1 h2 => (fr2 a h0 h2).trans (fr1 a h0 h1), fun a => by rw [rd2, rd1],
    fun a => by rw [wr2, wr1]⟩

/-- `write_str`'s stack frames: write_str at S … S + 32, `do_reserve_and_handle` at S − 56,
    `finish_grow` at S − 96, the allocator below. -/
theorem stack_wr {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) {lo hi : Nat} (h1 : S0 ≤ lo) (h2 : hi ≤ S1) :
    ∀ a, lo ≤ a → a < hi → μ.writable a = true := fun a ha hb => H.st a (by omega) (by omega)

/-- **The reserve path of `write_str`**, from 60030 when cap − len < n: `do_reserve_and_handle`
    and `finish_grow` get newcap = max(len + n, 8, 2 · cap) octets from the allocator (`alloc` for
    cap = 0, else `realloc`), store newcap and the new buffer in the `String` W and come back to
    59989 (the copy), with S, n, W, src and len in ω₁, ω₅, ω₆, ω₈, ω₉. The `String` holds the new
    capacity, the context is kept, and the frame `Keeps` from S + 8 up, but for the capacity and
    buffer at W … W + 16. Or the allocator fails (`Exhausts`). -/
theorem ws_reserve {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (S W n len cap src : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str s₀ s μ W cap len)
    (h1 : ω[1] = UInt64.ofNat S) (h5 : ω[5] = UInt64.ofNat n) (h6 : ω[6] = UInt64.ofNat W)
    (h8 : ω[8] = UInt64.ofNat src) (h9 : ω[9] = UInt64.ofNat len)
    (hlt : cap < len + n) (hn : len + n < 134217728) (hsrc : src < 4294967296)
    (hS : S0 + 416 ≤ S ∧ S % 8 = 0 ∧ 2147484064 ≤ S) (hW : S + 32 ≤ W ∧ W + 24 ≤ S1) :
    (∃ ω' μ' x' s', FreeStepsH p R 60030 ω μ x 59989 ω' μ' x' (2 * (newcap (len + n) cap - cap) + 1500) ∧
      ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat W ∧
      ω'[8] = UInt64.ofNat src ∧ ω'[9] = UInt64.ofNat len ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W (newcap (len + n) cap) len ∧
      Keeps pb (S + 8) (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ' s') ∨
    Exhausts p R pb 60030 ω μ x (2 * (newcap (len + n) cap - cap) + 1500) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hm := newcap_ge (len + n) cap
  have hml := newcap_lt (len + n) cap (by omega) (by have := hs.lt; omega)
  have hm2 : newcap (len + n) cap < 268435456 := by
    have : newcap (len + n) cap ≤ max (len + n) 8 ∨ newcap (len + n) cap ≤ 2 * cap := by
      unfold newcap; simp only [Nat.max_def]; split <;> split <;> omega
    omega
  generalize hmd : newcap (len + n) cap = m at hm hml hm2 ⊢
  obtain ⟨hm1, hm8, hm3⟩ := hm
  have hcap := hs.lt
  have hle := hs.le
  have hst := stack_wr H (lo := S0) (hi := S1) (Nat.le_refl _) (Nat.le_refl _)
  -- the String's buffer address
  generalize hpd : rdN μ (W + 8) 8 = ptr
  have hp64 : ptr < 18446744073709551616 := by rw [← hpd]; exact rdN_lt _ _ _
  -- 60030 … 58615
  obtain ⟨ω1, run1, a0, a1, a5, a6, a7, a8, a9, a10, a11⟩ := rs1 (p := p) (P := P) (R := R) x ω μ S W n len src
    ⟨by omega, by omega⟩ h1 h5 h6 h8 h9 ⟨by omega, by omega, by omega, hsrc⟩
    (fun a h1 h2 => hst a (by omega) (by omega))
  generalize hM1 : μ.writeN S (Num.encodeLE 8 src) = μ1 at run1
  have k1 : ∀ a, a < 4294967296 → (a < S ∨ S + 8 ≤ a) → μ1.read a = μ.read a := fun a ha0 ha1 => by
    rw [← hM1, Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
      (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega)]
  have w1 : ∀ a, μ1.writable a = μ.writable a := fun a => by rw [← hM1, Memory.writable_writeN]
  -- 58615 … 58667
  obtain ⟨ω2, μ2, run2, b1, b6, b8, b9, b10, b11, b12, s48, s40, s32, s0, k2, rd2, wr2⟩ :=
    rs2a (p := p) (P := P) (R := R) x ω1 μ1 (S - 56) W n len cap ptr 2600 n W ⟨by omega, by omega⟩
    a0 (by rw [a1, h1]; congr 1; omega) (a5.trans h5) (a6.trans h6) a7 a8 a9 a10 a11
    ⟨by omega, by omega, by omega, hp64⟩ ⟨by omega, by omega, by omega⟩ (Or.inr (by omega))
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (Or.inr (by omega)))]; exact hs.rc)
    (by rw [rdN_frame (fun j hj => k1 _ (by omega) (Or.inr (by omega)))]; exact hpd)
    (fun a h1 h2 => by rw [Memory.readable_of_writable (by rw [w1]; exact hst a (by omega) (by omega))])
    (fun a h1 h2 => by rw [w1]; exact hst a (by omega) (by omega))
  -- 58667 … 58759
  obtain ⟨ω3, run3, c1, c6, c8, c9, c10, c11, c12⟩ := rs2b (p := p) (P := P) (R := R) x ω2 μ2 (S - 96) len n cap
    ⟨by omega, by omega⟩ (by rw [b1]; congr 1; omega) b6 b8 (by rw [b10]) b12 ⟨by omega, by omega⟩
    (fun a h1 h2 => by rw [wr2, w1]; exact hst a (by omega) (by omega))
  rw [hmd] at run3 c10
  generalize hM3 : ((μ2.writeN (S - 96 + 32) (Num.encodeLE 8 2558)).writeN (S - 96 + 24)
    (Num.encodeLE 8 m)).writeN (S - 96 + 16) (Num.encodeLE 8 8) = μ3 at run3
  have k3 : ∀ a, a < 4294967296 → (a < S - 96 + 16 ∨ S - 96 + 40 ≤ a) → μ3.read a = μ2.read a := fun a ha0 ha1 => by
    rw [← hM3]
    simp (disch := pvm_arith) only [Memory.read_writeN_disjoint, Num.length_encodeLE, two32]
  have w3 : ∀ a, μ3.writable a = μ2.writable a := fun a => by
    rw [← hM3]; simp only [Memory.writable_writeN]
  -- finish_grow's frame F = S − 96, do_reserve's D = S − 56
  have hF : 65536 ≤ S - 96 ∧ S - 96 + 96 < 4294967296 := ⟨by omega, by omega⟩
  have r58 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S + 8 ≤ a) → μ3.read a = μ.read a := fun a ha0 ha1 => by
    rw [k3 a ha0 (by omega), k2 a ha0 (by omega), k1 a ha0 (by omega)]
  have wr3 : ∀ a, μ3.writable a = μ.writable a := fun a => by rw [w3, wr2, w1]
  -- what μ3 holds: finish_grow's saved words, do_reserve's frame and src at S
  have q32 : rdN μ3 (S - 96 + 32) 8 = 2558 := by
    rw [← hM3]; simp (disch := pvm_arith) only [rdN_writeN_disjoint, rdN_writeN_same8]
  have q24 : rdN μ3 (S - 96 + 24) 8 = m := by
    rw [← hM3]; simp (disch := pvm_arith) only [rdN_writeN_disjoint, rdN_writeN_same8]; omega
  have q16 : rdN μ3 (S - 96 + 16) 8 = 8 := by
    rw [← hM3]; simp (disch := pvm_arith) only [rdN_writeN_disjoint, rdN_writeN_same8]
  have kk : ∀ a, S - 96 + 40 ≤ a → a < S → μ3.read a = μ2.read a := fun a h1 h2 => k3 a (by omega) (Or.inr h1)
  have q40 : rdN μ3 (S - 96 + 40) 8 = W := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 40 = S - 56 by omega]
    exact rdN_of_readN s0 (by omega)
  have q88 : rdN μ3 (S - 96 + 88) 8 = 2600 := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 88 = S - 56 + 48 by omega]
    exact rdN_of_readN s48 (by omega)
  have q80 : rdN μ3 (S - 96 + 80) 8 = n := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 80 = S - 56 + 40 by omega]
    exact rdN_of_readN s40 (by omega)
  have q72 : rdN μ3 (S - 96 + 72) 8 = W := by
    rw [rdN_frame (fun j hj => kk _ (by omega) (by omega)), show S - 96 + 72 = S - 56 + 32 by omega]
    exact rdN_of_readN s32 (by omega)
  have q96 : rdN μ3 (S - 96 + 96) 8 = src := by
    rw [rdN_frame (fun j hj => k3 _ (by omega) (Or.inr (by omega))),
      rdN_frame (fun j hj => k2 _ (by omega) (Or.inr (by omega))), show S - 96 + 96 = S by omega, ← hM1]
    exact rdN_writeN_same8 _ _ _ (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
  have qlen : rdN μ3 (W + 16) 8 = len := by
    rw [rdN_frame (fun j hj => r58 _ (by omega) (Or.inr (by omega)))]; exact hs.rl
  -- the common end: from finish_grow's success (58848) to 59989
  have fin : ∀ (μ5 : Memory) (x5 : X) (s' : State) (ω6 : Regs) (q N : Nat),
      FreeStepsH p R 60030 ω μ x 58848 ω6 μ5 x5 N → N ≤ 2 * (m - cap) + 1468 →
      ω6[1] = UInt64.ofNat (S - 96) → ω6[6] = UInt64.ofNat (S - 96 + 48) → ω6[7] = UInt64.ofNat q →
      ω6[10] = UInt64.ofNat m → 0 < q → q < 2147483648 →
      HeapCtx env pb S0 S1 μ5 s' → s'.base = s.base →
      Keeps pb (S + 8) (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ5 s' →
      (∀ a, S - 96 + 16 ≤ a → a < 4294967296 → μ5.read a = μ3.read a) →
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = q ∧ d.size = (m + 31) / 32 + 1 ∧
        ∀ e ∈ chunks s₀, e.used = true → e.addr ≠ d.addr) →
      (∃ ω' μ' x' s', FreeStepsH p R 60030 ω μ x 59989 ω' μ' x' (2 * (m - cap) + 1500) ∧
        ω'[1] = UInt64.ofNat S ∧ ω'[5] = UInt64.ofNat n ∧ ω'[6] = UInt64.ofNat W ∧
        ω'[8] = UInt64.ofNat src ∧ ω'[9] = UInt64.ofNat len ∧
        HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W m len ∧
        Keeps pb (S + 8) (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ' s') := by
    intro μ5 x5 s' ω6 q N run hN g1 g6 g7 g10 hq0 hq1 H5 hb5 K5 hk5 hbuf
    have rr : ∀ {a : Nat} {v : Nat}, S - 96 + 16 ≤ a → a + 8 ≤ 4294967296 → rdN μ3 a 8 = v →
        rdN μ5 a 8 = v := fun h1 h2 h3 => by
      rw [rdN_frame (fun j hj => hk5 _ (by omega) (by omega))]; exact h3
    obtain ⟨ω7, μ7, run7, e1, e5, e6, e8, e9, eW, eq, el, fr7, rd7, wr7⟩ := ws_back (p := p) (P := P) (R := R)
      x5 ω6 μ5 (S - 96) W q m n src len ⟨by omega, by have := hW.2; have := hS1; have := hW.1; omega⟩ g1 g6 g7 g10 (by omega) (by omega) (by omega : n < 4294967296)
      hsrc ⟨by omega, by omega⟩ (rr (by omega) (by omega) q32) (rr (by omega) (by omega) q24)
      (rr (by omega) (by omega) q16) (rr (by omega) (by omega) q40) (rr (by omega) (by omega) q88)
      (rr (by omega) (by omega) q80) (rr (by omega) (by omega) q72) (rr (by omega) (by omega) q96)
      (rr (by omega) (by omega) qlen) (fun a h1 h2 => H5.st a (by omega) (by omega))
      (fun a h1 h2 => H5.st a (by omega) (by omega))
    have H7 : HeapCtx env pb S0 S1 μ7 s' := ctx_hi H5 (fun a ha => fr7 a (by omega) (Or.inl (by omega))
      (Or.inl (by omega))) wr7
    obtain ⟨d, hd, hdu, hdq, hds, hdf⟩ := hbuf
    have K7 : Keeps pb (S + 8) (fun a => W ≤ a ∧ a < W + 16) s₀ μ5 μ7 s' :=
      Keeps.of_frame (Z := fun a => (S - 96 + 48 ≤ a ∧ a < S - 96 + 72) ∨ (W ≤ a ∧ a < W + 16)) K5.used
        (fun a ha hz => fr7 a ha (by omega) (by omega)) rd7 wr7
        (fun a hz => H5.st a (by omega) (by omega)) (fun a hz h => by omega)
        (fun a hz hg => by unfold Glob at hg; omega)
        (fun c hc hu a ha => by
          have := chunk_bounds H5.wf (K5.used c hc hu)
          have := H5.hbT
          unfold InData at ha; omega)
    refine ⟨ω7, μ7, x5, s', (run.trans run7).mono (by omega), by rw [e1, show S - 96 + 96 = S by omega],
      e5, e6, e8, e9, H7, hb5, ⟨eW, el, by omega, by omega, K5.used,
        Or.inr ⟨d, hd, hdu, by rw [eq]; exact hdq, hds, hdf⟩⟩, ?_⟩
    have := K5.trans' K7
    rwa [Nat.max_self] at this
  -- the frame of the steps before the allocator: only S − 96 … S + 8 written
  have Kpre : ∀ μ4 : Memory, (∀ a, a < 4294967296 → (a < S - 96 ∨ S - 96 + 16 ≤ a) → μ4.read a = μ3.read a) →
      (∀ a, μ4.readable a = μ.readable a) → (∀ a, μ4.writable a = μ.writable a) →
      Keeps pb (S + 8) (fun a => W ≤ a ∧ a < W + 16) s₀ μ μ4 s := fun μ4 h4 rd4 wr4 =>
    Keeps.of_frame (Z := fun a => S - 96 ≤ a ∧ a < S + 8) hs.base
      (fun a ha hz => by rw [h4 a ha (by omega), r58 a ha (by omega)]) rd4 wr4
      (fun a hz => hst a (by omega) (by omega)) (fun a hz h => by omega)
      (fun a hz hg => by unfold Glob at hg; omega)
      (fun c hc hu a ha => by
        have := chunk_bounds H.wf (hs.base c hc hu)
        have := H.hbT
        unfold InData at ha; omega)
  have rd3 : ∀ a, μ3.readable a = μ.readable a := fun a => by
    rw [← hM3]; simp only [Memory.readable_writeN]; rw [rd2, ← hM1, Memory.readable_writeN]
  by_cases hc0 : cap = 0
  · -- no buffer yet: `alloc`
    subst hc0
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8⟩ := rs3a (p := p) (P := P) (R := R) x ω3 μ3 (S - 96) m hF
      c1 (by rw [c8, b8]) c10 ⟨by omega, by omega⟩ (fun a h1 h2 => by rw [wr3]; exact hst a (by omega) (by omega))
    generalize hM4 : (μ3.writeN (S - 96) (Num.encodeLE 8 1)).writeN (S - 96 + 8) (Num.encodeLE 8 m) = μ4 at run4
    have k4 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S - 96 + 16 ≤ a) → μ4.read a = μ3.read a := fun a ha0 ha1 => by
      rw [← hM4]; simp (disch := pvm_arith) only [Memory.read_writeN_disjoint, Num.length_encodeLE, two32]
    have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by
      rw [← hM4]; simp only [Memory.readable_writeN]; exact rd3 a
    have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by
      rw [← hM4]; simp only [Memory.writable_writeN]; exact wr3 a
    have H4 : HeapCtx env pb S0 S1 μ4 s := ctx_hi H (fun a ha => by
      rw [k4 a (by omega) (Or.inl (by omega)), r58 a (by omega) (Or.inl (by omega))]) (fun a => wr4 a)
    have K4 := Kpre μ4 k4 rd4 wr4
    rcases HA ω4 μ4 x s (S - 96) m 1 H4 (d1.trans c1) d7 d8 (Nat.le_refl _) (by omega) (by omega) (by omega)
      (by omega) (by omega) with ⟨q, s', ω5, μ5, x5, run5, H5, hb5, K5, hnew, hfresh, hq32, e7, e0, e1, e5, e6⟩ |
      ⟨ω5, μ5, x5, run5, e7, hb, hfail⟩
    · have hq := chunk_bounds H5.wf hnew
      have hbT := H.hbT
      simp only at hq
      obtain ⟨ω6, run6, f1, f5, f6, f7, f10⟩ := rt_a (p := p) (P := P) (R := R) x5 ω5 μ5 (S - 96) q m hF
        (e1.trans (d1.trans c1)) e7 ⟨by omega, by omega⟩
        (by rw [rdN_frame (fun j hj => K5.hi _ (by omega) (by omega) id), ← hM4]
            simp (disch := pvm_arith) only [rdN_writeN_same8]; omega)
        (fun a h1 h2 => by
          rw [Memory.readable_of_writable (H5.st a (by omega) (by omega))])
      have rt0 := ret_alloc (p := p) (P := P) (R := R) x5 ω5 μ5 (e0.trans d0)
      exact Or.inl (fin μ5 x5 s' ω6 q _ ((((((run1.trans run2).trans run3).trans run4).trans run5).trans rt0).trans run6)
        (by omega) (f1.trans (e1.trans (d1.trans c1))) (f6.trans (e6.trans (d6.trans c6))) (f7.trans e7)
        (f10) (by omega) (by omega) H5 (by rw [hb5])
        (by have := K4.trans' ((K5.rebase hs.base).mono (sp' := S + 8) (by omega) (fun _ h => h.elim))
            rwa [Nat.max_self] at this)
        (fun a h1 h2 => by rw [K5.hi a (by omega) h2 id, k4 a h2 (by omega)])
        ⟨_, hnew, rfl, by simp only; omega, rfl, fun e he hu => by
          simp only; exact hfresh e (hs.base e he hu) hu⟩)
    · exact Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4)
        (⟨ω5, μ5, x5, 40611, run5, e7, Or.inl ⟨rfl, s, hb, _, hfail⟩⟩ : Exhausts p R pb 40494 ω4 μ4 x 540)).mono
        (by omega))
  · -- a buffer of cap > 0 octets: `realloc`
    obtain ⟨c, hc, hcu, hca, hcs, hcf⟩ := hs.buf.resolve_left hc0
    rw [hpd] at hca
    have hcb := chunk_bounds H.wf hc
    have hbT := H.hbT
    obtain ⟨ω4, run4, d0, d1, d5, d6, d7, d8, d9, d10⟩ := rs3r (p := p) (P := P) (R := R) x ω3 μ3 (S - 96) cap ptr m
      hF c1 (by rw [c8, b8]) (by rw [c9, b9]) c10 (by rw [c11, b11]) ⟨by omega, by omega⟩ (by omega) (by omega)
      (fun a h1 h2 => by rw [wr3]; exact hst a (by omega) (by omega))
    generalize hM4 : (μ3.writeN (S - 96) (Num.encodeLE 8 1)).writeN (S - 96 + 8) (Num.encodeLE 8 m) = μ4 at run4
    have k4 : ∀ a, a < 4294967296 → (a < S - 96 ∨ S - 96 + 16 ≤ a) → μ4.read a = μ3.read a := fun a ha0 ha1 => by
      rw [← hM4]; simp (disch := pvm_arith) only [Memory.read_writeN_disjoint, Num.length_encodeLE, two32]
    have rd4 : ∀ a, μ4.readable a = μ.readable a := fun a => by
      rw [← hM4]; simp only [Memory.readable_writeN]; exact rd3 a
    have wr4 : ∀ a, μ4.writable a = μ.writable a := fun a => by
      rw [← hM4]; simp only [Memory.writable_writeN]; exact wr3 a
    have H4 : HeapCtx env pb S0 S1 μ4 s := ctx_hi H (fun a ha => by
      rw [k4 a (by omega) (Or.inl (by omega)), r58 a (by omega) (Or.inl (by omega))]) (fun a => wr4 a)
    have K4 := Kpre μ4 k4 rd4 wr4
    rcases HR ω4 μ4 x s (S - 96) ptr 1 m c H4 hba hc hcu hca (by omega) (by omega) (d1.trans c1) d7 d9 d10
      (Nat.le_refl _) (by omega) (by omega) (by omega) (by omega) (by omega) with
      ⟨r, s', ω5, μ5, x5, run5, H5, hb5, O5, oth, ⟨d, hd, hdu, hdr, hds, hdf⟩, e7, e0, e1, e5, e6⟩ |
      ⟨ω5, μ5, x5, run5, e7, hb, hfail⟩
    · have hq := chunk_bounds H5.wf hd
      rw [hb5] at hq
      obtain ⟨ω6, run6, f1, f5, f6, f7, f10⟩ := rt_r (p := p) (P := P) (R := R) x5 ω5 μ5 (S - 96) r m hF
        (e1.trans (d1.trans c1)) e7 ⟨by omega, by omega⟩
        (by rw [rdN_frame (fun j hj => O5.hi _ (by omega) (by omega) id), ← hM4]
            simp (disch := pvm_arith) only [rdN_writeN_same8]; omega)
        (fun a h1 h2 => by
          rw [Memory.readable_of_writable (H5.st a (by omega) (by omega))])
      have rt0 := ret_realloc (p := p) (P := P) (R := R) x5 ω5 μ5 (e0.trans d0)
      have K5 : Keeps pb (S - 96) (fun _ => False) s₀ μ4 μ5 s' :=
        ⟨O5, fun e he hu => (oth e (hs.base e he hu) hu (fun h => hcf e he hu (by rw [h]))).1,
          fun e he hu => (oth e (hs.base e he hu) hu (fun h => hcf e he hu (by rw [h]))).2⟩
      exact Or.inl (fin μ5 x5 s' ω6 r _ ((((((run1.trans run2).trans run3).trans run4).trans run5).trans rt0).trans run6)
        (by rw [hcs]; omega) (f1.trans (e1.trans (d1.trans c1))) (f6.trans (e6.trans (d6.trans c6))) (f7.trans e7)
        (f10) (by omega) (by omega) H5 (by rw [hb5])
        (by have := K4.trans' (K5.mono (sp' := S + 8) (by omega) (fun _ h => h.elim))
            rwa [Nat.max_self] at this)
        (fun a h1 h2 => by rw [O5.hi a (by omega) h2 id, k4 a h2 (by omega)])
        ⟨d, hd, hdu, hdr, hds, fun e he hu => by
          rcases hdf with h | h
          · rw [h]; exact hcf e he hu
          · exact h e (hs.base e he hu) hu⟩)
    · exact Or.inr ((Exhausts.pre (((run1.trans run2).trans run3).trans run4)
        (⟨ω5, μ5, x5, 40821, run5, e7, Or.inr ⟨rfl, s, hb, _, _, _, hfail⟩⟩ :
          Exhausts p R pb 40701 ω4 μ4 x (64 * (c.size - 1) + 1300))).mono (by rw [hcs]; omega))

/-- The `String` after a write that kept its capacity and buffer words and set its length. -/
theorem Str.update {s₀ s : State} {μ μ' : Memory} {W cap len len' : Nat} (hs : Str s₀ s μ W cap len)
    (hk : ∀ j, j < 16 → μ'.read (W + j) = μ.read (W + j)) (hl : rdN μ' (W + 16) 8 = len')
    (hle : len' ≤ cap) : Str s₀ s μ' W cap len' := by
  have e0 : rdN μ' W 8 = rdN μ W 8 := rdN_frame (fun j hj => by rw [hk j (by omega)])
  have e8 : rdN μ' (W + 8) 8 = rdN μ (W + 8) 8 := rdN_frame (fun j hj => by
    rw [show W + 8 + j = W + (8 + j) by omega, hk _ (by omega)])
  exact ⟨by rw [e0]; exact hs.rc, hl, hle, hs.lt, hs.base, by rw [e8]; exact hs.buf⟩

/-- **`<String as fmt::Write>::write_str`, frame-only** (59959): called with the `String` W (ω₇),
    the n octets at src (ω₈, ω₉) and a return address ω₀ that `djump` resolves to `t`, it either
    - returns `Ok` (ω₇ = 0) to `t` within 7n + 2 · (cap' − cap) + 2000 steps, with ω₀, ω₁, ω₅, ω₆ as
      they were. The `String` now has length len + n and a capacity cap' ≥ cap (grown, if it had too
      little room, to max(len + n, 8, 2 · cap) through the allocator). The allocator's context is
      kept with the same base, and the frame `Keeps`: from sp up only W … W + 24 changes, and every
      allocated chunk of s₀ keeps its data; or
    - reaches a failed allocator call (`Exhausts`).

    What the octets say is not stated. The octets come from read-only data (below 196608) or from
    the stack above sp. -/
theorem write_str {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocOk p R env pb S0 S1)
    (x : X) (ω : Regs) (μ : Memory) (s₀ s : State) (sp W src n cap len ret t v5 v6 : Nat)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0) (hs : Str s₀ s μ W cap len)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat sp) (h5 : ω[5] = UInt64.ofNat v5)
    (h6 : ω[6] = UInt64.ofNat v6) (h7 : ω[7] = UInt64.ofNat W) (h8 : ω[8] = UInt64.ofNat src)
    (h9 : ω[9] = UInt64.ofNat n) (hv : v5 < 18446744073709551616 ∧ v6 < 18446744073709551616)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hsp : S0 + 448 ≤ sp ∧ sp % 8 = 0 ∧ 2147484096 ≤ sp) (hW : sp ≤ W ∧ W + 24 ≤ S1)
    (hn : len + n < 134217728)
    (hsrc : (65536 ≤ src ∧ src + n + 24 ≤ 196608) ∨
      (sp + 8 ≤ src ∧ src + n + 16 < 4294967296 ∧ (src + n ≤ W ∨ W + 24 ≤ src)))
    (hr : ∀ a, src ≤ a → a < src + n → μ.readable a = true) :
    (∃ ω' μ' x' s' cap', FreeStepsH p R 59959 ω μ x t ω' μ' x' (7 * n + 2 * (cap' - cap) + 2000) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Str s₀ s' μ' W cap' (len + n) ∧ cap ≤ cap' ∧
      cap' ≤ max cap (max 8 (2 * (len + n))) ∧
      Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ' s' ∧
      ω'[0] = UInt64.ofNat ret ∧ ω'[1] = UInt64.ofNat sp ∧ ω'[5] = UInt64.ofNat v5 ∧
      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 59959 ω μ x (7 * n + 1073741824 + 2000) := by
  have hS1 := H.hS1
  have hSb := H.hSb
  have hcap := hs.lt
  have hle := hs.le
  have hbT := H.hbT
  have hst : ∀ a, S0 ≤ a → a < S1 → μ.writable a = true := H.st
  have hWr : ∀ a, W ≤ a → a < W + 24 → μ.readable a = true := fun a h1 h2 =>
    Memory.readable_of_writable (hst a (by omega) (by omega))
  -- the entry: write_str's frame at S = sp − 32
  obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a8, a9, sv0, sv5, sv6, fr1, rd1, wr1⟩ := ws_entry (p := p) (P := P) (R := R)
    x ω μ sp W src n cap len ret v5 v6 ⟨by omega, by omega⟩ h0 h5 h6 ⟨by omega, hv.1, hv.2⟩ h1 h7 h8 h9
    (by omega) hs.rc hs.rl hle (by omega) (by omega) (Or.inr hW.1) hWr
    (fun a h1 h2 => hst a (by omega) (by omega))
  have hS : 65536 + 48 ≤ sp - 32 ∧ sp - 32 + 32 < 4294967296 ∧ (sp - 32) % 8 = 0 := ⟨by omega, by omega, by omega⟩
  have hsr : ∀ a, sp - 32 ≤ a → a < sp → μ1.readable a = true := fun a h1 h2 => by
    rw [rd1]; exact Memory.readable_of_writable (hst a (by omega) (by omega))
  have sv0' : rdN μ1 (sp - 32 + 24) 8 = ret := sv0
  -- the String's words are above sp, untouched by the entry
  have kW : ∀ j, j < 24 → μ1.read (W + j) = μ.read (W + j) := fun j hj => fr1 _ (by omega) (Or.inr (by omega))
  by_cases hb : cap - len < n
  · -- too little room: the reserve path
    rw [if_pos hb] at run1
    have hs1 : Str s₀ s μ1 W cap len := hs.update (fun j hj => kW j (by omega))
      ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hs.rl) hle
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
    have hsrc' : src < 4294967296 := by omega
    rcases ws_reserve (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω1 μ1 s₀ s (sp - 32) W n len cap src H1 hba hs1
      a1 a5 a6 a8 a9 (by omega) hn hsrc' ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2⟩ with
      ⟨ω2, μ2, x2, s', run2, b1, b5, b6, b8, b9, H2, hb2, hs2, K2⟩ | hx
    · generalize hmd : newcap (len + n) cap = m at run2 hs2
      have hm := newcap_ge (len + n) cap
      have hmx : newcap (len + n) cap ≤ max cap (max 8 (2 * (len + n))) := by
        unfold newcap; simp only [Nat.max_def]; split <;> split <;> split <;> split <;> omega
      rw [hmd] at hm hmx
      obtain ⟨c, hc, hcu, hca, hcs, hcf⟩ := hs2.buf.resolve_left (by omega)
      have hcb := chunk_bounds H2.wf hc
      have := H.hb0
      rw [hb2] at hcb
      generalize hpd : rdN μ2 (W + 8) 8 = ptr at hca
      have hwb : ∀ a, ptr + len ≤ a → a < ptr + len + n → μ2.writable a = true := fun a h1 h2 =>
        Decode.VecU8.heap_writable H2 hc hcu (by unfold InData; omega)
      have hk2 : ∀ a, sp - 32 + 8 ≤ a → a < 4294967296 → ¬ (W ≤ a ∧ a < W + 16) → μ2.read a = μ1.read a :=
        fun a h1 h2 h3 => K2.hi a h1 h2 h3
      obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, cl, fr3, rd3, wr3⟩ := ws_copytail (p := p) (P := P) (R := R) x2 ω2 μ2
        (sp - 32) W n len ptr src ret t v5 v6 hS b1 b5 b6 b8 b9 (by omega) hpd ⟨by omega, by omega⟩
        (by omega) ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
        (by rw [rdN_frame (fun j hj => hk2 _ (by omega) (by omega) (by omega))]; exact sv0')
        (by rw [rdN_frame (fun j hj => hk2 _ (by omega) (by omega) (by omega))]; exact sv5)
        (by rw [rdN_frame (fun j hj => hk2 _ (by omega) (by omega) (by omega))]; exact sv6)
        hv.1 hv.2 hret hjt hbt
        (fun a h1 h2 => by
          rcases hsrc with h | h
          · rw [(K2.access a (Or.inl (by unfold pageSize; omega))).1, rd1]; exact hr a h1 h2
          · rw [(K2.access a (Or.inr (by unfold pageSize; omega))).1, rd1]; exact hr a h1 h2)
        hwb (fun a h1 h2 => H2.st a (by omega) (by omega)) (fun a h1 h2 => H2.st a (by omega) (by omega))
      have H3 : HeapCtx env pb S0 S1 μ3 s' := Decode.VecU8.ctx_congr_data H2 hc
        (fun a ha h => fr3 a (by omega) (by omega) (by omega) (by omega)) wr3
      have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ2 μ3 s' :=
        Keeps.of_frame (Z := fun a => (sp - 32 - 48 ≤ a ∧ a < sp) ∨ (ptr + len ≤ a ∧ a < ptr + len + n) ∨
          (W + 16 ≤ a ∧ a < W + 24)) K2.used
          (fun a ha hz => fr3 a ha (by omega) (by omega) (by omega)) rd3 wr3
          (fun a hz => by
            rcases hz with h | h | h
            · exact H2.st a (by omega) (by omega)
            · exact hwb a h.1 h.2
            · exact H2.st a (by omega) (by omega))
          (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
          (fun d hd hu a ha => by
            have hd' := K2.used d hd hu
            have := chunk_bounds H2.wf hd'
            have hne : d ≠ c := fun e => hcf d hd hu (by rw [e])
            have := Decode.VecU8.data_disj H2.wf hd' hc hne ha
            unfold InData at ha; omega)
      refine Or.inl ⟨ω3, μ3, x2, s', m, ((run1.trans run2).trans run3).mono (by omega), H3, hb2,
        ?_, by omega, hmx, ?_, c0, by rw [c1, show sp - 32 + 32 = sp by omega], c5, c6, c7⟩
      · refine hs2.update (fun j hj => fr3 _ (by omega) (by omega) (by omega) (by omega)) ?_ (by omega)
        rw [cl]; omega
      · have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
          Keeps.of_frame (Z := fun a => sp - 32 ≤ a ∧ a < sp) hs.base
            (fun a ha hz => fr1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
            (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
            (fun d hd hu a ha => by
              have := chunk_bounds H.wf (hs.base d hd hu)
              unfold InData at ha; omega)
        have K12 := K1.trans' (K2.mono (sp' := sp) (by omega) (fun a h => ⟨h.1, by omega⟩))
        have K123 := K12.trans' K3
        rwa [Nat.max_self, Nat.max_self] at K123
    · have : newcap (len + n) cap - cap < 536870912 := by
        unfold newcap; simp only [Nat.max_def]; split <;> split <;> omega
      exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))
  · -- room enough: no allocation
    rw [if_neg hb] at run1
    have K1 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ μ1 s :=
      Keeps.of_frame (Z := fun a => sp - 32 ≤ a ∧ a < sp) hs.base
        (fun a ha hz => fr1 a ha (by omega)) rd1 wr1 (fun a hz => hst a (by omega) (by omega))
        (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
        (fun d hd hu a ha => by
          have := chunk_bounds H.wf (hs.base d hd hu)
          unfold InData at ha; omega)
    have H1 : HeapCtx env pb S0 S1 μ1 s := ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1
    by_cases hn0 : n = 0
    · -- nothing to copy: the length rewritten as it was
      subst hn0
      have run2 := ws_zero (p := p) (P := P) (R := R) x ω1 μ1 a5
      obtain ⟨ω3, run3, c0, c1, c5, c6, c7⟩ := ws_fin (p := p) (P := P) (R := R) x ω1 μ1 (sp - 32) W 0 len ret t v5 v6
        ⟨by omega, by omega⟩ a1 a5 a6 a9 (by omega) (by omega) (Or.inr (by omega))
        (fun a h1 h2 => H1.st a (by omega) (by omega)) sv0' sv5 sv6 hv.1 hv.2 hret hjt hbt (fun a h1 h2 => hsr a h1 (by omega))
      have fr3 : ∀ a, a < 4294967296 → (a < W + 16 ∨ W + 24 ≤ a) →
          (μ1.writeN (W + 16) (Num.encodeLE 8 (0 + len))).read a = μ1.read a := fun a ha h => by
        rw [Memory.read_writeN_disjoint _ _ _ _ (by simp only [Num.length_encodeLE]; omega)
          (by simp only [Num.length_encodeLE, two32]; omega) (by simp only [two32]; omega)]
      refine Or.inl ⟨ω3, _, x, s, cap, ((run1.trans run2).trans run3).mono (by omega),
        ctx_hi H1 (fun a ha => fr3 a (by omega) (Or.inl (by omega))) (fun a => Memory.writable_writeN ..),
        rfl, ?_, Nat.le_refl _, by omega, ?_, c0, by rw [c1, show sp - 32 + 32 = sp by omega], c5, c6, c7⟩
      · have hs1 : Str s₀ s μ1 W cap len := hs.update (fun j hj => kW j (by omega))
          ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
            rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hs.rl) hle
        refine hs1.update (fun j hj => fr3 _ (by omega) (Or.inl (by omega))) ?_ (by omega)
        rw [rdN_writeN_same8 _ _ _ (by omega)]; omega
      · have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ1
            (μ1.writeN (W + 16) (Num.encodeLE 8 (0 + len))) s :=
          Keeps.of_frame (Z := fun a => W + 16 ≤ a ∧ a < W + 24) hs.base
            (fun a ha hz => fr3 a ha (by omega)) (fun a => Memory.readable_writeN ..)
            (fun a => Memory.writable_writeN ..) (fun a hz => H1.st a (by omega) (by omega))
            (fun a hz h => ⟨by omega, by omega⟩) (fun a hz hg => by unfold Glob at hg; omega)
            (fun d hd hu a ha => by
              have := chunk_bounds H.wf (hs.base d hd hu)
              unfold InData at ha; omega)
        have := K1.trans' K3
        rwa [Nat.max_self] at this
    · -- the copy into the buffer
      obtain ⟨c, hc, hcu, hca, hcs, hcf⟩ := hs.buf.resolve_left (by omega)
      have hcb := chunk_bounds H.wf hc
      have := H.hb0
      generalize hpd : rdN μ (W + 8) 8 = ptr at hca
      have hpd1 : rdN μ1 (W + 8) 8 = ptr := by
        rw [rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
          rw [show W + 8 + j = W + (8 + j) by omega, kW _ (by omega)])]; exact hpd
      have hwb : ∀ a, ptr + len ≤ a → a < ptr + len + n → μ1.writable a = true := fun a h1 h2 =>
        Decode.VecU8.heap_writable H1 hc hcu (by unfold InData; omega)
      have run2 := ws_pos (p := p) (P := P) (R := R) x ω1 μ1 n a5 ⟨by omega, by omega⟩
      obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, cl, fr3, rd3, wr3⟩ := ws_copytail (p := p) (P := P) (R := R) x ω1 μ1
        (sp - 32) W n len ptr src ret t v5 v6 hS a1 a5 a6 a8 a9 (by omega) hpd1 ⟨by omega, by omega⟩
        (by omega) ⟨by omega, by omega⟩ (by omega) (by omega) (by omega) (by omega)
        sv0' sv5 sv6 hv.1 hv.2 hret hjt hbt (fun a h1 h2 => by rw [rd1]; exact hr a h1 h2)
        hwb (fun a h1 h2 => H1.st a (by omega) (by omega)) (fun a h1 h2 => H1.st a (by omega) (by omega))
      have H3 : HeapCtx env pb S0 S1 μ3 s := Decode.VecU8.ctx_congr_data H1 hc
        (fun a ha h => fr3 a (by omega) (by omega) (by omega) (by omega)) wr3
      have K3 : Keeps pb sp (fun a => W ≤ a ∧ a < W + 24) s₀ μ1 μ3 s :=
        Keeps.of_frame (Z := fun a => (sp - 32 - 48 ≤ a ∧ a < sp) ∨ (ptr + len ≤ a ∧ a < ptr + len + n) ∨
          (W + 16 ≤ a ∧ a < W + 24)) hs.base
          (fun a ha hz => fr3 a ha (by omega) (by omega) (by omega)) rd3 wr3
          (fun a hz => by
            rcases hz with h | h | h
            · exact H1.st a (by omega) (by omega)
            · exact hwb a h.1 h.2
            · exact H1.st a (by omega) (by omega))
          (fun a hz h => by omega) (fun a hz hg => by unfold Glob at hg; omega)
          (fun d hd hu a ha => by
            have hd' := hs.base d hd hu
            have := chunk_bounds H.wf hd'
            have hne : d ≠ c := fun e => hcf d hd hu (by rw [e])
            have := Decode.VecU8.data_disj H.wf hd' hc hne ha
            unfold InData at ha; omega)
      refine Or.inl ⟨ω3, μ3, x, s, cap, ((run1.trans run2).trans run3).mono (by omega), H3, rfl,
        ?_, Nat.le_refl _, by omega, ?_, c0, by rw [c1, show sp - 32 + 32 = sp by omega], c5, c6, c7⟩
      · have hs1 : Str s₀ s μ1 W cap len := hs.update (fun j hj => kW j (by omega))
          ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
            rw [show W + 16 + j = W + (16 + j) by omega, kW _ (by omega)])).trans hs.rl) hle
        refine hs1.update (fun j hj => fr3 _ (by omega) (by omega) (by omega) (by omega)) ?_ (by omega)
        rw [cl]; omega
      · have := K1.trans' K3
        rwa [Nat.max_self] at this

end Services.Bootstrap.Fmt
