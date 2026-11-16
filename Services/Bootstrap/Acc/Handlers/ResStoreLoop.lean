import Services.Bootstrap.Acc.Handlers.ResultsHyp
import Services.Bootstrap.Acc.Handlers.ResStoreLoopSeg

/-!
# The results store (36170), n ≥ 1: one pass of the loop, against `ExtendH` and `OkEncH`

`LoopInv k`: at 36346 (or 36405 once k = n), the value `Vec` at S + 32 (S = sp − 96) holds
ℰ(n) ++ ℰ(rs₀) ++ … ++ ℰ(rs_{k−1}) (`encK`), ω₅ = 144·(n − k), ω₆ = rp + 144·k, the allocator's context
holds, every allocated chunk of st is kept with its data and is not the buffer's, and the callee frame
(but the vector and the staging octet at S + 56), read-only data and the globals are kept against μ₀.

`rl_item`: from `LoopInv k` with k < n, one pass reaches `LoopInv (k + 1)`, or exhausts the heap.
-/

namespace Services.Bootstrap.Acc.Handlers.ResStore

open PVM JAM Picoalloc Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA
  Services.Bootstrap.Spec Services.Bootstrap.Acc Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA Services.Bootstrap.Encode.Writer Services.Bootstrap.Encode.WriterGrow
  Services.Bootstrap.Acc.Handlers.Results

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- `ExhaustsP` from a later point of a run that keeps the context and the stream. -/
theorem ExhaustsP.pre {p : ByteArray} {env : AccEnv} {pb i j : Nat} {ω ω' : Regs} {μ μ' : Memory}
    {c : AccCtx} {f : Stream} {N : Nat}
    (run : FreeStepsH p (KeepCtx (accContractS env)) i ω μ (c, f) j ω' μ' (c, f) N)
    (h : ExhaustsP p env pb j ω' μ' c f) : ExhaustsP p env pb i ω μ c f := by
  obtain ⟨ω₁, μ₁, q₁, j₁, N₁, r₁, e7, hj, rest⟩ := h
  exact ⟨ω₁, μ₁, q₁, j₁, N + N₁, run.trans r₁, e7, hj, rest⟩

theorem encode_ok (r : Ret) : Spec.Result.encode (.ok r) = 0 :: (Spec.Result.encode (.ok r)).drop 1 := by
  cases r <;> rfl

theorem encode_error (e : Err) : Spec.Result.encode (.error e) = [1, UInt8.ofNat e.tag] := rfl

theorem tag_lt (e : Err) : e.tag < 14 := by cases e <;> decide

theorem encodeLE_one {x : Nat} (h : x < 256) : Num.encodeLE 1 x = [UInt8.ofNat x] := by
  simp [Num.encodeLE, Nat.mod_eq_of_lt h]

theorem encode_ok_len (r : Ret) : 2 ≤ (Spec.Result.encode (.ok r)).length := by
  cases r <;> simp [Spec.Result.encode]

theorem OkAt.tag {μ : Memory} {st : State} {a : Nat} {r : Ret} (h : OkAt μ st a r) :
    ∃ t, t < 7 ∧ μ.readN a 1 = Num.encodeLE 1 t := by
  cases r with
  | unit => exact ⟨0, by decide, h⟩
  | serviceId _ => exact ⟨1, by decide, h.1⟩
  | length _ => exact ⟨2, by decide, h.1⟩
  | transferred _ _ _ => exact ⟨3, by decide, h.1⟩
  | hash _ => exact ⟨4, by decide, h.1⟩
  | data _ => exact ⟨5, by decide, h.1⟩
  | dataVec _ => exact ⟨6, by decide, h.1⟩

/-- `WriterPre` depends only on the vector's 24 octets (and the allocator state). -/
theorem WriterPre.congr {μ μ' : Memory} {s : State} {sp v cap ptr len S1 : Nat}
    (h : WriterPre μ s sp v cap ptr len S1) (hk : ∀ b, v ≤ b → b < v + 24 → μ'.read b = μ.read b) :
    WriterPre μ' s sp v cap ptr len S1 := by
  obtain ⟨h1, h2, m0, m8, m16, rest⟩ := h
  have e : ∀ o, o + 8 ≤ 24 → μ'.readN (v + o) 8 = μ.readN (v + o) 8 := fun o ho =>
    Memory.readN_congr fun j hj => hk _ (by omega) (by omega)
  exact ⟨h1, h2, (e 0 (by omega)).trans m0, (e 8 (by omega)).trans m8, (e 16 (by omega)).trans m16, rest⟩

/-- The first k results' encodings after ℰ(n). -/
def encK (n : Nat) (rs : List Spec.Result) (k : Nat) : List UInt8 :=
  Blob.encodeNat n ++ ((rs.take k).map Spec.Result.encode).flatten

theorem encK_succ (n : Nat) (rs : List Spec.Result) (k : Nat) (hk : k < rs.length) :
    encK n rs (k + 1) = encK n rs k ++ Spec.Result.encode rs[k] := by
  unfold encK
  rw [List.append_assoc, List.take_succ_eq_append_getElem hk, List.map_append, List.flatten_append]
  simp

theorem encK_len_le (n : Nat) (rs : List Spec.Result) (k : Nat) (hn : rs.length = n) :
    (encK n rs k).length ≤ (encodeResults rs).length := by
  unfold encK encodeResults vec
  have h := congrArg (fun l => (l.map Spec.Result.encode).flatten.length) (List.take_append_drop k rs)
  simp only [List.map_append, List.flatten_append, List.length_append] at h
  simp only [List.length_append, JAM.Codec.nat, hn]
  omega

/-- **The loop's invariant** after k items (see the module doc). -/
def LoopInv (code : ByteArray) (pb S0 S1 sp rp n : Nat) (rs : List Spec.Result) (st : State) (μ₀ : Memory)
    (k : Nat) (ω : Regs) (μ : Memory) (s : State) : Prop :=
  ω[1] = UInt64.ofNat (sp - 96) ∧ ω[5] = UInt64.ofNat (144 * (n - k)) ∧ ω[6] = UInt64.ofNat (rp + 144 * k) ∧
  HeapCtxC code pb S0 S1 μ s ∧
  (∃ cap ptr, WriterPre μ s (sp - 96) (sp - 96 + 32) cap ptr (encK n rs k).length S1 ∧
    μ.readN ptr (encK n rs k).length = encK n rs k ∧
    cap ≤ max (144 * n + 4) (max 8 (2 * (encK n rs k).length)) ∧
    ∀ d ∈ chunks st, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr ∧ ∀ a, InData d a → μ.read a = μ₀.read a) ∧
  (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 57 ≤ a) → μ.read a = μ₀.read a) ∧
  (∀ a, a < 196608 → μ.read a = μ₀.read a ∧ μ.readable a = μ₀.readable a) ∧
  (∀ a, Glob a → μ.read a = μ₀.read a)

/-- The common hypotheses of the loop: the stack frame, the items' bound and the encodings' size. -/
structure LoopHyp (pb S0 S1 sp rp n : Nat) (rs : List Spec.Result) (st : State) (μ₀ : Memory) : Prop where
  hsp : S0 + 520 ≤ sp ∧ 2147484168 ≤ sp ∧ sp % 8 = 0 ∧ sp ≤ S1
  hS1 : S1 < 4294967296
  hn : rs.length = n
  hrp : 65536 ≤ rp ∧ rp + 144 * n < 2147483648
  hB : 2 * (144 * n + 4) + 4 * (encodeResults rs).length + 64 < 1073741760
  hR : ResultsAt μ₀ st rp rs

/-- One `extend` call's outcome folded into the invariant's buffer facts (used twice per item). -/
theorem writer_chain {code : ByteArray} {pb S0 S1 sp : Nat} {μ μ' : Memory} {s s' : State}
    {cap ptr len : Nat} {bs : List UInt8} {st : State} {μ₀ : Memory}
    (hpost : WriterPost code pb S0 S1 μ s (sp - 96) (sp - 96 + 32) cap ptr len bs μ' s')
    (hst : ∀ d ∈ chunks st, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr ∧ ∀ a, InData d a → μ.read a = μ₀.read a)
    (hpre : WriterPre μ s (sp - 96) (sp - 96 + 32) cap ptr len S1) (hbig : 4 * (len + bs.length) + 16 < 1073741760)
    (hbs : 0 < bs.length)
    (hcapb : 2 * cap < 1073741760) :
    ∃ cap' r, WriterPre μ' s' (sp - 96) (sp - 96 + 32) cap' r (len + bs.length) S1 ∧
      μ'.readN r (len + bs.length) = μ.readN ptr len ++ bs ∧ cap' ≤ max cap (max 8 (2 * (len + bs.length))) ∧
      HeapCtxC code pb S0 S1 μ' s' ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks s' ∧ d.addr + 32 ≠ r ∧ ∀ a, InData d a → μ'.read a = μ₀.read a) ∧
      (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 56 ≤ a) → μ'.read a = μ.read a) ∧
      (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
      (∀ a, Glob a → μ'.read a = μ.read a) := by
  obtain ⟨cap', r, m0, m8, m16, hroom, hcap', eo, en, H', ⟨d, hd, hdu, hda, hds⟩, others, hr, stk, lo, gl⟩ := hpost
  obtain ⟨hv1, hv2, -, -, -, -, -, -, -⟩ := hpre
  have hc2 : cap' ≤ cap ∨ cap' ≤ 8 ∨ cap' ≤ 2 * (len + bs.length) := by
    omega
  refine ⟨cap', r, ⟨hv1, hv2, m0, m8, m16, hroom, by omega, by omega, d, hd, hdu, hda, hds⟩, ?_, hcap', H', ?_,
    fun a h0 h1 h2 => stk a h0 h1 (by omega), lo, gl⟩
  · rw [Services.Bootstrap.Decode.VecU8.readN_split, eo, en]
  · intro e he hu
    obtain ⟨k1, k2, k3⟩ := hst e he hu
    obtain ⟨k4, k5⟩ := others e k1 hu k2
    refine ⟨k4, ?_, fun a ha => (k5 a ha).trans (k3 a ha)⟩
    rcases hr with rfl | hr
    · exact k2
    · exact hr e k1 hu

/-- **One `extend` of the octet staged at S + 56** (S = sp − 96, the vector at S + 32), against `ExtendH`:
    the buffer facts move on by that octet, or the heap is exhausted. -/
theorem ext_step {p : ByteArray} {P : Program} {env : AccEnv} {pb S0 S1 : Nat} (hE : ExtendH p P env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s st : State) (μ₀ : Memory) (sp cap ptr len ret t : Nat)
    (H : HeapCtxC env.code pb S0 S1 μ s) (WP : WriterPre μ s (sp - 96) (sp - 96 + 32) cap ptr len S1)
    (hst : ∀ d ∈ chunks st, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr ∧ ∀ a, InData d a → μ.read a = μ₀.read a)
    (hbig : 4 * (len + 1) + 16 < 1073741760)
    (hsp : S0 + 520 ≤ sp ∧ 2147484168 ≤ sp ∧ sp % 8 = 0 ∧ sp ≤ S1) (hS1 : S1 < 4294967296)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat (sp - 96)) (h7 : ω[7] = UInt64.ofNat (sp - 96 + 32))
    (h8 : ω[8] = UInt64.ofNat (sp - 96 + 56)) (h9 : ω[9] = UInt64.ofNat 1)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true) :
    (∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 58508 ω μ (c, f) t ω' μ' (c, f) N ∧
      ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6] ∧
      ∃ cap' r, WriterPre μ' s' (sp - 96) (sp - 96 + 32) cap' r (len + 1) S1 ∧
        μ'.readN r (len + 1) = μ.readN ptr len ++ μ.readN (sp - 96 + 56) 1 ∧
        cap' ≤ max cap (max 8 (2 * (len + 1))) ∧ HeapCtxC env.code pb S0 S1 μ' s' ∧
        (∀ d ∈ chunks st, d.used = true → d ∈ chunks s' ∧ d.addr + 32 ≠ r ∧ ∀ a, InData d a → μ'.read a = μ₀.read a) ∧
        (∀ a, a < 4294967296 → sp - 96 ≤ a → (a < sp - 96 + 32 ∨ sp - 96 + 56 ≤ a) → μ'.read a = μ.read a) ∧
        (∀ a, a < 196608 → μ'.read a = μ.read a ∧ μ'.readable a = μ.readable a) ∧
        (∀ a, Glob a → μ'.read a = μ.read a)) ∨
    ExhaustsP p env pb 58508 ω μ c f := by
  have hSt := H.st
  obtain ⟨hv1, hv2, -, -, -, -, -, hcb, -⟩ := id WP
  rcases hE c f ω μ s (sp - 96) (sp - 96 + 32) (sp - 96 + 56) 1 cap ptr len ret t H WP (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ h0 h1 h7 h8 h9 hret hjt hbt
      (.inl ⟨by omega, by omega, .inr (by omega),
        fun a h1 h2 => Memory.readable_of_writable (hSt a (by omega) (by omega))⟩) with
    ⟨ω', μ', s', N, run, e0, e1, e5, e6, post⟩ | hx
  · obtain ⟨cap', r, WP', out, hc', H', hst', stk, lo, gl⟩ :=
      writer_chain post hst WP (by rw [Memory.length_readN]; omega) (by rw [Memory.length_readN]; omega) hcb
    rw [Memory.length_readN] at WP' out hc'
    exact .inl ⟨ω', μ', s', N, run, e1.trans h1.symm, e5, e6, cap', r, WP', out, hc', H', hst', stk, lo, gl⟩
  · exact .inr hx

/-- **One pass of the results loop** (36346 → 36346, or 36405 after the last item), against `ExtendH` and
    `OkEncH`: from `LoopInv k` with k < n, `LoopInv (k + 1)`, or the heap is exhausted. -/
theorem rl_item {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {env : AccEnv} {pb S0 S1 : Nat}
    (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (c : AccCtx) (f : Stream) (ω : Regs) (μ : Memory) (s : State) (sp rp n : Nat) (rs : List Spec.Result)
    (st : State) (μ₀ : Memory) (k : Nat) (L : LoopHyp pb S0 S1 sp rp n rs st μ₀) (hk : k < n)
    (I : LoopInv env.code pb S0 S1 sp rp n rs st μ₀ k ω μ s) :
    (∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 36346 ω μ (c, f)
        (if n - (k + 1) = 0 then 36405 else 36346) ω' μ' (c, f) N ∧
      LoopInv env.code pb S0 S1 sp rp n rs st μ₀ (k + 1) ω' μ' s') ∨
    ExhaustsP p env pb 36346 ω μ c f := by
  obtain ⟨h1, h5, h6, H, ⟨cap, ptr, WP, mout, hcapb, hst⟩, hfr, hlo, hgl⟩ := I
  obtain ⟨hsp, hS1, hn, ⟨hrp1, hrp2⟩, hB, hR⟩ := L
  have hSt := H.st
  have hk' : k < rs.length := hn ▸ hk
  have hlen := encK_len_le n rs (k + 1) hn
  rw [encK_succ n rs k hk', List.length_append] at hlen
  have hcb : 2 * cap < 1073741760 := WP.2.2.2.2.2.2.2.1
  -- the item, against μ₀, and its octets in st's heap
  have hitem0 := hR.2 k hk'
  have hIH : InHeap st (rp + 144 * k) 144 := hR.1.sub (by omega) (by
    have := Nat.mul_le_mul_left 144 (Nat.succ_le_of_lt hk'); omega)
  have rdI : ∀ (μ' : Memory) (s' : State), HeapCtxC env.code pb S0 S1 μ' s' →
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks s') → ∀ j, j < 144 → μ'.readable (rp + 144 * k + j) = true :=
    fun μ' s' H' hs' j hj => by
      obtain ⟨d, hd, hu, hi⟩ := hIH j hj
      exact Memory.readable_of_writable (HeapKeep.writableData H' (hs' d hd hu) hu hi)
  have itemAt : ∀ (μ' : Memory), (∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ'.read a = μ₀.read a) →
      ResultAt μ' st (rp + 144 * k) rs[k] := fun μ' hk2 =>
    ResultAt.keep (fun d hd hu => ⟨hd, hk2 d hd hu⟩) hIH hitem0
  have hstd : ∀ d ∈ chunks st, d.used = true → ∀ a, InData d a → μ.read a = μ₀.read a :=
    fun d hd hu => (hst d hd hu).2.2
  -- the staged octet's write keeps the vector, the heap and the frame
  have stage : ∀ (μ1 : Memory), (∀ b, b < 4294967296 → b ≠ sp - 96 + 56 → μ1.read b = μ.read b) →
      (∀ b, μ1.writable b = μ.writable b) →
      HeapCtxC env.code pb S0 S1 μ1 s ∧ WriterPre μ1 s (sp - 96) (sp - 96 + 32) cap ptr (encK n rs k).length S1 ∧
      μ1.readN ptr (encK n rs k).length = encK n rs k ∧
      (∀ d ∈ chunks st, d.used = true → d ∈ chunks s ∧ d.addr + 32 ≠ ptr ∧ ∀ a, InData d a → μ1.read a = μ₀.read a) :=
    fun μ1 fr1 wr1 => by
      obtain ⟨-, -, -, -, -, -, -, -, ch, hch, hchu, hcha, hchs⟩ := id WP
      have hci := Services.Bootstrap.Decode.VecU8.chunk_in H.wf hch hchu
      have hbT := H.hbT
      have hlc : (encK n rs k).length ≤ cap := WP.2.2.2.2.2.1
      have hc0 : 0 < cap := WP.2.2.2.2.2.2.1
      have hpb : ptr + cap ≤ 2147483648 := by omega
      refine ⟨HeapKeep.keepHi H (fun a ha => fr1 a (by omega) (by omega)) wr1,
        WriterPre.congr WP (fun b h1 h2 => fr1 b (by omega) (by omega)), ?_, fun d hd hu => ?_⟩
      · have e : μ1.readN ptr (encK n rs k).length = μ.readN ptr (encK n rs k).length :=
          Memory.readN_congr fun j (hj : j < (encK n rs k).length) => fr1 (ptr + j) (by omega) (by omega)
        rw [e, mout]
      · obtain ⟨k1, k2, k3⟩ := hst d hd hu
        refine ⟨k1, k2, fun a ha => ?_⟩
        have := Services.Bootstrap.Decode.VecU8.chunk_in H.wf k1 hu
        unfold InData at ha
        rw [fr1 a (by omega) (by omega)]; exact k3 a ⟨ha.1, ha.2⟩
  have hS56 : μ.writable (sp - 96 + 56) = true := hSt _ (by omega) (by omega)
  generalize hrk : rs[k] = res at hitem0 itemAt
  cases res with
  | error e =>
    have hi := itemAt μ hstd
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, m56, fr1, rd1, wr1⟩ :=
      rl_err (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ (sp - 96) (rp + 144 * k) h1 h6 (by omega)
        (by omega) (by rw [hi.1]; rfl) (by have := rdI μ s H (fun d hd hu => (hst d hd hu).1) 0 (by omega); simpa using this)
        hS56
    obtain ⟨H1, WP1, mout1, hst1⟩ := stage μ1 fr1 wr1
    rcases ext_step hE c f ω1 μ1 s st μ₀ sp cap ptr (encK n rs k).length 1700 36373 H1 WP1 hst1 (by omega) hsp hS1
        a0 (a1.trans h1) a7 a8 a9 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_849]) bs_36373 with
      ⟨ω2, μ2, s2, N2, run2, b1, b5, b6, cap2, r2, WP2, out2, hc2, H2, hst2, stk2, lo2, gl2⟩ | hx
    rotate_left
    · exact .inr (ExhaustsP.pre run1 hx)
    have hi2 := itemAt μ2 (fun d hd hu => (hst2 d hd hu).2.2)
    obtain ⟨ω3, μ3, run3, c0, c1, c5, c6, c7, c8, c9, m56', fr3, rd3, wr3⟩ :=
      rl_errcode (R := KeepCtx (accContractS env)) (P := P) (c, f) ω2 μ2 (sp - 96) (rp + 144 * k) e.tag
        (b1.trans (a1.trans h1)) (b6.trans (a6.trans h6)) (by omega) (by omega) (by have := tag_lt e; omega)
        (by rw [hi2.2, encodeLE_one (by have := tag_lt e; omega)])
        (rdI μ2 s2 H2 (fun d hd hu => (hst2 d hd hu).1) 1 (by omega))
        (H2.st _ (by omega) (by omega))
    have H3 : HeapCtxC env.code pb S0 S1 μ3 s2 := HeapKeep.keepHi H2 (fun a ha => fr3 a (by omega) (by omega)) wr3
    obtain ⟨-, -, -, -, -, hl2, -, -, ch2, hch2, hchu2, hcha2, hchs2⟩ := id WP2
    have := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf hch2 hchu2
    have := H2.hbT
    have WP3 := WriterPre.congr WP2 (fun b h1 h2 => fr3 b (by omega) (by omega))
    have hst3 : ∀ d ∈ chunks st, d.used = true → d ∈ chunks s2 ∧ d.addr + 32 ≠ r2 ∧
        ∀ a, InData d a → μ3.read a = μ₀.read a := fun d hd hu => by
      obtain ⟨k1, k2, k3⟩ := hst2 d hd hu
      refine ⟨k1, k2, fun a ha => ?_⟩
      have := Services.Bootstrap.Decode.VecU8.chunk_in H2.wf k1 hu
      unfold InData at ha
      rw [fr3 a (by omega) (by omega)]; exact k3 a ⟨ha.1, ha.2⟩
    rcases ext_step hE c f ω3 μ3 s2 st μ₀ sp cap2 r2 ((encK n rs k).length + 1) 1702 36394 H3 WP3 hst3
        (by rw [hrk, encode_error] at hlen; simp at hlen; omega) hsp hS1
        c0 (c1.trans (b1.trans (a1.trans h1))) c7 c8 c9 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_850]) bs_36394 with
      ⟨ω4, μ4, s4, N4, run4, d1, d5, d6, cap4, r4, WP4, out4, hc4, H4, hst4, stk4, lo4, gl4⟩ | hx
    rotate_left
    · exact .inr (ExhaustsP.pre ((run1.trans run2).trans run3) hx)
    obtain ⟨ω5, run5, g1, g5, g6, -⟩ := rl_next (R := KeepCtx (accContractS env)) (P := P) (c, f) ω4 μ4 36394
      (n - k - 1) (rp + 144 * k) (.inr rfl)
      (by rw [d5, c5, b5, a5, h5]; congr 1; omega) (by rw [d6, c6, b6, a6, h6]) (by omega) (by omega)
    refine .inl ⟨ω5, μ4, s4, _, by
        rw [show n - (k + 1) = n - k - 1 by omega]
        exact (((run1.trans run2).trans run3).trans run4).trans run5, ?_⟩
    have hlenE : (encK n rs (k + 1)).length = (encK n rs k).length + 1 + 1 := by
      rw [encK_succ n rs k hk', hrk, encode_error]; simp
    refine ⟨by rw [g1, d1, c1, b1, a1, h1], by rw [g5, show n - (k + 1) = n - k - 1 by omega],
      by rw [g6, show rp + 144 * (k + 1) = rp + 144 * k + 144 by omega], H4,
      ⟨cap4, r4, by rw [hlenE]; exact WP4, ?_, by rw [hlenE]; omega, hst4⟩, ?_, ?_, ?_⟩
    · rw [hlenE, out4, m56', show (encK n rs k).length + 1 = (encK n rs k).length + 1 from rfl]
      have e3 : μ3.readN r2 ((encK n rs k).length + 1) = μ2.readN r2 ((encK n rs k).length + 1) :=
        Memory.readN_congr fun j hj => fr3 _ (by omega) (by omega)
      rw [e3, out2, m56, mout1, encK_succ n rs k hk', hrk, encode_error, encodeLE_one (by have := tag_lt e; omega)]
      simp
    · intro a h0 ha hb
      rw [stk4 a h0 ha (by omega), fr3 a h0 (by omega), stk2 a h0 ha (by omega), fr1 a h0 (by omega)]
      exact hfr a h0 ha hb
    · intro a ha
      obtain ⟨l4, l4'⟩ := lo4 a ha
      obtain ⟨l2, l2'⟩ := lo2 a ha
      obtain ⟨l0, l0'⟩ := hlo a ha
      refine ⟨by rw [l4, fr3 a (by omega) (by omega), l2, fr1 a (by omega) (by omega), l0], ?_⟩
      rw [l4', show μ3.readable a = μ2.readable a from by rw [rd3], l2', rd1, l0']
    · intro a ha
      have hg := ha; unfold Glob at hg
      rw [gl4 a ha, fr3 a (by omega) (by omega), gl2 a ha, fr1 a (by omega) (by omega), hgl a ha]
  | ok r =>
    have hi := itemAt μ hstd
    obtain ⟨t, ht7, mt⟩ := OkAt.tag hi
    obtain ⟨ω1, μ1, run1, a0, a1, a5, a6, a7, a8, a9, m56, fr1, rd1, wr1⟩ :=
      rl_ok (R := KeepCtx (accContractS env)) (P := P) (c, f) ω μ (sp - 96) (rp + 144 * k) t h1 h6 (by omega)
        (by omega) (by omega) (by omega) mt
        (by have := rdI μ s H (fun d hd hu => (hst d hd hu).1) 0 (by omega); simpa using this) hS56
    obtain ⟨H1, WP1, mout1, hst1⟩ := stage μ1 fr1 wr1
    rcases ext_step hE c f ω1 μ1 s st μ₀ sp cap ptr (encK n rs k).length 1696 36290 H1 WP1 hst1 (by
          have := encode_ok_len r; rw [hrk] at hlen; omega) hsp hS1
        a0 (a1.trans h1) a7 a8 a9 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_847]) bs_36290 with
      ⟨ω2, μ2, s2, N2, run2, b1, b5, b6, cap2, r2, WP2, out2, hc2, H2, hst2, stk2, lo2, gl2⟩ | hx
    rotate_left
    · exact .inr (ExhaustsP.pre run1 hx)
    obtain ⟨ω3, run3, c0, c1, c5, c6, c7, c8⟩ :=
      rl_okenc (R := KeepCtx (accContractS env)) (P := P) (c, f) ω2 μ2 (sp - 96) (b1.trans (a1.trans h1)) (by omega)
    have hi2 := itemAt μ2 (fun d hd hu => (hst2 d hd hu).2.2)
    rcases hO c f ω3 μ2 s2 st r (sp - 96) (sp - 96 + 32) (rp + 144 * k) cap2 r2 ((encK n rs k).length + 1)
        1698 36335 H2 WP2 (by rw [hrk] at hlen; omega) ⟨by omega, by omega, by omega, by omega⟩ hi2 hIH
        (fun d hd hu => ⟨(hst2 d hd hu).1, (hst2 d hd hu).2.1⟩) c0 (c1.trans (b1.trans (a1.trans h1)))
        (c7.trans (b6.trans (a6.trans h6))) c8 ⟨by decide, by decide, by decide⟩
        (by simp only [Nat.reduceDiv, Nat.reduceSub, jte_848]) bs_36335 with
      ⟨ω4, μ4, s4, N4, run4, d1, d5, d6, post4⟩ | hx
    rotate_left
    · exact .inr (ExhaustsP.pre ((run1.trans run2).trans run3) hx)
    have hbs : 0 < ((Spec.Result.encode (.ok r)).drop 1).length := by
      have := encode_ok_len r; simp; omega
    obtain ⟨cap4, r4, WP4, out4, hc4, H4, hst4, stk4, lo4, gl4⟩ := writer_chain post4 hst2 WP2
      (by rw [hrk] at hlen; simp only [List.length_drop]; have := encode_ok_len r; omega) hbs WP2.2.2.2.2.2.2.2.1
    obtain ⟨ω5, run5, g1, g5, g6, -⟩ := rl_next (R := KeepCtx (accContractS env)) (P := P) (c, f) ω4 μ4 36335
      (n - k - 1) (rp + 144 * k) (.inl rfl)
      (by rw [d5, c5, b5, a5, h5]; congr 1; omega) (by rw [d6, c6, b6, a6, h6]) (by omega) (by omega)
    have hlenO : (encK n rs (k + 1)).length =
        (encK n rs k).length + 1 + ((Spec.Result.encode (.ok r)).drop 1).length := by
      rw [encK_succ n rs k hk', hrk, List.length_append, encode_ok r]; simp; omega
    refine .inl ⟨ω5, μ4, s4, _, by
        rw [show n - (k + 1) = n - k - 1 by omega]
        exact (((run1.trans run2).trans run3).trans run4).trans run5, ?_⟩
    refine ⟨by rw [g1, d1], by rw [g5, show n - (k + 1) = n - k - 1 by omega],
      by rw [g6, show rp + 144 * (k + 1) = rp + 144 * k + 144 by omega], H4,
      ⟨cap4, r4, by rw [hlenO]; exact WP4, ?_, by rw [hlenO]; omega, hst4⟩, ?_, ?_, ?_⟩
    · rw [hlenO, out4, out2, m56, mout1, encK_succ n rs k hk', hrk, encode_ok r]
      simp
    · intro a h0 ha hb
      rw [stk4 a h0 ha (by omega), stk2 a h0 ha (by omega), fr1 a h0 (by omega)]
      exact hfr a h0 ha hb
    · intro a ha
      obtain ⟨l4, l4'⟩ := lo4 a ha
      obtain ⟨l2, l2'⟩ := lo2 a ha
      obtain ⟨l0, l0'⟩ := hlo a ha
      exact ⟨by rw [l4, l2, fr1 a (by omega) (by omega), l0], by rw [l4', l2', rd1, l0']⟩
    · intro a ha
      have hg := ha; unfold Glob at hg
      rw [gl4 a ha, gl2 a ha, fr1 a (by omega) (by omega), hgl a ha]


/-- **The results loop** (36346 → 36405): from `LoopInv k` with k < n, the remaining n − k passes reach
    `LoopInv n` at 36405, or the heap is exhausted. -/
theorem rl_loop {p : ByteArray} {P : Program} [HasCode p P] [HasCodeA p P] {env : AccEnv} {pb S0 S1 : Nat}
    (hE : ExtendH p P env pb S0 S1) (hO : OkEncH p P env pb S0 S1)
    (c : AccCtx) (f : Stream) (sp rp n : Nat) (rs : List Spec.Result)
    (st : State) (μ₀ : Memory) (L : LoopHyp pb S0 S1 sp rp n rs st μ₀) :
    ∀ (k : Nat) (ω : Regs) (μ : Memory) (s : State), k < n →
    LoopInv env.code pb S0 S1 sp rp n rs st μ₀ k ω μ s →
    (∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 36346 ω μ (c, f) 36405 ω' μ' (c, f) N ∧
      LoopInv env.code pb S0 S1 sp rp n rs st μ₀ n ω' μ' s') ∨
    ExhaustsP p env pb 36346 ω μ c f := by
  suffices h : ∀ m k ω μ s, n - (k + 1) = m → k < n →
      LoopInv env.code pb S0 S1 sp rp n rs st μ₀ k ω μ s →
      (∃ ω' μ' s' N, FreeStepsH p (KeepCtx (accContractS env)) 36346 ω μ (c, f) 36405 ω' μ' (c, f) N ∧
        LoopInv env.code pb S0 S1 sp rp n rs st μ₀ n ω' μ' s') ∨
      ExhaustsP p env pb 36346 ω μ c f from
    fun k ω μ s hk I => h _ k ω μ s rfl hk I
  intro m
  induction m with
  | zero =>
    intro k ω μ s hm hk I
    rcases rl_item hE hO c f ω μ s sp rp n rs st μ₀ k L hk I with ⟨ω', μ', s', N, run, I'⟩ | hx
    · simp only [hm, ↓reduceIte] at run
      have e : k + 1 = n := by omega
      rw [e] at I'
      exact .inl ⟨ω', μ', s', N, run, I'⟩
    · exact .inr hx
  | succ m ih =>
    intro k ω μ s hm hk I
    rcases rl_item hE hO c f ω μ s sp rp n rs st μ₀ k L hk I with ⟨ω', μ', s', N, run, I'⟩ | hx
    · have hm' : n - (k + 1) ≠ 0 := by omega
      simp only [hm', ↓reduceIte] at run
      rcases ih (k + 1) ω' μ' s' (by omega) (by omega) I' with ⟨ω'', μ'', s'', N', run', I''⟩ | hx
      · exact .inl ⟨ω'', μ'', s'', N + N', run.trans run', I''⟩
      · exact .inr (ExhaustsP.pre run hx)
    · exact .inr hx

end Services.Bootstrap.Acc.Handlers.ResStore
