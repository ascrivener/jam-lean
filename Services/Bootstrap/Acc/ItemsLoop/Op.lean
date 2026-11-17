import Services.Bootstrap.Acc.ItemsLoop.OpDec
import Services.Bootstrap.Acc.ItemsLoop.OpHead
import Services.Bootstrap.Acc.ItemsLoop.OpSpec
import Services.Bootstrap.Acc.ItemsLoop.ImplRO
import Services.Bootstrap.Acc.Handlers.RecentAdd
import Services.Bootstrap.Acc.Handlers.ResultsInit

/-!
# The items loop's operand arm (R2)

An operand whose work result is an output b (`Spec.Item.work p (some b)`): the spec runs
`onWorkItem C now p b` (GP v0.8.0 Appendix B, Ω_W) then `yield`. The binary:
- 6766 → 7009, the arms' common head (`opArm_head`, with the item's log line `ItemLogFmt`);
- 7009 → 8013, the output's decode (`op_dec`, the named hypothesis `OutDecH`): a decode error is the
  spec's `panic` (15361); otherwise the results `Vec` gets capacity |is| and the package is copied;
- 8013 → 8416, row 8 (`add_recent`, spec `addRecent`);
- 8416 → 8492, row 9 (`results_init`, the empty results' write and `checkpoint`);
- 8492 → 6766, R5 and R7 (`loop_row11`, the instruction loop and row 11, with Handlers A's named
  hypotheses `InstrLogH`, `ResultLogH`, `HandlerH`, `PushH`, `ExtendH`, `OkEncH`, `DropInstrsH`);
back at the loop head with `ItemsInv` for the rest (`op_r57`).
-/

namespace Services.Bootstrap.Acc

open PVM JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeA Services.Bootstrap.CodeX
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Picoalloc Services.Bootstrap.Spec
  Services.Bootstrap.Acc.Handlers.InstrRep Services.Bootstrap.Acc.Handlers.InstrLoop
  Services.Bootstrap.Acc.Handlers.RowEleven Services.Bootstrap.Acc.Handlers.ResultsDrop
  Services.Bootstrap.Acc.Handlers.HeapKeep
open JAM.Codec (fixed)

/-- Every operation. -/
def TrueOp : ∀ {β : Type}, AOp β → Prop := fun _ => True

theorem prog_all_true {α : Type} : ∀ prog : Prog AOp α, Prog.All TrueOp prog
  | .pure _ => trivial
  | .call _ k => ⟨trivial, fun b => prog_all_true (k b)⟩
  | .panic => trivial

/-- **`Impl` keeps `ValuesFit` and the read-only data.** -/
theorem Impl.fitRO {p : ByteArray} {env : AccEnv} {pb : Nat} (hbd : heapBounds env.code = (48, pb))
    {Ab : St Stream → Prop} {α : Type} {Q : α → St Stream → Prop} (prog : Prog AOp α) (s : St Stream)
    (hw : ∀ a, a < 196608 → s.μ.writable a = false) (hf : ValuesFit env s.c.1)
    (h : Impl p (accContractS env) env Ab prog Q s) :
    Impl p (accContractS env) env Ab prog
      (fun a s' => (Q a s' ∧ ValuesFit env s'.c.1) ∧ LoKept s.μ s'.μ) s :=
  Impl.keepRO hbd prog s hw (Impl.inv TrueOp (fun c => ValuesFit env c.1)
    (fun o _ _ _ _ h hs => ValuesFit.step o h hs) prog s (prog_all_true prog) hf h)

/-- An address among three optional buffers. -/
theorem mem_opt3 {q n r c1 p1 c2 p2 : Nat} (h : q ∈ optBuf n r ++ optBuf c1 p1 ++ optBuf c2 p2) :
    (n ≠ 0 ∧ q = r) ∨ (c1 ≠ 0 ∧ q = p1) ∨ (c2 ≠ 0 ∧ q = p2) := by
  unfold optBuf at h
  by_cases a : n = 0 <;> by_cases b : c1 = 0 <;> by_cases c : c2 = 0 <;> simp_all

/-- The instructions' buffers and three optional buffers, pairwise distinct. -/
theorem nodup_opt3 {V : List Nat} {n r c1 p1 c2 p2 : Nat} (hV : V.Nodup)
    (h1 : n ≠ 0 → r ∉ V) (h2 : c1 ≠ 0 → p1 ∉ V) (h3 : c2 ≠ 0 → p2 ∉ V)
    (h12 : n ≠ 0 → c1 ≠ 0 → r ≠ p1) (h13 : n ≠ 0 → c2 ≠ 0 → r ≠ p2)
    (h23 : c1 ≠ 0 → c2 ≠ 0 → p1 ≠ p2) :
    (V ++ (optBuf n r ++ optBuf c1 p1 ++ optBuf c2 p2)).Nodup := by
  rw [List.nodup_append]
  refine ⟨hV, ?_, fun a ha b hb hab => ?_⟩
  · unfold optBuf
    by_cases a : n = 0 <;> by_cases b : c1 = 0 <;> by_cases c : c2 = 0 <;>
      simp_all [List.nodup_append, List.nodup_cons, eq_comm]
  · subst hab
    rcases mem_opt3 hb with ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩
    · exact h1 hn ha
    · exact h2 hn ha
    · exact h3 hn ha

/-- `tailFree` with no results. -/
theorem tailFree_nil {μ : Memory} {sp : Nat} (h : rdN μ (sp + 464) 8 = 0) :
    tailFree μ sp = optBuf (rdN μ (sp + 448) 8) (rdN μ (sp + 456) 8) ++
      optBuf (rdN μ (sp + 128) 8) (rdN μ (sp + 104) 8) ++ optBuf (rdN μ (sp + 264) 8) (rdN μ (sp + 272) 8) := by
  unfold tailFree tailBufs
  rw [h, show resPtrs μ (rdN μ (sp + 456) 8) 0 = [] from rfl, List.nil_append]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **8492 → 6766, then `yield`**: from row 9's end with `EntryHyp`, `loop_row11` (R5, R7) implements the
    instruction loop and the final write, and the loop head's `ItemsInv` holds for the rest, given what
    the state s₄ at 8492 kept of the loop head's state s (the frame words, the cursor advanced, the slot
    buffer's chunk and the rest's buffers with their data and outside what R5 / R7 free, the statics,
    the read-only data, `ValuesFit`). -/
theorem op_r57 {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (B : InstrRep) {C : Consts} {now pb S0 S1 : Nat} {Ab : St Stream → Prop}
    (hL : InstrLogH B p env pb S0 S1) (hR : ResultLogH p env pb S0 S1) (hH : HandlerH B p env C now pb S0 S1 Ab)
    (hP : PushH p env pb S0 S1) (hE : Handlers.Results.ExtendH p P env pb S0 S1) (hO : Handlers.Results.OkEncH p P env pb S0 S1)
    (hD : DropInstrsH B p P env.code pb S0 S1)
    (gcap : Nat) (hcap1 : 134217728 ≤ gcap) (hcap : gcap < 18446744073709551616)
    (hAb1 : ∀ s : St Stream, s.i = 36528 → Ab s) (hAb2 : ∀ s : St Stream, s.i = 34070 → Ab s)
    (hAbX : ∀ s : St Stream, (s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0 → Ab s)
    {sp q nc e : Nat} {μ₀ : Memory} (o : OperandTuple) (rest : List AccumulateInput) (s : St Stream)
    (Q : ForInStep PUnit → St Stream → Prop)
    (hQ : ∀ s', ItemsInv env pb S0 S1 sp q nc e μ₀ rest s' → Q (.yield ⟨⟩) s')
    (hI : ItemsInv env pb S0 S1 sp q nc e μ₀ (.operand o :: rest) s) (st : State) (cur : Nat)
    (hc : curAt sp s = cur) (db : Chunk) (hdb : db ∈ chunks st) (hdbu : db.used = true)
    (hdbq : db.addr + 32 = q) (hdata : ∀ a, cur ≤ a → a < e → InDataA db a)
    (hslots : ∀ (j : Nat) (i : AccumulateInput), (.operand o :: rest)[j]? = some i →
      (itemOf i).2 (s.μ.readN (cur + 184 * j) 184) s.μ)
    (hown : ItemsOwn st s.μ cur q (.operand o :: rest))
    (s₄ : St Stream) (st₄ : State) (b c item kc : Nat) (is : List Spec.Instr) (pkg : List UInt8)
    (hi : s₄.i = 8492) (h1 : s₄.ω[1] = UInt64.ofNat sp) (h6 : s₄.ω[6] = UInt64.ofNat b)
    (E : EntryHyp B env.code pb S0 S1 sp b c is s₄.μ st₄) (hfit : ValuesFit env s₄.c.1)
    (hpkg : s₄.μ.readN (sp + 312) 32 = pkg) (hitem : s₄.μ.readN (sp + 176) 2 = fixed 2 item)
    (hro : TrRO s₄.μ) (hro2 : OpRO s₄.μ)
    (mkc : s₄.μ.readN 68696 8 = Num.encodeLE 8 kc) (hkc : 35 ≤ kc ∧ kc + 31 < 68719476736)
    (hw : ∀ a, a < 196608 → s₄.μ.writable a = false)
    (kw : ∀ k, (k = 16 ∨ k = 32 ∨ k = 136 ∨ k = 144 ∨ k = 184 ∨ k = 208 ∨ k = 216 ∨ k = 1848) →
      rdN s₄.μ (sp + k) 8 = rdN s.μ (sp + k) 8)
    (k168 : rdN s₄.μ (sp + 168) 8 = cur + 184)
    (hK : ∀ d ∈ chunks st, d.used = true → (d.addr + 32 ∈ (footL rest (cur + 184) s.μ).map Prod.fst ∨ d = db) →
      d ∈ chunks st₄ ∧ (∀ a, InDataA d a → s₄.μ.read a = s.μ.read a) ∧
      d.addr + 32 ∉ vecFree B s₄.μ b c is.length ++ tailFree s₄.μ sp)
    (hgl : ∀ a, Glob a → s₄.μ.read a = s.μ.read a) :
    Impl p (accContractS env) env Ab
      (Prog.bind (Prog.bind (forIn is [] (wiBody C now (.results pkg item))) (fun rs =>
        if is.any isZomb then pure () else store (.results pkg item) (encodeResults rs)))
        (fun _ => pure (ForInStep.yield PUnit.unit))) Q s₄ := by
  have hsp := hI.hsp
  have hstk := hI.hstk
  have hS1 := E.H.hS1
  have hl := hI.cur
  simp only [List.length_cons] at hl
  rw [hc] at hl
  obtain ⟨⟨k0, e0, b0⟩, ⟨k1, e1, b1⟩, ⟨k2, e2, b2⟩, r1, ej, r2⟩ := hro2
  have LR := loop_row11 (P := P) env B hL hR hH hP hE hO hD gcap hcap1 hcap hAb1 hAb2 hAbX
    (fun c => ValuesFit env c.1) (fun o _ _ _ h hs => ValuesFit.step o h hs) (fun c h => ValuesFit.storage h)
    s₄ st₄ sp b c item kc is hi h1 h6 E hfit (wiBody C now (.results pkg item))
    (fun rs => by rw [wiBody_ck, hpkg]) (fun i rs hne => wiBody_other C now _ i rs hne) hitem mkc hkc
    hro.2.2.1 hro.2.2.2.1 r1 ej r2
  rw [hpkg] at LR
  refine Impl.bind _ Q _ _ (Impl.mono_post ?_ _ _ (Impl.fitRO E.H.bd _ s₄ hw hfit LR))
  rintro _ s₅ ⟨⟨⟨hi5, h15, st₅, H₅, keep₅, stab₅, gl₅⟩, hfit₅⟩, lo₅⟩
  refine Impl.pure_of (hQ s₅ ?_)
  have ks : ∀ k, 16 ≤ k → k + 8 ≤ 40 ∨ (104 ≤ k ∧ k + 8 ≤ 152) ∨ (168 ≤ k ∧ k + 8 ≤ 224) ∨ 1632 ≤ k →
      k + 8 ≤ 1856 → rdN s₅.μ (sp + k) 8 = rdN s₄.μ (sp + k) 8 := fun k hk0 hk h8 =>
    rdN_frame fun j hj => stab₅ _ (by omega) (by unfold StableKeep; omega)
  have hcur' : curAt sp s₅ = cur + 184 := by
    rw [curAt_6766 hi5, ks 168 (by omega) (by omega) (by omega), k168]
  have kw' : ∀ k, (k = 16 ∨ k = 32 ∨ k = 136 ∨ k = 144 ∨ k = 184 ∨ k = 208 ∨ k = 216 ∨ k = 1848) →
      rdN s₅.μ (sp + k) 8 = rdN s.μ (sp + k) 8 := fun k hk => by
    rw [ks k (by omega) (by omega) (by omega), kw k hk]
  have datf : ∀ d ∈ chunks st, d.used = true →
      (d.addr + 32 ∈ (footL rest (cur + 184) s.μ).map Prod.fst ∨ d = db) →
      d ∈ chunks st₅ ∧ ∀ a, InDataA d a → s₅.μ.read a = s.μ.read a := fun d hd hu hm => by
    obtain ⟨h4, d4, n4⟩ := hK d hd hu hm
    obtain ⟨h5, d5⟩ := keep₅ d h4 hu n4
    exact ⟨h5, fun a ha => (d5 a ha).trans (d4 a ha)⟩
  obtain ⟨sl', own'⟩ := rest_keep (st' := st₅) (μ' := s₅.μ) (db := db) hslots hown
    (fun a h1 h2 => hdata a h1 (by omega)) (fun a ha => (datf db hdb hdbu (.inr rfl)).2 a ha)
    (fun d0 h0 hu hm => datf d0 h0 hu (.inl hm))
  refine ⟨.inl hi5, h15, hsp, hstk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfit₅, ?_⟩
  · rw [hcur']; omega
  · rw [kw' 144 (by omega)]; exact hI.m144
  · rw [kw' 16 (by omega)]; exact hI.m16
  · rw [kw' 32 (by omega)]; exact hI.m32
  · rw [kw' 208 (by omega)]; exact hI.m208
  · rw [kw' 136 (by omega)]; exact hI.m136
  · rw [kw' 184 (by omega)]; exact hI.m184
  · rw [kw' 216 (by omega)]; exact hI.m216
  · rw [kw' 1848 (by omega)]; exact hI.m1848
  · have := hI.hcap; simp only [List.length_cons] at this; omega
  · refine ⟨st₅, H₅, fun _ => ⟨db, (datf db hdb hdbu (.inr rfl)).1, hdbu, hdbq, fun a h1 h2 => ?_⟩, ?_, ?_⟩
    · rw [hcur'] at h1; exact hdata a (by omega) h2
    · rw [hcur']; exact sl'
    · rw [hcur']; exact own'
  · exact hro.keep fun a ha => ⟨(lo₅ a ha).1, (lo₅ a ha).2.1⟩
  · exact (show OpRO s₄.μ from ⟨⟨k0, e0, b0⟩, ⟨k1, e1, b1⟩, ⟨k2, e2, b2⟩, r1, ej, r2⟩).keep
      fun a ha => ⟨(lo₅ a ha).1, (lo₅ a ha).2.1⟩
  · intro a ha
    rw [gl₅ a ha, hgl a ha]; exact hI.glob a ha
  · intro i hi; exact hI.sized i (by simp [hi])

/-- The package hash in an operand slot (octets 48 … 80). -/
theorem pkg_of_slot {μ : Memory} {cur : Nat} {o : OperandTuple}
    (bh : ((μ.readN cur 184).drop 48).take 128 = opHashes o) (hs : o.packageHash.size = 32) :
    μ.readN (cur + 48) 32 = o.packageHash.toList := by
  rw [← readN_drop_take μ cur 184 48 32 (by omega)]
  have e : ((μ.readN cur 184).drop 48).take 32 = (((μ.readN cur 184).drop 48).take 128).take 32 := by
    rw [List.take_take]; rfl
  rw [e, bh, opHashes, List.append_assoc, List.append_assoc]
  exact List.take_left' (by rw [ByteArray.length_toList']; exact hs)

/-- An octet range inside a copied block. -/
theorem readN_of_copy {μ ν : Memory} {d s n k m : Nat} (h : μ.readN d n = ν.readN s n) (hk : k + m ≤ n) :
    μ.readN (d + k) m = ν.readN (s + k) m := by
  rw [← readN_drop_take μ d n k m hk, ← readN_drop_take ν s n k m hk, h]

/-- A buffer of the current slot is not one of the rest's, nor the slot buffer. -/
theorem ne_slot {st : State} {μ : Memory} {cur q : Nat} {i : AccumulateInput} {rest : List AccumulateInput}
    (hown : ItemsOwn st μ cur q (i :: rest)) {x : Nat}
    (hx : x ∈ (slotFoot i (μ.readN cur 184)).map Prod.fst) {y : Nat}
    (hy : y ∈ (footL rest (cur + 184) μ).map Prod.fst ∨ y = q) : y ≠ x := by
  obtain ⟨hnd, hq, -⟩ := hown
  simp only [footL, List.map_append] at hnd hq
  rintro rfl
  rcases hy with hy | rfl
  · exact (List.nodup_append.1 hnd).2.2 _ hx _ hy rfl
  · exact hq (List.mem_append_left _ hx)

/-- The words row 8 and row 9 leave: off `AddOut` and `R9Out`. -/
theorem safe89 {sp a : Nat}
    (h : a < sp + 88 ∨ (sp + 104 ≤ a ∧ a < sp + 232) ∨ (sp + 240 ≤ a ∧ a < sp + 744) ∨ sp + 1604 ≤ a) :
    ¬ Handlers.RecentAdd.AddOut sp a ∧ ¬ Handlers.ResultsInit.R9Out sp a := by
  simp only [Handlers.RecentAdd.AddOut, Handlers.RecentMatch.RmOut, Handlers.RecentSlotWrite.SwOut,
    Handlers.RecentCounter.CwOut, Handlers.ResultsInit.R9Out]
  omega

/-- `ResultsOwn` of no results. -/
theorem resultsOwn_nil (μ : Memory) (st : State) (rp : Nat) : ResultsOwn μ st rp 0 :=
  ⟨by simp [resPtrs], by simp [resPtrs], fun k hk => absurd hk (by omega), fun i hi => absurd hi (by omega)⟩

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **R2, the items loop's operand arm** (`OpArm`): from the loop head with an operand with a work
    output b next, the run implements `onWorkItem C now p b` then `yield` (GP v0.8.0 Appendix B, Ω_W)
    and returns to the loop head with `ItemsInv` for the rest; early ☇ only where `Ab` holds (heap
    exhaustion: `HeapFailT`, the traps 15364, 34070, 47977, 32584, 36528, a failed allocator call at
    40611 / 40821 with ω₇ = 0). Named hypotheses: `ItemLogFmt` (the item's log line), `OutDecH` (R3, the output's decode),
    Handlers A's `InstrLogH`, `ResultLogH` (G4), `HandlerH` (R6), `PushH` (R8), `ExtendH`, `OkEncH`
    (R8 / R9), `DropInstrsH`; `ParamStatics μ₀ Cp I` for the statics μ₀ fixes (proved from the prologue,
    `start_to_6429_statics`), `RingFits Cp I` and maxRecent = 2·𝖢·𝖨 (row 8). -/
theorem op_arm {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P] (env : AccEnv)
    (B : InstrRep) (C : Consts) (now : Nat) {Ab : St Stream → Prop} {pb S0 S1 : Nat}
    (gcap : Nat) (hcap1 : 134217728 ≤ gcap) (hcap : gcap < 18446744073709551616)
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (hAbT : ∀ s : St Stream, s.i = 15364 ∨ s.i = 34070 ∨ s.i = 47977 ∨ s.i = 32584 ∨ s.i = 36528 → Ab s)
    (hAbX : ∀ s : St Stream, (s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0 → Ab s)
    (hIL : ItemLogFmt p env pb S0 S1) (hOD : OutDecH B C p env pb S0 S1)
    (hL : InstrLogH B p env pb S0 S1) (hR : ResultLogH p env pb S0 S1) (hH : HandlerH B p env C now pb S0 S1 Ab)
    (hP : PushH p env pb S0 S1) (hE : Handlers.Results.ExtendH p P env pb S0 S1) (hO : Handlers.Results.OkEncH p P env pb S0 S1)
    (hD : DropInstrsH B p P env.code pb S0 S1)
    {Cp I : Nat} (hRF : Handlers.RecentSlotWrite.RingFits Cp I) (hmax : C.maxRecent = 2 * Cp * I)
    {sp q nc e : Nat} {μ₀ : Memory} (hPS : Handlers.RecentSlotWrite.ParamStatics μ₀ Cp I) :
    OpArm p env Ab C now pb S0 S1 sp q nc e μ₀ := by
  intro o bo rest s Q hr hQ hI
  obtain ⟨st, H, hbuf, hslots, hown⟩ := hI.heap
  have hS1 := H.hS1
  have hsp := hI.hsp
  have hstk := hI.hstk
  have hl := hI.cur
  simp only [List.length_cons] at hl
  generalize hc : curAt sp s = cur at hl hbuf hslots hown
  have hnc : nc ≠ 0 := by have := hI.hcap; simp only [List.length_cons] at this; omega
  obtain ⟨db, hdb, hdbu, hdbq, hdata⟩ := hbuf hnc
  have hin : ∀ a, cur ≤ a → a < cur + 184 → InDataA db a := fun a h1 h2 => hdata a h1 (by omega)
  have hlo := heapC_data_lt H hdb (hin cur (Nat.le_refl _) (by omega))
  -- the slot
  have hslot := hslots 0 (.operand o) rfl
  simp only [itemOf, hr, Nat.mul_zero, Nat.add_zero] at hslot
  obtain ⟨⟨b0, -, -, bh, -⟩, b24, b40, bo32⟩ := hslot
  have hsz := hI.sized (.operand o) (by simp)
  simp only [InputSized] at hsz
  have htl : o.authTrace.toList.length ≤ 16384 := by
    rw [ByteArray.length_toList']; exact hsz.2.2.2.2.2.1
  have hbl : bo.toList.length ≤ 16384 := by rw [ByteArray.length_toList']; exact hsz.2.2.2.2.2.2 bo hr
  have e0 : rdN s.μ cur 8 = o.authTrace.toList.length := by
    rw [← b0, wd_slot s.μ cur 0 (by omega), Nat.add_zero]
  generalize hW8 : wd (s.μ.readN cur 184) 8 = tp
  generalize hW32 : wd (s.μ.readN cur 184) 32 = ptr at bo32
  -- the head, 6766 → 7009
  rcases opArm_head (P := P) env hAb hIL o rest s hI st H cur hc db hdb hdbu hin (by rw [e0]; omega) with
    hab | ⟨s₁, run1, Hd⟩
  · exact Impl.abort _ _ hab
  obtain ⟨hi1, hc1, h11, ⟨st₁, H₁, keep₁⟩, cpy, m168, m200, m264, kw1, gl1, lo1⟩ := Hd
  refine Impl.pre _ Q run1 hc1 ?_
  have cpw : ∀ k, k + 8 ≤ 128 → rdN s₁.μ (sp + 272 + k) 8 = rdN s.μ (cur + 8 + k) 8 := fun k hk =>
    rdN_of_copy cpy hk
  have w288 : rdN s₁.μ (sp + 288) 8 = bo.toList.length := by
    have := cpw 16 (by omega)
    rw [show sp + 272 + 16 = sp + 288 by omega, show cur + 8 + 16 = cur + 24 by omega,
      ← wd_slot s.μ cur 24 (by omega), b24] at this
    exact this
  have w296 : rdN s₁.μ (sp + 296) 8 = ptr := by
    have := cpw 24 (by omega)
    rw [show sp + 272 + 24 = sp + 296 by omega, show cur + 8 + 24 = cur + 32 by omega,
      ← wd_slot s.μ cur 32 (by omega), hW32] at this
    exact this
  have w304 : rdN s₁.μ (sp + 304) 8 = bo.toList.length := by
    have := cpw 32 (by omega)
    rw [show sp + 272 + 32 = sp + 304 by omega, show cur + 8 + 32 = cur + 40 by omega,
      ← wd_slot s.μ cur 40 (by omega), b40] at this
    exact this
  have w272 : rdN s₁.μ (sp + 272) 8 = tp := by
    have := cpw 0 (by omega)
    rw [Nat.add_zero, Nat.add_zero, ← wd_slot s.μ cur 8 (by omega), hW8] at this
    exact this
  have w264 : rdN s₁.μ (sp + 264) 8 = o.authTrace.toList.length := m264.trans e0
  have pk1 : s₁.μ.readN (sp + 312) 32 = o.packageHash.toList := by
    have := readN_of_copy (k := 40) (m := 32) cpy (by omega)
    rw [show sp + 272 + 40 = sp + 312 by omega, show cur + 8 + 40 = cur + 48 by omega] at this
    rw [this]; exact pkg_of_slot bh hsz.1
  -- the slot's buffers: the trace's (tp) and the output's (ptr), when their capacities are not 0
  have memT : o.authTrace.toList.length ≠ 0 → tp ∈ (slotFoot (.operand o) (s.μ.readN cur 184)).map Prod.fst :=
    fun h => by
      have hw0 : wd (s.μ.readN cur 184) 0 ≠ 0 := by rw [b0]; exact h
      simp [slotFoot, hr, hw0, hW8]
  have memO : bo.toList.length ≠ 0 → ptr ∈ (slotFoot (.operand o) (s.μ.readN cur 184)).map Prod.fst :=
    fun h => by
      have hw24 : wd (s.μ.readN cur 184) 24 ≠ 0 := by rw [b24]; exact h
      simp [slotFoot, hr, hw24, hW32]
  have chT : o.authTrace.toList.length ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = tp := fun h => by
    have hw0 : wd (s.μ.readN cur 184) 0 ≠ 0 := by rw [b0]; exact h
    obtain ⟨d, hd, hu, ha, -⟩ := hown.2.2 (wd (s.μ.readN cur 184) 8, wd (s.μ.readN cur 184) 16)
      (by simp [footL, slotFoot, hr, hw0])
    exact ⟨d, hd, hu, by rw [ha, hW8]⟩
  have chO : bo.toList.length ≠ 0 → ∃ d ∈ chunks st, d.used = true ∧ d.addr + 32 = ptr ∧
      ∀ a, ptr ≤ a → a < ptr + bo.toList.length → InDataA d a := fun h => by
    have hw24 : wd (s.μ.readN cur 184) 24 ≠ 0 := by rw [b24]; exact h
    obtain ⟨d, hd, hu, ha, hdr⟩ := hown.2.2 (wd (s.μ.readN cur 184) 32, wd (s.μ.readN cur 184) 40)
      (by simp [footL, slotFoot, hr, hw24])
    refine ⟨d, hd, hu, by rw [ha, hW32], fun a h1 h2 => hdr a (by rw [hW32]; exact h1) ?_⟩
    rw [hW32, b40]; exact h2
  have hout1 : s₁.μ.readN ptr bo.toList.length = bo.toList ∧
      ∀ a, ptr ≤ a → a < ptr + bo.toList.length → s₁.μ.readable a = true := by
    by_cases hb0 : bo.toList.length = 0
    · have hnil : bo.toList = [] := List.length_eq_zero_iff.1 hb0
      rw [hnil]; exact ⟨rfl, fun a h1 h2 => by simp at h2; omega⟩
    · obtain ⟨d, hd, hu, -, hdr⟩ := chO hb0
      obtain ⟨hd1, kd1⟩ := keep₁ d hd hu
      refine ⟨?_, fun a h1 h2 => Memory.readable_of_writable (heapC_writable_data H₁ hd1 hu (hdr a h1 h2))⟩
      rw [Memory.readN_congr fun j hj => kd1 _ (hdr _ (by omega) (by omega))]
      exact bo32
  -- the decode, 7009 → 8013
  rcases op_dec (P := P) env B C gcap hcap1 hcap hAb (fun s h => hAbT s (.inl h)) hOD s₁ st₁ sp
      bo.toList.length ptr bo.toList hi1 h11 H₁ hstk ⟨by omega, hsp.2⟩ w288 (by omega) w296 w304
      hout1.1 hout1.2 (fun h => by
        obtain ⟨d, hd, -, -, hdr⟩ := chO h
        have := heapC_data_lt H hd (hdr (ptr + bo.toList.length - 1) (by omega) (by omega))
        omega) with
    hab | ⟨hnone, hend⟩ | ⟨is, item, hsome, bv, cv, rp, st₂, s₂, run2, hc2, A⟩
  · exact Impl.abort _ _ hab
  · rw [onWorkItem_none C now _ _ hnone]; exact hend
  refine Impl.pre _ Q run2 hc2 ?_
  have H₂ := A.H
  have hfit2 : ValuesFit env s₂.c.1 := by rw [hc2, hc1]; exact hI.fit
  have lo2 : ∀ a, a < 196608 → s₂.μ.read a = s.μ.read a ∧ s₂.μ.readable a = s.μ.readable a := fun a ha =>
    ⟨(A.lo a ha).1.trans (lo1 a ha).1, (A.lo a ha).2.trans (lo1 a ha).2⟩
  have ro2 : OpRO s₂.μ := hI.ro2.keep lo2
  have tro2 : TrRO s₂.μ := hI.ro.keep lo2
  obtain ⟨k0, mc0, hk0⟩ := ro2.1
  obtain ⟨k1, mc1, hk1⟩ := ro2.2.1
  have rro := ro2.2.2.2.1
  have gl2 : ∀ a, Glob a → s₂.μ.read a = μ₀.read a := fun a ha => by
    rw [A.glob a ha, gl1 a ha]; exact hI.glob a ha
  have hPS2 : Handlers.RecentSlotWrite.ParamStatics s₂.μ Cp I := by
    obtain ⟨p1, p2, p3, p4⟩ := hPS
    refine ⟨?_, p2, ?_, p4⟩
    · rw [Memory.readN_congr fun j hj => gl2 _ (by unfold Glob; omega)]; exact p1
    · rw [Memory.readN_congr fun j hj => gl2 _ (by unfold Glob; omega)]; exact p3
  have pk2 : s₂.μ.readN (sp + 512) 32 = o.packageHash.toList := A.pkg.trans pk1
  -- row 8
  have hA1 : ∀ s : St Stream, s.i = 34070 → Ab s := fun s h => hAbT s (.inr (.inl h))
  have hA2 : ∀ s : St Stream, s.i = 47977 → Ab s := fun s h => hAbT s (.inr (.inr (.inl h)))
  have hA3 : ∀ s : St Stream, s.i = 32584 → Ab s := fun s h => hAbT s (.inr (.inr (.inr (.inl h))))
  have hA4 : ∀ s : St Stream, s.i = 36528 → Ab s := fun s h => hAbT s (.inr (.inr (.inr (.inr h))))
  have hsp352 : 2147483648 + 352 ≤ sp := Nat.le_trans (by decide) hsp.1
  have hS352 : S0 + 352 ≤ sp := Nat.le_trans (Nat.add_le_add_left (by decide : 352 ≤ 4096) S0) hstk.1
  -- (applied to all but its last premise: the full application would make the elaborator unfold the
  -- spec program; the program is generalized first)
  have ARk := @Handlers.RecentAdd.add_recent p P _ _ env gcap hcap1 hcap Ab hA1 hA2 hA3 C item s₂ st₂ sp k0 k1
    Cp I pb S0 S1 H₂ A.pc A.r1 ⟨hsp352, hsp.2⟩ hS352 hstk.2 mc0 hk0 mc1 hk1 tro2.2.2.1 tro2.2.2.2.1 rro
    hPS2 hRF hmax A.m176
  rw [pk2] at ARk
  rw [onWorkItem_some C now _ _ is item hsome, Prog.bind_assoc']
  generalize addRecent C o.packageHash.toList item = prg at ARk ⊢
  have AR := ARk (fun k w h => ValuesFit.storage hfit2 k w h)
  refine Impl.bind _ Q _ s₂ (Impl.mono_post ?_ _ _ (Impl.fitRO H₂.bd _ s₂ H₂.ro hfit2 AR))
  rintro _ s₃ ⟨⟨⟨hi3, h13, h63, st₃, H₃, keep₃, fr3, gl3, -⟩, hfit3⟩, lo3⟩
  have w3 : ∀ k, k + 8 ≤ 88 ∨ (104 ≤ k ∧ k + 8 ≤ 232) ∨ (240 ≤ k ∧ k + 8 ≤ 744) ∨ (1604 ≤ k ∧ k + 8 ≤ 1856) →
      rdN s₃.μ (sp + k) 8 = rdN s₂.μ (sp + k) 8 := fun k hk =>
    rdN_frame fun j hj => fr3 _ (by omega) (by omega) (safe89 (by omega)).1
  have hn3 : s₃.μ.readN (sp + 464) 8 = Num.encodeLE 8 0 := by
    have h0 : Num.decodeLE (s₃.μ.readN (sp + 464) 8) = 0 := (w3 464 (by omega)).trans A.m464
    rw [Handlers.KeyEnc.readN_enc s₃.μ (sp + 464) 8, h0]
  have it3 : s₃.μ.readN (sp + 176) 2 = fixed 2 item := by
    rw [Memory.readN_congr fun j hj => fr3 _ (by omega) (by omega) (safe89 (by omega)).1]; exact A.m176
  have pk3 : s₃.μ.readN (sp + 312) 32 = o.packageHash.toList := by
    rw [Memory.readN_congr fun j hj => fr3 _ (by omega) (by omega) (safe89 (by omega)).1,
      Memory.readN_congr fun j hj => A.frame _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact pk1
  have lo23 : ∀ a, a < 196608 → s₃.μ.read a = s₂.μ.read a ∧ s₃.μ.readable a = s₂.μ.readable a := fun a ha =>
    ⟨(lo3 a ha).1, (lo3 a ha).2.1⟩
  have ro3 := (show OpRO s₂.μ from hI.ro2.keep lo2).keep lo23
  have tro3 := tro2.keep lo23
  obtain ⟨k2', mc2', hk2'⟩ := ro3.2.2.1
  have rro3 := ro3.2.2.2.1
  -- row 9
  have RIk := @Handlers.ResultsInit.results_init p P _ _ _ env gcap hcap1 hcap Ab hA4 hA1 item s₃ st₃ sp k2' pb S0
    S1 H₃ hi3 h13 ⟨hsp352, hsp.2⟩ hS352 (Nat.le_trans (Nat.add_le_add_left (by decide : 1632 ≤ 1856) sp) hstk.2)
    hn3 mc2' hk2' tro3.2.2.1 tro3.2.2.2.1 rro3 it3
  rw [pk3] at RIk
  rw [show ∀ (M : PUnit → Prog AOp PUnit),
      Prog.bind (Prog.bind (store (.results o.packageHash.toList item) (encodeResults []))
        (fun _ => Prog.bind (Prog.op AOp.checkpoint) M)) (fun _ => pure (ForInStep.yield PUnit.unit)) =
      Prog.bind (Prog.bind (store (.results o.packageHash.toList item) (encodeResults []))
        (fun _ => Prog.op AOp.checkpoint)) (fun x => Prog.bind (M x) (fun _ => pure (ForInStep.yield PUnit.unit)))
      from fun M => by rw [Prog.bind_assoc', Prog.bind_assoc', Prog.bind_assoc']]
  generalize Prog.bind (store (.results o.packageHash.toList item) (encodeResults []))
    (fun _ => Prog.op AOp.checkpoint) = prg2 at RIk ⊢
  have RI := RIk (fun k w h => ValuesFit.storage hfit3 k w h)
  refine Impl.bind _ Q _ s₃ (Impl.mono_post ?_ _ _ (Impl.fitRO H₃.bd _ s₃ H₃.ro hfit3 RI))
  rintro _ s₄ ⟨⟨⟨hi4, h14, h64, st₄, H₄, keep₄, fr4, gl4, -, -⟩, hfit4⟩, lo4⟩
  -- the state at 8492 against the earlier ones
  have fr24 : ∀ a, a < 4294967296 → sp ≤ a →
      (a < sp + 88 ∨ (sp + 104 ≤ a ∧ a < sp + 232) ∨ (sp + 240 ≤ a ∧ a < sp + 744) ∨ sp + 1604 ≤ a) →
      s₄.μ.read a = s₂.μ.read a := fun a h1 h2 h3 =>
    (fr4 a h1 h2 (safe89 h3).2).trans (fr3 a h1 h2 (safe89 h3).1)
  have w4 : ∀ k, k + 8 ≤ 88 ∨ (104 ≤ k ∧ k + 8 ≤ 232) ∨ (240 ≤ k ∧ k + 8 ≤ 744) ∨ (1604 ≤ k ∧ k + 8 ≤ 1856) →
      rdN s₄.μ (sp + k) 8 = rdN s₂.μ (sp + k) 8 := fun k hk =>
    rdN_frame fun j hj => fr24 _ (by omega) (by omega) (by omega)
  have w21 : ∀ k, (k + 8 ≤ 104 ∨ (112 ≤ k ∧ k + 8 ≤ 128) ∨ (136 ≤ k ∧ k + 8 ≤ 176) ∨ (184 ≤ k ∧ k + 8 ≤ 240) ∨
      (256 ≤ k ∧ k + 8 ≤ 448) ∨ (1600 ≤ k ∧ k + 8 ≤ 1856)) → rdN s₂.μ (sp + k) 8 = rdN s₁.μ (sp + k) 8 :=
    fun k hk => rdN_frame fun j hj => A.frame _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have keep24 : ∀ d ∈ chunks st₂, d.used = true → d ∈ chunks st₄ ∧ ∀ a, InData d a → s₄.μ.read a = s₂.μ.read a :=
    fun d hd hu => ⟨(keep₄ d (keep₃ d hd hu).1 hu).1, fun a ha =>
      ((keep₄ d (keep₃ d hd hu).1 hu).2 a ha).trans ((keep₃ d hd hu).2 a ha)⟩
  obtain ⟨V4, hvf⟩ := VecOwn.keep A.V keep24
  have keep14 : ∀ d ∈ chunks st, d.used = true → d ∈ chunks st₁ ∧ d ∈ chunks st₄ ∧
      ∀ a, InDataA d a → s₄.μ.read a = s.μ.read a := fun d hd hu => by
    obtain ⟨h1, k1⟩ := keep₁ d hd hu
    obtain ⟨h2, k2⟩ := A.keep d h1 hu
    obtain ⟨h4, k4⟩ := keep24 d h2 hu
    exact ⟨h1, h4, fun a ha => ((k4 a ha).trans (k2 a ha)).trans (k1 a ha)⟩
  -- the words row 11 frees by
  have v448 : rdN s₄.μ (sp + 448) 8 = rdN s₂.μ (sp + 448) 8 := w4 448 (by omega)
  have v456 : rdN s₄.μ (sp + 456) 8 = rp := (w4 456 (by omega)).trans A.m456
  have v464 : rdN s₄.μ (sp + 464) 8 = 0 := (w4 464 (by omega)).trans A.m464
  have v128 : rdN s₄.μ (sp + 128) 8 = bo.toList.length := (w4 128 (by omega)).trans A.m128
  have v104 : rdN s₄.μ (sp + 104) 8 = ptr := (w4 104 (by omega)).trans A.m104
  have v264 : rdN s₄.μ (sp + 264) 8 = o.authTrace.toList.length := by
    rw [w4 264 (by omega), w21 264 (by omega)]; exact w264
  have v272 : rdN s₄.μ (sp + 272) 8 = tp := by
    rw [w4 272 (by omega), w21 272 (by omega)]; exact w272
  have htf : tailFree s₄.μ sp = optBuf (rdN s₂.μ (sp + 448) 8) rp ++ optBuf bo.toList.length ptr ++
      optBuf o.authTrace.toList.length tp := by
    rw [tailFree_nil v464, v448, v456, v128, v104, v264, v272]
  -- the results buffer: none, or a fresh chunk
  have hrp : rdN s₂.μ (sp + 448) 8 ≠ 0 → (∃ d ∈ chunks st₄, d.used = true ∧ d.addr + 32 = rp) ∧
      (∀ d ∈ chunks st₁, d.used = true → d.addr + 32 ≠ rp) ∧ rp ∉ vecFree B s₂.μ bv cv is.length := by
    intro h
    rcases A.res with ⟨-, h0, -⟩ | ⟨-, -, hch, hfr, hnv⟩
    · exact absurd h0 h
    · refine ⟨⟨_, (keep24 _ hch rfl).1, rfl, ?_⟩, hfr, hnv⟩
      have hcb := Services.Bootstrap.Fmt.chunk_bounds H₂.wf hch
      have := H₂.hb0
      dsimp only at hcb ⊢; omega
  -- the slot's buffers are old chunks, so not the instructions' nor the results'
  have oldT : o.authTrace.toList.length ≠ 0 → ∃ d ∈ chunks st₁, d.used = true ∧ d.addr + 32 = tp ∧ d ∈ chunks st₄ :=
    fun h => by
      obtain ⟨d, hd, hu, ha⟩ := chT h
      exact ⟨d, (keep14 d hd hu).1, hu, ha, (keep14 d hd hu).2.1⟩
  have oldO : bo.toList.length ≠ 0 → ∃ d ∈ chunks st₁, d.used = true ∧ d.addr + 32 = ptr ∧ d ∈ chunks st₄ :=
    fun h => by
      obtain ⟨d, hd, hu, ha, -⟩ := chO h
      exact ⟨d, (keep14 d hd hu).1, hu, ha, (keep14 d hd hu).2.1⟩
  have hTO : o.authTrace.toList.length ≠ 0 → bo.toList.length ≠ 0 → ptr ≠ tp := fun h1 h2 he => by
    obtain ⟨hnd, -, -⟩ := hown
    simp only [footL, List.map_append] at hnd
    have hn := (List.nodup_append.1 hnd).1
    have hw0 : wd (s.μ.readN cur 184) 0 ≠ 0 := by rw [b0]; exact h1
    have hw24 : wd (s.μ.readN cur 184) 24 ≠ 0 := by rw [b24]; exact h2
    simp only [slotFoot, hr, hw0, hw24, if_false, hW8, hW32] at hn
    subst he
    simp at hn
  have e0r : resPtrs s₄.μ rp 0 = [] := rfl
  have hres4 : (rdN s₄.μ (sp + 448) 8 = 0 ∧ rdN s₄.μ (sp + 456) 8 < 32) ∨
      (rdN s₄.μ (sp + 448) 8 ≠ 0 ∧ ∃ d ∈ chunks st₄, d.used = true ∧ d.addr + 32 = rdN s₄.μ (sp + 456) 8 ∧
        rdN s₄.μ (sp + 456) 8 + 144 * rdN s₄.μ (sp + 448) 8 ≤ d.addr + 32 * d.size) := by
    rw [v448, v456]
    rcases A.res with ⟨-, h0, hrp8⟩ | ⟨hne, hn, hch, -, -⟩
    · exact .inl ⟨h0, by omega⟩
    · have hb := Services.Bootstrap.Fmt.chunk_bounds H₂.wf hch
      have := H₂.hb0
      dsimp only at hb
      refine .inr ⟨by rw [hn]; exact fun h => hne (List.length_eq_zero_iff.1 h), _, (keep24 _ hch rfl).1, rfl,
        by dsimp only; omega, ?_⟩
      rw [hn]; dsimp only; omega
  -- the loop's entry state at 8492 (`EntryHyp`)
  have E : EntryHyp B env.code pb S0 S1 sp bv cv is s₄.μ st₄ := by
    refine ⟨H₄, ⟨by omega, by omega, by omega⟩, hsp.2, ?_, ?_, V4, A.hb, ?_, hres4, v464, ?_, ?_, ?_, ?_⟩
    · rw [w4 240 (by omega)]; exact A.m240
    · rw [w4 248 (by omega)]; exact A.m248
    · refine ⟨H₄, ⟨by omega, by omega, by omega⟩, ?_, ?_, ?_, ?_⟩
      · rw [v456, v464]; exact resultsOwn_nil _ _ _
      · rw [v456, v464, v448, e0r]; intro h; exact ⟨(hrp h).1, List.not_mem_nil⟩
      · rw [v456, v464, v448, v128, v104, e0r, List.nil_append]
        intro h
        obtain ⟨d, hd1, hu, ha, hd4⟩ := oldO h
        refine ⟨⟨d, hd4, hu, ha⟩, fun hm => ?_⟩
        unfold optBuf at hm
        by_cases h0 : rdN s₂.μ (sp + 448) 8 = 0
        · simp [h0] at hm
        · simp only [h0, if_false, List.mem_singleton] at hm; exact (hrp h0).2.1 d hd1 hu (ha.trans hm)
      · rw [v456, v464, v448, v128, v104, v264, v272, e0r, List.nil_append]
        intro h
        obtain ⟨d, hd1, hu, ha, hd4⟩ := oldT h
        refine ⟨⟨d, hd4, hu, ha⟩, fun hm => ?_⟩
        rcases List.mem_append.1 hm with hm | hm
        · unfold optBuf at hm
          by_cases h0 : rdN s₂.μ (sp + 448) 8 = 0
          · simp [h0] at hm
          · simp only [h0, if_false, List.mem_singleton] at hm; exact (hrp h0).2.1 d hd1 hu (ha.trans hm)
        · unfold optBuf at hm
          by_cases h0 : bo.toList.length = 0
          · simp [h0] at hm
          · simp only [h0, if_false, List.mem_singleton] at hm; exact hTO h h0 hm.symm
    · rw [hvf, htf]
      refine nodup_opt3 A.V.nodup (fun h => (hrp h).2.2) (fun h hv => ?_) (fun h hv => ?_)
        (fun h h' he => ?_) (fun h h' he => ?_) (fun h h' => hTO h' h)
      · obtain ⟨d, hd1, hu, ha, -⟩ := oldO h; exact A.fresh _ hv d hd1 hu ha
      · obtain ⟨d, hd1, hu, ha, -⟩ := oldT h; exact A.fresh _ hv d hd1 hu ha
      · obtain ⟨d, hd1, hu, ha, -⟩ := oldO h'; exact (hrp h).2.1 d hd1 hu (ha.trans he.symm)
      · obtain ⟨d, hd1, hu, ha, -⟩ := oldT h'; exact (hrp h).2.1 d hd1 hu (ha.trans he.symm)
    · rw [w4 184 (by omega), w21 184 (by omega), kw1 184 (by omega)]; exact hI.m184
    · rw [w4 216 (by omega), w21 216 (by omega), kw1 216 (by omega)]; exact hI.m216
    · rw [w4 200 (by omega), w21 200 (by omega)]; exact m200
  -- R5 and R7, then back at the loop head
  have lo34 : ∀ a, a < 196608 → s₄.μ.read a = s₃.μ.read a ∧ s₄.μ.readable a = s₃.μ.readable a := fun a ha =>
    ⟨(lo4 a ha).1, (lo4 a ha).2.1⟩
  have ro4 : OpRO s₄.μ := ((hI.ro2.keep lo2).keep lo23).keep lo34
  have mk4 : s₄.μ.readN 68696 8 = Num.encodeLE 8 k2' := by
    rw [Memory.readN_congr fun j hj => (lo4 _ (by omega)).1]; exact mc2'
  refine op_r57 (P := P) env B hL hR hH hP hE hO hD gcap hcap1 hcap hA4 hA1 hAbX o rest s Q hQ hI st cur hc db hdb hdbu hdbq hdata hslots hown s₄ st₄
    bv cv item k2' is o.packageHash.toList hi4 h14 (h64.trans (h63.trans A.r6)) E hfit4 ?_ ?_
    (tro3.keep lo34) ro4 mk4 hk2' H₄.ro ?_ ?_ ?_ ?_
  · rw [Memory.readN_congr fun j hj => fr4 _ (by omega) (by omega) (safe89 (by omega)).2]; exact pk3
  · rw [Memory.readN_congr fun j hj => fr4 _ (by omega) (by omega) (safe89 (by omega)).2]; exact it3
  · intro k hk
    rw [w4 k (by omega), w21 k (by omega), kw1 k hk]
  · rw [w4 168 (by omega), w21 168 (by omega)]; exact m168
  · intro d hd hu hm
    obtain ⟨h1, h4, k4⟩ := keep14 d hd hu
    refine ⟨h4, k4, fun hmem => ?_⟩
    have hy : d.addr + 32 ∈ (footL rest (cur + 184) s.μ).map Prod.fst ∨ d.addr + 32 = q := by
      rcases hm with hm | rfl
      · exact .inl hm
      · exact .inr hdbq
    rw [hvf, htf] at hmem
    rcases List.mem_append.1 hmem with hv | ht
    · exact A.fresh _ hv d h1 hu rfl
    · rcases mem_opt3 ht with ⟨hn, he⟩ | ⟨hn, he⟩ | ⟨hn, he⟩
      · exact (hrp hn).2.1 d h1 hu he
      · exact ne_slot hown (memO hn) hy he
      · exact ne_slot hown (memT hn) hy he
  · intro a ha
    rw [gl4 a ha, gl3 a ha, A.glob a ha, gl1 a ha]

set_option maxRecDepth 20000 in
/-- **R1 with R2: the items loop**, `items_loop` with its two arm premises discharged (`op_arm`,
    `err_arm`): from the loop head with `ItemsInv` for the inputs `ins`, the run implements
    `Spec.accumulate`'s loop over `ins.map Spec.specItem`, then halts with ω₈ = 0; early ☇ only where
    `Ab` holds (heap exhaustion). Named hypotheses: `Utf8Call`, `LogFmt`, `KeyFmt` (the transfer arm),
    `ItemLogFmt`, `OutDecH`, `InstrLogH`, `ResultLogH`, `HandlerH`, `PushH`, `ExtendH`, `OkEncH`,
    `DropInstrsH`; `ParamStatics μ₀ Cp I`, `RingFits Cp I`, maxRecent = 2·𝖢·𝖨. -/
theorem items_loop_full {p : ByteArray} {P : Program} [HasCode p P] [HasCodeX p P] [HasCodeA p P]
    (env : AccEnv) (B : InstrRep) (C : Consts) (now : Nat) {Ab : St Stream → Prop} {pb S0 S1 : Nat}
    (gcap : Nat) (hcap1 : 134217728 ≤ gcap) (hcap : gcap < 18446744073709551616)
    (hAb : ∀ s : St Stream, HeapFailT s → Ab s)
    (hAbT : ∀ s : St Stream, s.i = 15364 ∨ s.i = 34070 ∨ s.i = 47977 ∨ s.i = 32584 ∨ s.i = 36528 → Ab s)
    (hAbX : ∀ s : St Stream, (s.i = 40611 ∨ s.i = 40821) ∧ s.ω[7] = UInt64.ofNat 0 → Ab s)
    (hU : Utf8Call p env pb S0 S1) (hLF : LogFmt p env pb S0 S1) (hK : KeyFmt p env pb S0 S1)
    (hIL : ItemLogFmt p env pb S0 S1) (hOD : OutDecH B C p env pb S0 S1)
    (hL : InstrLogH B p env pb S0 S1) (hR : ResultLogH p env pb S0 S1) (hH : HandlerH B p env C now pb S0 S1 Ab)
    (hP : PushH p env pb S0 S1) (hE : Handlers.Results.ExtendH p P env pb S0 S1)
    (hO : Handlers.Results.OkEncH p P env pb S0 S1) (hD : DropInstrsH B p P env.code pb S0 S1)
    {Cp I : Nat} (hRF : Handlers.RecentSlotWrite.RingFits Cp I) (hmax : C.maxRecent = 2 * Cp * I)
    {sp q nc e : Nat} {μ₀ : Memory} (hPS : Handlers.RecentSlotWrite.ParamStatics μ₀ Cp I) :
    ∀ (ins : List AccumulateInput) (s : St Stream), ItemsInv env pb S0 S1 sp q nc e μ₀ ins s →
      Impl p (accContractS env) env Ab
        (Prog.bind (forIn (ins.map Spec.specItem) PUnit.unit (accBody C now)) fun _ => pure ())
        (Halts p (accContractS env)) s :=
  items_loop env gcap pb hcap1 hcap (P := P) hAb hU hLF hK C now
    (op_arm (P := P) env B C now gcap hcap1 hcap hAb hAbT hAbX hIL hOD hL hR hH hP hE hO hD hRF hmax hPS)
    (err_arm (P := P) env hAb hIL)

end Services.Bootstrap.Acc
