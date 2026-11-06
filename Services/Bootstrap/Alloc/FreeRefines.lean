import Services.Bootstrap.Alloc.FreeImpl
import Services.Picoalloc.ListFacts
import Services.Picoalloc.First

/-!
# The binary's `free` on a well-formed heap

The facts `free_impl` takes about the heap, from the invariant.
-/

namespace Services.Bootstrap.Alloc

open PVM Picoalloc Services.Bootstrap.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- A bin's head is 0 or the address of one of the free chunks. -/
theorem heads_ok {t : State} {cs : List Chunk} {b : Nat} (h : FreeLists t (Fof cs)) (hb : b < binCount) :
    t.heads b = 0 ∨ ∃ c ∈ cs, c.addr = t.heads b ∧ c.used = false := by
  obtain ⟨l, hl, -, -, hex⟩ := h b hb
  by_cases h0 : t.heads b = 0
  · exact Or.inl h0
  · cases l with
    | nil => exact absurd ((hl.head).mpr rfl) h0
    | cons y ys =>
      obtain ⟨c, hc, h1, h2, -⟩ := (hex y).mp List.mem_cons_self
      exact Or.inr ⟨c, hc, by rw [h1, hl.1], h2⟩

/-- A member x of bin b's list: its `next` is 0 or a free chunk; if it is not the head, its
    `prevL` is a free chunk, other than its `next`. -/
theorem member_facts {t : State} {cs : List Chunk} {b x : Nat} (h : FreeLists t (Fof cs)) (hb : b < binCount)
    (hx : Fof cs b x) :
    ((t.hdr x).next ≠ 0 → ∃ c ∈ cs, c.addr = (t.hdr x).next ∧ c.used = false) ∧
      (t.heads b ≠ x → (∃ c ∈ cs, c.addr = (t.hdr x).prevL ∧ c.used = false) ∧
        ((t.hdr x).next ≠ 0 → (t.hdr x).next ≠ (t.hdr x).prevL)) := by
  obtain ⟨l, hl, hbl, hnd, hex⟩ := h b hb
  have hxl := (hex x).mpr hx
  refine ⟨fun h0 => ?_, fun hne => ⟨?_, fun h0 => next_ne_prevL hl hbl hnd hxl (Ne.symm hne) h0⟩⟩
  · rcases hl.next_mem hxl with h | h
    · exact absurd h h0
    · obtain ⟨c, hc, h1, h2, -⟩ := (hex _).mp h; exact ⟨c, hc, h1, h2⟩
  · obtain ⟨c, hc, h1, h2, -⟩ := (hex _).mp (hbl.prevL_mem hl hxl (Ne.symm hne)); exact ⟨c, hc, h1, h2⟩


variable {X : Type} {R : HostRel X}

/-- The addresses of a chunk list, and of its free chunks. -/
def HA (cs : List Chunk) (a : Nat) : Prop := ∃ c ∈ cs, c.addr = a
def FA (cs : List Chunk) (a : Nat) : Prop := ∃ c ∈ cs, c.addr = a ∧ c.used = false

/-- **The binary's `free` on a well-formed heap**: from memory holding a well-formed `s` and the
    data address of an allocated chunk, the compiled free path returns into `dealloc` with memory
    holding the model's `free s ptr`, itself well-formed. -/
theorem free_refines {p : ByteArray} {P : Program} [HasCode p P] (x : X) (ω : Regs) (μ : Memory)
    (s : State) (sp ptr : Nat) (hwf : WF s) (hrep : Rep μ s)
    (hc : ∃ c ∈ chunks s, c.addr + 32 = ptr ∧ c.used = true)
    (h1 : ω[1] = UInt64.ofNat sp) (h8 : ω[8] = UInt64.ofNat ptr) (h7 : ω[7] = UInt64.ofNat 196792)
    (h0 : ω[0] = UInt64.ofNat 1986) (hsp : 2147483700 ≤ sp) (hsp1 : sp < 4294967296)
    (hb0 : 206864 ≤ s.base) (hbT : s.base + 1073741824 < 2147483648)
    (hfo : FirstOk s) (hw : ∀ a, μ.writable a = true) :
    ∃ ω' μ', FreeStepsH p R 42327 ω μ x 40681 ω' μ' x 220 ∧ Rep μ' (free s ptr) ∧ WF (free s ptr) ∧
      FirstOk (free s ptr) ∧
      (∀ a, μ'.writable a = true) ∧ ω'[0] = UInt64.ofNat 1986 ∧ ω'[1] = UInt64.ofNat sp ∧
      ω'[5] = ω[5] ∧ ω'[6] = ω[6] := by
  have hp0 : (s.hdr s.base).prev < 2147483648 := by unfold FirstOk at hfo; omega
  obtain ⟨c, hcm, hca, hcu⟩ := hc
  obtain ⟨pre, post, hcs⟩ := List.append_of_mem hcm
  have hceq : c = ⟨ptr - 32, c.size, true⟩ := by
    cases c; simp only at hca hcu ⊢; subst hcu; simp only [Chunk.mk.injEq, and_true]; omega
  rw [hceq] at hcs
  generalize hn0 : c.size = n at hcs
  have hfirst := free_first hwf hfo hcs
  obtain ⟨pre0F, LF, RF, post0F, MF, totF, hpreF, hpostF, -, hchF, hwfF, hMF⟩ := free_ok hwf hcs
  have hwf' := hwf
  obtain ⟨-, hbal, hfit, htiles, hcoal, hprev, hlists, hspace⟩ := hwf'
  unfold TilesOk at htiles
  unfold CoalOk at hcoal
  unfold PrevsOk at hprev
  unfold ListsOk' at hlists
  have henc := @chunks_hdr s
  have htop : s.top = s.base + 1073741824 := by unfold State.top; rw [maxSize_val]
  rw [hcs] at htiles hcoal hprev hlists henc
  rw [htop] at htiles
  generalize hXd : ptr - 32 = Xa at *
  -- the header addresses
  generalize hH : HA (pre ++ ⟨Xa, n, true⟩ :: post) = H
  generalize hF : FA (pre ++ ⟨Xa, n, true⟩ :: post) = F
  have mkH : ∀ c ∈ pre ++ ⟨Xa, n, true⟩ :: post, H c.addr := fun c hc => hH ▸ ⟨c, hc, rfl⟩
  have mkF : ∀ c ∈ pre ++ ⟨Xa, n, true⟩ :: post, c.used = false → F c.addr := fun c hc hu => hF ▸ ⟨c, hc, rfl, hu⟩
  have unH : ∀ a, H a → ∃ c ∈ pre ++ ⟨Xa, n, true⟩ :: post, c.addr = a := fun a h => by rw [← hH] at h; exact h
  have unF : ∀ a, F a → ∃ c ∈ pre ++ ⟨Xa, n, true⟩ :: post, c.addr = a ∧ c.used = false := fun a h => by
    rw [← hF] at h; exact h
  have hHF : ∀ a, H a ∨ F a → Al s.base a := by
    intro a h
    obtain ⟨c, hc, rfl⟩ : ∃ c ∈ pre ++ ⟨Xa, n, true⟩ :: post, c.addr = a := by
      rcases h with h | h
      · exact unH a h
      · obtain ⟨c, hc, h1, -⟩ := unF a h; exact ⟨c, hc, h1⟩
    have := htiles.aligned c hc; have := htiles.mem_lt c hc; unfold Al; omega
  have hcs' : chunks s = pre ++ ⟨Xa, n, true⟩ :: post := hcs
  have hrep' : RepAt μ s H F :=
    ⟨hrep.heads, hrep.sec, hrep.pri, hrep.base, hrep.alloc,
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.prev c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl⟩ := unH a h; exact hrep.size c (hcs' ▸ hc),
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.next c (hcs' ▸ hc) hu,
      fun a h => by obtain ⟨c, hc, rfl, hu⟩ := unF a h; exact hrep.prevL c (hcs' ▸ hc) hu⟩
  have hXm : (⟨Xa, n, true⟩ : Chunk) ∈ pre ++ ⟨Xa, n, true⟩ :: post := List.mem_append_right _ List.mem_cons_self
  have hXl := htiles.mem_lt _ hXm
  have hXa := htiles.aligned _ hXm
  simp only at hXl hXa
  have hXs : (s.hdr Xa).size = sizeWord n true := henc _ hXm
  have hwn : wordSize (s.hdr Xa).size = n := by rw [hXs, wordSize_sizeWord]
  -- the chunk before X
  have hpre : Xa ≠ s.base → ∃ pre1 d, pre = pre1 ++ [d] ∧ (s.hdr Xa).prev = d.size ∧
      d.addr + 32 * d.size = Xa := by
    intro hXb
    rcases List.eq_nil_or_concat pre with h | ⟨pre1, d, h⟩
    · subst h; exact absurd htiles.1 hXb
    · rw [List.concat_eq_append] at h; subst h
      refine ⟨pre1, d, rfl, ?_, ?_⟩
      · have := (PrevOk.append.mp hprev).2.2 d (by simp) ⟨Xa, n, true⟩ rfl
        exact this
      · have := (Tiles.around (pre := pre1) (C := d.addr) (S := d.size) (u := d.used)
          (post := ⟨Xa, n, true⟩ :: post) (by
            have e : pre1 ++ [d] ++ ⟨Xa, n, true⟩ :: post = pre1 ++ ⟨d.addr, d.size, d.used⟩ :: ⟨Xa, n, true⟩ :: post := by
              simp
            rw [← e]; exact htiles)).2.1 ⟨Xa, n, true⟩ rfl
        simp only at this; omega
  have hpvX : (s.hdr Xa).prev < 2147483648 := by
    by_cases hXb : Xa = s.base
    · rw [hXb]; exact hp0
    · obtain ⟨pre1, d, rfl, hd, -⟩ := hpre hXb
      have := htiles.mem_lt d (by simp); rw [hd]; omega
  rw [hwn] at hMF
  rcases hm : mergePrev s Xa n (s.hdr Xa).prev with ⟨s1, M, sz1, pv'⟩
  rw [hm] at hMF
  simp only at hMF
  have hF0 : FreeLists s (Fof (pre ++ ⟨Xa, n, true⟩ :: post)) := fun b hb => hlists.lists b hb
  have hbits : BitsOk s.secondary s.primary s.heads := ⟨hlists.bits, hlists.prim, hlists.words, hlists.primW⟩
  have hsub : ∀ c, c ∈ pre ∨ c ∈ post → c ∈ pre ++ ⟨Xa, n, true⟩ :: post := by
    rintro c (h | h)
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hAlc : ∀ c ∈ pre ++ ⟨Xa, n, true⟩ :: post, Al s.base c.addr := fun c hc => hHF _ (Or.inl (mkH c hc))
  -- the prev of a chunk before X
  have hpvd : ∀ pre1 d, pre = pre1 ++ [d] → (s.hdr d.addr).prev < 2147483648 := by
    intro pre1 d hpd
    rw [hpd] at htiles hprev
    rcases List.eq_nil_or_concat pre1 with h | ⟨pre2, e, h⟩
    · subst h
      have : d.addr = s.base := htiles.1
      rw [this]; exact hp0
    · rw [List.concat_eq_append] at h; subst h
      have hl := (PrevOk.append (xs := pre2 ++ [e]) (ys := d :: ⟨Xa, n, true⟩ :: post)).mp
        (by simpa using hprev)
      have := hl.2.2 e (by simp) d rfl
      have := htiles.mem_lt e (by simp)
      omega
  obtain ⟨pre0, L, hpre0, hLf, htl1, hsum1, hlast, hF1, hb1, hps1, hbase1, -, hMw⟩ :=
    mergePrev_ok htiles hprev henc hcoal hF0 hbits hm
  have hcX : Coalesced (⟨Xa, n, true⟩ :: post) := (Coalesced.append.mp hcoal).2.1
  have hcp : Coalesced post := ((Coalesced.append (xs := [⟨Xa, n, true⟩]) (ys := post)).mp hcX).2.1
  have henc' : ∀ c ∈ post, (s1.hdr c.addr).size = sizeWord c.size c.used := fun c hc => by
    rw [(hps1 _).2]; exact henc c (hsub c (Or.inr hc))
  rcases hnx : mergeNext s1 M sz1 (s.base + 1073741824) with ⟨s2, total⟩
  obtain ⟨R', post0, hpost0, hRf, htl2, hhead, hF2, hb2, -, -, -, -⟩ :=
    mergeNext_ok htl1 henc' hcp hF1 hb1 hnx
  -- the chunk after X
  have hpostX : ∀ e es, post = e :: es → e.addr = Xa + 32 * n := by
    intro e es he; subst he
    exact (Tiles.around htiles).2.1 e rfl
  have hM2 := htl2.mem_lt ⟨M, total, true⟩ (List.mem_append_right _ List.mem_cons_self)
  simp only at hM2
  have hMa : Al s.base M := by
    rcases hMw with h | ⟨c, hc, h⟩
    · rw [h]; exact hHF _ (Or.inl (mkH _ hXm))
    · rw [← h]; exact hAlc c (hsub c (Or.inl hc))
  clear hMw
  have hsub0 : ∀ c ∈ pre0 ++ post0, c ∈ pre ++ ⟨Xa, n, true⟩ :: post := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hsub c (Or.inl (by rw [hpre0]; exact List.mem_append_left _ h))
    · exact hsub c (Or.inr (by rw [hpost0]; exact List.mem_append_right _ h))
  have hsubP : ∀ c ∈ pre0 ++ post, c ∈ pre ++ ⟨Xa, n, true⟩ :: post := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hsub c (Or.inl (by rw [hpre0]; exact List.mem_append_left _ h))
    · exact hsub c (Or.inr h)
  have hbinlt : ∀ y, binDown y < binCount := fun y => toBin_lt false (Nat.min_le_right _ _)
  have hpH' : Xa ≠ s.base → 32 * (s.hdr Xa).prev ≤ Xa - s.base ∧ H (Xa - 32 * (s.hdr Xa).prev) := by
    intro hXb
    obtain ⟨pre1, d, hpd, hd, hda⟩ := hpre hXb
    have hdm : d ∈ pre ++ ⟨Xa, n, true⟩ :: post := by rw [hpd]; simp
    obtain ⟨l1, l2, l3⟩ := htiles.mem_lt d hdm
    refine ⟨by rw [hd]; omega, by rw [hd, show Xa - 32 * d.size = d.addr by omega]; exact mkH d hdm⟩
  have hpf' : Xa ≠ s.base → (s.hdr (Xa - 32 * (s.hdr Xa).prev)).size % 2 = 0 →
      PvFree s F s.base (Xa - 32 * (s.hdr Xa).prev) n (s.hdr Xa).prev := by
    intro hXb hev
    obtain ⟨pre1, d, hpd, hd, hda⟩ := hpre hXb
    have hdm : d ∈ pre ++ ⟨Xa, n, true⟩ :: post := by rw [hpd]; simp
    have hPa : Xa - 32 * (s.hdr Xa).prev = d.addr := by rw [hd]; omega
    rw [hPa] at hev ⊢
    rw [hd]
    have hds := henc d hdm
    have hdu : d.used = false := by
      rw [hds] at hev; cases hu : d.used
      · rfl
      · exfalso; rw [hu] at hev; simp [sizeWord] at hev; try omega
    have hdl := htiles.mem_lt d hdm
    have hFd : Fof (pre ++ ⟨Xa, n, true⟩ :: post) (binDown d.size) d.addr := ⟨d, hdm, rfl, hdu, rfl⟩
    obtain ⟨m1, m2⟩ := member_facts hF0 (hbinlt _) hFd
    refine ⟨mkF d hdm hdu, by rw [hds, hdu]; simp [sizeWord], by omega, by omega, by omega,
      hpvd pre1 d hpd, ?_, fun h => ?_, fun h => ?_⟩
    · rcases heads_ok hF0 (hbinlt d.size) with h | ⟨c, hc, h1, -⟩
      · exact Or.inl h
      · exact Or.inr (h1 ▸ hAlc c hc)
    · obtain ⟨c, hc, h1, h2⟩ := m1 h; exact h1 ▸ mkF c hc h2
    · obtain ⟨⟨c, hc, h1, h2⟩, h3⟩ := m2 h; exact ⟨h1 ▸ mkF c hc h2, h3⟩
  have hnc' : M + 32 * sz1 < s.base + 1073741824 → H (M + 32 * sz1) := by
    intro hlt
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      have := (Tiles.append.mp htiles); obtain ⟨m, -, hm1, -, hm3⟩ := this
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      rw [show M + 32 * sz1 = e.addr by rw [hpostX e es hp]; omega]
      exact mkH e (hsub e (Or.inr (by rw [hp]; simp)))
  have hnf' : M + 32 * sz1 < s.base + 1073741824 → (s1.hdr (M + 32 * sz1)).size % 2 = 0 →
      NxFree s1 F s.base (M + 32 * sz1) sz1 := by
    intro hlt hev
    cases hp : post with
    | nil =>
      rw [hp] at htiles
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htiles
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      have hea := hpostX e es hp
      have hem : e ∈ pre ++ ⟨Xa, n, true⟩ :: post := hsub e (Or.inr (by rw [hp]; simp))
      have hncE : M + 32 * sz1 = e.addr := by omega
      unfold NxFree
      rw [hncE] at hev ⊢
      have hes : (s1.hdr e.addr).size = sizeWord e.size e.used := henc' e (by rw [hp]; simp)
      rw [hes] at hev ⊢
      have heu : e.used = false := by
        cases hu : e.used
        · rfl
        · exfalso; rw [hu] at hev; simp [sizeWord] at hev; try omega
      rw [heu, show sizeWord e.size false / 2 = e.size by simp [sizeWord]]
      have hel := htiles.mem_lt e hem
      have hFe : Fof (pre0 ++ post) (binDown e.size) e.addr :=
        ⟨e, List.mem_append_right _ (by rw [hp]; simp), rfl, heu, rfl⟩
      obtain ⟨m1, m2⟩ := member_facts hF1 (hbinlt _) hFe
      refine ⟨mkF e hem heu, by simp [sizeWord]; omega, by simp [sizeWord]; omega, by omega, ?_,
        fun h => ?_, fun h => ?_⟩
      · rcases heads_ok hF1 (hbinlt e.size) with h | ⟨c, hc, h1, -⟩
        · exact Or.inl h
        · exact Or.inr (h1 ▸ hAlc c (hsubP c hc))
      · obtain ⟨c, hc, h1, h2⟩ := m1 h; exact h1 ▸ mkF c (hsubP c hc) h2
      · obtain ⟨⟨c, hc, h1, h2⟩, h3⟩ := m2 h; exact ⟨h1 ▸ mkF c (hsubP c hc) h2, h3⟩
  have hpv'' : pv' < 4294967296 := by
    unfold mergePrev at hm
    split at hm
    · dsimp only at hm
      split at hm
      · simp only [Prod.mk.injEq] at hm; obtain ⟨-, -, -, rfl⟩ := hm
        rename_i hXb _
        obtain ⟨pre1, d, hpd, hd, hda⟩ := hpre hXb
        have hPa : Xa - 32 * (s.hdr Xa).prev = d.addr := by rw [hd]; omega
        rw [hPa]; have := hpvd pre1 d hpd; omega
      · simp only [Prod.mk.injEq] at hm; obtain ⟨-, -, -, rfl⟩ := hm; omega
    · simp only [Prod.mk.injEq] at hm; obtain ⟨-, -, -, rfl⟩ := hm; omega
  have hold' : s2.heads (binDown total) ≠ M := by
    rcases heads_ok hF2 (hbinlt total) with h | ⟨c, hc, h1, -⟩
    · rw [h]; unfold Al at hMa; omega
    · rw [← h1]; exact htl2.others c hc
  have hold1' : s2.heads (binDown total) ≠ 0 → Al s.base (s2.heads (binDown total)) := by
    intro h0
    rcases heads_ok hF2 (hbinlt total) with h | ⟨c, hc, h1, -⟩
    · exact absurd h h0
    · rw [← h1]; exact hAlc c (hsub0 c hc)
  have hnext' : M + 32 * total < s.base + 1073741824 → H (M + 32 * total) := by
    intro hlt
    cases hp : post0 with
    | nil =>
      rw [hp] at htl2
      obtain ⟨m, -, hm1, -, hm3⟩ := Tiles.append.mp htl2
      simp only [Tiles] at hm1 hm3; omega
    | cons e es =>
      have := (Tiles.around htl2).2.1 e (by rw [hp]; rfl)
      exact this ▸ mkH e (hsub0 e (by rw [hp]; simp))
  obtain ⟨ω', μ', run, rep', ww, e0, e1, e5, e6⟩ := free_impl (p := p) (P := P) (R := R) x ω μ s s1 s2 H F
    sp ptr M sz1 pv' total hrep' h1 h8 h7 h0 hsp hsp1 hb0 hbT
    (by rw [hXd]; exact hHF _ (Or.inl (mkH _ hXm))) (by omega) (by rw [hXd]; exact mkH _ hXm) hHF
    (by rw [hXd]; exact hpvX) (by rw [hXd, hwn]; exact hm) hnx
    (by rw [hXd]; exact hpH')
    (by rw [hXd, hwn]; exact hpf')
    hbase1 hMa (by omega)
    hnc'
    hnf'
    (by omega) (by unfold Al at hMa; omega) (by omega)
    hpv''
    hold'
    hold1'
    hnext'
    hw
  refine ⟨ω', μ', run, ?_, hwfF, hfirst, ww, e0, e1, e5, e6⟩
  -- the model's result, read from memory
  have hcsF := hchF
  rw [hMF] at hcsF
  have hinF : ∀ c ∈ pre0F ++ post0F, c ∈ pre ++ ⟨Xa, n, true⟩ :: post := by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact hsub c (Or.inl (by rw [hpreF]; exact List.mem_append_left _ h))
    · exact hsub c (Or.inr (by rw [hpostF]; exact List.mem_append_right _ h))
  have cls : ∀ c ∈ chunks (free s ptr), c ∈ pre ++ ⟨Xa, n, true⟩ :: post ∨ c = ⟨M, totF, false⟩ := by
    intro c hc
    rw [hcsF] at hc
    rcases List.mem_append.mp hc with h | h
    · exact Or.inl (hinF c (List.mem_append_left _ h))
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr h
      · exact Or.inl (hinF c (List.mem_append_right _ h))
  have clsF : ∀ c ∈ chunks (free s ptr), c.used = false → F c.addr ∨ c.addr = M := by
    intro c hc hu
    rw [hcsF] at hc
    rcases List.mem_append.mp hc with h | h
    · exact Or.inl (mkF c (hinF c (List.mem_append_left _ h)) hu)
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inr (by rw [h])
      · exact Or.inl (mkF c (hinF c (List.mem_append_right _ h)) hu)
  refine ⟨rep'.heads, rep'.sec, rep'.pri, rep'.base, rep'.alloc, fun c hc => ?_, fun c hc => ?_,
    fun c hc hu => ?_, fun c hc hu => ?_⟩
  · rcases cls c hc with h | rfl
    · exact rep'.prev _ (Or.inl (mkH c h))
    · exact rep'.prev _ (Or.inr rfl)
  · rcases cls c hc with h | rfl
    · exact rep'.size _ (Or.inl (mkH c h))
    · exact rep'.size _ (Or.inr rfl)
  · rcases clsF c hc hu with h | h
    · exact rep'.next _ (Or.inl h)
    · exact rep'.next _ (Or.inr h)
  · rcases clsF c hc hu with h | h
    · exact rep'.prevL _ (Or.inl h)
    · exact rep'.prevL _ (Or.inr h)

end Services.Bootstrap.Alloc
