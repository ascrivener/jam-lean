import re, sys
W = open('/home/user/jam-lean/Services/Bootstrap/Fmt/Write.lean').read()
T = open('/home/user/jam-lean/Services/Bootstrap/Fmt/Template.lean').read()
def block(src, start_pat, end_pat):
    s = src.index(start_pat)
    e = src.index(end_pat, s + 1)
    return src[s:e].rstrip() + '\n'
def rep(blk, a, b, cnt=1):
    assert blk.count(a) == cnt, (a[:80], blk.count(a))
    return blk.replace(a, b)

# ---------- ArgOkT
argok = block(T, 'def ArgOk ', '/-- An `ArgOk` holds')
argok = rep(argok, 'def ArgOk ', 'def ArgOkT ')
argok = rep(argok, '(spA e v M C : Nat) : Prop :=', '(spA e v : Nat) (bs : List UInt8) (M C : Nat) : Prop :=')
argok = rep(argok, """(sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →""",
 """(sp ≤ F ∧ F + 24 ≤ S1 ∧ (F + 24 ≤ W ∨ W + 24 ≤ F)) → len + M < 134217728 →
    ∀ txt : List UInt8, μ.readN (rdN μ (W + 8) 8) len = txt →""")
argok = rep(argok, """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨""",
 """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧ n = bs.length ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ bs) ∨""")
argok = '''/-- **An argument's formatting function, with its text**: `ArgOk`, and the octets the function
    appends to the `String` are `bs`: when the `String`'s `len` octets were `txt`, its `len + n`
    octets are then `txt ++ bs`, with n = |bs|. -/
''' + argok

# ---------- ArgsAtT
argsat = block(W, 'def ArgsAt ', 'theorem exh_lit')
argsat = rep(argsat, 'def ArgsAt ', 'def ArgsAtT ')
argsat = rep(argsat, '(spA args i : Nat) (ts : List TItem) (M C : Nat) : Prop :=',
             '(spA args i : Nat) (ts : List TItem) (bsf : Nat → List UInt8) (M C : Nat) : Prop :=')
argsat = rep(argsat, 'ArgOk p P R env pb S0 S1 μA sA spA e v M C', 'ArgOkT p P R env pb S0 S1 μA sA spA e v (bsf (i + j)) M C')
argsat = '''/-- `ArgsAt` with each argument's text: the (i + j)-th argument's function appends `bsf (i + j)`. -/
''' + argsat

# ---------- WrLoopT
wl = block(W, 'def WrLoop ', '/-- The first byte of an item.')
wl = rep(wl, 'def WrLoop ', 'def WrLoopT ')
wl = rep(wl, '(ts : List TItem) : Prop :=', '(bsf : Nat → List UInt8) (ts : List TItem) : Prop :=')
wl = rep(wl, 'ArgsAt p P R env pb S0 S1 μA sA spA args i ts M C →', 'ArgsAtT p P R env pb S0 S1 μA sA spA args i ts bsf M C →')
wl = rep(wl, """    len + tlen M ts < 134217728 →
""", """    len + tlen M ts < 134217728 →
    ∀ txt : List UInt8, μ.readN (rdN μ (W + 8) 8) len = txt →
""")
wl = rep(wl, """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨""",
 """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ ttext μ c ts bsf i) ∨""")
wl = '''/-- `WrLoop` with the text: the `String` gains `ttext μ c ts bsf i`. -/
''' + wl

# ---------- wr_item_text
wi = block(W, 'theorem wr_item ', '/-- **The template loop** (from 64600)')
wi = rep(wi, 'theorem wr_item ', 'theorem wr_item_text ')
wi = rep(wi, '(HR : ReallocOk p R env pb S0 S1)', '(HR : ReallocCopyOk p R env pb S0 S1)')
wi = rep(wi, '(it : TItem) (ts : List TItem) (ih : WrLoop p P R env pb S0 S1 μA sA spA T W args ret t v5 v6 M C ts)',
         '(it : TItem) (ts : List TItem) (bsf : Nat → List UInt8)\n    (ih : WrLoopT p P R env pb S0 S1 μA sA spA T W args ret t v5 v6 M C bsf ts)')
wi = rep(wi, '(hA : ArgsAt p P R env pb S0 S1 μA sA spA args i (it :: ts) M C)', '(hA : ArgsAtT p P R env pb S0 S1 μA sA spA args i (it :: ts) bsf M C)')
wi = rep(wi, """    (hn : len + tlen M (it :: ts) < 134217728) :""", """    (hn : len + tlen M (it :: ts) < 134217728) (txt : List UInt8)
    (htx : μ.readN (rdN μ (W + 8) 8) len = txt) :""")
wi = rep(wi, """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 64611""", """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ ttext μ c (it :: ts) bsf i) ∨
    Exhausts p R pb 64611""")
wi = rep(wi, "simp only [Tmpl, tsize, tlen, tcost, nargs, TItem.byte] at hTm hc1 hn hA hi a5 ⊢",
         "simp only [Tmpl, tsize, tlen, tcost, nargs, TItem.byte, ttext] at hTm hc1 hn hA hi a5 ⊢", 2)
# lit
wi = rep(wi, """    rcases write_str (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ sA s T W (c + 1) n cap len 2728""",
 """    rcases write_str_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR x ω2 μ sA s T W (c + 1) n cap len 2728""")
wi = rep(wi, """        (Or.inl ⟨by omega, by omega⟩) (fun a h1 h2 => hrb a (by omega) (by omega)) with
      ⟨ω3, μ3, x3, s3, cap3, run3, H3, hb3, hs3, hc31, hc32, K3, e0, e1, e5, e6, e7⟩ | hx""",
 """        (Or.inl ⟨by omega, by omega⟩) (fun a h1 h2 => hrb a (by omega) (by omega)) txt htx with
      ⟨ω3, μ3, x3, s3, cap3, run3, H3, hb3, hs3, hc31, hc32, K3, e0, e1, e5, e6, e7, tx3⟩ | hx""")
wi = rep(wi, """          (by rw [f6]) hA hi (by omega) with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7⟩
        have := (K3.mono (Nat.le_refl _) (fun a h => Or.inl h)).trans' (E := wrE T W) K'
        rwa [Nat.max_self] at this""",
 """          (by rw [f6]) hA hi (by omega) _ tx3 with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7, gT⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7, ?_⟩
        · have := (K3.mono (Nat.le_refl _) (fun a h => Or.inl h)).trans' (E := wrE T W) K'
          rwa [Nat.max_self] at this
        · rw [← Nat.add_assoc, gT, ttext_congr ts _ (by omega) (fun a ha => (hro3 a ha).1), List.append_assoc]""")
# arg
wi = rep(wi, "rw [Nat.add_zero] at hA0 hA1 hAr hAv hAf", "rw [Nat.add_zero] at hA0 hA1 hAr hAv hAf hok")
wi = rep(wi, """        ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) with
      ⟨ω3, μ3, x3, s3, cap3, n, hnM, run3, H3, hb3, hf3, hc31, hc32, K3, e0, e1, e5, e6, e7⟩ | hx""",
 """        ⟨by omega, by omega, Or.inl (by omega)⟩ (by omega) txt htx2 with
      ⟨ω3, μ3, x3, s3, cap3, n, hnM, run3, H3, hb3, hf3, hc31, hc32, K3, e0, e1, e5, e6, e7, hnb, tx3⟩ | hx""")
wi = rep(wi, """    rcases hok ω2 μ2 x s T (T + 48) W""", """    have hbl := buf_lt hs H
    have hle := hs.le
    have htx2 : μ2.readN (rdN μ2 (W + 8) 8) len = txt := by
      rw [rdN_frame (μ := μ) (μ' := μ2) (fun j hj => fr2 _ (by omega) (Or.inr (by omega))), ← htx]
      exact readN_congr2 fun j hj => fr2 _ (by omega) (Or.inl (by omega))
    rcases hok ω2 μ2 x s T (T + 48) W""")
wi = rep(wi, """      rcases ih (c + 1) (i + 1) cap3 (len + n) ω4 μ4 x3 s3 H4""", """      have hbl3 := buf_lt hf3.str H3
      have htx4 : μ4.readN (rdN μ4 (W + 8) 8) (len + n) = txt ++ bsf i := by
        rw [rdN_frame (μ := μ3) (μ' := μ4) (fun j hj => fr4 _ (by omega) (Or.inr (by omega))), ← tx3]
        exact readN_congr2 fun j hj => fr4 _ (by omega) (Or.inl (by have := hf3.str.le; omega))
      rcases ih (c + 1) (i + 1) cap3 (len + n) ω4 μ4 x3 s3 H4""")
wi = rep(wi, """          (by omega) (by omega) with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7⟩
        have := K14.trans' K'
        rwa [Nat.max_self] at this""",
 """          (by omega) (by omega) _ htx4 with
        ⟨ω', μ', x', s', cap', n', hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7, gT⟩ | hx
      · refine Or.inl ⟨ω', μ', x', s', cap', n + n', by omega,
          ((((run1.trans run2).trans run3).trans run4).trans run').mono (by omega), H', hb'.trans hb3,
          by rw [← Nat.add_assoc]; exact hs', by omega, by omega, ?_, g0, g1, g5, g6, g7, ?_⟩
        · have := K14.trans' K'
          rwa [Nat.max_self] at this
        · rw [← Nat.add_assoc, gT, ttext_congr ts _ (by omega) (fun a ha => (hro4 a ha).1), List.append_assoc]""")
wi = '/-- `wr_item` with the text. -/\n' + wi

# ---------- wr_loop_text
lp = block(W, 'theorem wr_loop ', '/-- **`core::fmt::write` into a `String`, frame-only**')
lp = rep(lp, 'theorem wr_loop ', 'theorem wr_loop_text ')
lp = rep(lp, '(HR : ReallocOk p R env pb S0 S1)', '(HR : ReallocCopyOk p R env pb S0 S1)')
lp = rep(lp, '(μA : Memory) (sA : State) (spA T W args ret t v5 v6 M C : Nat)', '(μA : Memory) (sA : State) (spA T W args ret t v5 v6 M C : Nat) (bsf : Nat → List UInt8)')
lp = rep(lp, '∀ ts, WrLoop p P R env pb S0 S1 μA sA spA T W args ret t v5 v6 M C ts', '∀ ts, WrLoopT p P R env pb S0 S1 μA sA spA T W args ret t v5 v6 M C bsf ts')
lp = rep(lp, 'intro c i cap len ω μ x s H hba hs KA hF hro hTm hc0 hc1 h1 h6 _ _ _', 'intro c i cap len ω μ x s H hba hs KA hF hro hTm hc0 hc1 h1 h6 _ _ _ txt htx')
lp = rep(lp, """      e0, e1, e5, e6, e7⟩
  | cons""", """      e0, e1, e5, e6, e7, by simp only [ttext, List.append_nil, Nat.add_zero]; exact htx⟩
  | cons""")
lp = rep(lp, 'intro c i cap len ω μ x s H hba hs KA hF hro hTm hc0 hc1 h1 h6 hA hi hn', 'intro c i cap len ω μ x s H hba hs KA hF hro hTm hc0 hc1 h1 h6 hA hi hn txt htx')
lp = rep(lp, 'rcases wr_item (p := p)', 'rcases wr_item_text (p := p)')
lp = rep(lp, 'it ts ih c i cap len ω1 μ x s H hba hs KA hF hro hTm hc0 hc1 (a1.trans h1) a5 a9 a12 hA hi hn with',
         'it ts bsf ih c i cap len ω1 μ x s H hba hs KA hF hro hTm hc0 hc1 (a1.trans h1) a5 a9 a12 hA hi hn txt htx with')
lp = '/-- **The template loop, with the text** (from 64600): `WrLoopT` for every template. -/\n' + lp

# ---------- fmt_write_text
fw = block(W, 'theorem fmt_write ', 'end Services.Bootstrap.Fmt')
fw = rep(fw, 'theorem fmt_write ', 'theorem fmt_write_text ')
fw = rep(fw, '(HR : ReallocOk p R env pb S0 S1)', '(HR : ReallocCopyOk p R env pb S0 S1)')
fw = rep(fw, '(μA : Memory) (sA : State) (spA S W tp args ret t v5 v6 M C : Nat) (ts : List TItem)',
         '(μA : Memory) (sA : State) (spA S W tp args ret t v5 v6 M C : Nat) (ts : List TItem) (bsf : Nat → List UInt8)')
fw = rep(fw, '(hA : ArgsAt p P R env pb S0 S1 μA sA spA args 0 ts M C)', '(hA : ArgsAtT p P R env pb S0 S1 μA sA spA args 0 ts bsf M C)')
fw = rep(fw, """    (hn : len + tlen M ts < 134217728) :""", """    (hn : len + tlen M ts < 134217728) (txt : List UInt8)
    (htx : μ.readN (rdN μ (W + 8) 8) len = txt) :""")
fw = rep(fw, """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0) ∨
    Exhausts p R pb 64495""", """      ω'[6] = UInt64.ofNat v6 ∧ ω'[7] = UInt64.ofNat 0 ∧
      μ'.readN (rdN μ' (W + 8) 8) (len + n) = txt ++ ttext μ tp ts bsf 0) ∨
    Exhausts p R pb 64495""")
fw = rep(fw, """  have htc := tcost_ge M C ts
""", """  have htc := tcost_ge M C ts
  have hbl := buf_lt hs H
  have hle := hs.le
""")
# nil
fw = rep(fw, """      ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1, rfl, ?_, Nat.le_refl _, by omega, K1,
      e0, e1, e5, e6, e7⟩
    rw [Nat.add_zero]
    exact hs.update""", """      ctx_hi H (fun a ha => fr1 a (by omega) (Or.inl (by omega))) wr1, rfl, ?_, Nat.le_refl _, by omega, K1,
      e0, e1, e5, e6, e7, ?_⟩
    · rw [Nat.add_zero]
      exact hs.update""")
fw = rep(fw, """      ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
        rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
  | cons it ts =>""", """        ((rdN_frame (μ := μ) (μ' := μ1) (fun j hj => by
          rw [show W + 16 + j = W + (16 + j) by omega, fr1 _ (by omega) (Or.inr (by omega))])).trans hs.rl) hs.le
    · simp only [ttext, List.append_nil, Nat.add_zero]
      rw [rdN_frame (μ := μ) (μ' := μ1) (fun j hj => fr1 _ (by omega) (Or.inr (by omega))), ← htx]
      exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))
  | cons it ts =>""")
# cons
fw = rep(fw, """    have hF1 : WFrame μ1 (S - 96) W args 0 ret v5 v6 := ⟨m0, m8, m16, m24, m32, m40, m72, m80, m88⟩""",
 """    have hF1 : WFrame μ1 (S - 96) W args 0 ret v5 v6 := ⟨m0, m8, m16, m24, m32, m40, m72, m80, m88⟩
    have htx1 : μ1.readN (rdN μ1 (W + 8) 8) len = txt := by
      rw [rdN_frame (μ := μ) (μ' := μ1) (fun j hj => fr1 _ (by omega) (Or.inr (by omega))), ← htx]
      exact readN_congr2 fun j hj => fr1 _ (by omega) (Or.inl (by omega))""")
fw = rep(fw, """    rcases wr_item (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (S - 96) W args ret t v5 v6 M C
        ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv it ts
        (wr_loop (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (S - 96) W args ret t v5 v6 M C
          ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv hret hjt hbt ts)""",
 """    rcases wr_item_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (S - 96) W args ret t v5 v6 M C
        ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv it ts bsf
        (wr_loop_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR μA sA spA (S - 96) W args ret t v5 v6 M C bsf
          ⟨by omega, by omega, by omega⟩ ⟨by omega, hW.2.1, hW.2.2⟩ hv hret hjt hbt ts)""")
fw = rep(fw, """        (by omega) hn with
      ⟨ω', μ', x', s', cap', n, hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7⟩ | hx
    · refine Or.inl ⟨ω', μ', x', s', cap', n, hn', (run1.trans run').mono (by omega), H', hb', hs', hc1', hc2',
        ?_, g0, by rw [g1, show S - 96 + 96 = S by omega], g5, g6, g7⟩
      have := K1.trans'""", """        (by omega) hn txt htx1 with
      ⟨ω', μ', x', s', cap', n, hn', run', H', hb', hs', hc1', hc2', K', g0, g1, g5, g6, g7, gT⟩ | hx
    · refine Or.inl ⟨ω', μ', x', s', cap', n, hn', (run1.trans run').mono (by omega), H', hb', hs', hc1', hc2',
        ?_, g0, by rw [g1, show S - 96 + 96 = S by omega], g5, g6, g7, ?_⟩
      · have := K1.trans'""")
fw = rep(fw, """      · have := K1.trans' (K'.lift (sp' := S) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun a h h' => by
        unfold wrE at h; omega))
      rwa [Nat.max_self] at this
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))""", """      · have := K1.trans' (K'.lift (sp' := S) (E' := fun a => W ≤ a ∧ a < W + 24) (by omega) (fun a h h' => by
          unfold wrE at h; omega))
        rwa [Nat.max_self] at this
      · rw [gT, ttext_congr (it :: ts) _ (by omega) (fun a ha => fr1 a (by omega) (Or.inl (by omega)))]
    · exact Or.inr ((Exhausts.pre run1 hx).mono (by omega))""")
fw = '''/-- **`core::fmt::write` into a `String`, with the text** (64495): `fmt_write` on `ReallocCopyOk`,
    the arguments' functions `ArgOkT` with texts `bsf`; the `String`, whose `len` octets were `txt`,
    then holds `txt ++ ttext μ tp ts bsf 0`: the template's literals and the arguments' texts in
    order. -/
''' + fw

head = '''import Services.Bootstrap.Fmt.Write
import Services.Bootstrap.Fmt.Text

/-!
# `core::fmt::write` into a `String`, with the text

`fmt_write` (Fmt/Write.lean) is stated as a frame: the `String` grows by at most `tlen M ts`
octets. Here the same run is stated with its text. Each argument's function appends known octets
(`ArgOkT`), and the `String` gains the template's text `ttext μ tp ts bsf 0`: each literal's octets
from the template, each argument's octets `bsf i`, in order. The proofs follow Fmt/Write.lean
item by item, on `write_str_text` and `ReallocCopyOk`.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The text of a template** at c, items ts, the arguments from index i on appending `bsf i`,
    `bsf (i + 1)`, …: each literal's n octets (after its byte n), each argument's text. -/
def ttext (μ : Memory) : Nat → List TItem → (Nat → List UInt8) → Nat → List UInt8
  | _, [], _, _ => []
  | c, .lit n :: ts, bsf, i => μ.readN (c + 1) n ++ ttext μ (c + 1 + n) ts bsf i
  | c, .arg :: ts, bsf, i => bsf i ++ ttext μ (c + 1) ts bsf (i + 1)

/-- A template's text is kept by a change that keeps the read-only data. -/
theorem ttext_congr {μ μ' : Memory} {bsf : Nat → List UInt8} :
    ∀ (ts : List TItem) (c : Nat) {i : Nat}, c + tsize ts ≤ 196608 →
      (∀ b, b < 196608 → μ'.read b = μ.read b) → ttext μ' c ts bsf i = ttext μ c ts bsf i := by
  intro ts
  induction ts with
  | nil => intro c i _ _; rfl
  | cons it ts ih =>
    intro c i hc k
    cases it with
    | lit n =>
      simp only [ttext, tsize] at hc ⊢
      rw [readN_congr2 (fun j hj => k _ (by omega)), ih _ (by omega) k]
    | arg =>
      simp only [ttext, tsize] at hc ⊢
      rw [ih _ (by omega) k]

'''
out = head + argok + '\n' + argsat + '\nvariable {X : Type} {R : HostRel X}\n\n' + wl + '\n' + wi + '\n' + lp + '\n' + fw + '\nend Services.Bootstrap.Fmt\n'
open('/home/user/jam-lean/Services/Bootstrap/Fmt/WriteText.lean', 'w').write(out)
print('ok')
