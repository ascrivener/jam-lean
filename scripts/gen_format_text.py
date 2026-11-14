"""Generate Services/Bootstrap/Fmt/FormatText.lean from Fmt/Format.lean: `format_inner` with the
text, on `fmt_write_text` (Fmt/WriteText.lean)."""
F = open('/home/user/jam-lean/Services/Bootstrap/Fmt/Format.lean').read()
def block(src, start_pat, end_pat):
    s = src.index(start_pat); e = src.index(end_pat, s + 1)
    return src[s:e].rstrip() + '\n'
def rep(blk, a, b, cnt=1):
    assert blk.count(a) == cnt, (a[:90], blk.count(a))
    return blk.replace(a, b)

# fi_tail_text
ft = block(F, 'theorem fi_tail ', '/-- **`alloc::fmt::format_inner`, frame-only')
ft = rep(ft, 'theorem fi_tail ', 'theorem fi_tail_text ')
ft = rep(ft, '(HR : ReallocOk p R env pb S0 S1)', '(HR : ReallocCopyOk p R env pb S0 S1)')
ft = rep(ft, '(S O tp args ret t v5 v6 M C cap : Nat) (ts : List TItem)', '(S O tp args ret t v5 v6 M C cap : Nat) (ts : List TItem) (bsf : Nat → List UInt8)')
ft = rep(ft, '(hA : ArgsAt p P R env pb S0 S1 μ s S args 0 ts M C)', '(hA : ArgsAtT p P R env pb S0 S1 μ s S args 0 ts bsf M C)')
ft = rep(ft, """      StrOut s s' μ' O ∧ ω'[0] = UInt64.ofNat ret""", """      StrOutT s s' μ' O (ttext μ1 tp ts bsf 0) ∧ ω'[0] = UInt64.ofNat ret""")
ft = rep(ft, 'rcases fmt_write (p := p)', 'rcases fmt_write_text (p := p)')
ft = rep(ft, 'ω[5].toNat ω[6].toNat M C ts x ω μ1 s1 cap 0', 'ω[5].toNat ω[6].toNat M C ts bsf x ω μ1 s1 cap 0')
ft = rep(ft, """⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ hro hTm htp hargs hA hi (by omega) with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hs2, hc1, hc2, K2, e0, e1, e5, e6, e7⟩ | hx""",
 """⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ hro hTm htp hargs hA hi (by omega) [] rfl with
    ⟨ω2, μ2, x2, s2, cap2, n, hn2, run2, H2, hb2, hs2, hc1, hc2, K2, e0, e1, e5, e6, e7, tx2⟩ | hx""")
ft = rep(ft, """    have := hs2.lt
    refine Or.inl ⟨ω3, μ3, x2, s2, (run2.trans run3).mono (by omega),
      ctx_hi H2 (fun a ha => fr3 a (by omega) (Or.inl (by omega))) wr3, hb2, K23,
      ⟨cap2, 0 + n, hs2.move m0 m8 m16⟩, f0, by rw [f1, show S - 72 + 72 = S by omega], f5, f6⟩""",
 """    have := hs2.lt
    have hbl : 0 + n = 0 ∨ rdN μ2 (S - 72 + 32) 8 + cap2 < 2147483648 := by
      have := buf_lt hs2 H2
      rwa [show S - 72 + 24 + 8 = S - 72 + 32 by omega] at this
    have hle2 := hs2.le
    rw [List.nil_append] at tx2
    have hnl : n = (ttext μ1 tp ts bsf 0).length := by rw [← tx2, Memory.length_readN, Nat.zero_add]
    refine Or.inl ⟨ω3, μ3, x2, s2, (run2.trans run3).mono (by omega),
      ctx_hi H2 (fun a ha => fr3 a (by omega) (Or.inl (by omega))) wr3, hb2, K23,
      ⟨cap2, by rw [← hnl, ← Nat.zero_add n]; exact hs2.move m0 m8 m16, ?_⟩, f0,
      by rw [f1, show S - 72 + 72 = S by omega], f5, f6⟩
    rw [← hnl, m8, ← tx2, Nat.zero_add]
    exact readN_congr2 fun j hj => fr3 _ (by omega) (Or.inl (by omega))""")
ft = '/-- `fi_tail` with the text: the `String` moved to O holds the template\'s text. -/\n' + ft

# format_inner_text
fi = block(F, 'theorem format_inner ', 'end Services.Bootstrap.Fmt')
fi = rep(fi, 'theorem format_inner ', 'theorem format_inner_text ')
fi = rep(fi, '(HR : ReallocOk p R env pb S0 S1)', '(HR : ReallocCopyOk p R env pb S0 S1)')
fi = rep(fi, '(S O tp args ret t M C : Nat) (ts : List TItem)', '(S O tp args ret t M C : Nat) (ts : List TItem) (bsf : Nat → List UInt8)')
fi = rep(fi, '(hA : ArgsAt p P R env pb S0 S1 μ s S args 0 ts M C)', '(hA : ArgsAtT p P R env pb S0 S1 μ s S args 0 ts bsf M C)')
fi = rep(fi, 'FmtCall p R env pb S0 S1 ω μ x s S O t (fmtCost M C ts) := by', 'FmtCallT p R env pb S0 S1 ω μ x s S O t (fmtCost M C ts) (ttext μ tp ts bsf 0) := by', 2)
fi = rep(fi, """    rcases fi_tail (p := p) (P := P) (R := R) env pb S0 S1 HA HR S O tp args ret t ω[5].toNat ω[6].toNat M C cap
        ts x1""", """    rcases fi_tail_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR S O tp args ret t ω[5].toNat ω[6].toNat M C cap
        ts bsf x1""")
fi = rep(fi, """      have := (K1.mono (Nat.le_refl _) (fun a h => False.elim h)).trans' K'
      rwa [Nat.max_self] at this""", """      · have := (K1.mono (Nat.le_refl _) (fun a h => False.elim h)).trans' K'
        rwa [Nat.max_self] at this
      · rwa [ttext_congr ts tp (by omega) (fun a ha => (K1.ro_low H a ha).1)] at hso""")
fi = rep(fi, """    · refine Or.inl ⟨ω', μ', x', s', (run1.trans run').mono (by unfold fmtCost; omega), H', hb'.trans hb1, ?_,
        hso, g0.trans""", """    · refine Or.inl ⟨ω', μ', x', s', (run1.trans run').mono (by unfold fmtCost; omega), H', hb'.trans hb1, ?_,
        ?_, g0.trans""")
fi = '''/-- **`alloc::fmt::format_inner`, with the text: `FmtCallT`** (59375). `format_inner` (Fmt/Format.lean)
    on `ReallocCopyOk`, the arguments' functions `ArgOkT` with texts `bsf`: the `String` returned at
    O holds the template's text `ttext μ tp ts bsf 0`. -/
''' + fi

head = '''import Services.Bootstrap.Fmt.Format
import Services.Bootstrap.Fmt.WriteText

/-!
# `alloc::fmt::format_inner` with the text

`format_inner` (Fmt/Format.lean) returns a `String` whose text is left unstated (`StrOut`). Here
the same call is stated with its text (`StrOutT`). The `String` at O holds `ttext μ tp ts bsf 0`:
the template's literals and the arguments' texts, in order. The proofs follow Fmt/Format.lean on
`fmt_write_text`. Generated by scripts/gen_format_text.py.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- **The `String` a formatting call returns, at O, with its text**: some capacity (`Str`), and
    its |out| octets are `out`. -/
def StrOutT (s s' : State) (μ : Memory) (O : Nat) (out : List UInt8) : Prop :=
  ∃ cap, Str s s' μ O cap out.length ∧ μ.readN (rdN μ (O + 8) 8) out.length = out

/-- `FmtCall` with the text: the `String` returned at O holds `out` (`StrOutT`). -/
def FmtCallT (p : ByteArray) {X : Type} (R : HostRel X) (env : RefineHost.Env) (pb S0 S1 : Nat)
    (ω : Regs) (μ : Memory) (x : X) (s : State) (sp O t N : Nat) (out : List UInt8) : Prop :=
  (∃ ω' μ' x' s', FreeStepsH p R 59375 ω μ x t ω' μ' x' N ∧ HeapCtx env pb S0 S1 μ' s' ∧
    s'.base = s.base ∧ Keeps pb sp (fun a => O ≤ a ∧ a < O + 24) s μ μ' s' ∧ StrOutT s s' μ' O out ∧
    ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
  Exhausts p R pb 59375 ω μ x N

variable {X : Type} {R : HostRel X}

'''
open('/home/user/jam-lean/Services/Bootstrap/Fmt/FormatText.lean', 'w').write(head + ft + '\n' + fi + '\nend Services.Bootstrap.Fmt\n')
print('ok')
