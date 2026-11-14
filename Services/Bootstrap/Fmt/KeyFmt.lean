import Services.Bootstrap.Fmt.FormatText
import Services.Bootstrap.Fmt.Dec32Text

/-!
# `format!("transfer{n}")`: the storage key's text

The bootstrap service builds a storage key with `format!("transfer{n}")`, n a u32. That is a call
of `alloc::fmt::format_inner` (59375) with the byte template at 66607: the literal "transfer"
(the byte 8 and its 8 octets), one default-option argument (0xC0), and the end (0). The argument
is the u32 at v with `<u32 as Display>::fmt` (68146).

`key_fmt`: that call returns a `String` whose octets are `(s!"transfer{n}").toUTF8`, with
n = the u32 at v (`format_inner_text`, `dec32T_ok`). Its hypotheses on memory are the program's
read-only data: the template's 11 octets, the `String` vtable's words (`RoW`) and the digit-pair
table (`Dec32.Table`).
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap Services.Bootstrap.Code Services.Bootstrap.CodeF
  Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx Services.Bootstrap.Decode.LoopA
  Services.Bootstrap.SymExec

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {X : Type} {R : HostRel X}

/-- The template of `format!("transfer{n}")`: the literal "transfer", one argument. -/
def keyTmpl : List TItem := [.lit 8, .arg]

/-- The octets of "transfer". -/
theorem transfer_utf8 : "transfer".toUTF8.toList = [116, 114, 97, 110, 115, 102, 101, 114] := by
  decide +kernel

/-- `s!"transfer{n}"`'s octets: "transfer"'s, then n's decimal digits. -/
theorem key_utf8 (n : Nat) : (s!"transfer{n}").toUTF8.toList = "transfer".toUTF8.toList ++ decB n := by
  rw [← repr_utf8]
  simp [ByteArray.toList_eq, ByteArray.data_append]
  rfl

/-- The template's 11 octets at tp make `Tmpl μ tp keyTmpl`, given they are readable. -/
theorem keyTmpl_ok {μ : Memory} {tp : Nat}
    (hT : μ.readN tp 11 = [8] ++ "transfer".toUTF8.toList ++ [192, 0])
    (hr : ∀ a, tp ≤ a → a < tp + 11 → μ.readable a = true) : Tmpl μ tp keyTmpl := by
  rw [transfer_utf8] at hT
  simp only [List.cons_append, List.nil_append] at hT
  have hb : ∀ j, j < 11 → rdN μ (tp + j) 1 =
      Num.decodeLE ((([8, 116, 114, 97, 110, 115, 102, 101, 114, 192, 0] : List UInt8).drop j).take 1) :=
    fun j hj => by
      unfold rdN
      rw [← hT, readN_drop, readN_take _ _ _ _ (by omega)]
  have b0 := hb 0 (by decide)
  have b9 := hb 9 (by decide)
  have b10 := hb 10 (by decide)
  simp only [Nat.add_zero] at b0
  refine ⟨by decide, by decide, by rw [b0]; decide, fun b h1 h2 => hr b h1 (by omega),
    by rw [show tp + 1 + 8 = tp + 9 by omega, b9]; decide, hr _ (by omega) (by omega),
    by rw [show tp + 1 + 8 + 1 = tp + 10 by omega, b10]; decide, hr _ (by omega) (by omega)⟩

/-- **`format!("transfer{n}")`, with the text** (`format_inner`, 59375). Called with the output
    `String`'s address O (ω₇), the template at 66607 (ω₈) and the arguments at an even address
    args (ω₉), the one argument the pair (v, fn) at args: v the address of the u32, fn a jump-table
    address of `<u32 as Display>::fmt` (68146). The return address ω₀ is one that `djump` resolves
    to t. With the read-only data in place (the template's 11 octets, `RoW`, the digit-pair table),
    it either returns to t with a `String` at O holding `(s!"transfer{n}").toUTF8`,
    n = the u32 at v, the context kept, from S up only O … O + 24 changed, and ω₀, ω₁, ω₅, ω₆
    restored; or it reaches a failed allocator call. -/
theorem key_fmt {p : ByteArray} {P : Program} [HasCode p P] [HasCodeF p P] (env : RefineHost.Env)
    (pb S0 S1 : Nat) (HA : AllocOk p R env pb S0 S1) (HR : ReallocCopyOk p R env pb S0 S1)
    (S O args v fn ret t : Nat) (x : X) (ω : Regs) (μ : Memory) (s : State)
    (H : HeapCtx env pb S0 S1 μ s) (hba : s.base % 8 = 0)
    (h0 : ω[0] = UInt64.ofNat ret) (h1 : ω[1] = UInt64.ofNat S) (h7 : ω[7] = UInt64.ofNat O)
    (h8 : ω[8] = UInt64.ofNat 66607) (h9 : ω[9] = UInt64.ofNat args)
    (hret : 0 < ret ∧ ret ≤ 2806 ∧ ret % 2 = 0) (hjt : P.jumpTable.getD (ret / 2 - 1) 0 = t)
    (hbt : P.isBlockStart t = true)
    (hS : S0 + 800 ≤ S ∧ S % 8 = 0 ∧ 2147484500 ≤ S ∧ S ≤ S1) (hO : S ≤ O ∧ O + 24 ≤ S1)
    (hro : RoW μ) (hT : μ.readN 66607 11 = [8] ++ "transfer".toUTF8.toList ++ [192, 0])
    (ht : Dec32.Table μ)
    (hargs : S ≤ args ∧ args + 16 < 4294967296 ∧ args % 2 = 0)
    (hra : ∀ a, args ≤ a → a < args + 16 → μ.readable a = true)
    (hv : rdN μ args 8 = v) (hfn : rdN μ (args + 8) 8 = fn)
    (hf : 0 < fn ∧ fn ≤ 2806 ∧ fn % 2 = 0) (hje : P.jumpTable.getD (fn / 2 - 1) 0 = 68146)
    (hvv : S ≤ v ∧ v + 4 < 4294967296) (hrv : ∀ a, v ≤ a → a < v + 4 → μ.readable a = true) :
    FmtCallT p R env pb S0 S1 ω μ x s S O t (fmtCost 10 2700 keyTmpl)
      (s!"transfer{rdN μ v 4}").toUTF8.toList := by
  have hSb := H.hSb
  have hTm : Tmpl μ 66607 keyTmpl := keyTmpl_ok hT (fun a h1 h2 => hro.vrd a (by omega) (by omega))
  have hA : ArgsAtT p P R env pb S0 S1 μ s S args 0 keyTmpl (fun _ => decB (rdN μ v 4)) 10 2700 := by
    intro j hj
    simp only [keyTmpl, nargs] at hj
    obtain rfl : j = 0 := by omega
    refine ⟨v, fn, 68146, by omega, by omega, fun a h1 h2 => hra a (by omega) (by omega), hv, hfn, hf, hje,
      bs_68146, ?_⟩
    exact dec32T_ok (p := p) (P := P) (R := R) env pb S0 S1 HA HR μ s S v (by omega) hvv hrv ht
  have := format_inner_text (p := p) (P := P) (R := R) env pb S0 S1 HA HR S O 66607 args ret t 10 2700 keyTmpl
    (fun _ => decB (rdN μ v 4)) x ω μ s H hba h0 h1 h7 h8 h9 hret hjt hbt hS hO hro hTm
    ⟨by omega, by simp only [keyTmpl, tsize]; omega⟩ ⟨by omega, hargs.2.2⟩ hA
    (by simp only [keyTmpl, nargs]; omega) (by simp only [keyTmpl, tlen]; omega)
  have htx : ttext μ 66607 keyTmpl (fun _ => decB (rdN μ v 4)) 0 = (s!"transfer{rdN μ v 4}").toUTF8.toList := by
    rw [key_utf8, transfer_utf8]
    simp only [keyTmpl, ttext, List.append_nil]
    congr 1
    have h8 : μ.readN (66607 + 1) 8 = ((μ.readN 66607 11).drop 1).take 8 := by
      rw [readN_drop, readN_take _ _ _ _ (by omega)]
    rw [h8, hT, transfer_utf8]
    rfl
  rwa [htx] at this

end Services.Bootstrap.Fmt
