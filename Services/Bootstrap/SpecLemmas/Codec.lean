import Services.Bootstrap.Spec
import PVM.Logic.Words

/-!
# The codec round trip (step 0)

The decoder bootstrap runs (`Dec`, `jam-codec` 0.1.1's `Decode`) reads back what ℰ writes (GP
appendix C) for every well-formed value: `instr_run` for one instruction, and `decode_payload` and
`decode_output` for the payload `Instructions` and the work output `BootstrapWorkOutput` (step 0
of `docs/bootstrap-target.md`). Only the canonical direction is needed: `Dec.compact` also accepts
encodings ℰ never produces (quirk Q1).

The building blocks say that a parser reads back an encoding and leaves what follows:
`fixedN` inverts ℰ_l (`fixed`), `compact` inverts ℰ (`nat`) below 2^32, and `take`, `len`, `count`,
`vec`, `bytes` and `opt` compose them.
-/

set_option linter.unusedSimpArgs false
namespace Services.Bootstrap.Spec
open JAM.Codec (nat fixed)

namespace Dec

@[simp] theorem run_pure' {α : Type} (a : α) (s : Bytes) : (pure a : Dec α).run s = some (a, s) := rfl

@[simp] theorem run_fail {α : Type} (s : Bytes) : (fail : Dec α).run s = none := rfl

@[simp] theorem fail_bind {α β : Type} (f : α → Dec β) (s : Bytes) : (fail >>= f).run s = none := rfl

theorem bind_of_run {α β : Type} {p : Dec α} {f : α → Dec β} {s s' : Bytes} {a : α}
    (h : p.run s = some (a, s')) : (p >>= f).run s = (f a).run s' := by
  simp only [StateT.run_bind, h]; rfl

@[simp] theorem take_run (n : Nat) (l s : Bytes) (h : l.length = n) :
    (take n).run (l ++ s) = some (l, s) := by
  subst h; simp [take, StateT.run]

@[simp] theorem bind_take {β : Type} (n : Nat) (f : Bytes → Dec β) (l s : Bytes) (h : l.length = n) :
    (take n >>= f).run (l ++ s) = (f l).run s := bind_of_run (take_run n l s h)

@[simp] theorem byte_run (b : UInt8) (s : Bytes) : byte.run (b :: s) = some (b.toNat, s) := by
  have h := bind_of_run (f := fun b => (pure (b.headD 0).toNat : Dec Nat)) (take_run 1 [b] s rfl)
  exact h

@[simp] theorem bind_byte {β : Type} (f : Nat → Dec β) (b : UInt8) (s : Bytes) :
    (byte >>= f).run (b :: s) = (f b.toNat).run s := bind_of_run (byte_run b s)

@[simp] theorem fixedN_run (l x : Nat) (s : Bytes) :
    (fixedN l).run (fixed l x ++ s) = some (x % 2 ^ (8 * l), s) := by
  have h := bind_of_run (f := fun b => (pure (PVM.Num.decodeLE b) : Dec Nat))
    (take_run l (fixed l x) s (PVM.Num.length_encodeLE l x))
  show (take l >>= fun b => (pure (PVM.Num.decodeLE b) : Dec Nat)).run _ = _
  rw [h]; simp [JAM.Codec.fixed, PVM.Num.decodeLE_encodeLE]

@[simp] theorem bind_fixedN {β : Type} (f : Nat → Dec β) (l x : Nat) (s : Bytes) :
    (fixedN l >>= f).run (fixed l x ++ s) = (f (x % 2 ^ (8 * l))).run s := bind_of_run (fixedN_run l x s)

theorem ite_pos' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : c) : ite c a b = a := by simp [h]
theorem ite_neg' {c : Prop} [Decidable c] {α : Type} {a b : α} (h : ¬ c) : ite c a b = b := by simp [h]

theorem leadingOnes_eq : ∀ B < 255, leadingOnes B =
    (if B < 128 then 0 else if B < 192 then 1 else if B < 224 then 2 else if B < 240 then 3
     else if B < 248 then 4 else if B < 252 then 5 else if B < 254 then 6 else 7) := by
  decide +kernel

theorem compact_aux (l x B : Nat) (s : Bytes) (hB : B < 255) (hlo : leadingOnes B = l)
    (hval : x % 2 ^ (8 * l) + B % 2 ^ (7 - l) * 2 ^ (8 * l) = x) :
    compact.run (UInt8.ofNat B :: (PVM.Num.encodeLE l (x % 2 ^ (8 * l)) ++ s)) = some (x, s) := by
  have hB' : (UInt8.ofNat B).toNat = B := by simp; omega
  simp only [compact, bind_byte, hB', show B ≠ 255 by omega, ite_false, hlo]
  rw [show PVM.Num.encodeLE l (x % 2 ^ (8 * l)) = fixed l (x % 2 ^ (8 * l)) from rfl, bind_fixedN]
  simp [hval]

/-- `compact` inverts GP's ℰ on naturals below 2^32. -/
@[simp] theorem compact_run (x : Nat) (hx : x < 2 ^ 32) (s : Bytes) :
    compact.run (nat x ++ s) = some (x, s) := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · subst h0
    exact compact_aux 0 0 0 s (by decide) (by decide) (by decide)
  have : x < 128 ∨ (128 ≤ x ∧ x < 16384) ∨ (16384 ≤ x ∧ x < 2097152) ∨
      (2097152 ≤ x ∧ x < 268435456) ∨ 268435456 ≤ x := by omega
  rcases this with h1 | h1 | h1 | h1 | h1
  · rw [show nat x = _ from PVM.encodeNat_of_lt x 0 (by decide) h0 (by simp; omega) (by simp; omega)]
    refine compact_aux 0 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from PVM.encodeNat_of_lt x 1 (by decide) h0 (by simp; omega) (by simp; omega)]
    refine compact_aux 1 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from PVM.encodeNat_of_lt x 2 (by decide) h0 (by simp; omega) (by simp; omega)]
    refine compact_aux 2 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from PVM.encodeNat_of_lt x 3 (by decide) h0 (by simp; omega) (by simp; omega)]
    refine compact_aux 3 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.div_one, Nat.zero_add, ite_pos', ite_neg']
  · rw [show nat x = _ from PVM.encodeNat_of_lt x 4 (by decide) h0 (by simp; omega) (by simp; omega)]
    refine compact_aux 4 x _ s (by simp; omega) ?_ (by simp; omega)
    rw [leadingOnes_eq _ (by simp; omega)]
    simp (disch := omega) only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.div_one, Nat.zero_add, ite_pos', ite_neg']

@[simp] theorem bind_compact {β : Type} (f : Nat → Dec β) (x : Nat) (hx : x < 2 ^ 32) (s : Bytes) :
    (compact >>= f).run (nat x ++ s) = (f x).run s := bind_of_run (compact_run x hx s)

@[simp] theorem len_run (x : Nat) (hx : x < 2 ^ 32) (s : Bytes) : len.run (nat x ++ s) = some (x, s) := by
  simp only [len, bind_compact _ x hx, hx, ite_true]; rfl

@[simp] theorem bind_len {β : Type} (f : Nat → Dec β) (x : Nat) (hx : x < 2 ^ 32) (s : Bytes) :
    (len >>= f).run (nat x ++ s) = (f x).run s := bind_of_run (len_run x hx s)

/-- `p` reads back `e x`, whatever follows. -/
def Reads {α : Type} (p : Dec α) (e : α → Bytes) (x : α) : Prop := ∀ s, p.run (e x ++ s) = some (x, s)

/-- `p` reads back `e x` for every x in `xs` (a separate definition, so `simp` can discharge it from a
    hypothesis). -/
def AllReads {α : Type} {C : Type → Type} [Membership α (C α)] (p : Dec α) (e : α → Bytes) (xs : C α) :
    Prop := ∀ x ∈ xs, Reads p e x

theorem count_run {α : Type} (p : Dec α) (e : α → Bytes) (xs : List α) (h : AllReads p e xs)
    (s : Bytes) : (count p xs.length).run ((xs.map e).flatten ++ s) = some (xs, s) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [count, List.map_cons, List.flatten_cons, List.append_assoc, List.length_cons]
    rw [bind_of_run (h x (by simp) _), bind_of_run (ih (fun y hy => h y (by simp [hy])))]
    rfl

@[simp] theorem bind_count {α β : Type} (p : Dec α) (e : α → Bytes) (xs : List α) (n : Nat)
    (f : List α → Dec β) (hn : xs.length = n) (h : AllReads p e xs) (s : Bytes) :
    (count p n >>= f).run ((xs.map e).flatten ++ s) = (f xs).run s := by
  subst hn; exact bind_of_run (count_run p e xs h s)

theorem vec_run {α : Type} (p : Dec α) (e : α → Bytes) (xs : List α) (hn : short xs)
    (h : AllReads p e xs) (s : Bytes) : (Dec.vec p).run (Spec.vec e xs ++ s) = some (xs, s) := by
  simp only [Dec.vec, Spec.vec, List.append_assoc, bind_len _ _ hn]
  exact count_run p e xs h s

@[simp] theorem bind_vec {α β : Type} (p : Dec α) (e : α → Bytes) (xs : List α) (f : List α → Dec β)
    (hn : short xs) (h : AllReads p e xs) (s : Bytes) :
    (Dec.vec p >>= f).run (Spec.vec e xs ++ s) = (f xs).run s := bind_of_run (vec_run p e xs hn h s)

theorem bytes_run (b : Bytes) (hb : short b) (s : Bytes) : Dec.bytes.run (Spec.bytes b ++ s) = some (b, s) := by
  simp only [Dec.bytes, Spec.bytes, List.append_assoc, bind_len _ _ hb]
  exact take_run _ b s rfl

@[simp] theorem bind_bytes {β : Type} (b : Bytes) (f : Bytes → Dec β) (hb : short b) (s : Bytes) :
    (Dec.bytes >>= f).run (Spec.bytes b ++ s) = (f b).run s := bind_of_run (bytes_run b hb s)

theorem opt_run {α : Type} (p : Dec α) (e : α → Bytes) (o : Option α) (h : AllReads p e o)
    (s : Bytes) : (Dec.opt p).run (Spec.opt e o ++ s) = some (o, s) := by
  cases o with
  | none => rfl
  | some x =>
    simp only [Dec.opt, Spec.opt, List.cons_append, bind_byte]
    show ((some <$> p).run (e x ++ s)) = _
    simp [h x rfl s]

@[simp] theorem bind_opt {α β : Type} (p : Dec α) (e : α → Bytes) (o : Option α) (f : Option α → Dec β)
    (h : AllReads p e o) (s : Bytes) :
    (Dec.opt p >>= f).run (Spec.opt e o ++ s) = (f o).run s := bind_of_run (opt_run p e o h s)

theorem reads_take {x : Bytes} {n : Nat} (h : x.length = n) : Reads (take n) id x :=
  fun s => take_run n x s h

theorem reads_bytes {b : Bytes} (h : short b) : Reads Dec.bytes Spec.bytes b := bytes_run b h

theorem fits_mod {l x : Nat} (h : fits l x) : x % 2 ^ (8 * l) = x := Nat.mod_eq_of_lt h

theorem reads_fixedN {l x : Nat} (h : fits l x) : Reads (fixedN l) (fixed l) x := fun s => by
  simp [fits_mod h]

@[simp] theorem run_map {α β : Type} (f : α → β) (p : Dec α) (s : Bytes) :
    (f <$> p).run s = (p.run s).map (fun r => (f r.1, r.2)) := by
  simp only [StateT.run_map]; rfl

end Dec

open Dec

/-- Read back an encoding with the round-trip lemmas above and the hypotheses given. -/
local syntax "rt" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
local macro_rules
  | `(tactic| rt [$ts,*]) => `(tactic| simp only [bind_take, bind_fixedN, bind_byte, bind_len, bind_vec,
      bind_bytes, bind_opt, bind_count, take_run, fixedN_run, vec_run, bytes_run, opt_run, count_run,
      run_pure', run_map, Option.map_some, fits_mod, List.append_assoc, UInt8.reduceToNat, $ts,*])

/-- Prefix of every case of `instr_run`: unfold, read the tag octet and pick its branch. -/
local macro "tag" : tactic => `(tactic|
  simp only [Instr.encode, instr, List.append_assoc, List.cons_append, List.nil_append, bind_byte,
    UInt8.reduceToNat])

/-- `Dec.instr` reads back ℰ(x) for every well-formed instruction x. -/
theorem instr_run (C : Consts) (x : Instr) (hx : x.WF C) (s : Bytes) :
    (instr C).run (x.encode ++ s) = some (x, s) := by
  cases x with
  | createService h l g m b memo r f id =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hx
    have hr : AllReads Dec.bytes Spec.bytes r := fun n hn => reads_bytes (h7 n hn)
    have hi : AllReads (fixedN 4) (fixed 4) id := fun n hn => reads_fixedN (h9 n hn)
    tag
    rt [h1, h6, fits_mod h2, fits_mod h3, fits_mod h4, fits_mod h5, fits_mod h8, hr, hi]
  | upgrade h g m =>
    obtain ⟨h1, h2, h3⟩ := hx
    tag; rt [h1, fits_mod h2, fits_mod h3]
  | transfer d a g memo =>
    obtain ⟨h1, h2, h3, h4⟩ := hx
    tag; rt [h4, fits_mod h1, fits_mod h2, fits_mod h3]
  | zombify e => tag; rt [fits_mod hx]
  | eject t h =>
    obtain ⟨h1, h2⟩ := hx
    tag; rt [h2, fits_mod h1]
  | deleteItems ks =>
    obtain ⟨h1, h2⟩ := hx
    have hr : AllReads Dec.bytes Spec.bytes ks := fun k hk => reads_bytes (h2 k hk)
    tag; rt [h1, hr]
  | solicit h l =>
    obtain ⟨h1, h2⟩ := hx
    tag; rt [h1, fits_mod h2]
  | forget h l =>
    obtain ⟨h1, h2⟩ := hx
    tag; rt [h1, fits_mod h2]
  | lookup sv h e =>
    obtain ⟨h1, h2⟩ := hx
    cases e <;> (tag; rt [h2, fits_mod h1, Dec.bool]) <;> rfl
  | importSegs is =>
    obtain ⟨h1, h2⟩ := hx
    tag
    rw [bind_vec _ _ _ _ h1 ?_]
    · rfl
    · intro p hp s
      obtain ⟨a, b⟩ := p
      simp [fits_mod (h2 _ hp).1, fits_mod (h2 _ hp).2]
  | exportSegs ds =>
    obtain ⟨h1, h2⟩ := hx
    have hr : AllReads Dec.bytes Spec.bytes ds := fun k hk => reads_bytes (h2 k hk)
    tag; rt [h1, hr]
  | bless m a v r z =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hx
    tag
    simp only [bind_fixedN, fits_mod h1, fits_mod h2, fits_mod h3, fits_mod h4]
    rw [bind_vec _ _ _ _ h5 ?_]
    · rfl
    · intro p hp s
      obtain ⟨a, b⟩ := p
      simp [fits_mod (h6 _ hp).1, fits_mod (h6 _ hp).2]
  | assign c q a =>
    obtain ⟨h1, h2, h3, h4⟩ := hx
    have hr : AllReads (take 32) id q := fun h hh => reads_take (h3 h hh)
    tag
    rw [show q.flatten = (q.map id).flatten by simp]
    rt [fits_mod h1, fits_mod h4, h2, hr]
  | designate ks =>
    obtain ⟨h1, h2, h3⟩ := hx
    have hr : AllReads (take 336) id ks := fun h hh => reads_take (h3 h hh)
    tag
    have hn : ks.length < 2 ^ 32 := h2
    rt [Spec.vec, hn, hr, show ¬ ks.length > C.maxValCount by omega, ite_false]
  | yield h => tag; rt [show h.length = 32 from hx]
  | checkpoint => rfl
  | panic => rfl
  | provide sv pre =>
    cases pre with
    | hash h =>
      obtain ⟨h1, h2⟩ := hx
      tag; rt [h2, fits_mod h1]
    | inline d =>
      obtain ⟨h1, h2⟩ := hx
      tag; rt [h2, fits_mod h1]
  | lookedUp d =>
    have hr : AllReads Dec.bytes Spec.bytes d := fun n hn => reads_bytes (hx n hn)
    tag; rt [hr]
  | imported ds =>
    obtain ⟨h1, h2⟩ := hx
    have hr : AllReads Dec.bytes Spec.bytes ds := fun k hk => reads_bytes (h2 k hk)
    tag; rt [h1, hr]
  | exported n => tag; rt [fits_mod hx]
  | randomStorageRefine sd n =>
    obtain ⟨h1, h2⟩ := hx
    tag; rt [fits_mod h1, fits_mod h2]
  | randomStorageAccumulate ks =>
    cases ks with
    | none => rfl
    | some ks =>
      obtain ⟨h1, h2⟩ := hx ks rfl
      have hr : AllReads (take 32) id ks := fun h hh => reads_take (h2 h hh)
      tag; rt [h1, hr]
  | benchmark => rfl
  | assignForGasCost c q a =>
    obtain ⟨h1, h2, h3, h4⟩ := hx
    have hr : AllReads (take 32) id q := fun h hh => reads_take (h3 h hh)
    tag; rt [fits_mod h1, fits_mod h4, h2, hr]

end Services.Bootstrap.Spec

namespace Services.Bootstrap.Spec
open JAM.Codec (nat fixed)
open Dec

theorem allReads_instr (C : Consts) (is : List Instr) (hwf : ∀ x ∈ is, x.WF C) :
    AllReads (instr C) Instr.encode is := fun x hx s => instr_run C x (hwf x hx) s

/-- **Step 0, payload.** Decoding ℰ(`Instructions { is, salt }`) ⌢ rest gives back `is` and the salt,
    for well-formed instructions, fewer than 2^32 of them, and a 32-octet salt. -/
theorem decode_payload (C : Consts) (is : List Instr) (salt rest : Bytes) (hwf : ∀ x ∈ is, x.WF C)
    (hn : is.length < 2 ^ 32) (hsalt : salt.length = 32) :
    decode (Dec.payload C) (encodePayload is salt ++ rest) = some (is, salt) := by
  have hr := allReads_instr C is hwf
  have hs : short is := hn
  simp only [decode, Dec.payload, encodePayload, List.append_assoc, bind_vec _ _ _ _ hs hr,
    bind_take _ _ _ _ hsalt, run_pure', Option.map_some]

/-- **Step 0, output.** Decoding ℰ(`BootstrapWorkOutput { is, i }`) ⌢ rest gives back `is` and i mod 2^16,
    for well-formed instructions, fewer than 2^32 of them. -/
theorem decode_output' (C : Consts) (is : List Instr) (i : Nat) (rest : Bytes) (hwf : ∀ x ∈ is, x.WF C)
    (hn : is.length < 2 ^ 32) :
    decode (Dec.output C) (encodeOutput is i ++ rest) = some (is, i % 2 ^ 16) := by
  have hr := allReads_instr C is hwf
  have hs : short is := hn
  simp only [decode, Dec.output, encodeOutput, List.append_assoc, bind_vec _ _ _ _ hs hr,
    bind_fixedN, run_pure', Option.map_some]

/-- **Step 0, output**, for a work-item index below 2^16. -/
theorem decode_output (C : Consts) (is : List Instr) (i : Nat) (rest : Bytes) (hwf : ∀ x ∈ is, x.WF C)
    (hn : is.length < 2 ^ 32) (hi : i < 2 ^ 16) :
    decode (Dec.output C) (encodeOutput is i ++ rest) = some (is, i) := by
  rw [decode_output' C is i rest hwf hn, Nat.mod_eq_of_lt hi]

end Services.Bootstrap.Spec
