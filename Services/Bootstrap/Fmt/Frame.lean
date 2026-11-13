import Services.Bootstrap.Decode.LoopA

/-!
# What a logging run keeps, and the allocator it calls

Logging (`format!`, `core::fmt`, the `log` host call) has no effect on a service's state or
output. So its proofs are **frame-only**. They show that a formatting run ends within a step
bound, makes no host calls other than the allocator's, and changes nothing except:
- its own stack frame;
- its own fresh allocations;
- the allocator's fields and headers;
- the `String` it writes into.

The text it produces is left unspecified.

* `Keeps pb sp E s₀ μ₀ μ s`: from memory μ₀ with allocator state s₀ to μ with state s, a run keeps:
  - every page entry outside the heap's pages 48 … pb;
  - every octet on such a page that is not writable (read-only data, for one);
  - every octet at or above sp except those in `E`;
  - the globals below the allocator (`Glob`);
  - every allocated chunk of s₀, still allocated in s, with its data.

  `Keeps.trans` composes two such runs.
* `Oracle p R env pb S0 S1`: what the proofs assume of one call of picoalloc's `alloc` wrapper
  (40494 → 40611) and `realloc` wrapper (40701 → 40821) under the host relation `R`:
  - either the call returns a block of a fresh chunk, with the allocator's context (`HeapCtx`)
    kept and the frame `Keeps`;
  - or it returns null where the model's operation fails.

  The summaries take the oracle as a hypothesis, so they serve any host relation for which it is
  proved: refine's `refineContractK` (`Fmt/OracleRefine.lean`), or accumulate's.
-/

namespace Services.Bootstrap.Fmt

open PVM Picoalloc JAM Services.Bootstrap.Alloc Services.Bootstrap.Decode.HeapCtx
  Services.Bootstrap.Decode.LoopA

/-- **Outside the heap and the stack below sp**, from μ₀ to μ: page entries outside the heap's
    pages, octets there that are not writable, octets at or above sp except `E` (the `String` and
    the `Formatter` a run was handed), and the globals, all kept. -/
structure Outside (pb sp : Nat) (E : Nat → Prop) (μ₀ μ : Memory) : Prop where
  access : ∀ b, (b / pageSize < 48 ∨ pb ≤ b / pageSize) →
    μ.readable b = μ₀.readable b ∧ μ.writable b = μ₀.writable b
  ro : ∀ b, b < 4294967296 → (b / pageSize < 48 ∨ pb ≤ b / pageSize) → μ₀.writable b = false →
    μ.read b = μ₀.read b
  hi : ∀ a, sp ≤ a → a < 4294967296 → ¬ E a → μ.read a = μ₀.read a
  glob : ∀ a, Glob a → μ.read a = μ₀.read a

/-- **The frame of a logging run** from (μ₀, s₀) to (μ, s): `Outside`, and every allocated chunk of
    s₀ still allocated in s with its data. -/
structure Keeps (pb sp : Nat) (E : Nat → Prop) (s₀ : State) (μ₀ μ : Memory) (s : State) : Prop
    extends Outside pb sp E μ₀ μ where
  used : ∀ c ∈ chunks s₀, c.used = true → c ∈ chunks s
  data : ∀ c ∈ chunks s₀, c.used = true → ∀ a, InData c a → μ.read a = μ₀.read a

theorem Keeps.refl (pb sp : Nat) (E : Nat → Prop) (s : State) (μ : Memory) : Keeps pb sp E s μ μ s :=
  ⟨⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl⟩, fun _ h _ => h,
    fun _ _ _ _ _ => rfl⟩

/-- Two runs, one after the other: the frame of both, above the higher stack pointer. -/
theorem Keeps.trans {pb sp₁ sp₂ : Nat} {E : Nat → Prop} {s₀ s₁ s₂ : State} {μ₀ μ₁ μ₂ : Memory}
    (h₁ : Keeps pb sp₁ E s₀ μ₀ μ₁ s₁) (h₂ : Keeps pb sp₂ E s₁ μ₁ μ₂ s₂) :
    Keeps pb (max sp₁ sp₂) E s₀ μ₀ μ₂ s₂ where
  access b hq := ⟨(h₂.access b hq).1.trans (h₁.access b hq).1, (h₂.access b hq).2.trans (h₁.access b hq).2⟩
  ro b hb hq hw := by
    have e := h₁.ro b hb hq hw
    have hw1 : μ₁.writable b = false := by rw [(h₁.access b hq).2]; exact hw
    exact (h₂.ro b hb hq hw1).trans e
  hi a ha hb hE := (h₂.hi a (by omega) hb hE).trans (h₁.hi a (by omega) hb hE)
  glob a ha := (h₂.glob a ha).trans (h₁.glob a ha)
  used c hc hu := h₂.used c (h₁.used c hc hu) hu
  data c hc hu a ha := (h₂.data c (h₁.used c hc hu) hu a ha).trans (h₁.data c hc hu a ha)

/-- Two runs, one after the other, both stated from the same s₀. -/
theorem Keeps.trans' {pb sp₁ sp₂ : Nat} {E : Nat → Prop} {s₀ s₁ s₂ : State} {μ₀ μ₁ μ₂ : Memory}
    (h₁ : Keeps pb sp₁ E s₀ μ₀ μ₁ s₁) (h₂ : Keeps pb sp₂ E s₀ μ₁ μ₂ s₂) :
    Keeps pb (max sp₁ sp₂) E s₀ μ₀ μ₂ s₂ where
  access b hq := ⟨(h₂.access b hq).1.trans (h₁.access b hq).1, (h₂.access b hq).2.trans (h₁.access b hq).2⟩
  ro b hb hq hw := by
    have e := h₁.ro b hb hq hw
    have hw1 : μ₁.writable b = false := by rw [(h₁.access b hq).2]; exact hw
    exact (h₂.ro b hb hq hw1).trans e
  hi a ha hb hE := (h₂.hi a (by omega) hb hE).trans (h₁.hi a (by omega) hb hE)
  glob a ha := (h₂.glob a ha).trans (h₁.glob a ha)
  used := h₂.used
  data c hc hu a ha := (h₂.data c hc hu a ha).trans (h₁.data c hc hu a ha)

/-- A frame from s, stated from an s₀ whose allocated chunks s has. -/
theorem Keeps.rebase {pb sp : Nat} {E : Nat → Prop} {s₀ s s' : State} {μ μ' : Memory}
    (h : Keeps pb sp E s μ μ' s') (hb : ∀ c ∈ chunks s₀, c.used = true → c ∈ chunks s) :
    Keeps pb sp E s₀ μ μ' s' :=
  ⟨h.toOutside, fun c hc hu => h.used c (hb c hc hu) hu, fun c hc hu => h.data c (hb c hc hu) hu⟩

/-- A frame is kept by a larger stack pointer and more writable octets. -/
theorem Keeps.mono {pb sp sp' : Nat} {E E' : Nat → Prop} {s₀ s : State} {μ₀ μ : Memory}
    (h : Keeps pb sp E s₀ μ₀ μ s) (hsp : sp ≤ sp') (hE : ∀ a, E a → E' a) :
    Keeps pb sp' E' s₀ μ₀ μ s :=
  { h with hi := fun a ha hb hn => h.hi a (by omega) hb (fun e => hn (hE a e)) }

/-- **A run that writes only writable octets in `Z`** keeps the frame, when `Z` meets neither the
    octets at or above sp outside `E`, nor the globals, nor the data of an allocated chunk of s, and
    every octet keeps its access. -/
theorem Keeps.of_frame {pb sp : Nat} {E Z : Nat → Prop} {s₀ s : State} {μ μ' : Memory}
    (hused : ∀ c ∈ chunks s₀, c.used = true → c ∈ chunks s)
    (hz : ∀ a, a < 4294967296 → ¬ Z a → μ'.read a = μ.read a)
    (hrd : ∀ a, μ'.readable a = μ.readable a) (hwr : ∀ a, μ'.writable a = μ.writable a)
    (hzw : ∀ a, Z a → μ.writable a = true) (hzhi : ∀ a, Z a → sp ≤ a → E a)
    (hzg : ∀ a, Z a → ¬ Glob a)
    (hzd : ∀ c ∈ chunks s₀, c.used = true → ∀ a, InData c a → a < 4294967296 ∧ ¬ Z a) :
    Keeps pb sp E s₀ μ μ' s where
  access b _ := ⟨hrd b, hwr b⟩
  ro b hb _ hw := hz b hb (fun h => by rw [hzw b h] at hw; exact absurd hw (by decide))
  hi a ha hb hE := hz a hb (fun h => hE (hzhi a h ha))
  glob a ha := hz a (by unfold Glob at ha; omega) (fun h => hzg a h ha)
  used := hused
  data c hc hu a ha := hz a (hzd c hc hu a ha).1 (hzd c hc hu a ha).2

/-- **The run reaches a failed allocator call**: the `alloc` wrapper's return (40611) where the
    model's `alloc` fails, or the `realloc` wrapper's return (40821) where the model's `realloc`
    fails, with null in ω₇. This is the start of heap exhaustion (bootstrap decision 4), where a
    logging run stops being followed. -/
def Exhausts (p : ByteArray) {X : Type} (R : HostRel X) (pb i : Nat) (ω : Regs) (μ : Memory) (x : X)
    (n : Nat) : Prop :=
  ∃ (ω' : Regs) (μ' : Memory) (x' : X) (j : Nat), FreeStepsH p R i ω μ x j ω' μ' x' n ∧
    ω'[7] = UInt64.ofNat 0 ∧
    ((j = 40611 ∧ ∃ (s : State) (hb r : Nat), alloc (growTo pb) hb 1 r s = none) ∨
     (j = 40821 ∧ ∃ (s : State) (hb ptr al r : Nat), realloc (growTo pb) hb s ptr al r = none))

/-- A run before a failed allocator call is still one. -/
theorem Exhausts.pre {p : ByteArray} {X : Type} {R : HostRel X} {pb i j n m : Nat} {ω ω1 : Regs}
    {μ μ1 : Memory} {x x1 : X} (run : FreeStepsH p R i ω μ x j ω1 μ1 x1 n)
    (h : Exhausts p R pb j ω1 μ1 x1 m) : Exhausts p R pb i ω μ x (n + m) := by
  obtain ⟨ω', μ', x', k, run', e7, ha⟩ := h
  exact ⟨ω', μ', x', k, run.trans run', e7, ha⟩

theorem Exhausts.mono {p : ByteArray} {X : Type} {R : HostRel X} {pb i n m : Nat} {ω : Regs}
    {μ : Memory} {x : X} (h : Exhausts p R pb i ω μ x n) (hnm : n ≤ m) : Exhausts p R pb i ω μ x m := by
  obtain ⟨ω', μ', x', k, run', e7, ha⟩ := h
  exact ⟨ω', μ', x', k, run'.mono hnm, e7, ha⟩

/-- The heap's writable pages (48 … pb) lie below `4096 · pb`; the stack, at S0 ≥ 4096 · pb. So
    `HeapCtx`'s heap and stack are apart. -/
theorem HeapCtx.pb_le {env : RefineHost.Env} {pb S0 S1 : Nat} {μ : Memory} {s : State}
    (H : HeapCtx env pb S0 S1 μ s) : 4096 * pb ≤ S0 := H.hSb

/-- **One call of the allocator's `alloc` wrapper, as the summaries use it**: from 40494 with
    ω₇ = size, ω₈ = align (1 … 32), and the stack pointer sp at least 168 above S0, either:
    - the wrapper reaches its return (40611) with the address `ptr` of a new allocated chunk of
      ⌈size/32⌉ + 1 units, at an address no allocated chunk of s had, the context and the frame
      `Keeps` kept, and ω₀, ω₁, ω₅, ω₆ restored; or
    - it reaches 40611 with null, where the model's `alloc` fails.

    The bound is 540 steps. -/
def AllocOk (p : ByteArray) {X : Type} (R : HostRel X) (env : RefineHost.Env) (pb S0 S1 : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp size al : Nat),
    HeapCtx env pb S0 S1 μ s → ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat size →
    ω[8] = UInt64.ofNat al → 1 ≤ al → al ≤ 32 → size + 31 < 68719476736 → 2147483816 ≤ sp →
    S0 + 168 ≤ sp → sp ≤ S1 →
    (∃ ptr s' ω' μ' x', FreeStepsH p R 40494 ω μ x 40611 ω' μ' x' 540 ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Keeps pb sp (fun _ => False) s μ μ' s' ∧
      (⟨ptr - 32, (size + 31) / 32 + 1, true⟩ : Chunk) ∈ chunks s' ∧
      (∀ d ∈ chunks s, d.used = true → d.addr ≠ ptr - 32) ∧ 32 ≤ ptr ∧
      ω'[7] = UInt64.ofNat ptr ∧ ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (∃ ω' μ' x', FreeStepsH p R 40494 ω μ x 40611 ω' μ' x' 540 ∧ ω'[7] = UInt64.ofNat 0 ∧
      ∃ hb, alloc (growTo pb) hb 1 ((size + 31) / 32) s = none)

/-- **One call of the allocator's `realloc` wrapper, as the summaries use it**: from 40701 with
    ω₇ = ptr, the data address of an allocated chunk c of s (based at an 8-aligned address),
    ω₉ = align (1 … 32), ω₁₀ = size > 0, and the stack pointer sp (8-aligned) at least 320 above S0,
    either:
    - the wrapper reaches its return (40821) with the address `r` of an allocated chunk d of exactly
      ⌈size/32⌉ + 1 units, at c's address or at one no allocated chunk of s had; the context is
      kept with the same base, `Outside` the heap too, and every allocated chunk of s other than c,
      with its data; ω₀, ω₁, ω₅, ω₆ are restored; or
    - it reaches 40821 with null, where the model's `realloc` fails.

    The bound is 64 · (c.size − 1) + 1300 steps. -/
def ReallocOk (p : ByteArray) {X : Type} (R : HostRel X) (env : RefineHost.Env) (pb S0 S1 : Nat) : Prop :=
  ∀ (ω : Regs) (μ : Memory) (x : X) (s : State) (sp ptr al size : Nat) (c : Chunk),
    HeapCtx env pb S0 S1 μ s → s.base % 8 = 0 → c ∈ chunks s → c.used = true → c.addr + 32 = ptr →
    0 < size → size < 536870912 →
    ω[1] = UInt64.ofNat sp → ω[7] = UInt64.ofNat ptr → ω[9] = UInt64.ofNat al →
    ω[10] = UInt64.ofNat size → 1 ≤ al → al ≤ 32 → 2147483968 ≤ sp → sp % 8 = 0 →
    S0 + 320 ≤ sp → sp ≤ S1 →
    (∃ r s' ω' μ' x', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x' (64 * (c.size - 1) + 1300) ∧
      HeapCtx env pb S0 S1 μ' s' ∧ s'.base = s.base ∧ Outside pb sp (fun _ => False) μ μ' ∧
      (∀ d ∈ chunks s, d.used = true → d ≠ c → d ∈ chunks s' ∧ ∀ a, InData d a → μ'.read a = μ.read a) ∧
      (∃ d ∈ chunks s', d.used = true ∧ d.addr + 32 = r ∧ d.size = (size + 31) / 32 + 1 ∧
        (d.addr = c.addr ∨ ∀ e ∈ chunks s, e.used = true → e.addr ≠ d.addr)) ∧
      ω'[7] = UInt64.ofNat r ∧ ω'[0] = ω[0] ∧ ω'[1] = ω[1] ∧ ω'[5] = ω[5] ∧ ω'[6] = ω[6]) ∨
    (∃ ω' μ' x', FreeStepsH p R 40701 ω μ x 40821 ω' μ' x' (64 * (c.size - 1) + 1300) ∧
      ω'[7] = UInt64.ofNat 0 ∧
      ∃ hb, realloc (growTo pb) hb s ptr ((al + 31) / 32) ((size + 31) / 32) = none)

end Services.Bootstrap.Fmt
