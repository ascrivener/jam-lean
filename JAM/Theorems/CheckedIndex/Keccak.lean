import JAM.Keccak
import JAM.Theorems.LoopRel

/-!
# Checked indexing in Keccak: the new definitions equal the old ones

`JAM.Keccak` keeps the state in a `Vector UInt64 25` and indexes it in bounds; `permute` and
`absorb` keep their `Array` interfaces for `JamCrypto`. This file keeps the earlier `Array` form with
`a[i]!` verbatim (`JAM.Theorems.CheckedIndex.Old.Keccak`) and proves each function equal to its new
form; `keccak_sponge256_eq_old` is the sponge. `JAM.Fast.Keccak` proves its fast form equal to the
old one and goes through these.
-/

namespace JAM.Theorems.CheckedIndex
open JAM.Theorems JAM.Theorems.LoopRel
open JAM.Keccak (lanes)

namespace Old.Keccak


/-- Round constants $\mathrm{RC}[i]$ (FIPS 202 §3.2.5). -/
def rc : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets $r[x + 5y]$ (FIPS 202 §3.2.2). -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

@[inline] def rotl (x : UInt64) (n : UInt64) : UInt64 := if n = 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- One round: $\theta$, $\rho$, $\pi$, $\chi$, $\iota$ on the state $A[x + 5y]$. -/
def round (a : Array UInt64) (r : UInt64) : Array UInt64 := Id.run do
  -- θ
  let c : Array UInt64 := (List.range 5).toArray.map fun x =>
    a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  let d : Array UInt64 := (List.range 5).toArray.map fun x => c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
  let a := (List.range 25).toArray.map fun i => a[i]! ^^^ d[i % 5]!
  -- ρ and π: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for x in [0:5] do
    for y in [0:5] do
      b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[x + 5 * y]! rotations[x + 5 * y]!)
  -- χ
  let a := (List.range 25).toArray.map fun i =>
    let x := i % 5
    let y := i / 5
    b[i]! ^^^ ((~~~ b[(x + 1) % 5 + 5 * y]!) &&& b[(x + 2) % 5 + 5 * y]!)
  -- ι
  return a.set! 0 (a[0]! ^^^ r)

/-- Keccak-f[1600]: 24 rounds. -/
def permute (a : Array UInt64) : Array UInt64 := rc.foldl round a

/-- XOR one rate-sized block (as little-endian 64-bit lanes) into the state and permute. -/
def absorb (a : Array UInt64) (block : List UInt8) : Array UInt64 :=
  let lanes := block.length / 8
  let a := (List.range lanes).foldl (fun a i =>
    let w : UInt64 := (List.range 8).foldr (fun k (acc : UInt64) => (acc <<< 8) ||| (block.getD (8 * i + k) 0).toUInt64) 0
    a.set! i (a[i]! ^^^ w)) a
  permute a

/-- The sponge with a 136-octet rate (capacity 512), padding
    `domain` $\frown 0^{\ast} \frown \mathtt{0x80}$, squeezing 32 octets. -/
def sponge256 (domain : UInt8) (msg : ByteArray) : ByteArray :=
  let rate := 136
  let m := msg.toList
  let full := m.length / rate
  let a := (List.range full).foldl (fun a k => absorb a ((m.drop (rate * k)).take rate))
    (Array.replicate 25 (0 : UInt64))
  let rest := m.drop (rate * full)
  let padded := (rest ++ [domain] ++ List.replicate (rate - rest.length - 1) 0).set (rate - 1)
    ((if rest.length = rate - 1 then domain else 0) ||| 0x80)
  let a := absorb a padded
  ⟨((List.range 32).map fun k => (a[k / 8]! >>> (8 * (k % 8)).toUInt64).toUInt8).toArray⟩

end Old.Keccak

private theorem getA (a : Array UInt64) (i : Nat) (hi : i < 25) : a[i]! = (lanes a)[i] := by
  simp [lanes, getElem!_def, Array.getD_eq_getD_getElem?]; rfl

theorem keccak_round_eq_old (a : Array UInt64) (r : UInt64) :
    Old.Keccak.round a r = (JAM.Keccak.round (lanes a) r).toArray := by
  unfold Old.Keccak.round JAM.Keccak.round
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn'_eq_forIn'_range']
  generalize hC : (Array.map (fun x => a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!)
    (List.range 5).toArray) = C
  generalize hCv : (Vector.ofFn fun (x : Fin 5) => (lanes a)[x.1] ^^^ (lanes a)[x.1 + 5] ^^^ (lanes a)[x.1 + 10] ^^^
    (lanes a)[x.1 + 15] ^^^ (lanes a)[x.1 + 20]) = Cv
  have eC : C = Cv.toArray := by
    subst hC hCv; apply Array.ext
    · simp
    · intro i h1 _; simp at h1
      simp [getA _ _ (show i < 25 by omega), getA _ _ (show i + 5 < 25 by omega), getA _ _ (show i + 10 < 25 by omega),
        getA _ _ (show i + 15 < 25 by omega), getA _ _ (show i + 20 < 25 by omega)]
  subst eC
  generalize hD : (Array.map (fun x => Cv.toArray[(x + 4) % 5]! ^^^ Old.Keccak.rotl Cv.toArray[(x + 1) % 5]! 1)
    (List.range 5).toArray) = D
  generalize hDv : (Vector.ofFn fun (x : Fin 5) => Cv[(x.1 + 4) % 5] ^^^ JAM.Keccak.rotl Cv[(x.1 + 1) % 5] 1) = Dv
  have eD : D = Dv.toArray := by
    subst hD hDv; apply Array.ext
    · simp
    · intro i h1 _; simp at h1
      simp [getV _ _ (show (i + 4) % 5 < 5 by omega), getV _ _ (show (i + 1) % 5 < 5 by omega)]; rfl
  subst eD
  generalize hA : (Array.map (fun i => a[i]! ^^^ Dv.toArray[i % 5]!) (List.range 25).toArray) = A
  generalize hAv : (Vector.ofFn fun (i : Fin 25) => (lanes a)[i] ^^^ Dv[i.1 % 5]) = Av
  have eA : A = Av.toArray := by
    subst hA hAv; apply Array.ext
    · simp
    · intro i h1 _; simp at h1
      simp [getA _ _ h1, getV _ _ (show i % 5 < 5 by omega)]
  subst eA
  have hR : ∀ k (hk : k < 25), Old.Keccak.rotations[k]! = JAM.Keccak.rotations[k] := fun k hk => by
    rw [show Old.Keccak.rotations = JAM.Keccak.rotations.toArray from rfl]; exact getV _ _ hk
  refine LoopRel.bind_rel (fun (w : Array UInt64) (v : Vector UInt64 25) => w = v.toArray)
    (fun (w : Array UInt64) (v : Vector UInt64 25) => w = v.toArray) ?_ ?_
  · refine LoopRel.forIn_forIn' (fun (w : Array UInt64) (v : Vector UInt64 25) => w = v.toArray) _ _ _ _ (by simp) ?_
    rintro x hx w v rfl
    refine LoopRel.bind_rel (fun (w : Array UInt64) (v : Vector UInt64 25) => w = v.toArray)
      (LoopRel.StepRel (fun (w : Array UInt64) (v : Vector UInt64 25) => w = v.toArray)) ?_ ?_
    · refine LoopRel.forIn_forIn' (fun (w : Array UInt64) (v : Vector UInt64 25) => w = v.toArray) _ _ _ _ rfl ?_
      rintro y hy w v rfl
      simp at hx hy
      simp only [LoopRel.StepRel, Id.run, pure]
      rw [getV _ _ (show x + 5 * y < 25 by omega), hR _ (show x + 5 * y < 25 by omega),
        setV _ _ (show y + 5 * ((2 * x + 3 * y) % 5) < 25 by omega)]
      rfl
    · rintro w v rfl; rfl
  · rintro w v rfl
    simp only [Id.run, pure]
    generalize hX : (Array.map (fun i => v.toArray[i]! ^^^ ~~~v.toArray[(i % 5 + 1) % 5 + 5 * (i / 5)]! &&&
      v.toArray[(i % 5 + 2) % 5 + 5 * (i / 5)]!) (List.range 25).toArray) = X
    generalize hXv : (Vector.ofFn fun (i : Fin 25) => v[i] ^^^ ~~~v[(i.1 % 5 + 1) % 5 + 5 * (i.1 / 5)] &&&
      v[(i.1 % 5 + 2) % 5 + 5 * (i.1 / 5)]) = Xv
    have eX : X = Xv.toArray := by
      subst hX hXv; apply Array.ext
      · simp
      · intro i h1 _; simp at h1
        simp [getV _ _ h1, getV _ _ (show (i + 1) % 5 + 5 * (i / 5) < 25 by omega),
          getV _ _ (show (i + 2) % 5 + 5 * (i / 5) < 25 by omega)]
    subst eX
    rw [getV _ _ (by decide), setV _ _ (by decide)]

theorem keccak_foldl_round_old (l : List UInt64) (v : Vector UInt64 25) :
    l.foldl Old.Keccak.round v.toArray = (l.foldl JAM.Keccak.round v).toArray := by
  induction l generalizing v with
  | nil => rfl
  | cons r l ih => simp only [List.foldl_cons, keccak_round_eq_old, JAM.Keccak.lanes_toArray, ih]

theorem keccak_permute_eq_old (a : Array UInt64) : Old.Keccak.permute a = JAM.Keccak.permute a := by
  unfold Old.Keccak.permute JAM.Keccak.permute JAM.Keccak.permuteLanes
  rw [show Old.Keccak.rc = JAM.Keccak.rc.toArray from rfl, ← Vector.foldl_toArray, ← Array.foldl_toList, ← Array.foldl_toList]
  obtain ⟨r, l, e⟩ : ∃ r l, JAM.Keccak.rc.toArray.toList = r :: l := ⟨_, _, rfl⟩
  rw [e, List.foldl_cons, List.foldl_cons, keccak_round_eq_old, keccak_foldl_round_old]

theorem keccak_permute_toArray (v : Vector UInt64 25) : JAM.Keccak.permute v.toArray = (JAM.Keccak.permuteLanes v).toArray := by
  rw [JAM.Keccak.permute, JAM.Keccak.lanes_toArray]

theorem keccak_absorb_eq_old (a : Array UInt64) (block : List UInt8) : Old.Keccak.absorb a block = JAM.Keccak.absorb a block := by
  unfold Old.Keccak.absorb JAM.Keccak.absorb
  simp only [keccak_permute_eq_old]
  congr 1
  generalize List.range (block.length / 8) = l
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [← ih]; congr 1
    by_cases h : i < a.size
    · simp [h, getElem!_pos, Array.set!_eq_setIfInBounds, Array.setIfInBounds]
    · simp [h, Array.set!_eq_setIfInBounds, Array.setIfInBounds]

theorem keccak_absorb_toArray (v : Vector UInt64 25) (block : List UInt8) :
    JAM.Keccak.absorb v.toArray block = (JAM.Keccak.absorbLanes v block).toArray := by
  unfold JAM.Keccak.absorb JAM.Keccak.absorbLanes
  simp only
  rw [← keccak_permute_toArray]
  congr 1
  generalize List.range (block.length / 8) = l
  induction l generalizing v with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [← ih]; congr 1
    by_cases h : i < 25
    · simp [h]
    · simp [h]

theorem keccak_sponge256_eq_old (domain : UInt8) (msg : ByteArray) : Old.Keccak.sponge256 domain msg = JAM.Keccak.sponge256 domain msg := by
  unfold Old.Keccak.sponge256 JAM.Keccak.sponge256
  simp only [keccak_absorb_eq_old]
  have hf : ∀ (l : List Nat) (v : Vector UInt64 25),
      l.foldl (fun a k => JAM.Keccak.absorb a ((msg.toList.drop (136 * k)).take 136)) v.toArray
        = (l.foldl (fun a k => JAM.Keccak.absorbLanes a ((msg.toList.drop (136 * k)).take 136)) v).toArray := by
    intro l; induction l with
    | nil => intro v; rfl
    | cons k l ih => intro v; simp only [List.foldl_cons, keccak_absorb_toArray, ih]
  rw [show Array.replicate 25 (0 : UInt64) = (Vector.replicate 25 0).toArray from rfl, hf, keccak_absorb_toArray]
  generalize JAM.Keccak.absorbLanes _ _ = v
  congr 2
  apply List.ext_getElem
  · simp
  · intro k h1 _; simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range, getV _ _ (show k / 8 < 25 by omega)]

end JAM.Theorems.CheckedIndex
