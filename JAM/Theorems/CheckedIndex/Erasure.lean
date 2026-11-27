import JAM.Erasure

/-!
# Checked indexing in the erasure code: the new definitions equal the old ones

`JAM.Erasure` reads its tables and arrays with `getD … 0` instead of `a[i]!`: every index is a
field element below 2¹⁶, an octet offset or a position inside an array of known size, but its type
is `ℕ`. The reads that never use the default are proved in bounds in `ErasureProofs.Interp`
(section "Reads in bounds"). Each changed definition is stated equal here to its earlier body,
written out verbatim.
-/

namespace JAM.Erasure

namespace GF

theorem logTable_eq_old :
    logTable = ( Id.run do
  let mut t : Array Nat := Array.replicate 65536 0
  for i in [0:65535] do
    t := t.set! expTable[i]! i
  return t) := by
  unfold logTable; simp only [Array.getElem!_eq_getD]; rfl

theorem mul_eq_old (a b : Nat) :
    mul a b = (if a = 0 ∨ b = 0 then 0 else expTable[(logTable[a]! + logTable[b]!) % 65535]!) := by
  unfold mul; simp only [Array.getElem!_eq_getD]; rfl

theorem inv_eq_old (a : Nat) :
    inv a = (expTable[(65535 - logTable[a]!) % 65535]!) := by
  unfold inv; simp only [Array.getElem!_eq_getD]; rfl

theorem toFieldTable_eq_old :
    toFieldTable = ( (Array.range 65536).map fun m =>
  (List.range 16).foldl (fun acc j => if m.testBit j then acc ^^^ cantor[j]! else acc) 0) := by
  unfold toFieldTable; simp only [Array.getElem!_eq_getD]; rfl

theorem ofFieldTable_eq_old :
    ofFieldTable = ( Id.run do
  let mut t : Array Nat := Array.replicate 65536 0
  for m in [0:65536] do
    t := t.set! toFieldTable[m]! m
  return t) := by
  unfold ofFieldTable; simp only [Array.getElem!_eq_getD]; rfl

theorem cantorIsBasis_eq_old :
    cantorIsBasis = ((List.range 65536).all fun m => ofFieldTable[toFieldTable[m]!]! == m) := by
  unfold cantorIsBasis; simp only [Array.getElem!_eq_getD]; rfl

end GF

theorem toField_eq_old (m : Nat) :
    toField m = (GF.toFieldTable[m % 65536]!) := by
  unfold toField; simp only [Array.getElem!_eq_getD]; rfl

theorem ofField_eq_old (x : Nat) :
    ofField x = (GF.ofFieldTable[x % 65536]!) := by
  unfold ofField; simp only [Array.getElem!_eq_getD]; rfl

theorem lagrange_eq_old (src tgt : List Nat) :
    lagrange src tgt = (
  let xs := (src.map toField).toArray
  let w := xs.mapIdx fun s xsv =>
    GF.inv (xs.foldl (init := (1, 0)) (fun (acc, r) xr =>
      (if r = s then acc else GF.mul acc (GF.add xsv xr), r + 1))).1
  (tgt.map fun t =>
    let x := toField t
    match xs.findIdx? (· == x) with
    | some s => (Array.range xs.size).map fun r => if r = s then 1 else 0
    | none =>
      let l := xs.foldl (fun acc xr => GF.mul acc (GF.add x xr)) 1
      (Array.range xs.size).map fun s => GF.mul l (GF.mul w[s]! (GF.inv (GF.add x xs[s]!)))).toArray) := by
  unfold lagrange; simp only [Array.getElem!_eq_getD]; rfl

theorem interpolate_eq_old (m : Array (Array Nat)) (words : Array Nat) :
    interpolate m words = (
  let ys := words.map toField
  m.map fun row => ofField ((List.range row.size).foldl (fun acc s => GF.add acc (GF.mul row[s]! ys[s]!)) 0)) := by
  unfold interpolate; simp only [Array.getElem!_eq_getD]; rfl

theorem word_eq_old (b : ByteArray) (o : Nat) :
    word b o = ((b.get! o).toNat + 256 * (b.get! (o + 1)).toNat) := by
  unfold word; simp only [Array.getElem!_eq_getD, ByteArray.get!]; rfl

theorem encodeWith_eq_old (d : Nat) (m : Array (Array Nat)) (data : ByteArray) :
    encodeWith d m data = (
  if d = 0 ∨ data.size % (2 * d) ≠ 0 then none
  else
    let k := data.size / (2 * d)
    let pieces := (List.range k).map fun p =>
      interpolate m ((Array.range (paddedShards d)).map fun j =>
        if j < d then word data (2 * k * j + 2 * p) else 0)
    some ((List.range m.size).map fun i => ⟨(pieces.flatMap fun c => wordOctets c[i]!).toArray⟩)) := by
  unfold encodeWith; simp only [Array.getElem!_eq_getD]; rfl

theorem recover_eq_old (v : Nat) (c : List (ByteArray × Nat)) :
    recover v c = (
  let d := originalShards v
  let n := paddedShards d
  let idx := c.map (·.2)
  match c with
  | [] => none
  | (x₀, _) :: _ =>
    let len := x₀.size
    if c.length ≠ d ∨ idx.eraseDups.length ≠ d ∨ idx.any (· ≥ v) ∨ len % 2 ≠ 0 ∨
        c.any (·.1.size ≠ len) then none
    else
      let k := len / 2
      let m := lagrange (idx.map (codeIndex d) ++ (List.range (n - d)).map (d + ·)) (List.range d)
      let pieces := (List.range k).map fun p =>
        interpolate m ((c.map fun (x, _) => word x (2 * p)).toArray ++ Array.replicate (n - d) 0)
      -- chunk j of the data is word j of every piece
      some ⟨((List.range d).flatMap fun j => pieces.flatMap fun ws => wordOctets ws[j]!).toArray⟩) := by
  unfold recover; simp only [Array.getElem!_eq_getD]; rfl

end JAM.Erasure
