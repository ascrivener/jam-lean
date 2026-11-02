/-!
# Keccak-256 (GP v0.8.0 §3.8: ℋ_K, used for the accumulation output root and BEEFY)

The Keccak-f[1600] permutation and sponge (FIPS 202 §3, §4), in pure Lean. `keccak256` uses the
original Keccak padding (domain byte 0x01) that the Gray Paper's ℋ_K means; `sha3_256` uses the
FIPS 202 padding (0x06) and is provided so the permutation can be tested against standard SHA3
implementations.
-/

namespace JAM.Keccak

/-- Round constants RC[i] (FIPS 202 §3.2.5). -/
def rc : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets r[x + 5y] (FIPS 202 §3.2.2). -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

@[inline] def rotl (x : UInt64) (n : UInt64) : UInt64 := if n = 0 then x else (x <<< n) ||| (x >>> (64 - n))

/-- One round: θ, ρ, π, χ, ι on the state A[x + 5y]. -/
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

/-- The sponge with a 136-octet rate (capacity 512), padding `domain` ⌢ 0* ⌢ 0x80, squeezing 32
    octets. -/
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

/-- ℋ_K: Keccak-256 with the original Keccak padding. -/
def keccak256 (msg : ByteArray) : ByteArray := sponge256 0x01 msg

/-- SHA3-256 (FIPS 202), the same permutation with FIPS padding; used to test the permutation. -/
def sha3_256 (msg : ByteArray) : ByteArray := sponge256 0x06 msg

end JAM.Keccak
