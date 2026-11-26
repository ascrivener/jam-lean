import JAM.Blake2b
import JAM.Keccak
import JAM.Trie

/-! Benchmark: Blake2b-256 and Keccak-256 throughput on 4 KB and 144 KB messages. -/

open JAM

def mkMsg (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for i in [0:n] do b := b.push (UInt8.ofNat ((7 * i + 3) % 256))
  return b

def timeIt (label : String) (bytes reps : Nat) (f : Unit → ByteArray) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : UInt8 := 0
  for _ in [0:reps] do
    let r := f ()
    acc := acc ^^^ r[0]!
  let t1 ← IO.monoNanosNow
  let ns := (t1 - t0).toFloat / reps.toFloat
  let mbs := bytes.toFloat * 1000.0 / ns
  IO.println s!"{label}: {ns / 1000.0} µs/hash, {mbs} MB/s (acc {acc})"

/-- A dictionary shaped like a tiny-chain state: `nk` keys of 31 octets, values of mixed sizes
    totalling about `total` octets (a few large ones, many small). -/
def mkDict (nk total : Nat) : OctetDict := Id.run do
  let mut d : OctetDict := {}
  for i in [0:nk] do
    let key := (List.range 31).map fun j => UInt8.ofNat ((i * 131 + j * 17 + (i * j) % 7) % 256)
    let sz := if i % 40 == 0 then total / (nk / 40 + 1) else (i * 13) % 70
    d := d.insert key ((List.range sz).map fun j => UInt8.ofNat ((i + j) % 256))
  return d

def timeRoot (label : String) (d : OctetDict) (reps : Nat) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut acc : UInt8 := 0
  for i in [0:reps] do
    let r := Trie.root (d.insert [UInt8.ofNat i] [])
    acc := acc ^^^ r[0]!
  let t1 ← IO.monoNanosNow
  IO.println s!"{label}: {(t1 - t0).toFloat / reps.toFloat / 1000000.0} ms/root (acc {acc})"

def main (args : List String) : IO Unit := do
  let d := mkDict 300 147456
  let bytes := d.foldl (fun n _ v => n + v.length) 0
  timeRoot s!"Trie.root, {d.size} keys, {bytes} value octets" d 20
  let reps := (args.head? >>= String.toNat?).getD 200
  for n in [64, 4096, 147456] do
    let m := mkMsg n
    let r := if n > 10000 then max 1 (reps / 20) else reps
    timeIt s!"blake2b-256 {n} B" n r fun _ => Blake2b.hash256 (m.push (UInt8.ofNat r))
    timeIt s!"keccak-256 {n} B" n r fun _ => Keccak.keccak256 (m.push (UInt8.ofNat r))
