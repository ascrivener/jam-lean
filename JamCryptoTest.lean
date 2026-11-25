import JamCrypto

/-!
# `lake exe cryptotest [DIR]`: the JamCrypto test vectors

Runs every vector of `DIR/ed25519.txt`, `DIR/bandersnatch_ietf.txt`, `DIR/bandersnatch_thin.txt`
and `DIR/signing.txt` (default
`JamCryptoTest/vectors`, see its README) and exits non-zero on a mismatch. Prints the time per
verification.
-/

open JamCrypto JamCrypto.Modular

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def unhex (s : String) : List UInt8 :=
  if s == "-" then [] else
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i =>
    UInt8.ofNat (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)

def toHex (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let h := Nat.toDigits 16 b.toNat
    String.ofList (if h.length == 1 then '0' :: h else h))

def check (name : String) (ok : Bool) (failures : IO.Ref Nat) : IO Unit := do
  unless ok do
    IO.eprintln s!"MISMATCH {name}"
    failures.modify (· + 1)

def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  return (a, t1 - t0)

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "JamCryptoTest/vectors"
  let failures ← IO.mkRef 0
  -- fixed points of the suites
  check "bandersnatch generator encoding"
    (toHex (Bandersnatch.encode Bandersnatch.G)
      == "664197ccb667315e6064e4ee81ad8c3586d5dcba508b7d150f3e12da9e666c2a") failures
  check "bandersnatch hash-to-curve of the empty input (ark-vrf vector 1, h)"
    ((Bandersnatch.hashToCurve []).map Bandersnatch.encode
      == some (unhex "c5eaf38334836d4b10e05d2c1021959a917e08eaf4eb46a8c4c8d1bec04e2c00")) failures
  check "bandersnatch hash-to-curve of 0a (ark-vrf vector 2, h)"
    ((Bandersnatch.hashToCurve [0x0a]).map Bandersnatch.encode
      == some (unhex "8c1d1425374f01d86b23bfeab770c60b58d2eeb9afc5900c8b8a918d09a6086b")) failures
  -- Ed25519: tag zip215 rfc8032Strict rfc8032Cofactorless key msg sig
  let mut edN := 0
  let mut edT := 0
  for line in (← IO.FS.lines s!"{dir}/ed25519.txt") do
    match line.splitOn " " with
    | [tag, z, s, c, key, msg, sig] =>
      let (key, msg, sig) := (unhex key, unhex msg, unhex sig)
      let (rz, t) ← timed fun _ => Ed25519.verify key msg sig
      if z == "1" then
        edN := edN + 1
        edT := edT + t
      check s!"ed25519 {tag} zip215" (rz == (z == "1")) failures
      check s!"ed25519 {tag} rfc8032Strict"
        (Ed25519.verifyWith Ed25519.rfc8032Strict key msg sig == (s == "1")) failures
      check s!"ed25519 {tag} rfc8032Cofactorless"
        (Ed25519.verifyWith Ed25519.rfc8032Cofactorless key msg sig == (c == "1")) failures
    | _ => if line != "" then check s!"ed25519 malformed line: {line}" false failures
  -- Bandersnatch IETF VRF: tag valid key ctx msg sig Y
  let mut bsN := 0
  let mut bsT := 0
  for line in (← IO.FS.lines s!"{dir}/bandersnatch_ietf.txt") do
    match line.splitOn " " with
    | [tag, v, key, ctx, msg, sig, y] =>
      let (key, ctx, msg, sig) := (unhex key, unhex ctx, unhex msg, unhex sig)
      let (ok, t) ← timed fun _ => Bandersnatch.ietfVerify key ctx msg sig
      if v == "1" then
        bsN := bsN + 1
        bsT := bsT + t
      check s!"bandersnatch {tag} verify" (ok == (v == "1")) failures
      if ok then
        check s!"bandersnatch {tag} Y" (Bandersnatch.vrfOutput sig == unhex y) failures
        check s!"bandersnatch {tag} Y = JAM.Sha512.vrfOutput"
          (Bandersnatch.vrfOutput sig == JAM.Sha512.vrfOutput sig) failures
    | _ => if line != "" then check s!"bandersnatch malformed line: {line}" false failures
  -- Signing (signing.txt): our signature must equal ed25519-dalek's / ark-vrf's byte for byte, and
  -- verify with our verifiers.
  let mut sgN := 0
  let mut sgT := 0
  for line in (← IO.FS.lines s!"{dir}/signing.txt") do
    match line.splitOn " " with
    | ["ed", tag, seed, msg, sig, key] =>
      let (seed, msg, sig, key) := (unhex seed, unhex msg, unhex sig, unhex key)
      let (mine, t) ← timed fun _ => Ed25519.sign seed msg
      sgN := sgN + 1; sgT := sgT + t
      check s!"ed25519 sign {tag} key" (Ed25519.publicKey seed == key) failures
      check s!"ed25519 sign {tag} = dalek" (mine == sig) failures
      check s!"ed25519 sign {tag} verifies (all rules)"
        (Ed25519.verify key msg mine && Ed25519.verifyWith Ed25519.rfc8032Cofactorless key msg mine) failures
    | [kind, tag, secret, ctx, msg, sig, key] =>
      if kind != "bssk" && kind != "bsseed" then check s!"signing malformed line: {line}" false failures
      let x := if kind == "bssk" then leToNat (unhex secret) else Bandersnatch.secretOfSeed (unhex secret)
      let (ctx, msg, sig, key) := (unhex ctx, unhex msg, unhex sig, unhex key)
      let (mine, t) ← timed fun _ => Bandersnatch.ietfSign x ctx msg
      sgN := sgN + 1; sgT := sgT + t
      check s!"bandersnatch sign {tag} key" (Bandersnatch.publicKey x == key) failures
      check s!"bandersnatch sign {tag} = ark-vrf" (mine == some sig) failures
      check s!"bandersnatch sign {tag} verifies" (Bandersnatch.ietfVerify key ctx msg sig) failures
      check s!"bandersnatch sign {tag} output" (Bandersnatch.ietfOutput x ctx == some (Bandersnatch.vrfOutput sig)) failures
    | _ => if line != "" then check s!"signing malformed line: {line}" false failures
  -- Bandersnatch Thin VRF (GP v0.8.1): the spec's Draft 35 vectors,
  -- tag sk pk alpha ad h gamma beta proof_r proof_s; sig = gamma ⌢ proof_r ⌢ proof_s.
  let mut thN := 0
  let mut thT := 0
  for line in (← IO.FS.lines s!"{dir}/bandersnatch_thin.txt") do
    match line.splitOn " " with
    | [tag, sk, pk, alpha, ad, h, gamma, beta, pr, ps] =>
      let x := leToNat (unhex sk)
      let (pk, alpha, ad, beta) := (unhex pk, unhex alpha, unhex ad, unhex beta)
      let sig := unhex gamma ++ unhex pr ++ unhex ps
      let T := Bandersnatch.Thin.verify
      check s!"thin {tag} pk" (Bandersnatch.Thin.publicKey x == pk) failures
      check s!"thin {tag} h" ((Bandersnatch.Thin.hashToCurve alpha).map Bandersnatch.encode == some (unhex h)) failures
      check s!"thin {tag} gamma" ((Bandersnatch.Thin.hashToCurve alpha).map
        (fun I => Bandersnatch.encode (Bandersnatch.curve.smul x I)) == some (unhex gamma)) failures
      check s!"thin {tag} beta" (Bandersnatch.Thin.vrfOutput sig == beta) failures
      check s!"thin {tag} signOutput" (Bandersnatch.Thin.signOutput x alpha == some beta) failures
      check s!"thin {tag} prove" (Bandersnatch.Thin.sign x alpha ad == some sig) failures
      let (ok, t) ← timed fun _ => T pk alpha ad sig
      thN := thN + 1; thT := thT + t
      check s!"thin {tag} verify" ok failures
      let c081 := withSignatures { edVerify := fun _ _ _ => false } (gp := .v081)
      let c080 := withSignatures { edVerify := fun _ _ _ => false }
      check s!"thin {tag} selected by GpVersion.v081"
        (c081.bsVerify pk alpha ad sig && c081.bsOut sig == beta && !c080.bsVerify pk alpha ad sig) failures
      -- mutations, all rejected
      let flip (i : Nat) := sig.set i (sig[i]! ^^^ 1)
      check s!"thin {tag} flipped O rejected" (!T pk alpha ad (flip 0)) failures
      check s!"thin {tag} flipped R rejected" (!T pk alpha ad (flip 32)) failures
      check s!"thin {tag} flipped s rejected" (!T pk alpha ad (flip 64)) failures
      check s!"thin {tag} s + r rejected" (!T pk alpha ad
        (sig.take 64 ++ natToLE 32 (leToNat (sig.drop 64) + Bandersnatch.r))) failures
      check s!"thin {tag} other ad rejected" (!T pk alpha (ad ++ [0]) sig) failures
      check s!"thin {tag} other input rejected" (!T pk (alpha ++ [0]) ad sig) failures
      check s!"thin {tag} other key rejected" (!T (Bandersnatch.Thin.publicKey (x + 1)) alpha ad sig) failures
      check s!"thin {tag} 95 octets rejected" (!T pk alpha ad (sig.take 95)) failures
      check s!"thin {tag} IETF verifier rejects it" (!Bandersnatch.ietfVerify pk alpha ad sig) failures
    | _ => if line != "" then check s!"thin malformed line: {line}" false failures
  -- Bandersnatch Pedersen VRF (GP v0.8.1 ring VRF component): the spec's Draft 35 vectors,
  -- tag sk pk alpha ad h gamma beta blinding pk_com r ok s sb.
  for line in (← IO.FS.lines s!"{dir}/bandersnatch_pedersen.txt") do
    match line.splitOn " " with
    | [tag, sk, _pk, alpha, ad, h, gamma, beta, bl, com, pr, pok, ps, psb] =>
      let x := leToNat (unhex sk)
      let (alpha, ad) := (unhex alpha, unhex ad)
      let proof := unhex com ++ unhex pr ++ unhex pok ++ unhex ps ++ unhex psb
      match Bandersnatch.Thin.hashToCurve alpha, Bandersnatch.decode (unhex gamma),
          Bandersnatch.Pedersen.Proof.decode proof with
      | some I, some O, some p =>
        check s!"pedersen {tag} h" (Bandersnatch.encode I == unhex h) failures
        let (mine, b) := Bandersnatch.Pedersen.prove x I ad
        check s!"pedersen {tag} blinding" (natToLE 32 b == unhex bl) failures
        check s!"pedersen {tag} prove" (mine.encode == proof) failures
        check s!"pedersen {tag} verify" (Bandersnatch.Pedersen.verify I O ad p) failures
        check s!"pedersen {tag} beta" (Bandersnatch.Thin.output O == unhex beta) failures
        check s!"pedersen {tag} other ad rejected" (!Bandersnatch.Pedersen.verify I O (ad ++ [0]) p) failures
        check s!"pedersen {tag} other s rejected"
          (!Bandersnatch.Pedersen.verify I O ad { p with s := (p.s + 1) % Bandersnatch.r }) failures
      | _, _, _ => check s!"pedersen {tag} decodes" false failures
    | _ => if line != "" then check s!"pedersen malformed line: {line}" false failures
  -- Draft 35's fixed points are hash_to_curve of their names
  let h2c (s : String) := (Bandersnatch.Thin.hashToCurve s.toUTF8.toList).map Bandersnatch.curve.toAffine
  check "d35 blinding base = h2c(pedersen-blinding)"
    (h2c "pedersen-blinding" == some (Bandersnatch.curve.toAffine Bandersnatch.Pedersen.blindingBase)) failures
  check "d35 accumulator = h2c(ring-accumulator)"
    (h2c "ring-accumulator" == some (Ring.Curve.accumulatorBase081.x, Ring.Curve.accumulatorBase081.y)) failures
  check "d35 padding = h2c(ring-padding)"
    (h2c "ring-padding" == some (Ring.Curve.padding081.x, Ring.Curve.padding081.y)) failures
  check "d35 blinding base (ring copy)"
    (h2c "pedersen-blinding" == some (Ring.Curve.blindingBase081.x, Ring.Curve.blindingBase081.y)) failures
  -- JIP-5 development keys = the genesis validators of the fuzzer's 0.8.0 sessions
  -- (jam-fuzzing fuzz-proto/examples/0.8.0/no_forks, Initialize, epoch mark).
  let genesis := [
    ("ff71c6c03ff88adb5ed52c9681de1629a54e702fc14729f6b50d2f0a76f185b3", "4418fb8c85bb3985394a8c2756d3643457ce614546202a2f50b093d762499ace"),
    ("dee6d555b82024f1ccf8a1e37e60fa60fd40b1958c4bb3006af78647950e1b91", "ad93247bd01307550ec7acd757ce6fb805fcf73db364063265b30a949e90d933"),
    ("9326edb21e5541717fde24ec085000b28709847b8aab1ac51f84e94b37ca1b66", "cab2b9ff25c2410fbe9b8a717abb298c716a03983c98ceb4def2087500b8e341"),
    ("0746846d17469fb2f95ef365efcab9f4e22fa1feb53111c995376be8019981cc", "f30aa5444688b3cab47697b37d5cac5707bb3289e986b19b17db437206931a8d"),
    ("151e5c8fe2b9d8a606966a79edd2f9e5db47e83947ce368ccba53bf6ba20a40b", "8b8c5d436f92ecf605421e873a99ec528761eb52a88a2f9a057b3b3003e6f32a"),
    ("2105650944fcd101621fd5bb3124c9fd191d114b7ad936c1d79d734f9f21392e", "ab0084d01534b31c1dd87c81645fd762482a90027754041ca1b56133d0466c06")]
  for (i, (bs, ed)) in (List.range 6).zip genesis do
    let k := DevKeys.dev i
    check s!"JIP-5 dev key {i}" (toHex k.bs == bs && toHex k.ed == ed) failures
  IO.println s!"signing: {sgT / 1000 / max sgN 1} µs per signature"
  IO.println s!"ed25519: {edT / 1000 / max edN 1} µs per valid signature (ZIP 215)"
  IO.println s!"bandersnatch ietf: {bsT / 1000 / max bsN 1} µs per valid signature"
  IO.println s!"bandersnatch thin: {thT / 1000 / max thN 1} µs per valid signature"
  let f ← failures.get
  if f == 0 then
    IO.println "all vectors pass"
    return 0
  else
    IO.eprintln s!"{f} mismatches"
    return 1
