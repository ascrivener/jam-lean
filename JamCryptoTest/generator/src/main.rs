//! Generates the JamCrypto test vectors (see JamCryptoTest/vectors/README.md).
//! Usage: gen RFC8032_VECTORS JAM_ED25519_JSON ARK_VRF_IETF_JSON OUT_DIR
//!        gen signing RFC8032_VECTORS RFC8032_SECRETS ARK_VRF_IETF_JSON OUT_DIR
//!        gen verify < LINES
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_vrf::suites::bandersnatch::{AffinePoint, IetfProof, Input, Output, Public, Secret};
use curve25519_dalek::{edwards::CompressedEdwardsY, scalar::Scalar, EdwardsPoint, traits::IsIdentity};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};
use sha2::{Digest, Sha512};
use std::fmt::Write as _;

fn h(b: &[u8]) -> String { if b.is_empty() { "-".into() } else { hex::encode(b) } }
fn unh(s: &str) -> Vec<u8> { if s == "-" { vec![] } else { hex::decode(s).unwrap() } }

/// Reference Ed25519 verification under (canonical points?, cofactored?), built on curve25519-dalek.
fn ed_ref(canonical: bool, cofactored: bool, key: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    if key.len() != 32 || sig.len() != 64 { return false; }
    let dec = |b: &[u8]| -> Option<EdwardsPoint> {
        let c = CompressedEdwardsY(b.try_into().unwrap());
        let p = c.decompress()?;
        if canonical && p.compress().0 != c.0 { return None; }
        Some(p)
    };
    let (Some(a), Some(r)) = (dec(key), dec(&sig[..32])) else { return false };
    let s: Option<Scalar> = Scalar::from_canonical_bytes(sig[32..].try_into().unwrap()).into();
    let Some(s) = s else { return false };
    let mut hs = Sha512::new(); hs.update(&sig[..32]); hs.update(key); hs.update(msg);
    let k = Scalar::from_bytes_mod_order_wide(&hs.finalize().into());
    let lhs = EdwardsPoint::mul_base(&s);
    if cofactored { (lhs - r - k * a).mul_by_cofactor().is_identity() } else { lhs == r + k * a }
}

fn ed_line(out: &mut String, tag: &str, key: &[u8], msg: &[u8], sig: &[u8]) {
    let zip = ed_ref(false, true, key, msg, sig);
    if key.len() == 32 && sig.len() == 64 {
        let vk = ed25519_zebra::VerificationKeyBytes::from(<[u8; 32]>::try_from(key).unwrap());
        let z = ed25519_zebra::VerificationKey::try_from(vk)
            .map(|vk| vk.verify(&ed25519_zebra::Signature::from(<[u8; 64]>::try_from(sig).unwrap()), msg).is_ok())
            .unwrap_or(false);
        assert_eq!(z, zip, "zebra disagrees with the reference: {tag}");
    }
    let b = |x: bool| if x { "1" } else { "0" };
    writeln!(out, "{} {} {} {} {} {} {}", tag, b(zip), b(ed_ref(true, true, key, msg, sig)),
        b(ed_ref(true, false, key, msg, sig)), h(key), h(msg), h(sig)).unwrap();
}

fn bs_verify(key: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    use ark_vrf::ietf::Verifier;
    if key.len() != 32 || sig.len() != 96 { return false; }
    let Ok(pk) = Public::deserialize_compressed(key) else { return false };
    let Ok(o) = Output::deserialize_compressed(&sig[..32]) else { return false };
    let Ok(p) = IetfProof::deserialize_compressed(&sig[32..]) else { return false };
    let Some(i) = Input::new(ctx) else { return false };
    pk.verify(i, o, msg, &p).is_ok()
}

fn bs_out(sig: &[u8]) -> Vec<u8> {
    Output::deserialize_compressed_unchecked(&sig[..32]).map(|o| o.hash()[..32].to_vec()).unwrap_or_default()
}

fn bs_line(out: &mut String, tag: &str, key: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]) {
    let ok = bs_verify(key, ctx, msg, sig);
    let y = if ok { bs_out(sig) } else { vec![] };
    writeln!(out, "{} {} {} {} {} {} {}", tag, if ok { 1 } else { 0 }, h(key), h(ctx), h(msg), h(sig), h(&y)).unwrap();
}

fn enc<T: CanonicalSerialize>(x: &T) -> Vec<u8> { let mut v = vec![]; x.serialize_compressed(&mut v).unwrap(); v }

/// `gen signing RFC8032_VECTORS RFC8032_SECRETS ARK_VRF_IETF_JSON OUT_DIR`: signing vectors
/// (JamCryptoTest/vectors/signing.txt), signatures by ed25519-dalek and ark-vrf 0.1.0.
fn signing(a: &[String]) {
    let mut out = String::new();
    let rfc: Vec<Vec<String>> = std::fs::read_to_string(&a[2]).unwrap().lines()
        .map(|l| l.split(' ').map(String::from).collect()).collect();
    for l in std::fs::read_to_string(&a[3]).unwrap().lines() {
        let f: Vec<&str> = l.split(' ').collect();
        let v = rfc.iter().find(|v| v[0] == f[0]).unwrap();
        let seed: [u8; 32] = unh(f[1]).try_into().unwrap();
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        use ed25519_dalek::Signer;
        let msg = unh(&v[2]);
        let sig = sk.sign(&msg).to_bytes().to_vec();
        assert_eq!(sk.verifying_key().to_bytes().to_vec(), unh(&v[1]));
        assert_eq!(sig, unh(&v[3]));
        writeln!(out, "ed rfc8032-{} {} {} {} {}", f[0], f[1], h(&msg), h(&sig), v[1]).unwrap();
    }
    let mut rng = ChaCha20Rng::from_seed([9; 32]);
    for i in 0..10 {
        let mut seed = [0u8; 32]; rng.fill_bytes(&mut seed);
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let mut msg = vec![0u8; (i * 41) % 300]; rng.fill_bytes(&mut msg);
        use ed25519_dalek::Signer;
        let sig = sk.sign(&msg).to_bytes().to_vec();
        writeln!(out, "ed gen-{i} {} {} {} {}", h(&seed), h(&msg), h(&sig), h(&sk.verifying_key().to_bytes())).unwrap();
    }
    let ark: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&a[4]).unwrap()).unwrap();
    for (n, v) in ark.as_array().unwrap().iter().enumerate() {
        let g = |k: &str| unh(match v[k].as_str().unwrap() { "" => "-", s => s });
        let sig = [g("gamma"), g("proof_c"), g("proof_s")].concat();
        writeln!(out, "bssk ark-vrf-{} {} {} {} {} {}", n + 1, h(&g("sk")), h(&g("alpha")), h(&g("ad")), h(&sig), h(&g("pk"))).unwrap();
    }
    for i in 0..10 {
        use ark_vrf::ietf::Prover;
        let mut seed = vec![0u8; [32, 0, 1, 64][i % 4]]; rng.fill_bytes(&mut seed);
        let sk = Secret::from_seed(&seed);
        let mut ctx = vec![0u8; (i * 13) % 70]; rng.fill_bytes(&mut ctx);
        let mut msg = vec![0u8; (i * 59) % 400]; rng.fill_bytes(&mut msg);
        let input = Input::new(&ctx).unwrap();
        let o = sk.output(input);
        let sig = [enc(&o.0), enc(&sk.prove(input, o, &msg))].concat();
        writeln!(out, "bsseed gen-{i} {} {} {} {} {}", h(&seed), h(&ctx), h(&msg), h(&sig), h(&enc(&sk.public().0))).unwrap();
    }
    std::fs::write(std::path::Path::new(&a[5]).join("signing.txt"), out).unwrap();
}

/// `gen verify < LINES`: checks signatures with ed25519-dalek (strict RFC 8032, `verify_strict`)
/// and ark-vrf 0.1.0. Lines: `ed KEY MSG SIG` or `bs KEY CTX MSG SIG`; prints `ok`/`BAD` per line.
fn verify() {
    use std::io::BufRead;
    let mut bad = 0;
    for l in std::io::stdin().lock().lines() {
        let l = l.unwrap();
        let f: Vec<&str> = l.split(' ').collect();
        let ok = match f[0] {
            "ed" => {
                let key: [u8; 32] = unh(f[1]).try_into().unwrap();
                let sig: [u8; 64] = unh(f[3]).try_into().unwrap();
                ed25519_dalek::VerifyingKey::from_bytes(&key).map(|k|
                    k.verify_strict(&unh(f[2]), &ed25519_dalek::Signature::from_bytes(&sig)).is_ok()).unwrap_or(false)
            }
            "bs" => bs_verify(&unh(f[1]), &unh(f[2]), &unh(f[3]), &unh(f[4])),
            _ => continue,
        };
        if !ok { bad += 1; }
        println!("{} {}", if ok { "ok" } else { "BAD" }, l.chars().take(80).collect::<String>());
    }
    eprintln!("{bad} bad");
    std::process::exit(if bad == 0 { 0 } else { 1 });
}

fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a[1] == "signing" { return signing(&a); }
    if a[1] == "verify" { return verify(); }
    let outdir = std::path::Path::new(&a[4]);
    let mut rng = ChaCha20Rng::from_seed([7; 32]);

    // ---------------- Ed25519 ----------------
    let mut ed = String::new();
    for l in std::fs::read_to_string(&a[1]).unwrap().lines() {
        let f: Vec<&str> = l.split(' ').collect();
        let (key, msg, sig) = (unh(f[1]), unh(f[2]), unh(f[3]));
        assert!(ed_ref(true, false, &key, &msg, &sig));
        ed_line(&mut ed, &format!("rfc8032-{}", f[0]), &key, &msg, &sig);
    }
    let jam: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&a[2]).unwrap()).unwrap();
    for v in jam.as_array().unwrap() {
        let sig = [unh(v["r"].as_str().unwrap()), unh(v["s"].as_str().unwrap())].concat();
        ed_line(&mut ed, &format!("jam-zip215-{}", v["number"]), &unh(v["pk"].as_str().unwrap()),
            &unh(v["msg"].as_str().unwrap()), &sig);
    }
    let l_bytes = { let mut b = [0u8; 32]; b.copy_from_slice(&hex::decode("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010").unwrap()); b };
    for i in 0..12 {
        let mut seed = [0u8; 32]; rng.fill_bytes(&mut seed);
        let sk = ed25519_dalek::SigningKey::from_bytes(&seed);
        let mut msg = vec![0u8; (i * 37) % 300]; rng.fill_bytes(&mut msg);
        let key = sk.verifying_key().to_bytes().to_vec();
        use ed25519_dalek::Signer;
        let sig = sk.sign(&msg).to_bytes().to_vec();
        ed_line(&mut ed, &format!("gen-{i}-valid"), &key, &msg, &sig);
        let flip = |v: &Vec<u8>, bit: usize| { let mut w = v.clone(); w[bit / 8] ^= 1 << (bit % 8); w };
        ed_line(&mut ed, &format!("gen-{i}-flip-r"), &key, &msg, &flip(&sig, (i * 13) % 256));
        ed_line(&mut ed, &format!("gen-{i}-flip-s"), &key, &msg, &flip(&sig, 256 + (i * 17) % 250));
        ed_line(&mut ed, &format!("gen-{i}-flip-key"), &flip(&key, (i * 29) % 255), &msg, &sig);
        if !msg.is_empty() { ed_line(&mut ed, &format!("gen-{i}-flip-msg"), &key, &flip(&msg, 0), &sig); }
        // S + L: the same point equation, a non-canonical scalar
        let mut s = [0u8; 32]; s.copy_from_slice(&sig[32..]);
        let mut carry = 0u16; let mut s2 = [0u8; 32];
        for j in 0..32 { let t = s[j] as u16 + l_bytes[j] as u16 + carry; s2[j] = t as u8; carry = t >> 8; }
        if carry == 0 { ed_line(&mut ed, &format!("gen-{i}-s-plus-l"), &key, &msg, &[&sig[..32], &s2[..]].concat()); }
        // torsion added to R: valid only under the cofactored equation
        let t = curve25519_dalek::constants::EIGHT_TORSION[(i % 7) + 1];
        let r = CompressedEdwardsY(sig[..32].try_into().unwrap()).decompress().unwrap();
        ed_line(&mut ed, &format!("gen-{i}-r-torsion"), &key, &msg, &[&(r + t).compress().0[..], &sig[32..]].concat());
        ed_line(&mut ed, &format!("gen-{i}-short-sig"), &key, &msg, &sig[..63]);
        // signatures made with a torsion component in R, or in A, then signed consistently:
        // valid under the cofactored equation only (for a torsion point of order > 1)
        let mut hsk = Sha512::new(); hsk.update(seed);
        let hd = hsk.finalize();
        let mut ab = [0u8; 32]; ab.copy_from_slice(&hd[..32]);
        ab[0] &= 248; ab[31] &= 127; ab[31] |= 64;
        let a_s = Scalar::from_bytes_mod_order(ab);
        let mut wide = [0u8; 64]; rng.fill_bytes(&mut wide);
        let rn = Scalar::from_bytes_mod_order_wide(&wide);
        for (what, rt, at) in [("tors-r", t, EdwardsPoint::default()), ("tors-a", EdwardsPoint::default(), t), ("tors-ra", t, t)] {
            let rr = (EdwardsPoint::mul_base(&rn) + rt).compress().0;
            let aa = (EdwardsPoint::mul_base(&a_s) + at).compress().0;
            let mut hk = Sha512::new(); hk.update(rr); hk.update(aa); hk.update(&msg);
            let k = Scalar::from_bytes_mod_order_wide(&hk.finalize().into());
            let s = rn + k * a_s;
            ed_line(&mut ed, &format!("gen-{i}-{what}"), &aa, &msg, &[&rr[..], &s.to_bytes()[..]].concat());
        }
    }
    std::fs::write(outdir.join("ed25519.txt"), ed).unwrap();

    // ---------------- Bandersnatch IETF VRF ----------------
    let mut bs = String::new();
    let ark: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&a[3]).unwrap()).unwrap();
    for (n, v) in ark.as_array().unwrap().iter().enumerate() {
        let g = |k: &str| unh(match v[k].as_str().unwrap() { "" => "-", s => s });
        assert!(g("salt").is_empty());
        let sig = [g("gamma"), g("proof_c"), g("proof_s")].concat();
        assert!(bs_verify(&g("pk"), &g("alpha"), &g("ad"), &sig));
        assert_eq!(bs_out(&sig), g("beta")[..32].to_vec());
        bs_line(&mut bs, &format!("ark-vrf-{}", n + 1), &g("pk"), &g("alpha"), &g("ad"), &sig);
    }
    let r_bytes = hex::decode("e1e77628b506fd7471041974008f8fff0076680202760ecc525f67cad4697bfc1c").unwrap();
    let r_le: Vec<u8> = { let mut x = hex::decode("1cfb69d4ca675f520cce760202687600ff8f87007419047174fd06b52876e7e1").unwrap(); x.reverse(); x };
    let _ = r_bytes;
    let add_le = |a: &[u8], b: &[u8]| -> Option<Vec<u8>> {
        let mut c = 0u16; let mut o = vec![0u8; 32];
        for j in 0..32 { let t = a[j] as u16 + b[j] as u16 + c; o[j] = t as u8; c = t >> 8; }
        if c == 0 { Some(o) } else { None }
    };
    // q (base field order) little-endian, for non-canonical y encodings
    let q_le: Vec<u8> = { let mut x = hex::decode("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001").unwrap(); x.reverse(); x };
    let two_torsion = AffinePoint::new_unchecked(0u64.into(), -ark_ff::Fp::from(1u64));
    for i in 0..10 {
        use ark_vrf::ietf::Prover;
        use ark_ec::{AffineRepr, CurveGroup};
        let mut seed = [0u8; 32]; rng.fill_bytes(&mut seed);
        let sk = Secret::from_seed(&seed);
        let key = enc(&sk.public().0);
        let mut ctx = vec![0u8; (i * 11) % 70]; rng.fill_bytes(&mut ctx);
        let mut msg = vec![0u8; (i * 53) % 400]; rng.fill_bytes(&mut msg);
        let input = Input::new(&ctx).unwrap();
        let out = sk.output(input);
        let proof = sk.prove(input, out, &msg);
        let sig = [enc(&out.0), enc(&proof)].concat();
        bs_line(&mut bs, &format!("gen-{i}-valid"), &key, &ctx, &msg, &sig);
        let flip = |v: &Vec<u8>, bit: usize| { let mut w = v.clone(); w[bit / 8] ^= 1 << (bit % 8); w };
        bs_line(&mut bs, &format!("gen-{i}-flip-out"), &key, &ctx, &msg, &flip(&sig, (i * 7) % 255));
        bs_line(&mut bs, &format!("gen-{i}-flip-c"), &key, &ctx, &msg, &flip(&sig, 256 + (i * 19) % 250));
        bs_line(&mut bs, &format!("gen-{i}-flip-s"), &key, &ctx, &msg, &flip(&sig, 512 + (i * 23) % 250));
        bs_line(&mut bs, &format!("gen-{i}-flip-key"), &flip(&key, (i * 31) % 255), &ctx, &msg, &sig);
        bs_line(&mut bs, &format!("gen-{i}-other-ctx"), &key, &[ctx.clone(), vec![i as u8]].concat(), &msg, &sig);
        bs_line(&mut bs, &format!("gen-{i}-other-msg"), &key, &ctx, &[msg.clone(), vec![0]].concat(), &sig);
        if let Some(c2) = add_le(&sig[32..64], &r_le) {
            bs_line(&mut bs, &format!("gen-{i}-c-plus-r"), &key, &ctx, &msg, &[&sig[..32], &c2[..], &sig[64..]].concat());
        }
        let s2 = add_le(&sig[64..96], &r_le).unwrap();
        bs_line(&mut bs, &format!("gen-{i}-s-plus-r"), &key, &ctx, &msg, &[&sig[..64], &s2[..]].concat());
        // key and output outside the prime subgroup (plus the 2-torsion point (0, -1))
        let key_t = enc(&(sk.public().0 + two_torsion).into_affine());
        bs_line(&mut bs, &format!("gen-{i}-key-torsion"), &key_t, &ctx, &msg, &sig);
        let out_t = enc(&(out.0 + two_torsion).into_affine());
        bs_line(&mut bs, &format!("gen-{i}-out-torsion"), &key, &ctx, &msg, &[&out_t[..], &sig[32..]].concat());
        // non-canonical y (y + q) for the key, keeping the sign bit
        let mut y = key.clone(); let sign = y[31] & 0x80; y[31] &= 0x7f;
        if let Some(mut y2) = add_le(&y, &q_le) { if y2[31] & 0x80 == 0 { y2[31] |= sign;
            bs_line(&mut bs, &format!("gen-{i}-key-y-plus-q"), &y2, &ctx, &msg, &sig); } }
        let _ = AffinePoint::generator();
        bs_line(&mut bs, &format!("gen-{i}-short-sig"), &key, &ctx, &msg, &sig[..95]);
    }
    std::fs::write(outdir.join("bandersnatch_ietf.txt"), bs).unwrap();
}
