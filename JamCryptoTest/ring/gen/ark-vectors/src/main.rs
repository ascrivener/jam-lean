//! Ring vector generator (ark-vrf 0.1.0, features ring + bandersnatch, as JAM uses it).
//! usage: SRS=path/to/bls12-381-srs-2-11-uncompressed-zcash.bin gen roots > ring-root-ark.txt
//!        SRS=... gen proofs > ring-proof-ark.txt
use ark_vrf::suites::bandersnatch::*;
use ark_vrf::reexports::ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use std::env;

fn srs() -> PcsParams {
    let path = env::var("SRS").unwrap();
    let raw = std::fs::read(path).unwrap();
    PcsParams::deserialize_uncompressed_unchecked(&mut &raw[..]).unwrap()
}

fn points(keys: &[Vec<u8>]) -> Vec<AffinePoint> {
    keys.iter().map(|k| Public::deserialize_compressed(&k[..]).map(|p| p.0)
        .unwrap_or(RingProofParams::padding_point())).collect()
}

fn commit(params: &RingProofParams, keys: &[Vec<u8>]) -> Vec<u8> {
    let vk = params.verifier_key(&points(keys));
    let mut out = vec![];
    vk.commitment().serialize_compressed(&mut out).unwrap();
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let pcs = srs();
    match args[1].as_str() {
        // commit RINGSIZE hexkey...
        "commit" => {
            let rs: usize = args[2].parse().unwrap();
            let params = RingProofParams::from_pcs_params(rs, pcs).unwrap();
            let keys: Vec<Vec<u8>> = args[3..].iter().map(|h| hex::decode(h.trim_start_matches("0x")).unwrap()).collect();
            println!("{}", hex::encode(commit(&params, &keys)));
        }
        // roots: ark-vrf-generated ring roots, one `root ROOT KEY...` line each
        "roots" => roots(pcs),
        // proofs: `proof RINGSIZE ROOT CTX MSG SIG VALID OUT` lines (SIG = output ‖ ring proof)
        "proofs" => proofs(pcs),
        // label: fills VALID and OUT of `proof` lines read from stdin (other lines are copied)
        "label" => label(pcs),
        _ => panic!(),
    }
}

use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

fn enc(p: &AffinePoint) -> Vec<u8> {
    let mut v = vec![];
    p.serialize_compressed(&mut v).unwrap();
    v
}

fn line(size: usize, params: &RingProofParams, keys: &[Vec<u8>]) {
    let ks: Vec<String> = keys.iter().map(|k| hex::encode(k)).collect();
    println!("root {} {} {}", size, hex::encode(commit(params, keys)), ks.join(" "));
}

fn roots(pcs: PcsParams) {
    let mut rng = ChaCha20Rng::from_seed([7u8; 32]);
    let key = |rng: &mut ChaCha20Rng| -> Vec<u8> {
        let mut seed = [0u8; 32];
        rng.fill_bytes(&mut seed);
        enc(&Secret::from_seed(&seed).public().0)
    };
    for &(size, n) in &[(6usize, 6usize), (6, 3), (1023, 1023), (1023, 6), (300, 200)] {
        let params = RingProofParams::from_pcs_params(size, pcs.clone()).unwrap();
        let mut keys: Vec<Vec<u8>> = (0..n).map(|_| key(&mut rng)).collect();
        line(size, &params, &keys);
        // padding: bad encodings, off-curve, non-subgroup (x, -y), y >= r, explicit padding point
        let p0 = Public::deserialize_compressed(&keys[0][..]).unwrap().0;
        let mut nonsub = p0; nonsub.y = -nonsub.y;
        let mut yhigh = vec![0xffu8; 32]; yhigh[31] = 0x7f;
        let mut flagged = keys[1].clone(); flagged[31] ^= 0x80; // the other x: -P, still valid
        let specials: Vec<Vec<u8>> = vec![
            vec![0u8; 32], vec![0xffu8; 32], yhigh, enc(&nonsub), vec![1, 2, 3],
            enc(&RingProofParams::padding_point()), flagged,
            { let mut v = vec![0u8; 32]; v[0] = 2; v },
        ];
        for (i, s) in specials.iter().enumerate() {
            let at = (i * 7 + 1) % n;
            keys[at] = s.clone();
        }
        line(size, &params, &keys);
        if n == 1023 { continue; } // keep the committed vectors small
        // a permutation
        let mut perm = keys.clone();
        perm.reverse();
        perm.swap(0, n / 2);
        line(size, &params, &perm);
    }
}

fn verify_sig(params: &RingProofParams, root: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]) -> bool {
    use ark_vrf::ring::Verifier;
    let Ok(commitment) = RingCommitment::deserialize_compressed(root) else { return false };
    let Some(input) = Input::new(ctx) else { return false };
    if sig.len() < 32 { return false; }
    let Ok(output) = Output::deserialize_compressed(&sig[..32]) else { return false };
    let Ok(proof) = RingProof::deserialize_compressed(&sig[32..]) else { return false };
    let vk = params.verifier_key_from_commitment(commitment);
    let verifier = params.verifier(vk);
    Public::verify(input, output, msg, &proof, &verifier).is_ok()
}

fn proofs(pcs: PcsParams) {
    use ark_vrf::ring::Prover;
    let mut rng = ChaCha20Rng::from_seed([9u8; 32]);
    for &(size, n, idx) in &[(6usize, 6usize, 2usize), (6, 4, 0), (1023, 1023, 700)] {
        let params = RingProofParams::from_pcs_params(size, pcs.clone()).unwrap();
        let secrets: Vec<Secret> = (0..n).map(|_| {
            let mut seed = [0u8; 32];
            rng.fill_bytes(&mut seed);
            Secret::from_seed(&seed)
        }).collect();
        let pks: Vec<AffinePoint> = secrets.iter().map(|s| s.public().0).collect();
        let keys: Vec<Vec<u8>> = pks.iter().map(enc).collect();
        let root = commit(&params, &keys);
        let prover = params.prover(params.prover_key(&pks), idx);
        let mut ctx = b"jam_ticket_seal".to_vec();
        let mut e = [0u8; 33];
        rng.fill_bytes(&mut e);
        ctx.extend_from_slice(&e);
        let msg: Vec<u8> = if n == 4 { b"some aux data".to_vec() } else { vec![] };
        let input = Input::new(&ctx).unwrap();
        let output = secrets[idx].output(input);
        let proof = secrets[idx].prove(input, output, &msg, &prover);
        let mut sig = vec![];
        output.serialize_compressed(&mut sig).unwrap();
        proof.serialize_compressed(&mut sig).unwrap();
        assert_eq!(sig.len(), 784);
        let out = hex::encode(&output.hash()[..32]);
        let emit = |root: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]| {
            let ok = verify_sig(&params, root, ctx, msg, sig);
            println!("proof {} {} {} {} {} {} {}", size, hex::encode(root), hex::encode(ctx),
                if msg.is_empty() { "-".to_string() } else { hex::encode(msg) }, hex::encode(sig), ok as u8, out);
        };
        emit(&root, &ctx, &msg, &sig);
        if size == 1023 { continue; }
        // wrong context, wrong message, wrong ring
        let mut ctx2 = ctx.clone(); ctx2[20] ^= 1;
        emit(&root, &ctx2, &msg, &sig);
        emit(&root, &ctx, b"x", &sig);
        let mut keys2 = keys.clone(); keys2.swap(0, 1);
        emit(&commit(&params, &keys2), &ctx, &msg, &sig);
        // tampered octets in each part of the signature
        for &pos in &[0usize, 40, 100, 140, 180, 200, 300, 450, 470, 600, 700, 740, 760, 783] {
            let mut bad = sig.clone();
            bad[pos] ^= 0x04;
            emit(&root, &ctx, &msg, &bad);
        }
        emit(&root, &ctx, &msg, &sig[..783]);
    }
}

fn label(pcs: PcsParams) {
    use std::io::BufRead;
    let mut ctxs: Vec<(usize, RingProofParams)> = vec![];
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.split_whitespace().collect();
        if f.len() < 6 || f[0] != "proof" { println!("{}", line); continue; }
        let size: usize = f[1].parse().unwrap();
        if !ctxs.iter().any(|(s, _)| *s == size) {
            ctxs.push((size, RingProofParams::from_pcs_params(size, pcs.clone()).unwrap()));
        }
        let params = &ctxs.iter().find(|(s, _)| *s == size).unwrap().1;
        let d = |h: &str| if h == "-" { vec![] } else { hex::decode(h).unwrap() };
        let (root, ctx, msg, sig) = (d(f[2]), d(f[3]), d(f[4]), d(f[5]));
        let ok = verify_sig(params, &root, &ctx, &msg, &sig);
        let out = Output::deserialize_compressed(&sig[..32]).map(|o| hex::encode(&o.hash()[..32])).unwrap_or("-".into());
        println!("proof {} {} {} {} {} {} {}", f[1], f[2], f[3], f[4], f[5], ok as u8, out);
    }
}
