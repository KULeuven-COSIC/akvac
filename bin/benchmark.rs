use std::time::Instant;
use ark_std::rand::{rngs::StdRng, SeedableRng};
use akvac::saga::bbs_saga::*;
use akvac::mkvak::mkvak::*;
use akvac::mkvak::nizks::*; // just in case of direct types
use akvac::saga::bbs_saga;
use ark_serialize::CanonicalSerialize;
use ark_std::UniformRand;

// ---------------------------
// Tunables (can override by env):
//   BENCH_ROUNDS=100
//   BENCH_ATTRS=1,2,4,8
//   BENCH_SEED=42
// ---------------------------
const DEFAULT_ROUNDS: usize = 200;
const DEFAULT_ATTRS: &[usize] = &[4,6,8,10,12];
const DEFAULT_SEED: u64 = 42;

// Utilities to read env (optional)
fn env_or_default_rounds() -> usize {
    std::env::var("BENCH_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_ROUNDS)
}

fn env_or_default_seed() -> u64 {
    std::env::var("BENCH_SEED")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_SEED)
}

fn env_or_default_attrs() -> Vec<usize> {
    // helper: 2^exp as usize with overflow guard
    fn pow2_usize(exp: u32) -> Option<usize> {
        if exp as u32 >= usize::BITS { return None; } // would overflow
        Some(1usize << exp)
    }

    if let Ok(s) = std::env::var("BENCH_ATTRS") {
        // Interpret as exponents (e.g., "0,1,2,3" => n = 1,2,4,8)
        let mut out = Vec::new();
        for tok in s.split(',') {
            let tok = tok.trim();
            if tok.is_empty() { continue; }
            // accept both small and big exponents (u32)
            match tok.parse::<u32>().ok().and_then(pow2_usize) {
                Some(n) => out.push(n),
                None => {
                    eprintln!("WARN: ignoring BENCH_ATTRS token '{tok}' (invalid exponent or overflow)");
                }
            }
        }
        if !out.is_empty() { return out; }
    }
    // defaults are already powers of two
    DEFAULT_ATTRS.to_vec()
}

// ---------- Size helpers ----------
fn ser_len_point(p: &Point) -> usize {
    let mut v = Vec::new();
    p.serialize_compressed(&mut v).unwrap();
    v.len()
}
fn ser_len_scalar(s: &Scalar) -> usize {
    let mut v = Vec::new();
    s.serialize_compressed(&mut v).unwrap();
    v.len()
}
fn ser_len_point_vec(vs: &[Point]) -> usize {
    vs.iter().map(ser_len_point).sum()
}
fn ser_len_scalar_vec(vs: &[Scalar]) -> usize {
    vs.iter().map(ser_len_scalar).sum()
}

#[inline]
fn kib(bytes: usize) -> f64 {
    (bytes as f64) / 1024.0
}
#[inline]
fn fmt_kib(bytes: usize) -> String {
    format!("{:.1} KiB", kib(bytes))
}

// Sizes of artifacts you’ll likely report in a table:
fn size_saga_sig(sig: &Signature) -> usize {
    // A (Point) + e (Scalar) + MacProof { c, s_x, s_y_vec }
    let mut bytes = 0usize;
    bytes += ser_len_point(&sig.A);
    bytes += ser_len_scalar(&sig.e);
    bytes += ser_len_scalar(&sig.proof.c);
    bytes += ser_len_scalar(&sig.proof.s_x);
    bytes += ser_len_scalar_vec(&sig.proof.s_y_vec);
    bytes
}
fn size_saga_present_tuple(pres: &SAGAPres, C_j_vec: &[Point]) -> usize {
    ser_len_point(&pres.C_A) + ser_len_point(&pres.T) + ser_len_point_vec(C_j_vec)
}


fn size_req_nizk(p: &ReqProof) -> usize {
    let mut bytes = 0usize;
    bytes += ser_len_scalar(&p.c);
    bytes += ser_len_scalar(&p.s_s);
    bytes += p.s_attrs.iter().map(ser_len_scalar).sum::<usize>();
    bytes += p.s_xi_prime.iter().map(ser_len_scalar).sum::<usize>();
    bytes += ser_len_scalar(&p.s_bar_x0);
    bytes += ser_len_scalar(&p.s_bar_nu);
    bytes += ser_len_scalar(&p.s_r);
    bytes += ser_len_scalar(&p.s_e);
    bytes += p.s_xi.iter().map(ser_len_scalar).sum::<usize>();
    bytes += ser_len_scalar(&p.s_eta);
    bytes += ser_len_scalar(&p.s_prod);
    bytes += ser_len_scalar(&p.s_prod_prime);
    bytes += ser_len_point(&p.prod_com);
    bytes
}

// generic helper
// #[inline]
// fn ser_len<T: CanonicalSerialize>(x: &T) -> usize {
//     let mut v = Vec::new();
//     x.serialize_compressed(&mut v).unwrap();
//     v.len()
// }

// Helper: serialized length for a slice of Points
fn ser_len_points(xs: &[Point]) -> usize {
    xs.iter().map(|p| ser_len_point(p)).sum()
}

fn size_req(credreq: &CredReq) -> usize {
    // (C_A, T) + C_j_vec + bar_X0 + bar_Z0 + C_attr + ReqProof
    let mut bytes = 0usize;
    bytes += ser_len_point(&credreq.saga_pres.C_A);
    bytes += ser_len_point(&credreq.saga_pres.T);
    bytes += ser_len_point_vec(&credreq.C_j_vec);
    bytes += ser_len_point(&credreq.bar_X0);
    bytes += ser_len_point(&credreq.bar_Z0);
    bytes += ser_len_point(&credreq.C_attr);

    // ReqProof fields
    let p = &credreq.nizk;
    bytes += ser_len_scalar(&p.c);
    bytes += ser_len_scalar(&p.s_s);
    bytes += ser_len_scalar_vec(&p.s_attrs);
    bytes += ser_len_scalar_vec(&p.s_xi_prime);
    bytes += ser_len_scalar(&p.s_bar_x0);
    bytes += ser_len_scalar(&p.s_bar_nu);
    bytes += ser_len_scalar(&p.s_r);
    bytes += ser_len_scalar(&p.s_e);
    bytes += ser_len_scalar_vec(&p.s_xi);
    bytes += ser_len_scalar(&p.s_eta);
    bytes += ser_len_scalar(&p.s_prod);
    bytes += ser_len_scalar(&p.s_prod_prime);
    bytes += ser_len_point(&p.prod_com);
    bytes
}
fn size_blind(blind: &BlindCred) -> usize {
    // bar_U, bar_V, IssProof { c, s_e, s_u, s_prod }
    let mut bytes = 0usize;
    bytes += ser_len_point(&blind.bar_U);
    bytes += ser_len_point(&blind.bar_V);
    bytes += ser_len_scalar(&blind.nizk.c);
    bytes += ser_len_scalar(&blind.nizk.s_e);
    bytes += ser_len_scalar(&blind.nizk.s_u);
    bytes += ser_len_scalar(&blind.nizk.s_prod);
    bytes
}
fn size_credential(cred: &Credential) -> usize {
    // U, V, attrs[]
    ser_len_point(&cred.U) + ser_len_point(&cred.V) //+ ser_len_scalar_vec(&cred.attrs)
}
fn size_presentation(p: &Presentation) -> usize {
    // tilde_U, Z, C_v, C_j_vec + ShowProof { c1,c2, s_tilde_gamma, s_attrs[], s_gamma_js[], s2 }
    let mut bytes = 0usize;
    bytes += ser_len_point(&p.tilde_U);
    bytes += ser_len_point(&p.Z);
    bytes += ser_len_point(&p.C_v);
    bytes += ser_len_point_vec(&p.C_j_vec);
    bytes += ser_len_scalar(&p.nizk.c1);
    bytes += ser_len_scalar(&p.nizk.c2);
    bytes += ser_len_scalar(&p.nizk.s_tilde_gamma);
    bytes += ser_len_scalar_vec(&p.nizk.s_attrs);
    bytes += ser_len_scalar_vec(&p.nizk.s_gamma_js);
    bytes += ser_len_scalar(&p.nizk.s2);
    bytes
}

// ---------- stats helpers ----------
fn mean_std_ms(samples_ns: &[u128]) -> (f64, f64) {
    if samples_ns.is_empty() { return (0.0, 0.0); }
    let n = samples_ns.len() as f64;
    let mean_ns = samples_ns.iter().copied().map(|x| x as f64).sum::<f64>() / n;
    let var_ns = samples_ns.iter()
        .map(|&x| {
            let dx = (x as f64) - mean_ns;
            dx * dx
        })
        .sum::<f64>() / n;
    let std_ns = var_ns.sqrt();
    (mean_ns / 1e6, std_ns / 1e6) // to ms
}

fn rand_attrs(rng: &mut StdRng, n: usize) -> Vec<Scalar> {
    (0..n).map(|_| Scalar::rand(rng)).collect()
}

// ---------- The benchmark proper ----------
fn bench_for_n(n: usize, rounds: usize, seed: u64) -> anyhow::Result<()> {
    // Collect timings
    let mut t_setup = vec![];
    let mut t_issuerkg = vec![];
    let mut t_verifierkg = vec![];
    let mut t_recv1 = vec![];
    let mut t_issue = vec![];
    let mut t_recv2 = vec![];
    let mut t_show = vec![];
    let mut t_verify = vec![];

    // Sizes — accumulate and average
    let mut bytes_tau = 0usize;
    let mut bytes_present_tuple = 0usize; // (C_A,T,C_j_vec)
    let mut bytes_credreq = 0usize;
    let mut bytes_req = 0usize;
    let mut bytes_blind = 0usize;
    let mut bytes_cred = 0usize;
    let mut bytes_pres = 0usize;

    // let mut rng = StdRng::seed_from_u64(seed ^ (n as u64 * 0x9E3779B97F4A7C15));
    // Option A: explicit wrapping_mul (recommended)
    let mix = (n as u64).wrapping_mul(0x9E3779B97F4A7C15);
    let mut rng = StdRng::seed_from_u64(seed ^ mix);

    // Option B: do it in u128 and truncate (equivalent to wrapping)
    let mix = (((n as u128) * 0x9E3779B97F4A7C15u128) as u64);
    let mut rng = StdRng::seed_from_u64(seed ^ mix);

    for _round in 0..rounds {
        // Setup
        let t0 = Instant::now();
        let pp = akvac_setup(&mut rng, n);
        t_setup.push(t0.elapsed().as_nanos());

        // Issuer + Verifier keygen
        let t0 = Instant::now();
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        t_issuerkg.push(t0.elapsed().as_nanos());

        let t0 = Instant::now();
        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        t_verifierkg.push(t0.elapsed().as_nanos());

        // Artifact: tau size (saga MAC)
        let tau_size = size_saga_sig(&vpk.tau);
        bytes_tau += tau_size;

        // Prepare attrs
        let attrs = rand_attrs(&mut rng, n);

        // receive_cred_1
        let t0 = Instant::now();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        t_recv1.push(t0.elapsed().as_nanos());

        // artifact sizes from receive_cred_1:
        // bytes_present_tuple += size_saga_present_tuple(&cred_req.saga_pres, &cred_req.C_j_vec);
        // bytes_req += size_req(&cred_req);

        // size creq
        bytes_credreq += size_req(&cred_req);

        // issue_cred
        let t0 = Instant::now();
        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        t_issue.push(t0.elapsed().as_nanos());

        bytes_blind += size_blind(&blind);

        // receive_cred_2
        let t0 = Instant::now();
        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        t_recv2.push(t0.elapsed().as_nanos());

        bytes_cred += size_credential(&cred);

        // show_cred
        let pres_ctx = b"bench-context";
        let t0 = Instant::now();
        let pres = show_cred(&mut rng, &pp, &ipk, &vpk, &cred, pres_ctx);
        t_show.push(t0.elapsed().as_nanos());

        bytes_pres += size_presentation(&pres);

        // verify
        let t0 = Instant::now();
        let ok = verify_cred_show(&pp, &vsk, &vpk, &pres, pres_ctx);
        t_verify.push(t0.elapsed().as_nanos());
        assert!(ok, "verification failed in benchmark");
    }

// Compute stats
    let (setup_mean, setup_std) = mean_std_ms(&t_setup);
    let (ikg_mean, ikg_std) = mean_std_ms(&t_issuerkg);
    let (vkg_mean, vkg_std) = mean_std_ms(&t_verifierkg);
    let (r1_mean, r1_std)  = mean_std_ms(&t_recv1);
    let (iss_mean, iss_std) = mean_std_ms(&t_issue);
    let (r2_mean, r2_std)  = mean_std_ms(&t_recv2);
    let (show_mean, show_std) = mean_std_ms(&t_show);
    let (ver_mean, ver_std)   = mean_std_ms(&t_verify);

    let r = rounds as f64;
    let avg_tau   = (bytes_tau as f64 / r).round() as usize;
// Option A (if you still have both counters):
//     let avg_credreq = (((bytes_present_tuple + bytes_req) as f64) / r).round() as usize;
// Option B (if you switched to a single counter bytes_credreq):
    let avg_credreq = (bytes_credreq as f64 / r).round() as usize;
    let avg_blind = (bytes_blind as f64 / r).round() as usize;
    let avg_cred  = (bytes_cred  as f64 / r).round() as usize;
    let avg_pres  = (bytes_pres  as f64 / r).round() as usize;

// Print a compact Markdown row (with 'credreq' instead of presTuple/req)
    println!(
        "|   {:>3}    |   {:>7.2} ± {:>5.2} | {:>7.2} ± {:>5.2}   |   {:>7.2} ± {:>5.2}   |  {:>8.2} ± {:>5.2}   |  {:>7.2} ± {:>5.2}  |  {:>8.2} ± {:>5.2} |  {:>7.2} ± {:>5.2}  |  {:>7.2} ± {:>5.2}   |  {:>9}  |  {:>11}  |  {:>9}   |  {:>8}    | {:>8} |",
        n,
        setup_mean, setup_std,
        ikg_mean, ikg_std,
        vkg_mean, vkg_std,
        r1_mean, r1_std,
        iss_mean, iss_std,
        r2_mean, r2_std,
        show_mean, show_std,
        ver_mean, ver_std,
        fmt_kib(avg_tau),
        fmt_kib(avg_credreq),
        fmt_kib(avg_blind),
        fmt_kib(avg_cred),
        fmt_kib(avg_pres),
    );

    Ok(())
}

fn main() -> anyhow::Result<()> {
    let rounds = env_or_default_rounds();
    let seed = env_or_default_seed();
    let ns = env_or_default_attrs();

    println!("# AKVAC Benchmark");
    println!();
    println!("Rounds: {}  |  Seed: {}", rounds, seed);
    println!();
    println!("|   n      | setup [ms]        | issuerkg          |   verifierkg        |          obt_1      |     issue_cred    |          obt_2    |  present (ms)     | verify_show        | tau KiB.    | credreq KiB   | blind KiB    | cred KiB.    | pres KiB |");
    println!("|----------|-------------------|-------------------|---------------------|---------------------|-------------------|-------------------|-------------------|--------------------|-------------|---------------|--------------|--------------|----------|");

    for &n in &ns {
        bench_for_n(n, rounds, seed)?;
    }

    Ok(())
}