use ark_std::rand::{rngs::StdRng, SeedableRng};
use akvac::vka::bbs_vka::*;

fn main() -> anyhow::Result<()> {
    let mut rng = StdRng::seed_from_u64(42);
    let l = 3;

    // 1) Setup
    let params = vka_setup(&mut rng, l);

    // 2) Keygen
    let (sk, pk) = vka_keygen(&mut rng, &params);

    // 3) Messages as points (toy example: hash-free demo using multiples of G)
    let messages: Vec<Point> = (1..=l)
        .map(|i| {
            let s = Scalar::from(i as u64);
            smul(&params.G, &s)
        })
        .collect();

    // 4) Sign
    let tau = vka_mac(&mut rng, &sk, &params, &messages)?;

    // 5) Present
    let pres = vka_present(&mut rng, &pk, &params, &tau, &messages)?;

    // 6) Holder predicate check
    let ok_pred = vka_predicate(
        &pk,
        &params,
        &pres.vka_pres,
        &pres.witness_r,
        &pres.witness_e,
        &pres.xi_vec,
    )?;
    assert!(ok_pred, "predicate failed");

    // 7) Issuer verification (MAC verify on randomized commitments)
    let ok = vka_verify(&sk, &params, &pres.vka_pres, &pres.C_j_vec)?;
    assert!(ok, "verification failed");

    // 8) Issuer MAC verify on original (A,e,M)
    let ok_mac = vka_verify_mac(&sk, &params, &tau, &messages)?;
    assert!(ok_mac, "MAC check failed");

    println!("All checks passed");
    Ok(())
}