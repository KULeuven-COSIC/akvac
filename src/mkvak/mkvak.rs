use ark_ec::PrimeGroup;
use ark_ff::{PrimeField, Zero};
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::UniformRand;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use crate::mkvak::nizks::{IssProof, nizk_prove_issue, nizk_prove_req, nizk_prove_show, nizk_verify_issue, nizk_verify_req, nizk_verify_show, ReqProof, ShowProof};
use crate::saga::bbs_saga::{
    smul, saga_keygen, saga_mac, saga_setup, Params as SAGAParams, Point, Scalar, SecretKey as SagaSK,
    PublicKey as SagaPK, Signature as SAGASig, SAGAError,
};
use rayon::prelude::*;


/// Public parameters for AKVAC
#[derive(Clone, Debug)]
pub struct PublicParams {
    /// Group base (G) carried from saga params
    pub G: Point,
    /// Random presentation base H
    pub H: Point,
    /// saga params with ℓ = n + 2; contains:
    ///   - pp_saga = G_0
    ///   - G_vec = [G_1..G_{n+2}]
    pub saga_params: SAGAParams,
}

#[derive(thiserror::Error, Debug)]
pub enum AkvacError {
    #[error("length mismatch: expected {expected}, got {got}")]
    LengthMismatch { expected: usize, got: usize },
    #[error("saga error: {0}")]
    SAGA(#[from] SAGAError),
}

/// AKVAC issuer key material
#[derive(Clone, Debug)]
pub struct IssuerSecret {
    pub saga_sk: SagaSK,
    pub e: Scalar,
}

#[derive(Clone, Debug)]
pub struct IssuerPublic {
    pub saga_pk: SagaPK,
    pub E: Point, // E = e * G
}

/// AKVAC verifier key material
#[derive(Clone, Debug)]
pub struct VerifierSecret {
    /// x_0..x_n
    pub x_0_to_x_n: Vec<Scalar>,
}

#[derive(Clone, Debug)]
pub struct VerifierPublic {
    /// (X_1..X_n, X_0, Z_0)
    pub X_1_to_n: Vec<Point>,
    pub X_0: Point,
    pub Z_0: Point,
    /// τ (saga MAC over X_1..X_n, X_0, Z_0)
    pub tau: SAGASig,
}

#[derive(Clone, Debug)]
pub struct ReceiveCredState {
    pub s: Scalar,
    pub bar_x0: Scalar,
    pub bar_X0: Point,
    pub bar_Z0: Point,
    // not strictly required by the LaTeX to be stored;
    // keeping attrs here is handy for the final output:
    pub attrs: Vec<Scalar>,
}

#[derive(Clone, Debug)]
pub struct CredReq {
    pub saga_pres: crate::saga::bbs_saga::SAGAPres,
    pub C_j_vec: Vec<Point>,
    // C_1..C_{n+2}
    pub bar_X0: Point,
    pub bar_Z0: Point,
    pub C_attr: Point,
    pub nizk: ReqProof,
}

#[derive(Clone, Debug)]
pub struct BlindCred {
    pub bar_U: Point,
    pub bar_V: Point,
    pub nizk: IssProof,
}

#[derive(Clone, Debug)]
pub struct Credential {
    pub U: Point,
    pub V: Point,
    pub attrs: Vec<Scalar>,
}

// simple 32-byte digest proof
#[derive(Clone, Debug)]
pub struct Proof32 {
    pub digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub struct Presentation {
    pub tilde_U: Point,
    pub Z: Point,
    pub C_v: Point,
    pub C_j_vec: Vec<Point>,
    // C_1..C_n
    pub nizk: ShowProof,        // cmzcpzshow
}

// ------------------------------------
// Helper: vfcred (wraps saga.verify)
// ------------------------------------
fn vfcred(
    isk: &IssuerSecret,
    pp: &PublicParams,
    sagaPres: &crate::saga::bbs_saga::SAGAPres,
    C_j_vec: &[Point],
) -> Result<bool, AkvacError> {
    use crate::saga::bbs_saga::pres_verify;
    Ok(pres_verify(&isk.saga_sk, &pp.saga_params, sagaPres, C_j_vec)?)
}


/// AKVAC.setup(λ, 1^n)
/// Internally sets ℓ = n + 2 for the underlying saga.
pub fn akvac_setup<R: RngCore + CryptoRng>(rng: &mut R, n: usize) -> PublicParams {
    let l = n + 2;
    let saga_params = saga_setup(rng, l);

    // Sample H as a random multiple of G (prime-order group)
    let H = smul(&saga_params.G, &Scalar::rand(rng));

    PublicParams {
        G: saga_params.G,
        H: H,
        saga_params,
    }
}


/// AKVAC.issuerkg()
pub fn issuer_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
) -> (IssuerSecret, IssuerPublic) {
    let (saga_sk, saga_pk) = saga_keygen(rng, &pp.saga_params);

    let e = Scalar::rand(rng);
    let E = smul(&pp.G, &e);

    (
        IssuerSecret { saga_sk, e },
        IssuerPublic { saga_pk, E },
    )
}


/// AKVAC.verifierkg(isk, ipk)
/// Builds (X_1..X_n, X_0, Z_0) and requests a saga MAC τ from the issuer.
pub fn verifier_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    isk: &IssuerSecret,
    ipk: &IssuerPublic,
) -> Result<(VerifierSecret, VerifierPublic), AkvacError> {
    // ℓ = n + 2  ⇒  n = ℓ - 2
    let l = pp.saga_params.G_vec.len();
    assert!(l >= 2, "saga was not set with ℓ = n + 2");
    let n = l - 2;

    // Sample x_0..x_n, ν, x_r
    let mut x_0_to_x_n = Vec::with_capacity(n + 1);
    for _ in 0..=n {
        x_0_to_x_n.push(Scalar::rand(rng));
    }
    assert_eq!(x_0_to_x_n.len(), n + 1);
    let v = Scalar::rand(rng);

    // Compute X_i = x_i * G for i=1..n
    let mut X_1_to_n = Vec::with_capacity(n);
    for i in 1..=n {
        X_1_to_n.push(smul(&pp.G, &x_0_to_x_n[i]));
    }
    assert_eq!(X_1_to_n.len(), n);

    // Z_0 = ν G
    let Z_0 = smul(&pp.G, &v);

    // X_0 = x_0 G + ν E
    // let X_0 = smul(&pp.G, &x_vec[0]) + smul(&ipk.E, &Scalar::from(1u64)); // E already has e folded into it
    // let X_0 = X_0 + smul(&pp.G, &(v * isk.e)); // equivalently: x0*G + ν*(eG) = x0*G + (νe)*G
    let mut X_0 = smul(&pp.G, &x_0_to_x_n[0]);
    X_0 += smul(&pp.G, &(v * isk.e)); // equivalently: x0*G + ν*(eG) = x0*G + (νe)*G


    // Assemble messages for saga MAC in the order: (X_1..X_n, X_0, Z_0)
    let mut msgs = X_1_to_n.clone();
    msgs.push(X_0);
    msgs.push(Z_0);

    // Ask issuer to MAC (using issuer's saga secret)
    let tau = saga_mac(rng, &isk.saga_sk, &pp.saga_params, &msgs, &ipk.saga_pk)?;

    let vsk = VerifierSecret { x_0_to_x_n: x_0_to_x_n };
    let vpk = VerifierPublic {
        X_1_to_n: X_1_to_n,
        X_0: X_0,
        Z_0: Z_0,
        tau: tau,
    };
    Ok((vsk, vpk))
}


/// Client side (verifier) prepares a blinded request.
/// attrs: a_1..a_n in the paper; commitment C_attr = sum a_j X_j + s G
pub fn receive_cred_1<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    ipk: &IssuerPublic,
    vpk: &VerifierPublic,
    attrs: &[Scalar],
) -> Result<(ReceiveCredState, CredReq), AkvacError> {
    // n = ℓ - 2
    let l = pp.saga_params.G_vec.len();
    let n = l - 2;
    if attrs.len() != n {
        return Err(AkvacError::LengthMismatch {
            expected: n,
            got: attrs.len(),
        });
    }

    // Present the issuer MAC τ on (X_1..X_n, X_0, Z_0)
    // messages in the same order as when it was MACed
    let mut msgs = vpk.X_1_to_n.clone();
    msgs.push(vpk.X_0);
    msgs.push(vpk.Z_0);

    let saga_pres = crate::saga::bbs_saga::saga_present(
        rng,
        &ipk.saga_pk,
        &pp.saga_params,
        &vpk.tau,
        &msgs,
    )?;

    // Sample s, bar_x0, bar_v and compute the blinding of (X_0, Z_0)
    let s = Scalar::rand(rng);
    let bar_x0 = Scalar::rand(rng);
    let bar_v = Scalar::rand(rng);

    // bar_X0 = X_0 + bar_x0 * G + bar_v * E
    let bar_X0 = vpk.X_0 + smul(&pp.G, &bar_x0) + smul(&ipk.E, &bar_v);
    // bar_Z0 = Z_0 + bar_v * G
    let bar_Z0 = vpk.Z_0 + smul(&pp.G, &bar_v);

    // Commitment to attributes: C_attr = sum_j attr_j * X_j + s G
    // let mut C_attr = smul(&pp.G, &s);
    // for (a, Xj) in attrs.iter().zip(vpk.X_1_to_n.iter()) {
    //     C_attr += smul(Xj, a);
    // }
    // Parallel sum of a_j * X_j
    let sum_ax: Point = attrs
        .par_iter()
        .zip(vpk.X_1_to_n.par_iter())
        .map(|(a, Xj)| smul(Xj, a))
        .reduce(Point::zero, |acc, p| acc + p);

    // C_attr = sG + sum_j a_j X_j
    let C_attr = smul(&pp.G, &s) + sum_ax;

    // Build C_j = M_j + ξ_j G_j were returned already in pres.C_j_vec
    // Assemble statement and placeholder proof
    assert_eq!(saga_pres.C_j_vec.len(), n + 2);
    let stmt_Cs = saga_pres.C_j_vec.clone();

    // Witness scalars fed into the placeholder hash:
    // include s, bar_x0, bar_v, r, e, xi_1..xi_{n+2}, and (a_j * xi_j) if you like
    let mut witness_scalars = vec![s, bar_x0, bar_v, saga_pres.witness_r, saga_pres.witness_e];
    witness_scalars.extend_from_slice(&saga_pres.xi_vec);

    let nizk = nizk_prove_req(
        rng, pp, ipk, &pp.saga_params,
        &saga_pres.saga_pres,        // has C_A, T
        &stmt_Cs,                  // C_1..C_{n+2}
        &bar_X0, &bar_Z0, &C_attr,
        &s, &attrs, &bar_x0, &bar_v,            // note: bar_v is \bar\nu
        &saga_pres.witness_r, &saga_pres.witness_e,
        &saga_pres.xi_vec,
    );

    let state = ReceiveCredState {
        s: s,
        bar_x0: bar_x0,
        bar_X0: bar_X0,
        bar_Z0: bar_Z0,
        attrs: attrs.to_vec(),
    };

    let credreq = CredReq {
        saga_pres: saga_pres.saga_pres,
        C_j_vec: stmt_Cs,
        bar_X0,
        bar_Z0,
        C_attr,
        nizk,
    };

    Ok((state, credreq))
}


pub fn issue_cred<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    isk: &IssuerSecret,
    ipk: &IssuerPublic,
    cred_req: &CredReq,
) -> Result<BlindCred, AkvacError> {
    if !nizk_verify_req(
        pp, ipk, &pp.saga_params,
        &cred_req.saga_pres,
        &cred_req.C_j_vec,
        &cred_req.bar_X0,
        &cred_req.bar_Z0,
        &cred_req.C_attr,
        &cred_req.nizk,
    ) {
        println!("AKVAC request proof does not verify");
        return Err(AkvacError::SAGA(SAGAError::NonInvertible));
    }

    // Verify the saga presentation (MAC correctness over C_j etc.)
    let verified = vfcred(isk, pp, &cred_req.saga_pres, &cred_req.C_j_vec)?;
    if !verified {
        println!("AKVAC saga presentation does not verify");
        return Err(AkvacError::SAGA(SAGAError::NonInvertible));
    }

    // u ← Z_p,  ȗ = u G,  V̄ = u((X̄0 − e Z̄0) + C_attr)
    let u = Scalar::rand(rng);
    let bar_U = smul(&pp.G, &u);

    // (bar_X0 - e * bar_Z0)
    let x0_part = cred_req.bar_X0 - smul(&cred_req.bar_Z0, &isk.e);
    let bar_V = smul(&(x0_part + cred_req.C_attr), &u);

    let nizk = nizk_prove_issue(
        rng, pp,
        &ipk.E, &bar_U, &bar_V,
        &cred_req.bar_X0, &cred_req.bar_Z0, &cred_req.C_attr,
        &isk.e, &u,
    );

    Ok(BlindCred { bar_U: bar_U, bar_V: bar_V, nizk: nizk })
}

pub fn receive_cred_2(
    pp: &PublicParams,
    ipk: &IssuerPublic,
    state: &ReceiveCredState,
    credreq: &CredReq,
    blind: &BlindCred,
) -> Result<Credential, AkvacError> {
    if !nizk_verify_issue(
        pp,
        &ipk.E,
        &blind.bar_U,
        &blind.bar_V,
        &credreq.bar_X0,
        &credreq.bar_Z0,
        &credreq.C_attr,
        &blind.nizk,
    ) {
        println!("AKVAC issue proof does not verify");
        return Err(AkvacError::SAGA(SAGAError::NonInvertible));
    }

    let mut gamma = rand_nonzero(&mut ark_std::rand::rngs::OsRng);

    let U = smul(&blind.bar_U, &gamma);
    let correction = state.s + state.bar_x0;
    let V_inner = blind.bar_V - smul(&blind.bar_U, &correction);
    let V = smul(&V_inner, &gamma);

    Ok(Credential {
        U,
        V,
        attrs: state.attrs.clone(),
    })
}

fn hash_points_scalars_with_ctx(points: &[Point], scalars: &[Scalar], pres_ctx: &[u8]) -> [u8; 32] {
    let mut buf = Vec::new();
    for p in points {
        p.serialize_compressed(&mut buf).unwrap();
    }
    for s in scalars {
        s.serialize_compressed(&mut buf).unwrap();
    }
    buf.extend_from_slice(pres_ctx);
    let d = Sha256::digest(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d[..]);
    out
}

/// Prover: include witness scalars and pres_ctx in the digest
fn prove_cmzcpzshow(
    X_1_to_n: &[Point],
    tilde_U: &Point,
    tilde_gamma: &Scalar,
    attrs: &[Scalar],
    gamma_js: &[Scalar],
    pres_ctx: &[u8],
) -> Proof32 {
    let mut points = Vec::with_capacity(X_1_to_n.len() + 1);
    points.extend_from_slice(X_1_to_n);
    points.push(*tilde_U);

    // witness order: [tilde_gamma, attrs..., gamma_js...]
    let mut ws: Vec<Scalar> = Vec::with_capacity(1 + attrs.len() + gamma_js.len());
    ws.push(*tilde_gamma);
    ws.extend_from_slice(attrs);
    ws.extend_from_slice(gamma_js);

    Proof32 {
        digest: hash_points_scalars_with_ctx(&points, &ws, pres_ctx),
    }
}


/// Verifier: only statement + ctx (INSECURE placeholder)
fn verify_cmzcpzshow(
    X_1_to_n: &[Point],
    tilde_U: &Point,
    pres_ctx: &[u8],
    proof: &Proof32,
) -> bool {
    let mut points = Vec::with_capacity(X_1_to_n.len() + 1);
    points.extend_from_slice(X_1_to_n);
    points.push(*tilde_U);

    hash_points_scalars_with_ctx(&points, &[], pres_ctx) == proof.digest
}

#[inline]
fn rand_nonzero<R: RngCore + CryptoRng>(rng: &mut R) -> Scalar {
    loop {
        let s = Scalar::rand(rng);
        if !s.is_zero() {
            return s;
        }
    }
}

/// Show credential:
/// - Randomize (U,V) -> (tilde_U, tilde_V)
/// - Sample tilde_gamma, gamma_j in Z_p^*
/// - Compute:
///   Z  = sum_j gamma_j * X_j  - tilde_gamma * H
///   C_V = tilde_V + tilde_gamma * H
///   C_j = attr_j * tilde_U + gamma_j * G
/// - Produce placeholder NIZK bound to (X_1..X_n, tilde_U, pres_ctx)
pub fn show_cred<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    _ipk: &IssuerPublic,
    vpk: &VerifierPublic,
    cred: &Credential,
    pres_ctx: &[u8],
) -> Presentation {
    // γ, \tildeγ, γ_j ∈ Z_p^*
    let gamma = rand_nonzero(rng);
    let tilde_gamma = rand_nonzero(rng);
    let gamma_j_vec: Vec<Scalar> = (0..vpk.X_1_to_n.len()).map(|_| rand_nonzero(rng)).collect();

    // (tilde_U, tilde_V) = (γU, γV)
    let tilde_U = smul(&cred.U, &gamma);
    let tilde_V = smul(&cred.V, &gamma);

    // Z = sum_j γ_j X_j - tildeγ * H
    // let mut Z = Point::zero();
    // for (gamma_j, Xj) in gamma_j_vec.iter().zip(vpk.X_1_to_n.iter()) {
    //     Z += smul(Xj, gamma_j);
    // }
    // Z -= smul(&pp.H, &tilde_gamma);
    // Z = Σ_j γ_j X_j  -  tilde_gamma * H
    let sum_X = vpk
        .X_1_to_n
        .par_iter()
        .zip(gamma_j_vec.par_iter())
        .map(|(Xj, gamma_j)| smul(Xj, gamma_j))
        .reduce(|| Point::zero(), |a, b| a + b);

    let mut Z = sum_X - smul(&pp.H, &tilde_gamma);

    // C_V = tilde_V + tildeγ * H
    let C_v = tilde_V + smul(&pp.H, &tilde_gamma);

    // C_j = attr_j * tilde_U + γ_j * G
    // let mut C_j_vec = Vec::with_capacity(cred.attrs.len());
    // assert_eq!(cred.attrs.len(), gamma_j_vec.len());
    // for (attr, gamma_j) in cred.attrs.iter().zip(gamma_j_vec.iter()) {
    //     C_j_vec.push(smul(&tilde_U, attr) + smul(&pp.G, gamma_j));
    // }
    // C_j = attr_j * tilde_U + gamma_j * G
    assert_eq!(cred.attrs.len(), gamma_j_vec.len());
    let C_j_vec: Vec<Point> = cred
        .attrs
        .par_iter()
        .zip(gamma_j_vec.par_iter())
        .map(|(attr, gamma_j)| smul(&tilde_U, attr) + smul(&pp.G, gamma_j))
        .collect();

    // Placeholder NIZK bound to (X_1..X_n, tilde_U, pres_ctx)
    let nizk = nizk_prove_show(
        rng, pp, vpk,
        &tilde_U, &Z, &C_j_vec,
        &tilde_gamma, &cred.attrs, &gamma_j_vec,
        pres_ctx,
    );

    Presentation {
        tilde_U: tilde_U,
        Z: Z,
        C_v: C_v,
        C_j_vec: C_j_vec,
        nizk: nizk,
    }
}


/// Verify presentation:
/// - Check placeholder cmzcpzshow over (X_1..X_n, tilde_U, pres_ctx)
/// - Check Z == x0*tilde_U + sum_j xj * C_j - C_V
pub fn verify_cred_show(
    pp: &PublicParams,
    vsk: &VerifierSecret,
    vpk: &VerifierPublic,
    pres: &Presentation,
    pres_ctx: &[u8],
) -> bool {
    if !nizk_verify_show(pp, vpk, pres_ctx, &pres.tilde_U, &pres.Z, &pres.C_j_vec, &pres.nizk) {
        println!("AKVAC show proof does not verify");
        return false;
    }

    // Equation: Z ?= x0 * tilde_U + sum_j xj * C_j - C_V
    let mut rhs = smul(&pres.tilde_U, &vsk.x_0_to_x_n[0]);

    // for i in 1..vsk.x_0_to_x_n.len() {
    //     let xj = &vsk.x_0_to_x_n[i];
    //     let Cj = &pres.C_j_vec[i - 1];
    //     rhs += smul(Cj, xj);
    // }

    rhs += (1..vsk.x_0_to_x_n.len())
        .into_par_iter()
        .map(|i| {
            let xj = &vsk.x_0_to_x_n[i];
            let Cj = &pres.C_j_vec[i - 1];
            smul(Cj, xj)
        })
        .reduce(Point::zero, |a, b| a + b);


    rhs -= pres.C_v;

    pres.Z == rhs
}


#[cfg(test)]
mod akvac_tests {
    use ark_ff::Zero;
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use ark_std::UniformRand;
    use crate::mkvak::mkvak::{akvac_setup, AkvacError, issue_cred, issuer_keygen, receive_cred_1, receive_cred_2, show_cred, verifier_keygen, verify_cred_show};
    use crate::saga::bbs_saga::Scalar;

    #[test]
    fn setup_receive1() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(42);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.saga_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        Ok(())
    }

    #[test]
    fn setup_receive1_issue_cred() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.saga_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        Ok(())
    }

    #[test]
    fn setup_receive1_issue_cred_receive2() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.saga_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        assert!(!cred.U.is_zero());
        assert!(!cred.V.is_zero());
        assert_eq!(cred.attrs, attrs);

        Ok(())
    }

    #[test]
    fn setup_receive1_issue_cred_receive2_show_cred_verify() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.saga_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+3 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        assert!(!cred.U.is_zero());
        assert!(!cred.V.is_zero());
        assert_eq!(cred.attrs, attrs);

        let pres_ctx = b"presentation context";
        let pres = show_cred(&mut rng, &pp, &ipk, &vpk, &cred, pres_ctx);

        assert!(verify_cred_show(&pp, &vsk, &vpk, &pres, pres_ctx));

        Ok(())
    }

    #[test]
    fn akvac_setup_issuer_verifier_kg() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.saga_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+2 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        Ok(())
    }

    fn rand_attrs(rng: &mut StdRng, n: usize) -> Vec<Scalar> {
        (0..n).map(|_| Scalar::rand(rng)).collect()
    }

    #[test]
    fn akvac_end_to_end_ok() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(12345);
        let n = 3;

        // Setup
        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.saga_params.G_vec.len(), n + 2);

        // Issuer & Verifier keygen
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        assert_eq!(vpk.X_1_to_n.len(), n);
        assert!(!vpk.X_0.is_zero());
        assert!(!vpk.Z_0.is_zero());

        // Client request (receivecred_1)
        let attrs = rand_attrs(&mut rng, n);
        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        assert_eq!(state.attrs.len(), n);
        assert!(!state.bar_X0.is_zero());
        assert!(!state.bar_Z0.is_zero());
        assert_eq!(cred_req.C_j_vec.len(), n + 2);

        // Issuer issues blind credential
        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        assert!(!blind.bar_U.is_zero());
        assert!(!blind.bar_V.is_zero());

        // Client finalizes
        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;
        assert!(!cred.U.is_zero());
        assert!(!cred.V.is_zero());
        assert_eq!(cred.attrs, attrs);

        Ok(())
    }

    #[test]
    fn receivecred_1_rejects_wrong_attr_len() {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 2;

        let pp = akvac_setup(&mut rng, n);
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk).unwrap();

        // Wrong length (n-1)
        let attrs = rand_attrs(&mut rng, n - 1);
        let err = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs).unwrap_err();
        match err {
            AkvacError::LengthMismatch { expected, got } => {
                assert_eq!(expected, n);
                assert_eq!(got, n - 1);
            }
            _ => panic!("expected LengthMismatch, got {err:?}"),
        }
    }

    #[test]
    fn issue_cred_rejects_tampered_cj_vector() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(99);
        let n = 2;

        let pp = akvac_setup(&mut rng, n);
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;

        let attrs = rand_attrs(&mut rng, n);
        let (_state, mut credreq) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;

        // Tamper one C_j to break the saga verification
        credreq.C_j_vec[0] = credreq.C_j_vec[0] + pp.G;

        // The issuer should reject during vfcred or (earlier) proof check
        let err = issue_cred(&mut rng, &pp, &isk, &ipk, &credreq).unwrap_err();
        matches!(err, AkvacError::SAGA(_));
        Ok(())
    }

    #[test]
    fn akvac_show_verify_ok() -> anyhow::Result<()> {
        use super::*;
        use ark_std::rand::{rngs::StdRng, SeedableRng};

        let mut rng = StdRng::seed_from_u64(4242);
        let n = 3;

        // Setup + issuance (reuse your flow)
        let pp = akvac_setup(&mut rng, n);
        let (isk, ipk) = issuer_keygen(&mut rng, &pp);
        let (vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        let attrs: Vec<Scalar> = (0..n).map(|_| Scalar::rand(&mut rng)).collect();

        let (state, cred_req) = receive_cred_1(&mut rng, &pp, &ipk, &vpk, &attrs)?;
        let blind = issue_cred(&mut rng, &pp, &isk, &ipk, &cred_req)?;
        let cred = receive_cred_2(&pp, &ipk, &state, &cred_req, &blind)?;

        // Show
        let pres_ctx = b"demo-context-123";
        let pres = show_cred(&mut rng, &pp, &ipk, &vpk, &cred, pres_ctx);

        // Verify
        assert!(verify_cred_show(&pp, &vsk, &vpk, &pres, pres_ctx));
        Ok(())
    }
}