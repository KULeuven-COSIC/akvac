// use std::ops::{Mul, Sub};
// use ark_ec::{CurveGroup, PrimeGroup};
use ark_ec::{PrimeGroup};
use ark_ed25519::{Fr as ScalarField, EdwardsProjective as G};
// FrConfig, Fr, EdwardsProjective};
// use ark_ff::{BigInteger, Field, Fp256, MontBackend, PrimeField};
use ark_ff::{Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use ark_std::{UniformRand, Zero};
use rand::{CryptoRng, RngCore};
use sha2::Sha256;
use sha2::Digest;
use rayon::prelude::*;

/// Handy aliases
pub type Scalar = ScalarField;
pub type Point = G;

const PROT_NAME_MAC: &[u8] = b"AKVAC-BBSsaga-MAC";

/// Internal helper: scalar-multiply a point.
#[inline]
pub fn smul(p: &Point, s: &Scalar) -> Point {
    // In Arkworks 0.5, scalar mul via bigint is the stable way across curves
    p.mul_bigint((*s).into_bigint())
}

/// Parameters from setup. The authority keeps the discrete logs `a_j`.
#[derive(Clone, Debug)]
pub struct Params {
    /// The canonical curve generator G.
    pub G: Point,
    /// pp_saga := G_0
    pub pp_saga: Point,
    /// (G_1, ..., G_l)
    pub G_vec: Vec<Point>,
    /// (td_1, ..., td_l) where G_j = td_j * G and G_0 = td_0 * G
    pub td_vec: Vec<Scalar>,
}

/// Secret key and public key for a user.
#[derive(Clone, Debug)]
pub struct SecretKey {
    pub x: Scalar,
    pub y_vec: Vec<Scalar>, // y_1..y_ell
}

#[derive(Clone, Debug)]
pub struct PublicKey {
    pub X: Point,
    pub Y_vec: Vec<Point>, // Y_j = y_j * G_j
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub A: Point,
    pub e: Scalar,
    pub proof: MacProof,
}

/// Output of presentation
#[derive(Clone, Debug)]
pub struct SAGAPres {
    pub C_A: Point,
    pub T: Point,
}

/// Schnorr-style NIZK for BBS-SAGA MAC correctness (Fiat–Shamir)
#[derive(Clone, Debug)]
pub struct MacProof {
    pub c: Scalar,
    // challenge
    pub s_x: Scalar,
    // response for x
    pub s_y_vec: Vec<Scalar>, // responses for y_1..y_l
}


/// Convenience error type
#[derive(thiserror::Error, Debug)]
pub enum SAGAError {
    #[error("length mismatch: expected {expected}, got {got}")]
    LengthMismatch { expected: usize, got: usize },
    #[error("failed to invert scalar (x+e)=0 — resample e and retry")]
    NonInvertible,
}

/// Present: randomize with r, xi_j and compute commitments and T.
///
/// Returns:
/// - sagapres = (C_A, T)
/// - C_j with their blinding scalars xi_j
/// - witness (r, e) to pass to the predicate
#[derive(Clone, Debug)]
pub struct PresentResult {
    pub saga_pres: SAGAPres,
    pub C_j_vec: Vec<Point>,
    pub xi_vec: Vec<Scalar>,
    pub witness_r: Scalar,
    pub witness_e: Scalar,
}


#[inline]
fn hash_to_scalar(bytes: &[u8]) -> Scalar {
    let d = Sha256::digest(bytes);
    // Arkworks Fr: reduce 32 bytes mod field order
    Scalar::from_le_bytes_mod_order(&d)
}

fn hash_challenge_mac(
    // statement
    X: &Point,
    Y_vec: &[Point],
    eA_minus_G0: &Point,
    // announcement
    T1: &Point,
    T2_vec: &[Point],
    T3: &Point,
) -> Scalar {
    let mut buf = Vec::new();
    buf.extend_from_slice(PROT_NAME_MAC);

    // statement
    X.serialize_compressed(&mut buf).unwrap();
    for Yj in Y_vec {
        Yj.serialize_compressed(&mut buf).unwrap();
    }
    eA_minus_G0.serialize_compressed(&mut buf).unwrap();

    // announcement
    T1.serialize_compressed(&mut buf).unwrap();
    for t2j in T2_vec {
        t2j.serialize_compressed(&mut buf).unwrap();
    }
    T3.serialize_compressed(&mut buf).unwrap();

    hash_to_scalar(&buf)
}

/// Prover for \nizkbbssaga:
/// Statement  : (X, (Y_j)_{j=1..l}, eA - G0)
/// Witness    : (x, (y_j)_{j=1..l})
/// Homomorph. : (x,y)->(xG, (y_j G_j),  -xA + Σ y_j M_j)
fn nizk_prove_bbs_saga<R: RngCore + CryptoRng>(
    rng: &mut R,
    params: &Params,
    pk: &PublicKey,
    A: &Point,
    e: &Scalar,
    messages: &[Point],
    sk: &SecretKey,
) -> MacProof {
    let l = params.G_vec.len();
    debug_assert_eq!(messages.len(), l);
    debug_assert_eq!(sk.y_vec.len(), l);
    debug_assert_eq!(pk.Y_vec.len(), l);

    // 1) Sample a = (a_x, a_y1..a_yl)
    let a_x = Scalar::rand(rng);
    let mut a_y_vec = Vec::with_capacity(l);
    for _ in 0..l {
        a_y_vec.push(Scalar::rand(rng));
    }

    // 2) Announcement T = φ(a)
    // T1 = a_x * G
    let T1 = smul(&params.G, &a_x);
    // T2_j = a_yj * G_j
    let mut T2_vec = Vec::with_capacity(l);
    for j in 0..l {
        T2_vec.push(smul(&params.G_vec[j], &a_y_vec[j]));
    }
    // T3 = - a_x * A + Σ a_yj * M_j
    let mut T3 = -smul(A, &a_x);
    for j in 0..l {
        T3 += smul(&messages[j], &a_y_vec[j]);
    }

    // Statement: S = (X, Y_vec, eA - G0)
    let mut eA_minus_G0 = smul(A, e);
    eA_minus_G0 -= params.pp_saga;

    // 3) c = H(ProtName, statement, announcement)
    let c = hash_challenge_mac(&pk.X, &pk.Y_vec, &eA_minus_G0, &T1, &T2_vec, &T3);

    // 4) s = a + c * witness  (entry-wise)
    let s_x = a_x + c * sk.x;
    let mut s_y_vec = Vec::with_capacity(l);
    for j in 0..l {
        s_y_vec.push(a_y_vec[j] + c * sk.y_vec[j]);
    }

    MacProof { c, s_x, s_y_vec }
}

/// Verifier for \nizkbbssaga
fn nizk_verify_bbs_saga(
    params: &Params,
    pk: &PublicKey,
    A: &Point,
    e: &Scalar,
    messages: &[Point],
    proof: &MacProof,
) -> bool {
    let l = params.G_vec.len();
    if messages.len() != l || pk.Y_vec.len() != l || proof.s_y_vec.len() != l {
        println!("Length mismatch in nizk_verify_bbs_saga");
        return false;
    }

    // Statement: S = (X, Y_vec, eA - G0)
    let mut eA_minus_G0 = smul(A, e);
    eA_minus_G0 -= params.pp_saga;

    // Recompute accepting announcement  T' = φ(s) - c * S
    // φ(s): (s_x G, (s_yj G_j),  - s_x A + Σ s_yj M_j)
    let T1_s = smul(&params.G, &proof.s_x);
    let mut T2_s_vec = Vec::with_capacity(l);
    for j in 0..l {
        T2_s_vec.push(smul(&params.G_vec[j], &proof.s_y_vec[j]));
    }
    let mut T3_s = -smul(A, &proof.s_x);
    for j in 0..l {
        T3_s += smul(&messages[j], &proof.s_y_vec[j]);
    }

    // subtract c*S
    let T1 = T1_s - smul(&pk.X, &proof.c);
    let mut T2_vec = Vec::with_capacity(l);
    for j in 0..l {
        T2_vec.push(T2_s_vec[j] - smul(&pk.Y_vec[j], &proof.c));
    }
    let T3 = T3_s - smul(&eA_minus_G0, &proof.c);

    // c' = H(ProtName, statement, T')
    let c_prime = hash_challenge_mac(&pk.X, &pk.Y_vec, &eA_minus_G0, &T1, &T2_vec, &T3);
    c_prime == proof.c
}

/// Setup for SAGA scheme. Returns public parameters.
pub fn saga_setup<R: RngCore + CryptoRng>(rng: &mut R, l: usize) -> Params {
    let G = Point::generator();

    // G0
    let r = Scalar::rand(rng);
    let mut G0 = smul(&G, &r);

    // Sample td_1..td_l
    let mut td_vec = Vec::with_capacity(l);
    for _ in 1..=l {
        td_vec.push(Scalar::rand(rng));
    }

    // Build G_0 and G_1..G_l
    // let G0 = smul(&G, &td_vec[0]);
    let mut G_vec = Vec::with_capacity(l);
    for j in 0..l {
        G_vec.push(smul(&G, &td_vec[j]));
    }

    Params {
        G: G,
        pp_saga: G0,
        G_vec: G_vec,
        td_vec: td_vec,
    }
}


/// Keygen: sk=(x,y_1..y_l), pk=(X=xG, Y_j=y_j G_j)
pub fn saga_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    params: &Params,
) -> (SecretKey, PublicKey) {
    let l = params.G_vec.len();
    let x = Scalar::rand(rng);
    let mut y_vec = Vec::with_capacity(l);
    for _ in 1..=l {
        y_vec.push(Scalar::rand(rng));
    }

    let X = smul(&params.G, &x);
    let mut Y_vec = Vec::with_capacity(l);
    for j in 0..l {
        Y_vec.push(smul(&params.G_vec[j], &y_vec[j]));
    }

    (
        SecretKey { x, y_vec: y_vec },
        PublicKey { X, Y_vec: Y_vec },
    )
}


/// Sign: A = (x+e)^(-1) * (G_0 + sum_j y_j M_j), plus NIZK over (A,e,M).
pub fn saga_mac<R: RngCore + CryptoRng>(
    rng: &mut R,
    sk: &SecretKey,
    params: &Params,
    messages: &[Point],
    pk_saga: &PublicKey, // for NIZK, so that we don't need to recompute it
) -> Result<Signature, SAGAError> {
    let l = params.G_vec.len();
    if messages.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: messages.len() });
    }
    if sk.y_vec.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: sk.y_vec.len() });
    }

    // Sample e such that x + e != 0
    let e = loop {
        let e_try = Scalar::rand(rng);
        if !(sk.x + e_try).is_zero() {
            break e_try;
        }
    };

    // S = G_0 + Σ y_j * M_j
    let mut S = params.pp_saga; // G_0
    for j in 0..l {
        S += smul(&messages[j], &sk.y_vec[j]);
    }

    // A = (x+e)^(-1) * S
    let inv = (sk.x + e).inverse().ok_or(SAGAError::NonInvertible)?;
    let A = smul(&S, &inv);

    // Build a local pk-view from sk (no secret leakage; all recomputable)
    // TODO: performance opt: pass pk as argument
    // let local_pk = PublicKey {
    //     X: smul(&params.G, &sk.x),
    //     Y_vec: (0..l).map(|j| smul(&params.G_vec[j], &sk.y_vec[j])).collect(),
    // };
    let proof = nizk_prove_bbs_saga(rng, params, &pk_saga, &A, &e, messages, sk);

    Ok(Signature { A, e, proof })
}

pub fn saga_present<R: RngCore + CryptoRng>(
    rng: &mut R,
    pk: &PublicKey,
    params: &Params,
    tau: &Signature,
    messages: &[Point],
) -> Result<PresentResult, SAGAError> {
    let l = params.G_vec.len();
    if messages.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: messages.len() });
    }
    if pk.Y_vec.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: pk.Y_vec.len() });
    }

    let ok = nizk_verify_bbs_saga(params, pk, &tau.A, &tau.e, messages, &tau.proof);
    if !ok {
        println!("saga_present: invalid MAC proof");
        return Err(SAGAError::NonInvertible);
    }

    // r, xi_1..xi_l
    let r = Scalar::rand(rng);
    let mut xi_vec = Vec::with_capacity(l); // ξ
    for _ in 1..=l {
        xi_vec.push(Scalar::rand(rng));
    }

    // C_j = M_j + xi_j * G_j
    // let mut C_j_vec = Vec::with_capacity(l);
    // for j in 0..l {
    //     let cj = messages[j] + smul(&params.G_vec[j], &xi_vec[j]);
    //     C_j_vec.push(cj);
    // }
    let C_j_vec: Vec<Point> = messages
        .par_iter()
        .zip(params.G_vec.par_iter())
        .zip(xi_vec.par_iter())
        .map(|((msg, Gj), xi)| *msg + smul(Gj, xi))
        .collect();

    // C_A = A + r * G
    let C_A = tau.A + smul(&params.G, &r);

    // T = rX - e C_A + (e r) G - Σ xi_j Y_j
    // let mut T = smul(&pk.X, &r);         // rX
    // T -= smul(&C_A, &tau.e);                   // - e C_A
    // T += smul(&params.G, &(tau.e * r));        // + e r G
    // for j in 0..l {
    //     T -= smul(&pk.Y_vec[j], &xi_vec[j]);       // - xi_j Y_j
    // }
    // Parallel sum S = sum_j (xi_j * Y_j)
    let sum_yxi: Point = pk.Y_vec
        .par_iter()
        .zip(xi_vec.par_iter())
        .map(|(Yj, xij)| smul(Yj, xij))
        .reduce(Point::zero, |a, b| a + b);

    // T = rX - e C_A + e r G - sum_j xi_j Y_j
    let mut T = smul(&pk.X, &r);              // rX
    T -= smul(&C_A, &tau.e);                  // - e C_A
    T += smul(&params.G, &(tau.e * r));       // + e r G
    T -= sum_yxi;                             // - Σ xi_j Y_j

    Ok(PresentResult {
        saga_pres: SAGAPres { C_A, T },
        C_j_vec: C_j_vec,
        xi_vec: xi_vec,
        witness_r: r,
        witness_e: tau.e,
    })
}


/// Predicate check (holder side):
/// Verify T == rX - e C_A + e r G - Σ xi_j Y_j
pub fn saga_predicate(
    pk: &PublicKey,
    params: &Params,
    saga_pres: &SAGAPres,
    r: &Scalar,
    e: &Scalar,
    xi_vec: &[Scalar],
) -> Result<bool, SAGAError> {
    let l = pk.Y_vec.len();
    if xi_vec.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: xi_vec.len() });
    }

    let mut rhs = smul(&pk.X, r);
    rhs -= smul(&saga_pres.C_A, e);
    rhs += smul(&params.G, &(*e * *r));
    for j in 0..l {
        rhs -= smul(&pk.Y_vec[j], &xi_vec[j]);
    }

    Ok(rhs == saga_pres.T)
}


/// Verify (issuer/MAC owner side):
/// Check: x C_A ?= G_0 + Σ y_j C_j + T
pub fn pres_verify(
    sk: &SecretKey,
    params: &Params,
    saga_pres: &SAGAPres,
    C_j_vec: &[Point],
) -> Result<bool, SAGAError> {
    let l = params.G_vec.len();
    if C_j_vec.len() != l || sk.y_vec.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: C_j_vec.len() });
    }

    let lhs = smul(&saga_pres.C_A, &sk.x); // x C_A

    // RHS = G_0 + Σ y_j C_j + T
    let mut rhs = params.pp_saga;
    for j in 0..l {
        rhs += smul(&C_j_vec[j], &sk.y_vec[j]);
    }
    rhs += saga_pres.T;

    Ok(lhs == rhs)
}


/// Verify MAC (issuer): (x+e) A == G_0 + sum_j y_j M_j
pub fn saga_verify_mac(
    sk: &SecretKey,
    params: &Params,
    tau: &Signature,
    messages: &[Point],
) -> Result<bool, SAGAError> {
    let l = params.G_vec.len();
    if messages.len() != l || sk.y_vec.len() != l {
        return Err(SAGAError::LengthMismatch { expected: l, got: messages.len() });
    }

    let lhs = smul(&tau.A, &(sk.x + tau.e));

    let mut rhs = params.pp_saga;
    for j in 0..l {
        rhs += smul(&messages[j], &sk.y_vec[j]);
    }

    Ok(lhs == rhs)
}


#[cfg(test)]
mod bbs_saga_tests {
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use crate::saga::bbs_saga::*;

    #[test]
    fn full_bbs_saga_flow_test() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(42);
        let l = 3;

        // 1) Setup
        let params = saga_setup(&mut rng, l);

        // 2) Keygen
        let (sk, pk) = saga_keygen(&mut rng, &params);

        // 3) Messages as points (toy example: hash-free demo using multiples of G)
        let messages: Vec<Point> = (0..l)
            .map(|i| {
                let s = Scalar::from(i as u64);
                smul(&params.G, &s)
            })
            .collect();

        // 4) Sign
        let tau = saga_mac(&mut rng, &sk, &params, &messages, &pk)?;

        // 5) Present
        let pres = saga_present(&mut rng, &pk, &params, &tau, &messages)?;

        // 6) Holder predicate check
        let ok_pred = saga_predicate(
            &pk,
            &params,
            &pres.saga_pres,
            &pres.witness_r,
            &pres.witness_e,
            &pres.xi_vec,
        )?;
        assert!(ok_pred, "predicate failed");

        // 7) Issuer verification (MAC verify on randomized commitments)
        let ok = pres_verify(&sk, &params, &pres.saga_pres, &pres.C_j_vec)?;
        assert!(ok, "verification failed");

        // 8) Issuer MAC verify on original (A,e,M)
        let ok_mac = saga_verify_mac(&sk, &params, &tau, &messages)?;
        assert!(ok_mac, "MAC check failed");

        println!("All checks passed");
        Ok(())
    }
}
