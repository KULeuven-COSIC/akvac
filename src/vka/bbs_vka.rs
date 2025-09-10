// use std::ops::{Mul, Sub};
// use ark_ec::{CurveGroup, PrimeGroup};
use ark_ec::{PrimeGroup};
use ark_ed25519::{Fr as ScalarField, EdwardsProjective as G};// FrConfig, Fr, EdwardsProjective};
// use ark_ff::{BigInteger, Field, Fp256, MontBackend, PrimeField};
use ark_ff::{Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use ark_std::{UniformRand, Zero};
use rand::{CryptoRng, RngCore};
use sha2::Sha256;
use sha2::Digest;

/// Handy aliases
pub type Scalar = ScalarField;
pub type Point = G;

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
    /// pp_vka := G_0
    pub pp_vka: Point,
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

/// INSECURE placeholder proof — replace with a real NIZK!
/// TODO: implement a real proof
#[derive(Clone, Debug)]
pub struct Proof {
    pub digest: [u8; 32],
}

#[derive(Clone, Debug)]
pub struct Signature {
    pub A: Point,
    pub e: Scalar,
    pub proof: Proof,
}

/// Output of presentation
#[derive(Clone, Debug)]
pub struct VkaPres {
    pub C_A: Point,
    pub T: Point,
}


/// Convenience error type
#[derive(thiserror::Error, Debug)]
pub enum VkaError {
    #[error("length mismatch: expected {expected}, got {got}")]
    LengthMismatch { expected: usize, got: usize },
    #[error("failed to invert scalar (x+e)=0 — resample e and retry")]
    NonInvertible,
}

/// Present: randomize with r, xi_j and compute commitments and T.
///
/// Returns:
/// - vkapres = (C_A, T)
/// - C_j with their blinding scalars xi_j
/// - witness (r, e) to pass to the predicate
#[derive(Clone, Debug)]
pub struct PresentResult {
    pub vka_pres: VkaPres,
    pub C_j_vec: Vec<Point>,
    pub xi_vec: Vec<Scalar>,
    pub witness_r: Scalar,
    pub witness_e: Scalar,
}

/// Setup for VKA scheme. Returns public parameters.
pub fn vka_setup<R: RngCore + CryptoRng>(rng: &mut R, l: usize) -> Params {
    let G = Point::generator();

    // Sample td_0..td_l
    let mut td_vec = Vec::with_capacity(l + 1);
    for _ in 0..(l + 1) {
        td_vec.push(Scalar::rand(rng));
    }

    // Build G_0 and G_1..G_l
    let G0 = smul(&G, &td_vec[0]);
    let mut G_vec = Vec::with_capacity(l);
    for j in 1..=l {
        G_vec.push(smul(&G, &td_vec[j]));
    }

    Params {
        G: G,
        pp_vka: G0,
        G_vec: G_vec,
        td_vec: td_vec,
    }
}


/// Keygen: sk=(x,y_1..y_l), pk=(X=xG, Y_j=y_j G_j)
pub fn vka_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    params: &Params,
) -> (SecretKey, PublicKey) {
    let l = params.G_vec.len();
    let x = Scalar::rand(rng);
    let mut y_vec = Vec::with_capacity(l);
    for _ in 0..l {
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

/// TODO
/// Helper: insecure placeholder "proof of knowledge" — hash the statement.
/// Replace with a real NIZK system.
fn insecure_proof_of_statement(A: &Point, e: &Scalar, messages: &[Point]) -> Proof {
    let mut buf = Vec::new();
    A.serialize_compressed(&mut buf).unwrap();
    e.serialize_compressed(&mut buf).unwrap();
    for m in messages {
        m.serialize_compressed(&mut buf).unwrap();
    }
    let digest = Sha256::digest(&buf);
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest[..]);
    Proof { digest: out }
}

/// TODO
/// Helper: verify the insecure placeholder proof
fn insecure_verify_proof(A: &Point, e: &Scalar, messages: &[Point], proof: &Proof) -> bool {
    insecure_proof_of_statement(A, e, messages).digest == proof.digest
}

/// Sign: A = (x+e)^(-1) * (G_0 + sum_j y_j M_j), plus NIZK over (A,e,M).
pub fn vka_mac<R: RngCore + CryptoRng>(
    rng: &mut R,
    sk: &SecretKey,
    params: &Params,
    messages: &[Point],
) -> Result<Signature, VkaError> {
    let l = params.G_vec.len();
    if messages.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: messages.len() });
    }
    if sk.y_vec.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: sk.y_vec.len() });
    }

    // Sample e such that x + e != 0
    let e = loop {
        let e_try = Scalar::rand(rng);
        if !(sk.x + e_try).is_zero() {
            break e_try;
        }
    };

    // S = G_0 + Σ y_j * M_j
    let mut S = params.pp_vka; // G_0
    for j in 0..l {
        S += smul(&messages[j], &sk.y_vec[j]);
    }

    // A = (x+e)^(-1) * S
    let inv = (sk.x + e).inverse().ok_or(VkaError::NonInvertible)?;
    let A = smul(&S, &inv);

    // TODO: proof
    // Placeholder proof
     let proof = insecure_proof_of_statement(&A, &e, messages);

    Ok(Signature { A, e, proof })
}

pub fn vka_present<R: RngCore + CryptoRng>(
    rng: &mut R,
    pk: &PublicKey,
    params: &Params,
    tau: &Signature,
    messages: &[Point],
) -> Result<PresentResult, VkaError> {
    let l = params.G_vec.len();
    if messages.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: messages.len() });
    }
    if pk.Y_vec.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: pk.Y_vec.len() });
    }

    // TODO: zkp verification
    // Verify NIZK (placeholder)
    if !insecure_verify_proof(&tau.A, &tau.e, messages, &tau.proof) {
        // In real code, return an error; for now we can keep it strict:
        return Err(VkaError::NonInvertible);
    }

    // r, xi_1..xi_l
    let r = Scalar::rand(rng);
    let mut xi_vec = Vec::with_capacity(l); // ξ
    for _ in 0..l {
        xi_vec.push(Scalar::rand(rng));
    }

    // C_j = M_j + xi_j * G_j
    let mut C_j_vec = Vec::with_capacity(l);
    for j in 0..l {
        let cj = messages[j] + smul(&params.G_vec[j], &xi_vec[j]);
        C_j_vec.push(cj);
    }

    // C_A = A + r * G
    let C_A = tau.A + smul(&params.G, &r);

    // T = rX - e C_A + (e r) G - Σ xi_j Y_j
    let mut T = smul(&pk.X, &r);         // rX
    T -= smul(&C_A, &tau.e);                   // - e C_A
    T += smul(&params.G, &(tau.e * r));        // + e r G
    for j in 0..l {
        T -= smul(&pk.Y_vec[j], &xi_vec[j]);       // - xi_j Y_j
    }

    Ok(PresentResult {
        vka_pres: VkaPres { C_A, T },
        C_j_vec: C_j_vec,
        xi_vec: xi_vec,
        witness_r: r,
        witness_e: tau.e,
    })
}


/// Predicate check (holder side):
/// Verify T == rX - e C_A + e r G - Σ xi_j Y_j
pub fn vka_predicate(
    pk: &PublicKey,
    params: &Params,
    vka_pres: &VkaPres,
    r: &Scalar,
    e: &Scalar,
    xi_vec: &[Scalar],
) -> Result<bool, VkaError> {
    let l = pk.Y_vec.len();
    if xi_vec.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: xi_vec.len() });
    }

    let mut rhs = smul(&pk.X, r);
    rhs -= smul(&vka_pres.C_A, e);
    rhs += smul(&params.G, &(*e * *r));
    for j in 0..l {
        rhs -= smul(&pk.Y_vec[j], &xi_vec[j]);
    }

    Ok(rhs == vka_pres.T)
}


/// Verify (issuer/MAC owner side):
/// Check: x C_A ?= G_0 + Σ y_j C_j + T
pub fn vka_verify(
    sk: &SecretKey,
    params: &Params,
    vka_pres: &VkaPres,
    C_j_vec: &[Point],
) -> Result<bool, VkaError> {
    let l = params.G_vec.len();
    if C_j_vec.len() != l || sk.y_vec.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: C_j_vec.len() });
    }

    let lhs = smul(&vka_pres.C_A, &sk.x); // x C_A

    // RHS = G_0 + Σ y_j C_j + T
    let mut rhs = params.pp_vka;
    for j in 0..l {
        rhs += smul(&C_j_vec[j], &sk.y_vec[j]);
    }
    rhs += vka_pres.T;

    Ok(lhs == rhs)
}


/// Verify MAC (issuer): (x+e) A == G_0 + sum_j y_j M_j
pub fn vka_verify_mac(
    sk: &SecretKey,
    params: &Params,
    tau: &Signature,
    messages: &[Point],
) -> Result<bool, VkaError> {
    let l = params.G_vec.len();
    if messages.len() != l || sk.y_vec.len() != l {
        return Err(VkaError::LengthMismatch { expected: l, got: messages.len() });
    }

    let lhs = smul(&tau.A, &(sk.x + tau.e));

    let mut rhs = params.pp_vka;
    for j in 0..l {
        rhs += smul(&messages[j], &sk.y_vec[j]);
    }

    Ok(lhs == rhs)
}


#[cfg(test)]
mod bbs_vka_tests {
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use crate::vka::bbs_vka::*;

    #[test]
    fn full_bbs_vka_flow_test() -> anyhow::Result<()> {
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
}
