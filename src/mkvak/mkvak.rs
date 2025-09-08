use ark_std::rand::{CryptoRng, RngCore};
use ark_std::UniformRand;
use crate::vka::bbs_vka::{
    smul, vka_keygen, vka_mac, vka_setup, Params as VkaParams, Point, Scalar, SecretKey as VkaSK,
    PublicKey as VkaPK, Signature as VkaSig, VkaError,
};


/// Public parameters for AKVAC
#[derive(Clone, Debug)]
pub struct PublicParams {
    /// Group base (G) carried from VKA params
    pub G: Point,
    /// Random presentation base H
    pub H: Point,
    /// VKA params with ℓ = n + 2; contains:
    ///   - pp_vka = G_0
    ///   - G_vec = [G_1..G_{n+2}]
    pub vka_params: VkaParams,
}

#[derive(thiserror::Error, Debug)]
pub enum AkvacError {
    #[error("length mismatch: expected {expected}, got {got}")]
    LengthMismatch { expected: usize, got: usize },
    #[error("VKA error: {0}")]
    Vka(#[from] VkaError),
}

/// AKVAC issuer key material
#[derive(Clone, Debug)]
pub struct IssuerSecret {
    pub vka_sk: VkaSK,
    pub e: Scalar,
}

#[derive(Clone, Debug)]
pub struct IssuerPublic {
    pub vka_pk: VkaPK,
    pub E: Point, // E = e * G
}

/// AKVAC verifier key material
#[derive(Clone, Debug)]
pub struct VerifierSecret {
    /// x_0..x_n
    pub x: Vec<Scalar>,
    /// ν
    pub v: Scalar,
}

#[derive(Clone, Debug)]
pub struct VerifierPublic {
    /// (X_1..X_n, X_0, Z_0)
    pub X_1_to_n: Vec<Point>,
    pub X_0: Point,
    pub Z_0: Point,
    /// τ (VKA MAC over X_1..X_n, X_0, Z_0)
    pub tau: VkaSig,
}

/// AKVAC.setup(λ, 1^n)
/// Internally sets ℓ = n + 2 for the underlying VKA.
pub fn akvac_setup<R: RngCore + CryptoRng>(rng: &mut R, n: usize) -> PublicParams {
    let l = n + 2;
    let vka_params = vka_setup(rng, l);

    // Sample H as a random multiple of G (prime-order group)
    let H = smul(&vka_params.G, &Scalar::rand(rng));

    PublicParams {
        G: vka_params.G,
        H: H,
        vka_params,
    }
}


/// AKVAC.issuerkg()
pub fn issuer_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
) -> (IssuerSecret, IssuerPublic) {
    let (vka_sk, vka_pk) = vka_keygen(rng, &pp.vka_params);

    let e = Scalar::rand(rng);
    let E = smul(&pp.G, &e);

    (
        IssuerSecret { vka_sk, e },
        IssuerPublic { vka_pk, E },
    )
}


/// AKVAC.verifierkg(isk, ipk)
/// Builds (X_1..X_n, X_0, Z_0) and requests a VKA MAC τ from the issuer.
pub fn verifier_keygen<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    isk: &IssuerSecret,
    ipk: &IssuerPublic,
) -> Result<(VerifierSecret, VerifierPublic), AkvacError> {
    // ℓ = n + 2  ⇒  n = ℓ - 2
    let l = pp.vka_params.G_vec.len();
    assert!(l >= 2, "VKA was not set with ℓ = n + 2");
    let n = l - 2;

    // Sample x_0..x_n, ν
    let mut x_vec = Vec::with_capacity(n + 1);
    for _ in 0..=n {
        x_vec.push(Scalar::rand(rng));
    }
    let v = Scalar::rand(rng);

    // Compute X_i = x_i * G for i=1..n
    let mut X_1_to_n = Vec::with_capacity(n);
    for i in 1..=n {
        X_1_to_n.push(smul(&pp.G, &x_vec[i]));
    }

    // Z_0 = ν G
    let Z_0 = smul(&pp.G, &v);

    // X_0 = x_0 G + ν E
    // let X_0 = smul(&pp.G, &x_vec[0]) + smul(&ipk.E, &Scalar::from(1u64)); // E already has e folded into it
    // let X_0 = X_0 + smul(&pp.G, &(v * isk.e)); // equivalently: x0*G + ν*(eG) = x0*G + (νe)*G
    let mut X_0 = smul(&pp.G, &x_vec[0]);
    X_0 += smul(&pp.G, &(v * isk.e)); // equivalently: x0*G + ν*(eG) = x0*G + (νe)*G


    // Assemble messages for VKA MAC in the order: (X_1..X_n, X_0, Z_0)
    let mut msgs = X_1_to_n.clone();
    msgs.push(X_0);
    msgs.push(Z_0);

    // Ask issuer to MAC (using issuer's VKA secret)
    let tau = vka_mac(rng, &isk.vka_sk, &pp.vka_params, &msgs)?;

    let vsk = VerifierSecret { x: x_vec, v: v };
    let vpk = VerifierPublic {
        X_1_to_n,
        X_0,
        Z_0,
        tau,
    };
    Ok((vsk, vpk))
}


#[cfg(test)]
mod akvac_tests {
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    use crate::mkvak::mkvak::{akvac_setup, issuer_keygen, verifier_keygen};

    #[test]
    fn akvac_setup_issuer_verifier_kg() -> anyhow::Result<()> {
        let mut rng = StdRng::seed_from_u64(7);
        let n = 3;

        let pp = akvac_setup(&mut rng, n);
        assert_eq!(pp.vka_params.G_vec.len(), n + 2);

        let (isk, ipk) = issuer_keygen(&mut rng, &pp);

        let (_vsk, vpk) = verifier_keygen(&mut rng, &pp, &isk, &ipk)?;
        // Tuple has n+2 points: X_1..X_n, X_0, Z_0
        assert_eq!(vpk.X_1_to_n.len(), n);

        Ok(())
    }
}