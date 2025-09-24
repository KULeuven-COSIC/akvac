use ark_ff::{PrimeField, Zero};
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::UniformRand;
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use crate::mkvak::mkvak::{IssuerPublic, PublicParams};
use crate::vka::bbs_vka::{
    smul, vka_keygen, vka_mac, vka_setup, Params as VkaParams, Point, Scalar, SecretKey as VkaSK,
    PublicKey as VkaPK, Signature as VkaSig, VkaError,
};

const PROT_NAME_REQ: &[u8] = b"AKVAC-REQ";
const PROT_NAME_ISSUE: &[u8] = b"AKVAC-ISSUE";



/// Schnorr-style NIZK for AKVAC request (cmzcpzrec)
#[derive(Clone, Debug)]
pub struct ReqProof {
    pub c: Scalar,

    // responses
    pub s_s: Scalar,                  // for s
    pub s_attrs: Vec<Scalar>,         // for a_j, j=1..n
    pub s_xi_prime: Vec<Scalar>,      // for xi'_j = a_j * xi_j, j=1..n
    pub s_bar_x0: Scalar,             // for \bar x_0
    pub s_bar_nu: Scalar,             // for \bar \nu
    pub s_r: Scalar,                  // for r
    pub s_e: Scalar,                  // for e  (BBS signature scalar)
    pub s_xi: Vec<Scalar>,            // for xi_j, j=1..n+2  (from VKA present)
    pub s_eta: Scalar,                // for \eta
    pub s_prod: Scalar,               // for prod   = e * r
    pub s_prod_prime: Scalar,         // for prod'  = r * \eta

    // include ProdCom in the proof (part of the statement hash)
    pub prod_com: Point,              // eG + eta H
}

/// Schnorr-style NIZK for AKVAC issuance (cmzcpzissue)
#[derive(Clone, Debug)]
pub struct IssProof {
    pub c: Scalar,     // challenge
    pub s_e: Scalar,   // response for e
    pub s_u: Scalar,   // response for u
    pub s_prod: Scalar // response for prod = e * u
}





#[inline]
fn hash_to_scalar(bytes: &[u8]) -> Scalar {
    let d = Sha256::digest(bytes);
    Scalar::from_le_bytes_mod_order(&d)
}

fn hash_challenge_issue(
    // full public statement (binds everything used in T4):
    E: &Point,
    bar_U: &Point,
    bar_V: &Point,
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    // accepting announcement:
    t1: &Point,
    t2: &Point,
    t3: &Point,
    t4: &Point,
) -> Scalar {
    let mut buf = Vec::new();
    buf.extend_from_slice(PROT_NAME_ISSUE);

    // statement
    E.serialize_compressed(&mut buf).unwrap();
    bar_U.serialize_compressed(&mut buf).unwrap();
    bar_V.serialize_compressed(&mut buf).unwrap();
    bar_X0.serialize_compressed(&mut buf).unwrap();
    bar_Z0.serialize_compressed(&mut buf).unwrap();
    C_attr.serialize_compressed(&mut buf).unwrap();

    // announcement
    t1.serialize_compressed(&mut buf).unwrap();
    t2.serialize_compressed(&mut buf).unwrap();
    t3.serialize_compressed(&mut buf).unwrap();
    t4.serialize_compressed(&mut buf).unwrap();

    hash_to_scalar(&buf)
}

/// Prover for cmzcpzissue
/// Statement (public): (E, Ū, V̄, X̄0, Z̄0, C_attr)
/// Witness (secret):   (e, u), and we also include prod = e*u
pub fn nizk_prove_issue<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    E: &Point,
    bar_U: &Point,
    bar_V: &Point,
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    e: &Scalar,
    u: &Scalar,
) -> IssProof {
    // Witness value for the product:
    let prod = *e * *u;

    // a-values
    let a_e   = Scalar::rand(rng);
    let a_u   = Scalar::rand(rng);
    let a_prod= Scalar::rand(rng);

    // Announcement T = φ(a)
    // t1 = a_u G                    (corresponds to Ū)
    let t1 = smul(&pp.G, &a_u);
    // t2 = a_e G                    (corresponds to E)
    let t2 = smul(&pp.G, &a_e);
    // t3 = a_prod G - a_u E         (corresponds to 0)
    let t3 = smul(&pp.G, &a_prod) - smul(E, &a_u);
    // t4 = a_u*X̄0 - a_prod*Z̄0 + a_u*C_attr   (corresponds to V̄)
    let t4 = smul(bar_X0, &a_u) - smul(bar_Z0, &a_prod) + smul(C_attr, &a_u);

    // Challenge
    let c = hash_challenge_issue(E, bar_U, bar_V, bar_X0, bar_Z0, C_attr, &t1, &t2, &t3, &t4);

    // Responses
    let s_e    = a_e   + c * *e;
    let s_u    = a_u   + c * *u;
    let s_prod = a_prod+ c * prod;

    IssProof { c, s_e, s_u, s_prod }
}

/// Verifier for cmzcpzissue
pub fn nizk_verify_issue(
    pp: &PublicParams,
    E: &Point,
    bar_U: &Point,
    bar_V: &Point,
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    proof: &IssProof,
) -> bool {
    // Recompute accepting announcement U = φ(s) - c * S
    // Derived statement image S = (Ū, E, 0, V̄)
    // u1 = s_u G      - c*Ū
    let u1 = smul(&pp.G, &proof.s_u) - smul(bar_U, &proof.c);

    // u2 = s_e G      - c*E
    let u2 = smul(&pp.G, &proof.s_e) - smul(E, &proof.c);

    // u3 = s_prod G - s_u E    - c*0
    let u3 = smul(&pp.G, &proof.s_prod) - smul(E, &proof.s_u);

    // u4 = s_u*X̄0 - s_prod*Z̄0 + s_u*C_attr  - c*V̄
    let u4 = smul(bar_X0, &proof.s_u)
        - smul(bar_Z0, &proof.s_prod)
        + smul(C_attr, &proof.s_u)
        - smul(bar_V, &proof.c);

    // Challenge must match
    let c_prime = hash_challenge_issue(E, bar_U, bar_V, bar_X0, bar_Z0, C_attr, &u1, &u2, &u3, &u4);
    c_prime == proof.c
}

fn hash_challenge_req(
    // derived statement (6 group elements):
    s1: &Point, s2: &Point, s3: &Point, s4: &Point, s5: &Point, s6: &Point,
    // accepting announcement (6 group elements):
    t1: &Point, t2: &Point, t3: &Point, t4: &Point, t5: &Point, t6: &Point,
) -> Scalar {
    let mut buf = Vec::new();
    buf.extend_from_slice(PROT_NAME_REQ);

    // statement
    s1.serialize_compressed(&mut buf).unwrap();
    s2.serialize_compressed(&mut buf).unwrap();
    s3.serialize_compressed(&mut buf).unwrap();
    s4.serialize_compressed(&mut buf).unwrap();
    s5.serialize_compressed(&mut buf).unwrap();
    s6.serialize_compressed(&mut buf).unwrap();

    // announcement
    t1.serialize_compressed(&mut buf).unwrap();
    t2.serialize_compressed(&mut buf).unwrap();
    t3.serialize_compressed(&mut buf).unwrap();
    t4.serialize_compressed(&mut buf).unwrap();
    t5.serialize_compressed(&mut buf).unwrap();
    t6.serialize_compressed(&mut buf).unwrap();

    hash_to_scalar(&buf)
}

/// Prover for cmzcpzrec (request proof)
pub fn nizk_prove_req<R: RngCore + CryptoRng>(
    rng: &mut R,
    pp: &PublicParams,
    ipk: &IssuerPublic,                  // for E and (X, Y_j)
    params: &VkaParams,                  // for G, G_j
    // public statement inputs:
    vka_pres: &crate::vka::bbs_vka::VkaPres, // has C_A, T
    C_j_vec: &[Point],                   // C_1..C_{n+2}
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    // secret witness inputs:
    s: &Scalar,
    attrs: &[Scalar],                    // a_j, j=1..n
    bar_x0: &Scalar,
    bar_nu: &Scalar,
    r: &Scalar,
    e: &Scalar,                          // BBS signature e
    xi_vec: &[Scalar],                   // xi_1..xi_{n+2}
) -> ReqProof {
    let l = params.G_vec.len();                   // l = n + 2
    let n = l - 2;
    debug_assert_eq!(C_j_vec.len(), l);
    debug_assert_eq!(attrs.len(), n);
    debug_assert_eq!(xi_vec.len(), l);

    // prod commitments
    let eta = Scalar::rand(rng);
    let prod_com = smul(&pp.G, e) + smul(&pp.H, &eta);
    let prod = *e * *r;
    let prod_prime = *r * eta;

    // 1) randomizers (a-values)
    let a_s = Scalar::rand(rng);
    let a_attrs: Vec<Scalar>       = (0..n).map(|_| Scalar::rand(rng)).collect();
    let a_xi_prime: Vec<Scalar>    = (0..n).map(|_| Scalar::rand(rng)).collect();
    let a_bar_x0 = Scalar::rand(rng);
    let a_bar_nu = Scalar::rand(rng);
    let a_r = Scalar::rand(rng);
    let a_e = Scalar::rand(rng);
    let a_xi: Vec<Scalar>          = (0..l).map(|_| Scalar::rand(rng)).collect();
    let a_eta = Scalar::rand(rng);
    let a_prod = Scalar::rand(rng);
    let a_prod_prime = Scalar::rand(rng);

    // 2) announcement T = φ(a)
    // T1 = - a_xi_{n+1} G_{n+1} + a_bar_x0 G + a_bar_nu E
    let t1 = -smul(&params.G_vec[n], &a_xi[n]) + smul(&params.G, &a_bar_x0) + smul(&ipk.E, &a_bar_nu);
    // T2 = - a_xi_{n+2} G_{n+2} + a_bar_nu G
    let t2 = -smul(&params.G_vec[n+1], &a_xi[n+1]) + smul(&params.G, &a_bar_nu);
    // T3 = a_s G + sum_j a_j C_j - sum_j a_xi'_j G_j  (j in 1..n; our arrays are 0..n-1)
    let mut t3 = smul(&pp.G, &a_s);
    for j in 0..n {
        t3 += smul(&C_j_vec[j], &a_attrs[j]);
        t3 -= smul(&params.G_vec[j], &a_xi_prime[j]);
    }
    // T4 = a_r X - a_e C_A + a_prod G - sum_{j=1..l} a_xi_j Y_j
    let mut t4 = smul(&ipk.vka_pk.X, &a_r);
    t4 -= smul(&vka_pres.C_A, &a_e);
    t4 += smul(&pp.G, &a_prod);
    for j in 0..l {
        t4 -= smul(&ipk.vka_pk.Y_vec[j], &a_xi[j]);
    }
    // T5 = a_e G + a_eta H
    let t5 = smul(&pp.G, &a_e) + smul(&pp.H, &a_eta);
    // T6 = a_prod G + a_prod' H - a_r * ProdCom
    let t6 = smul(&pp.G, &a_prod) + smul(&pp.H, &a_prod_prime) - smul(&prod_com, &a_r);

    // 3) derive statement image S = (S1..S6)
    let s1 = *bar_X0 - C_j_vec[n];       // \bar X_0 - C_{n+1}
    let s2 = *bar_Z0 - C_j_vec[n+1];     // \bar Z_0 - C_{n+2}
    let s3 = *C_attr;                     // C_attr
    let s4 = vka_pres.T;                  // T
    let s5 = prod_com;                    // ProdCom = eG + eta H
    let s6 = Point::zero();               // 0

    // 4) FS challenge
    let c = hash_challenge_req(&s1, &s2, &s3, &s4, &s5, &s6, &t1, &t2, &t3, &t4, &t5, &t6);

    // 5) responses s = a + c * witness
    let s_s = a_s + c * *s;
    let mut s_attrs: Vec<Scalar> = Vec::with_capacity(n);
    let mut s_xi_prime: Vec<Scalar> = Vec::with_capacity(n);
    for j in 0..n {
        s_attrs.push(a_attrs[j] + c * attrs[j]);
        // xi'_j = a_j * xi_j  (witness value)
        let xi_prime_j = attrs[j] * xi_vec[j];
        s_xi_prime.push(a_xi_prime[j] + c * xi_prime_j);
    }
    let s_bar_x0 = a_bar_x0 + c * *bar_x0;
    let s_bar_nu = a_bar_nu + c * *bar_nu;
    let s_r = a_r + c * *r;
    let s_e = a_e + c * *e;

    let mut s_xi: Vec<Scalar> = Vec::with_capacity(l);
    for j in 0..l {
        s_xi.push(a_xi[j] + c * xi_vec[j]);
    }

    let s_eta = a_eta + c * eta;
    let s_prod = a_prod + c * prod;
    let s_prod_prime = a_prod_prime + c * prod_prime;

    ReqProof {
        c,
        s_s,
        s_attrs,
        s_xi_prime,
        s_bar_x0,
        s_bar_nu,
        s_r,
        s_e,
        s_xi,
        s_eta,
        s_prod,
        s_prod_prime,
        prod_com,
    }
}


/// Verifier for cmzcpzrec
pub fn nizk_verify_req(
    pp: &PublicParams,
    ipk: &IssuerPublic,
    params: &VkaParams,
    vka_pres: &crate::vka::bbs_vka::VkaPres,
    C_j_vec: &[Point],
    bar_X0: &Point,
    bar_Z0: &Point,
    C_attr: &Point,
    proof: &ReqProof,
) -> bool {
    let l = params.G_vec.len();
    let n = l - 2;
    if C_j_vec.len() != l { return false; }
    if proof.s_attrs.len() != n || proof.s_xi_prime.len() != n || proof.s_xi.len() != l { return false; }

    // Statement image S
    let s1 = *bar_X0 - C_j_vec[n];
    let s2 = *bar_Z0 - C_j_vec[n+1];
    let s3 = *C_attr;
    let s4 = vka_pres.T;
    let s5 = proof.prod_com;
    let s6 = Point::zero();

    // φ(s) - c S  (component-wise)
    // U1 = - s_xi_{n+1} G_{n+1} + s_bar_x0 G + s_bar_nu E  - c*s1
    let mut u1 = -smul(&params.G_vec[n], &proof.s_xi[n]);
    u1 += smul(&params.G, &proof.s_bar_x0);
    u1 += smul(&ipk.E, &proof.s_bar_nu);
    u1 -= smul(&s1, &proof.c);

    // U2 = - s_xi_{n+2} G_{n+2} + s_bar_nu G  - c*s2
    let mut u2 = -smul(&params.G_vec[n+1], &proof.s_xi[n+1]);
    u2 += smul(&params.G, &proof.s_bar_nu);
    u2 -= smul(&s2, &proof.c);

    // U3 = s_s G + Σ s_attrs_j C_j - Σ s_xi'_j G_j  - c*s3
    let mut u3 = smul(&pp.G, &proof.s_s);
    for j in 0..n {
        u3 += smul(&C_j_vec[j], &proof.s_attrs[j]);
        u3 -= smul(&params.G_vec[j], &proof.s_xi_prime[j]);
    }
    u3 -= smul(&s3, &proof.c);

    // U4 = s_r X - s_e C_A + s_prod G - Σ s_xi_j Y_j  - c*s4
    let mut u4 = smul(&ipk.vka_pk.X, &proof.s_r);
    u4 -= smul(&vka_pres.C_A, &proof.s_e);
    u4 += smul(&pp.G, &proof.s_prod);
    for j in 0..l {
        u4 -= smul(&ipk.vka_pk.Y_vec[j], &proof.s_xi[j]);
    }
    u4 -= smul(&s4, &proof.c);

    // U5 = s_e G + s_eta H  - c*s5
    let mut u5 = smul(&pp.G, &proof.s_e) + smul(&pp.H, &proof.s_eta);
    u5 -= smul(&s5, &proof.c);

    // U6 = s_prod G + s_prod' H - s_r * ProdCom  - c*s6 (s6=0)
    let u6 = smul(&pp.G, &proof.s_prod) + smul(&pp.H, &proof.s_prod_prime) - smul(&proof.prod_com, &proof.s_r);

    // Recompute challenge
    let c_prime = hash_challenge_req(&s1, &s2, &s3, &s4, &s5, &s6, &u1, &u2, &u3, &u4, &u5, &u6);
    c_prime == proof.c
}

