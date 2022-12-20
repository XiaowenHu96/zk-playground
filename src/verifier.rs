/**
 * This file implements the verifier's part for non-interactive use case.
 * After prover send over the proofstream, the verifier can use it to verifiy the result.
 */
use crate::algebra::{rand_scalars, Domain};
use crate::setup::Setup;
use crate::stream::ProofStream;
use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, Scalar};

// Verifier proof unit for batch proof
// We only need z and the set of commitments of {P_i}
pub struct VerifierProofUnit {
    pub z: Scalar,
    pub comm_ps: Vec<G1Projective>,
}

macro_rules! prepare_single_poly_multiple_points_verify {
    ($setup:ident, $stream:ident, $z:ident, $comm_ps:ident) => {{
        let mut f = G1Projective::identity();
        let mut ys = vec![];
        // sample gamma
        let mut gamma = Scalar::one();
        let sample = $stream.verifier_sample();
        for comm_p in $comm_ps {
            let y = $stream.read_scalar();
            f += comm_p * gamma - $setup.tau_p[0] * (gamma * y);
            gamma *= sample;
            ys.push(y);
        }
        // return F, W and ys
        (f, $stream.read_g1_affine(), ys)
    }};
}

// comm_t here should be the commitment of 8bits table
pub fn verify_range_proof_16bits(
    setup: &Setup,
    stream: &mut ProofStream,
    comm_f: G1Projective,
    comm_t: G1Projective,
    domain: &Domain,
) -> bool {
    let comm_h = stream.read_g1_projective();
    // check higher bits
    assert!(verify_lookup(&setup, stream, comm_h, comm_t, domain) == true);

    // check lower bits:
    let omega = domain.generator;
    let n = domain.size;
    // read s1 and s2
    let comm_s1 = stream.read_g1_projective();
    let comm_s2 = stream.read_g1_projective();
    // sample alhpa
    let alpha = stream.verifier_sample();

    // sample gamma
    let gamma = stream.verifier_sample();
    let comm_r_prime = stream.read_g1_projective();
    let comm_q = stream.read_g1_affine();
    // sample z
    let z = stream.verifier_sample();

    let mut sum_f = G1Projective::identity();
    let mut lhs_sum_w = G1Projective::identity();
    let mut rhs_sum_w = G1Projective::identity();
    let mut r = rand_scalars(3);
    r[0] = Scalar::one();
    // zw^2 at s1 and t
    let comm_ps = vec![comm_s1, comm_t];
    let zww = z * omega * omega;
    let (f, w, ys) = prepare_single_poly_multiple_points_verify!(setup, stream, zww, comm_ps);
    let s1w = ys[0];
    let tw = ys[1];
    sum_f += f * r[0];
    lhs_sum_w += w * zww * r[0];
    rhs_sum_w += w * r[0];

    // zw at s1, s2, t, f, h, r_prime
    let comm_ps = vec![comm_s1, comm_s2, comm_t, comm_f, comm_h, comm_r_prime];
    let zw = z * omega;
    let (f, w, ys) = prepare_single_poly_multiple_points_verify!(setup, stream, zww, comm_ps);
    let s1z = ys[0];
    let s2z = ys[1];
    let tz = ys[2];
    let fz = ys[3] - Scalar::from((1 << 8) as u64) * ys[4];
    let rpz = ys[5];
    sum_f += f * r[1];
    lhs_sum_w += w * zw * r[1];
    rhs_sum_w += w * r[1];

    // z at r_prime and q
    let sample = stream.verifier_sample();
    let mut tmp = G1Projective::identity();
    let y_r = stream.read_scalar();
    let f1 = s1z + alpha * s2z;
    let f2 = s2z + alpha * s1w;
    let g1 = tz + alpha * tw;
    let g2 = (alpha + Scalar::one()) * fz;
    let y_q = (((rpz * (z * omega - domain.invert_generator)) + Scalar::one())
        * (g1 + gamma)
        * (g2 + gamma)
        - (y_r * (z - domain.invert_generator) + Scalar::one()) * (f1 + gamma) * (f2 + gamma))
        * (z.pow(&[n as u64, 0, 0, 0]) - Scalar::one())
            .invert()
            .unwrap();
    tmp += comm_r_prime - setup.tau_p[0] * y_r;
    tmp += comm_q * sample - setup.tau_p[0] * (y_q * sample);
    sum_f += tmp * r[2];
    let w = stream.read_g1_projective();
    lhs_sum_w += w * z * r[2];
    rhs_sum_w += w * r[2];

    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));
    lhs == rhs
}

pub fn verify_lookup(
    setup: &Setup,
    stream: &mut ProofStream,
    comm_f: G1Projective,
    comm_t: G1Projective,
    domain: &Domain,
) -> bool {
    let omega = domain.generator;
    let n = domain.size;
    // read s1 and s2
    let comm_s1 = stream.read_g1_projective();
    let comm_s2 = stream.read_g1_projective();
    // sample alhpa
    let alpha = stream.verifier_sample();

    // sample gamma
    let gamma = stream.verifier_sample();
    let comm_r_prime = stream.read_g1_projective();
    let comm_q = stream.read_g1_affine();
    // sample z
    let z = stream.verifier_sample();

    let mut sum_f = G1Projective::identity();
    let mut lhs_sum_w = G1Projective::identity();
    let mut rhs_sum_w = G1Projective::identity();
    let mut r = rand_scalars(3);
    r[0] = Scalar::one();
    // zw^2 at s1 and t
    let comm_ps = vec![comm_s1, comm_t];
    let zww = z * omega * omega;
    let (f, w, ys) = prepare_single_poly_multiple_points_verify!(setup, stream, zww, comm_ps);
    let s1w = ys[0];
    let tw = ys[1];
    sum_f += f * r[0];
    lhs_sum_w += w * zww * r[0];
    rhs_sum_w += w * r[0];

    // zw at s1, s2, t, f, r_prime
    let comm_ps = vec![comm_s1, comm_s2, comm_t, comm_f, comm_r_prime];
    let zw = z * omega;
    let (f, w, ys) = prepare_single_poly_multiple_points_verify!(setup, stream, zww, comm_ps);
    let s1z = ys[0];
    let s2z = ys[1];
    let tz = ys[2];
    let fz = ys[3];
    let rpz = ys[4];
    sum_f += f * r[1];
    lhs_sum_w += w * zw * r[1];
    rhs_sum_w += w * r[1];

    // z at r_prime and q
    let sample = stream.verifier_sample();
    let mut tmp = G1Projective::identity();
    let y_r = stream.read_scalar();
    let f1 = s1z + alpha * s2z;
    let f2 = s2z + alpha * s1w;
    let g1 = tz + alpha * tw;
    let g2 = (alpha + Scalar::one()) * fz;
    let y_q = (((rpz * (z * omega - domain.invert_generator)) + Scalar::one())
        * (g1 + gamma)
        * (g2 + gamma)
        - (y_r * (z - domain.invert_generator) + Scalar::one()) * (f1 + gamma) * (f2 + gamma))
        * (z.pow(&[n as u64, 0, 0, 0]) - Scalar::one())
            .invert()
            .unwrap();
    tmp += comm_r_prime - setup.tau_p[0] * y_r;
    tmp += comm_q * sample - setup.tau_p[0] * (y_q * sample);
    sum_f += tmp * r[2];
    let w = stream.read_g1_projective();
    lhs_sum_w += w * z * r[2];
    rhs_sum_w += w * r[2];

    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));
    lhs == rhs
}

pub fn verify_permutation_argument_2n(
    setup: &Setup,
    stream: &mut ProofStream,
    comm_f1: G1Projective,
    comm_f2: G1Projective,
    comm_g1: G1Projective,
    comm_g2: G1Projective,
    domain: &Domain,
) -> bool {
    let omega = domain.generator;
    let n = domain.size;
    // sample gamma
    let gamma = stream.verifier_sample();
    let comm_r_prime = stream.read_g1_projective();
    let comm_q = stream.read_g1_affine();
    // sample z
    let z = stream.verifier_sample();

    let mut sum_f = G1Projective::identity();
    let mut lhs_sum_w = G1Projective::identity();
    let mut rhs_sum_w = G1Projective::identity();
    let mut r = rand_scalars(2);
    r[0] = Scalar::one();
    // Calculate F1, W1 (polynomial f1, f2, g1, g2, r_prime at zw)
    let comm_ps = vec![comm_f1, comm_f2, comm_g1, comm_g2, comm_r_prime];
    let zw = z * omega;
    let (f, w, ys) = prepare_single_poly_multiple_points_verify!(setup, stream, zw, comm_ps);
    sum_f += f * r[0];
    lhs_sum_w += w * zw * r[0];
    rhs_sum_w += w * r[0];

    // Calculate F2, W2 (polynomial r_prime and q at zw)
    // ys[0..4] = f1, f2, g1, g2, r_prime at zw
    let sample = stream.verifier_sample();
    let mut tmp = G1Projective::identity();
    let y_r = stream.read_scalar();
    let y_q = (((ys[4] * (z * omega - domain.invert_generator)) + Scalar::one())
        * (ys[2] + gamma)
        * (ys[3] + gamma)
        - (y_r * (z - domain.invert_generator) + Scalar::one())
            * (ys[0] + gamma)
            * (ys[1] + gamma))
        * (z.pow(&[n as u64, 0, 0, 0]) - Scalar::one())
            .invert()
            .unwrap();
    tmp += comm_r_prime - setup.tau_p[0] * y_r;
    tmp += comm_q * sample - setup.tau_p[0] * (y_q * sample);
    sum_f += tmp * r[1];
    let w = stream.read_g1_projective();
    lhs_sum_w += w * z * r[1];
    rhs_sum_w += w * r[1];

    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));
    lhs == rhs
}

pub fn verify_permutation_argument(
    setup: &Setup,
    stream: &mut ProofStream,
    comm_f: G1Projective,
    comm_g: G1Projective,
    domain: &Domain,
) -> bool {
    let omega = domain.generator;
    let n = domain.size;
    // sample gamma
    let gamma = stream.verifier_sample();
    let comm_r_prime = stream.read_g1_projective();
    let comm_q = stream.read_g1_affine();
    // sample z
    let z = stream.verifier_sample();

    let mut sum_f = G1Projective::identity();
    let mut lhs_sum_w = G1Projective::identity();
    let mut rhs_sum_w = G1Projective::identity();
    let mut r = rand_scalars(2);
    r[0] = Scalar::one();
    // Calculate F1, W1 (polynomial f, g, r_prime at zw)
    let comm_ps = vec![comm_f, comm_g, comm_r_prime];
    let zw = z * omega;
    let (f, w, ys) = prepare_single_poly_multiple_points_verify!(setup, stream, zw, comm_ps);
    sum_f += f * r[0];
    lhs_sum_w += w * zw * r[0];
    rhs_sum_w += w * r[0];
    // Calculate F2, W2 (polynomial r_prime and q at zw)
    let sample = stream.verifier_sample();
    let mut tmp = G1Projective::identity();
    // y_fw = ys[0] y_gw = ys[1] y_rw = ys[2]
    let y_r = stream.read_scalar();
    let y_q = (((ys[2] * (z * omega - domain.invert_generator)) + Scalar::one()) * (ys[1] + gamma)
        - (y_r * (z - domain.invert_generator) + Scalar::one()) * (ys[0] + gamma))
        * (z.pow(&[n as u64, 0, 0, 0]) - Scalar::one())
            .invert()
            .unwrap();
    tmp += comm_r_prime - setup.tau_p[0] * y_r;
    tmp += comm_q * sample - setup.tau_p[0] * (y_q * sample);
    sum_f += tmp * r[1];
    let w = stream.read_g1_projective();
    lhs_sum_w += w * z * r[1];
    rhs_sum_w += w * r[1];

    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));
    lhs == rhs
}

pub fn verify_multiple_poly_mulitple_points_open(
    setup: &Setup,
    stream: &mut ProofStream,
    units: &Vec<VerifierProofUnit>,
) -> (bool, Vec<Scalar>) {
    let mut sum_f = G1Projective::identity();
    let mut lhs_sum_w = G1Projective::identity();
    let mut rhs_sum_w = G1Projective::identity();
    let mut r = rand_scalars(units.len());
    r[0] = Scalar::one();
    let mut ys = vec![];
    for (idx, unit) in units.iter().enumerate() {
        let z = unit.z;
        let comm_ps = &unit.comm_ps;
        let (f, w, mut y) = prepare_single_poly_multiple_points_verify!(setup, stream, z, comm_ps);
        sum_f += f * r[idx];
        lhs_sum_w += w * z * r[idx];
        rhs_sum_w += w * r[idx];
        ys.append(&mut y);
    }

    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));

    (lhs == rhs, ys)
}
