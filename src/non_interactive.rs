use crate::algebra::{rand_scalars, Domain, Polynomial};
use crate::commitment::Setup;
use crate::stream::ProofStream;
use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Gt, Scalar};

// A single proof unit, to open z on each of {P_i}
pub struct ProverProofUnit {
    z: Scalar,
    ps: Vec<Polynomial>,
}

// Verifier only needs z and number of polynomials
pub struct VerifierProofUnit(Scalar, usize);

impl From<ProverProofUnit> for VerifierProofUnit {
    fn from(val: ProverProofUnit) -> VerifierProofUnit {
        VerifierProofUnit(val.z, val.ps.len())
    }
}

fn prove_multiple_poly_mulitple_points_open(
    setup: &Setup,
    stream: &mut ProofStream,
    units: &Vec<ProverProofUnit>,
) {
    for unit in units {
        let mut quotients = vec![];
        for poly in &unit.ps {
            let y = poly.evalulate_at(unit.z);
            // bind polynomial and its result y
            stream.write_g1_affine(G1Affine::from(setup.commit(&poly)));
            stream.write_scalar(y);
            // calculate quotient
            let dividend = poly - &Polynomial::new(vec![y].into_iter());
            let divisor = Polynomial::new(vec![unit.z.neg(), Scalar::one()].into_iter());
            quotients.push(&dividend / &divisor);
        }
        // sample gamma
        let mut gamma = Scalar::one();
        let sample = stream.prover_sample();
        // calculate sum of quotient and its commit (w)
        let mut comm_q = G1Projective::identity();
        for i in 0..unit.ps.len() {
            comm_q += setup.commit(&quotients[i]) * gamma;
            gamma *= sample
        }
        stream.write_g1_affine(G1Affine::from(comm_q));
    }
}

// generate proof to prove f_ys is a permutation of g_ys
fn prove_permutation_argument(
    setup: &Setup,
    stream: &mut ProofStream,
    mut f_ys: Vec<Scalar>,
    mut g_ys: Vec<Scalar>,
) {
    // Preparation
    let degree = f_ys.len().next_power_of_two();
    // make sure f and g are length of power of 2
    f_ys.resize(degree, Scalar::zero());
    g_ys.resize(degree, Scalar::zero());

    let d = Domain::new(degree);
    let mut domain = vec![];
    let mut v = Scalar::one();
    for _ in 0..degree {
        domain.push(v);
        v = v * d.generator;
    }
    let omega = d.generator;

    // interpolate f and g such that they evaluate to f_ys and g_ys over domain D
    let mut f_tmp = f_ys.clone();
    d.invert_fft(&mut f_tmp);
    let mut g_tmp = g_ys.clone();
    d.invert_fft(&mut g_tmp);
    let f = Polynomial::new(f_tmp.into_iter());
    let g = Polynomial::new(g_tmp.into_iter());

    //
    // Start the proof
    //

    // binds f and g
    let comm_f = setup.commit(&f);
    let comm_g = setup.commit(&g);
    stream.write_g1_affine(G1Affine::from(comm_f));
    stream.write_g1_affine(G1Affine::from(comm_g));

    // sample gamma
    let gamma = stream.prover_sample();

    // prover computes r and r'
    // Note: simply abort if divide-by-zero happen
    let mut rv = vec![(f_ys[0] + gamma) * (g_ys[0] + gamma).invert().unwrap()];
    for i in 1..degree {
        rv.push(rv[i - 1] * (f_ys[i] + gamma) * (g_ys[i] + gamma).invert().unwrap())
    }
    let r = Polynomial::fast_interpolate(&domain, &rv);
    let r_prime = &(&r - Polynomial::one())
        / &(Polynomial::new(vec![domain[degree - 1].neg(), Scalar::one()].into_iter()));
    // Prove compute q, r_prime_w, fw, gw
    let gamma_p = Polynomial::new(vec![gamma].into_iter());
    let r_prime_w = Polynomial::shift(&r_prime, omega);
    let rw = Polynomial::shift(&r, omega);
    let fw = Polynomial::shift(&f, omega);
    let gw = Polynomial::shift(&g, omega);
    let dividend = (&rw * (&gw + &gamma_p)) - (&r * (&fw + &gamma_p));
    let mut divisor = Polynomial::new(vec![Scalar::zero(); degree + 1].into_iter());
    divisor.coefficients[0] = Scalar::one().neg();
    divisor.coefficients[degree] = Scalar::one();
    let quotient = &dividend / &divisor;
    // Prover binds r' and q
    let comm_r_prime = setup.commit(&r_prime);
    let comm_q = setup.commit(&quotient);
    stream.write_g1_affine(G1Affine::from(comm_r_prime));
    stream.write_g1_affine(G1Affine::from(comm_q));

    // sample z
    let z = stream.prover_sample();
    // generate open proof on z over polynomials: r_prime_w, fw, gw r_prime and quotient
    // NOTE: from yuncong's note, the result of quotient(z) does not need to be sent
    // This can save us some space over the stream (48bytes)
    // However, doing so requires a customized protocol
    // (where the first four results are sent and only the result of quotient(z) is omitted)
    // This is too much code and I do not consider it ATM.
    let proof = vec![ProverProofUnit {
        z,
        ps: vec![r_prime_w, fw, gw, r_prime, quotient],
    }];
    prove_multiple_poly_mulitple_points_open(setup, stream, &proof);
}

fn verify_permutation_argument(setup: &Setup, stream: &mut ProofStream, degree: usize) -> bool {
    let d = Domain::new(degree);
    let mut domain = vec![];
    let mut v = Scalar::one();
    for _ in 0..degree {
        domain.push(v);
        v = v * d.generator;
    }
    let omega = d.generator;
    stream.read_g1_affine();
    stream.read_g1_affine();
    // sample gamma
    let gamma = stream.verifier_sample();
    stream.read_g1_affine();
    stream.read_g1_affine();
    // sample z
    let z = stream.verifier_sample();
    let vproofs = vec![VerifierProofUnit(z, 5)];
    let (res, vals) = verify_multiple_poly_mulitple_points_open(&setup, stream, &vproofs);
    if !res {
        return false;
    }
    let z_r_prime_w = vals[0];
    let z_fw = vals[1];
    let z_gw = vals[2];
    let z_r_prime = vals[3];
    let z_quotient = vals[4];
    z_quotient
        == (((z_r_prime_w * (z * omega - domain[degree - 1])) + Scalar::one()) * (z_gw + gamma)
            - (z_r_prime * (z - domain[degree - 1]) + Scalar::one()) * (z_fw + gamma))
            * (z.pow(&[degree as u64, 0, 0, 0]) - Scalar::one())
                .invert()
                .unwrap()
}

fn verify_multiple_poly_mulitple_points_open(
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
        let mut y = vec![];
        let mut comm_ps = vec![];
        for _ in 0..unit.1 {
            comm_ps.push(stream.read_g1_affine());
            y.push(stream.read_scalar());
        }
        // sample gamma
        let mut gamma = Scalar::one();
        let sample = stream.verifier_sample();
        // calculate sum_f
        let mut tmp = G1Projective::identity();
        for i in 0..unit.1 {
            tmp += comm_ps[i] * gamma - setup.tau_p[0] * (gamma * y[i]);
            gamma *= sample;
        }
        sum_f += tmp * r[idx];
        let w = stream.read_g1_projective();
        lhs_sum_w += w * unit.0 * r[idx];
        rhs_sum_w += w * r[idx];
        ys.append(&mut y);
    }

    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));

    (lhs == rhs, ys)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra;
    use rand::prelude::*;

    #[test]
    fn test_multiple_poly_mulitple_points_open() {
        let setup = Setup::new(16);
        // generate 4 points each corresponds to 8 polynomials
        // So there are 4 proofs in total.
        let z_points = algebra::rand_scalars(4);
        let mut proofs = vec![];
        for z in &z_points {
            let mut polys = vec![];
            for _ in 0..8 {
                polys.push(Polynomial::new(algebra::rand_scalars(16).into_iter()));
            }
            proofs.push(ProverProofUnit { z: *z, ps: polys })
        }
        let mut stream = ProofStream::new();
        // prover work:
        prove_multiple_poly_mulitple_points_open(&setup, &mut stream, &proofs);
        // verifier work:
        let vproofs = proofs
            .into_iter()
            .map(|x| VerifierProofUnit::from(x))
            .collect::<Vec<_>>();
        let (res, _) = verify_multiple_poly_mulitple_points_open(&setup, &mut stream, &vproofs);
        assert_eq!(res, true);
    }

    #[test]
    fn test_positive_permutation_argument() {
        let mut rng = thread_rng();
        // degree 16 < d <= 32
        let len = 17 + rng.gen::<usize>() % 16;
        // f_ys
        let f_ys = rand_scalars(len);
        let mut g_ys = f_ys.clone();
        g_ys.shuffle(&mut rng);

        let mut stream = ProofStream::new();
        let setup = Setup::new(32);
        // prover work
        prove_permutation_argument(&setup, &mut stream, f_ys, g_ys);
        // verifier work
        let res = verify_permutation_argument(&setup, &mut stream, len.next_power_of_two());
        assert_eq!(res, true);
    }

    #[test]
    fn test_negative_permutation_argument() {
        let mut rng = thread_rng();
        // degree 16 < d <= 32
        let len = 17 + rng.gen::<usize>() % 16;
        // f_ys != g_ys
        let f_ys = rand_scalars(len);
        let g_ys = rand_scalars(len);

        let mut stream = ProofStream::new();
        let setup = Setup::new(32);
        // prover work
        prove_permutation_argument(&setup, &mut stream, f_ys, g_ys);
        // verifier work
        let res = verify_permutation_argument(&setup, &mut stream, len.next_power_of_two());
        assert_eq!(res, false);
    }
}
