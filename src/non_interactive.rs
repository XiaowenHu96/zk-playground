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
        let divisor = Polynomial::new(vec![unit.z.neg(), Scalar::one()].into_iter());
        for poly in &unit.ps {
            let y = poly.evalulate_at(unit.z);
            // bind polynomial and its result y
            stream.write_g1_affine(G1Affine::from(setup.commit(&poly)));
            stream.write_scalar(y);
            // calculate quotient
            let dividend = poly - &Polynomial::new(vec![y].into_iter());
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

// generate proof to prove f(D) is a permutation of g(D)
// Here I assume f_ys g_ys and domain are given, although it is not necessary
fn prove_permutation_argument(
    setup: &Setup,
    stream: &mut ProofStream,
    f: &Polynomial,
    g: &Polynomial,
    f_ys: &Vec<Scalar>,
    g_ys: &Vec<Scalar>,
    domain: &Vec<Scalar>,
) {
    let omega = domain[0];
    let n = domain.len();

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
    for i in 1..n {
        rv.push(rv[i - 1] * (f_ys[i] + gamma) * (g_ys[i] + gamma).invert().unwrap())
    }
    let r = Polynomial::fast_interpolate(&domain, &rv);
    let r_prime = &(&r - Polynomial::one())
        / &(Polynomial::new(vec![domain[n - 1].neg(), Scalar::one()].into_iter()));
    // Prove compute q, r_prime_w, fw, gw
    let gamma_p = Polynomial::new(vec![gamma].into_iter());
    let rw = Polynomial::shift(&r, omega);
    let fw = Polynomial::shift(&f, omega);
    let gw = Polynomial::shift(&g, omega);
    let dividend = (rw * (gw + &gamma_p)) - (r * (fw + &gamma_p));
    let mut divisor = Polynomial::new(vec![Scalar::zero(); n + 1].into_iter());
    divisor.coefficients[0] = Scalar::one().neg();
    divisor.coefficients[n] = Scalar::one();
    let q = &dividend / &divisor;
    // Prover binds r' and q
    let comm_r_prime = setup.commit(&r_prime);
    let comm_q = setup.commit(&q);
    stream.write_g1_affine(G1Affine::from(comm_r_prime));
    stream.write_g1_affine(G1Affine::from(comm_q));

    // sample z
    let z = stream.prover_sample();

    // NOTE: it might seem convenient to reuse multiple_poly_multiple_open() here to
    // generate the proof.
    // However, since f, g, r_prime, and q were already commited into the stream
    // Generating another proof and resending commitments is a huge waste of resource.
    // So code reuse is NOT OK here. we should hand write the protocol.

    // y_fw, y_gw, y_rw
    // f, g, and r_prime open at z * omega
    {
        let ps = vec![f, g, &r_prime];
        let z = omega * z;
        let mut quotients = vec![];
        let divisor = Polynomial::new(vec![z.neg(), Scalar::one()].into_iter());
        for poly in &ps {
            let y = poly.evalulate_at(z);
            stream.write_scalar(y);
            // calcualte quotient
            let dividend = *poly - Polynomial::new(vec![y].into_iter());
            quotients.push(&dividend / &divisor);
        }
        // sample gamma
        let mut gamma = Scalar::one();
        let sample = stream.prover_sample();
        let mut comm_q = G1Projective::identity();
        for i in 0..ps.len() {
            comm_q += setup.commit(&quotients[i]) * gamma;
            gamma *= sample
        }
        stream.write_g1_affine(G1Affine::from(comm_q));
    }
    // y_r, y_q
    // r_prime and q open at z
    // NOTE: q needs special treament, we don't send result q(z) and let the verifier calcualtes it.
    {
        // r_prime
        let divisor = Polynomial::new(vec![z.neg(), Scalar::one()].into_iter());
        let y = r_prime.evalulate_at(z);
        stream.write_scalar(y);
        let dividend = r_prime - &Polynomial::new(vec![y].into_iter());
        let q1 = &dividend / &divisor;

        // q
        let y = q.evalulate_at(z);
        let dividend = q - &Polynomial::new(vec![y].into_iter());
        let q2 = &dividend / &divisor;

        // sample gamma
        let sample = stream.prover_sample();
        let mut comm_q = G1Projective::identity();
        comm_q += setup.commit(&q1);
        comm_q += setup.commit(&q2) * sample;
        stream.write_g1_affine(G1Affine::from(comm_q));
    }
}

fn verify_permutation_argument(
    setup: &Setup,
    stream: &mut ProofStream,
    domain: &Vec<Scalar>,
) -> bool {
    let omega = domain[0];
    let n = domain.len();
    let comm_f = stream.read_g1_affine();
    let comm_g = stream.read_g1_affine();
    // sample gamma
    let gamma_zero = stream.verifier_sample();
    let comm_r_prime = stream.read_g1_affine();
    let comm_q = stream.read_g1_affine();
    // sample z
    let z = stream.verifier_sample();

    let mut sum_f = G1Projective::identity();
    let mut lhs_sum_w = G1Projective::identity();
    let mut rhs_sum_w = G1Projective::identity();
    let mut r = rand_scalars(2);
    r[0] = Scalar::one();
    // Calculate F1, W1 (polynomial f, g and r_prime at z*omega)
    let mut y = vec![];
    {
        let comm_ps = vec![comm_f, comm_g, comm_r_prime];
        for _ in 0..comm_ps.len() {
            y.push(stream.read_scalar());
        }
        // sample gamma
        let mut gamma = Scalar::one();
        let sample = stream.verifier_sample();
        let mut tmp = G1Projective::identity();
        for i in 0..comm_ps.len() {
            tmp += comm_ps[i] * gamma - setup.tau_p[0] * (gamma * y[i]);
            gamma *= sample;
        }
        sum_f += tmp * r[0];
        let w = stream.read_g1_projective();
        lhs_sum_w += w * (omega * z);
        rhs_sum_w += w;
    }
    // Calculate F2, W2 (polynomial r_prime and q at z)
    {
        // y_fw = y[0]
        // y_gw = y[1]
        // y_rw = y[2]
        let y_r = stream.read_scalar();
        let y_q = (((y[2] * (z * omega - domain[n - 1])) + Scalar::one()) * (y[1] + gamma_zero)
            - (y_r * (z - domain[n - 1]) + Scalar::one()) * (y[0] + gamma_zero))
            * (z.pow(&[n as u64, 0, 0, 0]) - Scalar::one())
                .invert()
                .unwrap();
        // sample gamma
        let sample = stream.verifier_sample();
        let mut tmp = G1Projective::identity();
        tmp += comm_r_prime - setup.tau_p[0] * y_r;
        tmp += comm_q * sample - setup.tau_p[0] * (y_q * sample);
        sum_f += tmp * r[0];
        let w = stream.read_g1_projective();
        lhs_sum_w += w * z * r[1];
        rhs_sum_w += w * r[1];
    }
    let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
    let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(setup.tau_v));
    lhs == rhs
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
        let degree = 32;
        let mut rng = thread_rng();
        // generate domain
        let d = algebra::Domain::new(degree);
        let mut domain = vec![];
        let mut v = Scalar::one();
        for _ in 0..degree {
            domain.push(v);
            v = v * d.generator;
        }
        // generate random polynomial f with degree 32
        let f = Polynomial::new(algebra::rand_scalars(degree).into_iter());
        // calculate f over d
        let f_ys = Polynomial::fast_evalulate(&f, &domain);
        let mut g_ys = f_ys.clone();
        // shuffle values
        g_ys.shuffle(&mut rng);
        // produce g
        let g = Polynomial::fast_interpolate(&domain, &g_ys);
        // Now we have f, g with f(D) and g(D) being permutation of each other

        let setup = Setup::new(degree);
        let mut stream = ProofStream::new();
        // prover work
        prove_permutation_argument(&setup, &mut stream, &f, &g, &f_ys, &g_ys, &domain);
        // Verifier work
        verify_permutation_argument(&setup, &mut stream, &domain);
    }

    #[test]
    fn test_negative_permutation_argument() {
        let degree = 32;
        // generate domain
        let d = algebra::Domain::new(degree);
        let mut domain = vec![];
        let mut v = Scalar::one();
        for _ in 0..degree {
            domain.push(v);
            v = v * d.generator;
        }
        // generate random polynomial f with degree 32
        let f = Polynomial::new(algebra::rand_scalars(degree).into_iter());
        // calculate f over d
        let f_ys = Polynomial::fast_evalulate(&f, &domain);
        let g = Polynomial::new(algebra::rand_scalars(degree).into_iter());
        let g_ys = Polynomial::fast_evalulate(&g, &domain);

        let setup = Setup::new(degree);
        let mut stream = ProofStream::new();
        // prover work
        prove_permutation_argument(&setup, &mut stream, &f, &g, &f_ys, &g_ys, &domain);
        // Verifier work
        verify_permutation_argument(&setup, &mut stream, &domain);
    }
}
