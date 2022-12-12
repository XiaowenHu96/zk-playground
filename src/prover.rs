/**
 * This file implements prover part for non-interactive use case.
 * The prover interacts only with a proofstream.
 */
use crate::algebra::{Domain, Polynomial};
use crate::setup::Setup;
use crate::stream::ProofStream;
use bls12_381::{G1Affine, G1Projective, Scalar};

// Prover proof unit for batch proof, open z on each of {P_i}
pub struct ProverProofUnit {
    pub z: Scalar,
    pub ps: Vec<Polynomial>,
}

macro_rules! prepare_multiple_poly_single_point_open{
    ($stream:ident, $y:ident) => {
        $stream.write_scalar($y);
    };

    ($stream:ident, $y:ident, do_not_send_y) => {
    };

    ($setup:ident, $stream:ident, $z:ident, $polys:ident) => {
        let gamma = $stream.prover_sample();
        let mut comm_q = G1Projective::identity();
        let divisor = Polynomial::new(vec![$z.neg(), Scalar::one()].into_iter());
        let mut tmp = Scalar::one();
        for poly in $polys {
            let y = poly.evalulate_at($z);
            $stream.write_scalar(y);
            let dividend = poly - Polynomial::new(vec![y].into_iter());
            let quotient = &dividend / &divisor;
            comm_q += $setup.commit(&quotient) * tmp;
            tmp *= gamma;
        }
        $stream.write_g1_affine(G1Affine::from(comm_q));
    };

    ($setup:ident, $stream:ident, $z:ident, [$( ($poly:expr $(,$commit:tt)? ) ),+]) => {
        let gamma = $stream.prover_sample();
        let mut comm_q = G1Projective::identity();
        let divisor = Polynomial::new(vec![$z.neg(), Scalar::one()].into_iter());
        let mut tmp = Scalar::one();
        $(
            let y = $poly.evalulate_at($z);
            prepare_multiple_poly_single_point_open!($stream, y $(,$commit)?);
            let dividend = $poly - Polynomial::new(vec![y].into_iter());
            let quotient = &dividend / &divisor;
            comm_q += $setup.commit(&quotient) * tmp;
            tmp *= gamma;
        )*
        $stream.write_g1_affine(G1Affine::from(comm_q));
    }
}

pub fn prove_multiple_poly_mulitple_points_open(
    setup: &Setup,
    stream: &mut ProofStream,
    units: &Vec<ProverProofUnit>,
) {
    for unit in units {
        let z = unit.z;
        let ps = &unit.ps;
        prepare_multiple_poly_single_point_open!(setup, stream, z, ps);
    }
}

// TODO: Caller should prepare sorted f_y and sorted t for performance
// This requires implementing ord for Scalar
// TODO: Waiting for yuncong's update on the protocol
pub fn prove_lookup(
    setup: &Setup,
    stream: &mut ProofStream,
    f: &Polynomial,
    f_y: &Vec<Scalar>,
    domain: &Domain,
    t: &Polynomial,
    t_y: &Vec<Scalar>,
) {
    let n = domain.size;
    let omega = domain.generator;
    assert!(t_y.len() == f_y.len());
    // construct s
    let mut s = t_y.clone();
    s.reserve(t_y.len() * 2);
    for v in f_y {
        for j in 0..s.len() {
            if s[j] == *v {
                s.insert(j, *v);
            } else {
                assert!(false, "FATAL: Not a subset.");
            }
        }
    }
    assert!(s.len() == t_y.len() * 2);
    let s1_y = s[0..s.len()].to_vec();
    let s2_y = s[s.len()..].to_vec();
    let s1 = domain.invert_fft_interpolate(&s1_y);
    let s2 = domain.invert_fft_interpolate(&s2_y);
    stream.write_g1_affine(G1Affine::from(setup.commit(&s1)));
    stream.write_g1_affine(G1Affine::from(setup.commit(&s2)));
    // sample alpha
    let alpha = stream.prover_sample();
    let alpha_p = Polynomial::new(vec![alpha].into_iter());
    let s1w = Polynomial::shift(&s1, omega);
    let s2w = Polynomial::shift(&s2, omega);
    let tw = Polynomial::shift(&t, omega);
    let mut dividend = Polynomial::new(vec![Scalar::zero(); n + 1].into_iter());
    dividend.coefficients[0] = Scalar::one().neg();
    dividend.coefficients[n] = Scalar::one();
    let n_scalar = Scalar::from(n as u64);
    let divisor = Polynomial::new(vec![n_scalar.neg(), n_scalar * omega].into_iter());
    let lambda = &divisor / &divisor; // TODO this is not correct, cannot divide
    let f1 = s1 + &alpha_p * (&s1w * (Polynomial::one() - &lambda)) + &s2w * &lambda;
    let f2 = s2 + &alpha_p * (&s2w * (Polynomial::one() - &lambda)) + &s1w * &lambda;
    let g1 = t + &alpha_p * tw;
    let g2 = (&alpha_p + Polynomial::one()) * f;
    let f1_y = domain.fft_eval(&f1.coefficients);
    let f2_y = domain.fft_eval(&f2.coefficients);
    let g1_y = domain.fft_eval(&g1.coefficients);
    let g2_y = domain.fft_eval(&g2.coefficients);

    prove_permutation_argument_2n(
        setup, stream, &f1, &f2, &g1, &g2, &f1_y, &f2_y, &g1_y, &g2_y, &domain,
    );
}

pub fn prove_permutation_argument_2n(
    setup: &Setup,
    stream: &mut ProofStream,
    f1: &Polynomial,
    f2: &Polynomial,
    g1: &Polynomial,
    g2: &Polynomial,
    f1_ys: &Vec<Scalar>,
    f2_ys: &Vec<Scalar>,
    g1_ys: &Vec<Scalar>,
    g2_ys: &Vec<Scalar>,
    domain: &Domain,
) {
    let omega = domain.generator;
    let n = domain.size;

    // sample gamma
    let gamma = stream.prover_sample();

    let mut rv = vec![];
    rv.push(
        (f1_ys[0] + gamma)
            * (f2_ys[0] + gamma)
            * ((g1_ys[0] + gamma) * (g2_ys[0] + gamma)).invert().unwrap(),
    );
    for i in 1..n {
        rv.push(
            rv[i - 1]
                * ((f1_ys[i] + gamma)
                    * (f2_ys[i] + gamma)
                    * ((g1_ys[i] + gamma) * (g2_ys[i] + gamma)).invert().unwrap()),
        )
    }
    let r = domain.invert_fft_interpolate(&rv);
    let r_prime = &(&r - Polynomial::one())
        / &Polynomial::new(vec![domain.invert_generator.neg(), Scalar::one()].into_iter());
    let gamma_p = Polynomial::new(vec![gamma].into_iter());
    let rw = Polynomial::shift(&r, omega);
    let f1w = Polynomial::shift(&f1, omega);
    let g1w = Polynomial::shift(&g1, omega);
    let f2w = Polynomial::shift(&f2, omega);
    let g2w = Polynomial::shift(&g2, omega);
    let dividend =
        (rw * (g1w + &gamma_p) * (g2w + &gamma_p)) - (r * (f1w + &gamma_p) * (f2w + &gamma_p));
    let mut divisor = Polynomial::new(vec![Scalar::zero(); n + 1].into_iter());
    divisor.coefficients[0] = Scalar::one().neg();
    divisor.coefficients[n] = Scalar::one();
    let q = &dividend / &divisor;
    let comm_r_prime = setup.commit(&r_prime);
    let comm_q = setup.commit(&q);
    stream.write_g1_affine(G1Affine::from(comm_r_prime));
    stream.write_g1_affine(G1Affine::from(comm_q));

    // sample z
    let z = stream.prover_sample();
    {
        // open zw at r_prime, f1, f2, g1, g2
        let z = omega * z;
        prepare_multiple_poly_single_point_open!(
            setup,
            stream,
            z,
            [(f1), (f2), (g1), (g2), (&r_prime)]
        );
    }

    {
        // open z at r_prime and q, but do not send q(z)
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(r_prime), (q, do_not_send_y)]);
    }
}

// generate proof to prove f(D) is a permutation of g(D)
pub fn prove_permutation_argument(
    setup: &Setup,
    stream: &mut ProofStream,
    f: &Polynomial,
    g: &Polynomial,
    f_ys: &Vec<Scalar>,
    g_ys: &Vec<Scalar>,
    domain: &Domain,
) {
    let omega = domain.generator;
    let n = domain.size;

    // sample gamma
    let gamma = stream.prover_sample();

    // prover computes r and r'
    // Note: simply abort if divide-by-zero happen
    let mut rv = vec![(f_ys[0] + gamma) * (g_ys[0] + gamma).invert().unwrap()];
    for i in 1..n {
        rv.push(rv[i - 1] * (f_ys[i] + gamma) * (g_ys[i] + gamma).invert().unwrap())
    }
    let r = domain.invert_fft_interpolate(&rv);
    let r_prime = &(&r - Polynomial::one())
        / &(Polynomial::new(vec![domain.invert_generator.neg(), Scalar::one()].into_iter()));
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

    {
        // f, g, and r_prime open at z * omega (y_fw, y_gw, y_rw)
        let z = omega * z;
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(f), (g), (&r_prime)]);
    }
    {
        // r_prime and q open at z (y_r and y_q)
        // NOTE: q needs special treament, we don't send result q(z) and let the verifier calcualtes it.
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(r_prime), (q, do_not_send_y)]);
    }
}
