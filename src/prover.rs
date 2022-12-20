/**
 * This file implements prover part for non-interactive use case.
 * The prover interacts only with a proofstream.
 */
use crate::algebra::{Domain, Polynomial};
use crate::setup::Setup;
use crate::stream::ProofStream;
use bls12_381::{G1Affine, G1Projective, Scalar};
use std::collections::HashMap;

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

fn higher_8bits(v: &Scalar) -> Scalar {
    let mut res = [0; 32];
    res[0] = v.to_bytes()[1];
    Scalar::from_bytes(&res).unwrap()
}

// split into 2 8-bits lookup check
// t and t_y should be the 8-bits table (a global constant value)
pub fn prove_range_proof_16bits(
    setup: &Setup,
    stream: &mut ProofStream,
    f: &Polynomial,
    f_y: &Vec<Scalar>,
    t: &Polynomial,
    t_y: &Vec<Scalar>,
    domain: &Domain,
) {
    let omega = domain.generator;
    let n = domain.size;
    assert!(t_y.len() == f_y.len());

    // construct h (higher bits)
    let h_y = f_y.into_iter().map(|x| higher_8bits(x)).collect::<Vec<_>>();
    let h = domain.invert_fft_interpolate(&h_y);
    stream.write_g1_affine(G1Affine::from(setup.commit(&h)));

    // lookup for h, nothing special
    prove_lookup(&setup, stream, &h, &h_y, t, t_y, domain);

    // construct l by f - h
    let c = Scalar::from((1 << 8) as u64);
    let l_y = f_y
        .into_iter()
        .zip(&h_y)
        .map(|(a, b)| a - c * b)
        .collect::<Vec<_>>();
    let l = domain.invert_fft_interpolate(&l_y);

    // construct S
    let mut counter = HashMap::new();
    for v in l_y {
        let count = counter.entry(v.to_bytes()).or_insert(0);
        *count += 1;
    }
    let mut s = vec![];
    s.reserve_exact(t_y.len() * 2);
    for v in t_y {
        let n = counter.get(&v.to_bytes()).unwrap_or(&0);
        for _ in 0..n + 1 {
            s.push(v.clone());
        }
    }

    // construct s1 and s2
    let s1_y: Vec<Scalar> = s.clone().into_iter().step_by(2).collect();
    let s2_y: Vec<Scalar> = s.clone().into_iter().skip(1).step_by(2).collect();
    let s1 = domain.invert_fft_interpolate(&s1_y);
    let s2 = domain.invert_fft_interpolate(&s2_y);
    stream.write_g1_affine(G1Affine::from(setup.commit(&s1)));
    stream.write_g1_affine(G1Affine::from(setup.commit(&s2)));

    // sample alpha
    let alpha = stream.prover_sample();
    let as2 = Polynomial::scale(&s2, alpha);
    let s1w = Polynomial::shift(&s1, omega);
    let as1w = Polynomial::scale(&s1w, alpha);
    let tw = Polynomial::shift(&t, omega);
    let atw = Polynomial::scale(&tw, alpha);
    let f1 = &s1 + &as2;
    let f2 = &s2 + &as1w;
    let g1 = t + &atw;
    let g2 = Polynomial::scale(&l, alpha + Scalar::one());
    let f1_ys = domain.fft_eval(&f1.coefficients);
    let f2_ys = domain.fft_eval(&f2.coefficients);
    let g1_ys = domain.fft_eval(&g1.coefficients);
    let g2_ys = domain.fft_eval(&g2.coefficients);

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

    // The only change for range proof is that l is represented by f - h
    // so zw at [s1, s2, t, f, h, r_prime]
    
    // sample z
    let z = stream.prover_sample();
    {
        let z = omega * omega * z;
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(&s1), (t)]);
    }
    {
        let z = omega * z;
        prepare_multiple_poly_single_point_open!(
            setup,
            stream,
            z,
            [(s1), (s2), (t), (f), (h), (&r_prime)]
        );
    }
    {
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(r_prime), (q, do_not_send_y)]);
    }
}

// prove for every y \in f_y, we have y \in t_y.
pub fn prove_lookup(
    setup: &Setup,
    stream: &mut ProofStream,
    f: &Polynomial,
    f_y: &Vec<Scalar>,
    t: &Polynomial,
    t_y: &Vec<Scalar>,
    domain: &Domain,
) {
    let omega = domain.generator;
    let n = domain.size;
    assert!(t_y.len() == f_y.len());
    // construct S
    let mut counter = HashMap::new();
    for v in f_y {
        let count = counter.entry(v.to_bytes()).or_insert(0);
        *count += 1;
    }
    let mut s = vec![];
    s.reserve_exact(t_y.len() * 2);
    for v in t_y {
        let n = counter.get(&v.to_bytes()).unwrap_or(&0);
        for _ in 0..n + 1 {
            s.push(v.clone());
        }
    }

    // construct s1 and s2
    let s1_y: Vec<Scalar> = s.clone().into_iter().step_by(2).collect();
    let s2_y: Vec<Scalar> = s.clone().into_iter().skip(1).step_by(2).collect();
    let s1 = domain.invert_fft_interpolate(&s1_y);
    let s2 = domain.invert_fft_interpolate(&s2_y);
    stream.write_g1_affine(G1Affine::from(setup.commit(&s1)));
    stream.write_g1_affine(G1Affine::from(setup.commit(&s2)));

    // sample alpha
    let alpha = stream.prover_sample();
    let as2 = Polynomial::scale(&s2, alpha);
    let s1w = Polynomial::shift(&s1, omega);
    let as1w = Polynomial::scale(&s1w, alpha);
    let tw = Polynomial::shift(&t, omega);
    let atw = Polynomial::scale(&tw, alpha);
    let f1 = &s1 + &as2;
    let f2 = &s2 + &as1w;
    let g1 = t + &atw;
    let g2 = Polynomial::scale(f, alpha + Scalar::one());
    let f1_ys = domain.fft_eval(&f1.coefficients);
    let f2_ys = domain.fft_eval(&f2.coefficients);
    let g1_ys = domain.fft_eval(&g1.coefficients);
    let g2_ys = domain.fft_eval(&g2.coefficients);

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

    // Regular 2n permutation opens zw at [f1 f2 g1 g2 r_prime] and z at [r_prime, q]
    // for lookup, this is the same as open
    // zw^2 at [s1, t]
    // zw at [s1, s2, t, f, r_prime]
    // z at [r_prime, q]

    // sample z
    let z = stream.prover_sample();
    {
        let z = omega * omega * z;
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(&s1), (t)]);
    }
    {
        let z = omega * z;
        prepare_multiple_poly_single_point_open!(
            setup,
            stream,
            z,
            [(s1), (s2), (t), (f), (&r_prime)]
        );
    }
    {
        prepare_multiple_poly_single_point_open!(setup, stream, z, [(r_prime), (q, do_not_send_y)]);
    }
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
