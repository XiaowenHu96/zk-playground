/**
 * This file implements prover part for non-interactive use case.
 * The prover interacts only with a proofstream.
 */

use crate::algebra::Polynomial;
use crate::setup::Setup;
use crate::stream::ProofStream;
use bls12_381::{G1Affine, G1Projective, Scalar};

// Prover proof unit for batch proof, open z on each of {P_i}
pub struct ProverProofUnit {
    pub z: Scalar,
    pub ps: Vec<Polynomial>,
}

macro_rules! prepare_single_poly_multiple_points_prove{
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
            prepare_single_poly_multiple_points_prove!($stream, y $(,$commit)?);
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
        prepare_single_poly_multiple_points_prove!(setup, stream, z, ps);
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
    domain: &Vec<Scalar>,
) {
    let omega = domain[1];
    let n = domain.len();

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

    {
        // f, g, and r_prime open at z * omega (y_fw, y_gw, y_rw)
        let z = omega * z;
        prepare_single_poly_multiple_points_prove!(setup, stream, z, [(f), (g), (&r_prime)]);
    }
    {
        // r_prime and q open at z (y_r and y_q)
        // NOTE: q needs special treament, we don't send result q(z) and let the verifier calcualtes it.
        prepare_single_poly_multiple_points_prove!(
            setup,
            stream,
            z,
            [(r_prime), (q, do_not_send_y)]
        );
    }
}
