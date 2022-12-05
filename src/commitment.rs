use crate::algebra;
use crate::algebra::Polynomial;
use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Gt, Scalar};
use rand::prelude::*;

// Prover get tau_p = {\tau^i * G1}
// Verifier get tau_v = tau * G2
pub struct Setup {
    pub tau_p: Vec<G1Projective>,
    pub tau_v: G2Projective,
    // Do NOT use, this is So that I can play with commitment on G2 (for single poly multiple points)
    tau_vs: Vec<G2Projective>,
}

// A single batch proof contains prover work for
// z and a set of Polynomial {P_i, y_i}
pub struct BatchProof {
    comm_ps: Vec<G1Projective>,
    comm_q: G1Projective,
    ys: Vec<Scalar>,
    z: Scalar,
}

impl Setup {
    pub fn new(degree: usize) -> Self {
        let tau = algebra::rand_scalar();

        let mut tau_p: Vec<G1Projective> = vec![];
        let mut tmp = Scalar::one();
        let g1 = G1Projective::generator();
        for _ in 0..degree {
            tau_p.push(g1 * tmp);
            tmp *= tau;
        }

        let mut tau_vs: Vec<G2Projective> = vec![];
        let g2 = G2Projective::generator();
        let mut tmp = Scalar::one();
        for _ in 0..degree {
            tau_vs.push(g2 * tmp);
            tmp *= tau;
        }
        Self {
            tau_p,
            tau_v: G2Projective::generator() * tau,
            tau_vs,
        }
    }

    pub fn commit(&self, polynomial: &Polynomial) -> G1Projective {
        let mut res = G1Projective::identity();
        for i in 0..=polynomial.degree() as usize {
            res += self.tau_p[i] * polynomial.coefficients[i]
        }
        res
    }

    // Do NOT use, this is So that I can play with commitment on G2 (for single poly multiple points)
    pub fn commit_g2(&self, polynomial: &Polynomial) -> G2Projective {
        let mut res = G2Projective::identity();
        for i in 0..=polynomial.degree() as usize {
            res += self.tau_vs[i] * polynomial.coefficients[i]
        }
        res
    }

    // Verify p(z) = y by checking (comm_p - y) = (comm_q) * (x - z)
    pub fn verify_single_poly_single_open(
        &self,
        comm_p: &G1Projective,
        comm_q: &G1Projective,
        z: Scalar,
        y: Scalar,
    ) -> bool {
        let lhs = pairing(
            &G1Affine::from(comm_q),
            &G2Affine::from(self.tau_v - G2Projective::generator() * z),
        );
        let rhs = pairing(
            &G1Affine::from(comm_p - G1Projective::generator() * y),
            &G2Affine::generator(),
        );
        return lhs == rhs;
    }

    // Verify p([z_i]) = [y_i]
    // This uses a commitment over G2, which is not recommended
    // (why? Performance? Security?)
    // For a work around, use multiple_poly_mulitple_points_open()
    pub fn verify_single_poly_multiple_open(
        &self,
        comm_p: &G1Projective,
        comm_q: &G1Projective,
        z: Vec<Scalar>,
        y: Vec<Scalar>,
    ) -> bool {
        // interpolate I(x) on ([z, y])
        let i = Polynomial::fast_interpolate(&z, &y);
        // TODO: double-check with yuncong that this is correct.
        // Can verifier leave the computation of comm_i to prover?
        let comm_i = self.commit(&i);
        // compute commitment of zerofier on G2
        let zerofier = Polynomial::fast_zerofier(z.as_slice());
        let comm_z = self.commit_g2(&zerofier);
        let lhs = pairing(&G1Affine::from(comm_q), &G2Affine::from(comm_z));
        let rhs = pairing(&G1Affine::from(comm_p - comm_i), &G2Affine::generator());
        return lhs == rhs;
    }

    // Verify that [p_i(z)] = [y_i]
    pub fn verify_multiple_poly_single_open(
        &self,
        comm_p: &G1Projective,
        comm_q: &G1Projective,
        z: Scalar,
        ys: Vec<Scalar>,
    ) -> bool {
        let p_y = ys
            .into_iter()
            .map(|y| G1Projective::generator() * y)
            .collect::<Vec<_>>();
        let mut sum_p_y = G1Projective::identity();
        for y in p_y {
            sum_p_y += y;
        }
        let lhs = pairing(
            &G1Affine::from(comm_q),
            &G2Affine::from(self.tau_v - G2Projective::generator() * z),
        );
        let rhs = pairing(&G1Affine::from(comm_p - sum_p_y), &G2Affine::generator());
        return lhs == rhs;
    }

    // For {(zi, (P_ij, y_ij)}, check P_ij(zi) = y_ij
    // TODO missing random factor
    pub fn verify_multiple_poly_mulitple_points_open(&self, proves: Vec<BatchProof>) -> bool {
        let mut sum_f = G1Projective::identity();
        let mut lhs_sum_w = G1Projective::identity();
        let mut rhs_sum_w = G1Projective::identity();
        for prove in &proves {
            lhs_sum_w += prove.comm_q * prove.z;
            rhs_sum_w += prove.comm_q;
            let cm_ys: G1Projective = self.tau_p[0] * prove.ys.iter().sum::<Scalar>();
            sum_f += prove.comm_ps.iter().sum::<G1Projective>() - cm_ys;
        }
        let lhs = pairing(&G1Affine::from(sum_f + lhs_sum_w), &G2Affine::generator());
        let rhs = pairing(&G1Affine::from(rhs_sum_w), &G2Affine::from(self.tau_v));

        lhs == rhs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_permutation_argument() {
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
        let omega = d.generator;
        // san check
        assert_eq!(domain[0], Scalar::one());
        assert_eq!(domain[degree - 1] * omega, Scalar::one());
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

        //
        // Protocol start
        //
        let setup = Setup::new(degree);

        // Prover binds f and g
        let comm_f = setup.commit(&f);
        let comm_g = setup.commit(&g);

        // Verifier sends gamma
        let gamma = algebra::rand_scalar();

        // Prover Computes r
        // Note: simply abort if divide-by-zero happen
        let mut rv = vec![(f_ys[0] + gamma) * (g_ys[0] + gamma).invert().unwrap()];
        for i in 1..degree {
            rv.push(rv[i - 1] * (f_ys[i] + gamma) * (g_ys[i] + gamma).invert().unwrap())
        }
        let r = Polynomial::fast_interpolate(&domain, &rv);
        // san check
        assert_eq!(r.evalulate_at(domain[degree - 1]), Scalar::one());

        // Prove computes r'
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

        // Verifier sends z
        let z = algebra::rand_scalar();

        // Prover computes z over r_prime_w, fw, gw and r'
        let z_r_prime_w = r_prime_w.evalulate_at(z);
        let z_fw = fw.evalulate_at(z);
        let z_gw = gw.evalulate_at(z);
        let z_r_prime = r_prime.evalulate_at(z);
        // TODO: Here for each point, opening check should be performed.
        // I ommit it for now since we don't have proper generalized interface
        // for point-opening check, this will be a lot of code.

        // san check r and r_prime
        assert_eq!(
            r.evalulate_at(z),
            z_r_prime * (z - domain[degree - 1]) + Scalar::one()
        );
        // san check rw and r_prime_w
        assert_eq!(
            rw.evalulate_at(z),
            z_r_prime_w * (z * omega - domain[degree - 1]) + Scalar::one()
        );

        // Verifier compute the expected y
        let y = (((z_r_prime_w * (z * omega - domain[degree - 1])) + Scalar::one())
            * (z_gw + gamma)
            - (z_r_prime * (z - domain[degree - 1]) + Scalar::one()) * (z_fw + gamma))
            * (z.pow(&[degree as u64, 0, 0, 0]) - Scalar::one())
                .invert()
                .unwrap();

        // open q(z) = y
        // Prove computes q' = (q - q(y)) / (x - z)
        let q_prime = &(&quotient - Polynomial::new(vec![quotient.evalulate_at(z)].into_iter()))
            / &(Polynomial::new(vec![z.neg(), Scalar::one()].into_iter()));
        let comm_q_prime = setup.commit(&q_prime);

        // Final verification
        let res = setup.verify_single_poly_single_open(&comm_q, &comm_q_prime, z, y);
        assert!(res == true);
    }

    #[test]
    fn test_multiple_poly_mulitple_points_open() {
        let setup = Setup::new(16);
        // generate 4 points each corresponds to 8 polynomials
        // So there are 4 proofs in total.
        let z_points = algebra::rand_scalars(4);
        let mut proofs = vec![];
        for z in &z_points {
            let mut y_points = vec![];
            let mut comm_ps = vec![];
            let mut comm_q = G1Projective::identity();
            for _ in 0..8 {
                let poly = Polynomial::new(algebra::rand_scalars(16).into_iter());
                let y_point: Scalar;
                comm_ps.push(setup.commit(&poly));
                y_point = poly.evalulate_at(*z);
                let dividend = &poly - &Polynomial::new(vec![y_point].into_iter());
                let divisor = Polynomial::new(vec![z.neg(), Scalar::one()].into_iter());
                let quotient = &dividend / &divisor;
                comm_q += setup.commit(&quotient);
                y_points.push(y_point);
            }
            proofs.push(BatchProof {
                comm_ps,
                comm_q,
                ys: y_points,
                z: *z,
            })
        }
        // verifier work:
        let res = setup.verify_multiple_poly_mulitple_points_open(proofs);
        assert!(res == true);
    }

    #[test]
    fn test_single_poly_single_open() {
        let setup = Setup::new(32);
        let coeffs = algebra::rand_scalars(32);
        let poly = Polynomial::new(coeffs.into_iter());
        let z_point = algebra::rand_scalar();
        let y_point = poly.evalulate_at(z_point);
        // dividend = f(X) - y
        let dividend = &poly - &Polynomial::new(vec![y_point.neg()].into_iter());
        // divisor = (x-z)
        let divisor = Polynomial::new(vec![z_point.neg(), Scalar::one()].into_iter());

        // Prover work:
        let comm_p = setup.commit(&poly);
        let quotient = &dividend / &divisor;
        let comm_q = setup.commit(&quotient);

        // Verifier work:
        let res = setup.verify_single_poly_single_open(&comm_p, &comm_q, z_point, y_point);
        assert!(res == true);
    }

    #[test]
    fn test_single_poly_multiple_open() {
        let setup = Setup::new(32);
        let coeffs = algebra::rand_scalars(32);
        let poly = Polynomial::new(coeffs.into_iter());
        let z_points = algebra::rand_scalars(16);
        let y_points = Polynomial::fast_evalulate(&poly, &z_points);

        // Prover work:
        let zerofier = Polynomial::fast_zerofier(z_points.as_slice());
        let i = Polynomial::fast_interpolate(z_points.as_slice(), y_points.as_slice());
        let dividend = &poly - &i;
        let quotient = &dividend / &zerofier;
        let comm_p = setup.commit(&poly);
        let comm_q = setup.commit(&quotient);

        // Verifier work
        let res = setup.verify_single_poly_multiple_open(&comm_p, &comm_q, z_points, y_points);
        assert!(res == true);
    }

    #[test]
    fn test_multiply_poly_single_open() {
        let setup = Setup::new(32);
        let z_point = algebra::rand_scalar();
        let mut polys = vec![];
        let mut y_points = vec![];
        for i in 0..8 {
            polys.push(Polynomial::new(algebra::rand_scalars(32).into_iter()));
            y_points.push(polys[i].evalulate_at(z_point));
        }

        // Prover work:
        let mut dividend = Polynomial::zero();
        for i in 0..y_points.len() {
            dividend += &(&polys[i] - &Polynomial::new(vec![y_points[i]].into_iter()));
        }
        let divisor = Polynomial::new(vec![z_point.neg(), Scalar::one()].into_iter());
        let quotient = &dividend / &divisor;
        let comm_q = setup.commit(&quotient);
        let mut comm_p = G1Projective::identity();
        for p in &polys {
            comm_p += setup.commit(p);
        }

        // Verifier work
        let res = setup.verify_multiple_poly_single_open(&comm_p, &comm_q, z_point, y_points);
        assert!(res == true);
    }
}
