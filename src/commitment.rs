use crate::algebra::Polynomial;
use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use rand::prelude::*;

// Prover get tau_p = \sum_{i}{\tau^i * G1}
// Verifier get tau_v = tau * G2
struct Setup {
    pub tau_p: Vec<G1Projective>,
    pub tau_v: G2Projective,
    // TODO: So that I can do commitment on G2 (for single poly multiple points)
    // Ask yuncong whether it is necessary
    tau_vs: Vec<G2Projective>,
}

impl Setup {
    pub fn new(degree: usize) -> Self {
        let mut rng = thread_rng();

        let mut secret = [0u8; 32];
        loop {
            rng.fill_bytes(&mut secret);
            let r = Scalar::from_bytes(&secret);
            // until get a value that is smaller than MODULUS
            if r.is_some().into() {
                break;
            }
        }
        let tau = Scalar::from_bytes(&secret).unwrap();

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
        y: Vec<Scalar>,
    ) -> bool {
        let p_y = y
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra;
    use crate::algebra::Polynomial;

    #[test]
    fn test_single_poly_single_open() {
        let setup = Setup::new(32);
        let coeffs = algebra::rand_scalars(32);
        let poly = Polynomial::new(coeffs.into_iter());
        let z_point = algebra::rand_scalars(1)[0];
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
        let z_point = algebra::rand_scalars(1)[0];
        let mut polys = vec![];
        let mut y_points = vec![];
        for i in 0..8 {
            polys.push(Polynomial::new(algebra::rand_scalars(32).into_iter()));
            y_points.push(polys[i].evalulate_at(z_point));
        }

        // Prover work:
        let mut dividend = Polynomial::zero();
        for i in 0..y_points.len() {
            // TODO add xx-assign operator
            dividend = &dividend + &(&polys[i] - &Polynomial::new(vec![y_points[i]].into_iter()));
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
