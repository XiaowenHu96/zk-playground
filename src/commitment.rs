use crate::algebra::Polynomial;
use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use rand::prelude::*;

// Prover get tau_p = \sum_{i}{\tau^i * G1}
// Verifier get tau_v = tau * G2
struct Setup {
    pub tau_p: Vec<G1Projective>,
    pub tau_v: G2Projective,
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
        Self {
            tau_p,
            tau_v: G2Projective::generator() * tau,
        }
    }

    pub fn commit(&self, polynomial: &Polynomial) -> G1Projective {
        let mut res = G1Projective::identity();
        for i in 0..polynomial.coefficients.len() as usize {
            res += self.tau_p[i] * polynomial.coefficients[i]
        }
        res
    }

    // Verify p(z) = y by checking (comm_p - y) = (comm_q) * (x - z)
    pub fn verify_open_at(
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::Polynomial;

    #[test]
    fn test_commit() {
        let setup = Setup::new(10);
        let coefficients = vec![42, 1, 1, 0, 1].into_iter().map(Scalar::from);
        // p(x) = 42 + x + x^2 + x^4
        let polynomial = Polynomial::new(coefficients);
        // the point to open at, so f = (x-2) should divides p_hat = p(x)-64
        let z_point = Scalar::from(2);
        // the expected value at z: prove p(2) = 64
        let y_point = Scalar::from(64);

        let mut divisor = Polynomial::new(vec![2, 1].into_iter().map(Scalar::from));
        divisor.coefficients[0] = divisor.coefficients[0].neg(); //TODO ugly hack?
        let mut dividend = Polynomial::new(polynomial.coefficients.clone().into_iter());
        dividend.coefficients[0] = dividend.coefficients[0] + Scalar::from(64).neg();

        let comm_p = setup.commit(&polynomial);
        let quotient = &dividend / &divisor;
        let comm_q = setup.commit(&quotient);
        let res = setup.verify_open_at(&comm_p, &comm_q, z_point, y_point);
        assert!(res == true);
    }
}
