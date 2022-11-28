use bls12_381::{pairing, G1Affine, G1Projective, G2Affine, G2Projective, Scalar};
use rand::prelude::*;
// TODO: difference between a Scalar over Fp and Fr value?
// Ref: https://github.com/ralexstokes/kzg

/**
 * Polynomial representation
 * [a_0, a_1, ..., a_n] -> y = a_0x^0 + a_1x^1 + ... + a_nx^n
 */
#[derive(Debug)]
pub struct Polynomial {
    pub coefficients: Vec<Scalar>,
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
        if self.degree() == -1 || other.degree() == -1 {
            return true;
        }
        if self.degree() != other.degree() {
            return false;
        }
        for i in 0..self.degree() + 1 {
            if self.coefficients[i as usize] != other.coefficients[i as usize] {
                return false;
            }
        }
        return true;
    }
}

impl Polynomial {
    pub fn evalulate_at(self: &Self, point: Scalar) -> Scalar {
        let mut sum = self.coefficients[0].clone();
        let mut powers = point.clone();

        for coefficient in self.coefficients.iter().skip(1) {
            let term = *coefficient * powers;
            sum += term;
            powers *= point;
        }
        sum
    }

    pub fn degree(self: &Self) -> isize {
        for i in (0..self.coefficients.len()).rev() {
            if self.coefficients[i] != Scalar::zero() {
                return i as isize;
            }
        }
        // define zero polynomial (coefficients = [] / [0, 0,...,0]) to have degree -1.
        return -1;
    }

    pub fn new(coefficients: impl Iterator<Item = Scalar>) -> Self {
        Self {
            coefficients: coefficients.collect(),
        }
    }
}

// See long-division: https://mathworld.wolfram.com/LongDivision.html
// Remainder is not returned here as it is not important to our use case.
fn polynomial_divide(dividend: &Polynomial, divisor: &Polynomial) -> Polynomial {
    let mut res_coeffs: Vec<Scalar> = vec![];
    let mut dividend_coeffs = dividend.coefficients.clone();

    // Note our polynomial representation starts from lower order.
    let divisor_pos = divisor.degree();
    assert!(divisor_pos >= 0, "Divisor cannot be a zero polynomial");
    let mut dividend_pos = dividend.degree();
    let mut pos = dividend_pos - divisor_pos;
    while pos >= 0 {
        let quotient = dividend_coeffs[dividend_pos as usize]
            * divisor.coefficients[divisor_pos as usize].invert().unwrap();
        res_coeffs.push(quotient);

        for i in (0..divisor_pos as usize).rev() {
            let x = divisor.coefficients[i] * quotient;
            dividend_coeffs[pos as usize + i] -= x;
        }

        dividend_pos -= 1;
        pos -= 1;
    }
    res_coeffs.reverse();
    Polynomial::new(res_coeffs.into_iter())
}

// Prover get tau_p = \sum_{i}{\tau^i * G1}
// Verifier get tau_v = tau * G2
struct Setup {
    pub tau_p: Vec<G1Projective>,
    pub tau_v: G2Projective,
}

impl Setup {
    pub fn new(degree: usize) -> Self {
        let mut rng = SmallRng::seed_from_u64(20221128);

        let mut secret = [0u8; 32];
        // TODO: why Scalar::from_bytes() can fail, i.e. what is non-canonical input?
        // TODO later: current solution is kind of stupid
        loop {
            rng.fill_bytes(&mut secret);
            let r = Scalar::from_bytes(&secret);
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
}

fn commit(setup: &Setup, polynomial: &Polynomial) -> G1Projective {
    let mut res = G1Projective::identity();
    for i in 0..polynomial.coefficients.len() as usize {
        res += setup.tau_p[i] * polynomial.coefficients[i]
    }
    res
}

// verify that p(z) = y by checking q(x) * (x - z)  = p(z) - y
fn verify_pairing(
    comm_p: &G1Projective,
    comm_q: &G1Projective,
    z: Scalar,
    y: Scalar,
    setup: &Setup,
) -> bool {
    let lhs = pairing(
        &G1Affine::from(comm_q),
        &G2Affine::from(setup.tau_v - G2Projective::generator() * z),
    );
    let rhs = pairing(
        &G1Affine::from(comm_p - G1Projective::generator() * y),
        &G2Affine::generator(),
    );
    return lhs == rhs;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval_polynomial() {
        let coefficients = vec![42, 1, 1, 0, 1].into_iter().map(Scalar::from);
        let point = Scalar::from(2);
        let result_in_fr = Polynomial::new(coefficients).evalulate_at(point);
        assert_eq!(result_in_fr, Scalar::from(64));
    }

    #[test]
    fn test_long_divide() {
        let dividend_coeffs = vec![6, 15, 14, 7, 2, 6, 3, 8, 3, 2]
            .into_iter()
            .map(Scalar::from);
        let dividend = Polynomial::new(dividend_coeffs);

        let divisor_coeffs = vec![6, 3, 2].into_iter().map(Scalar::from);
        let divisor = Polynomial::new(divisor_coeffs);

        let expect_coeffs = vec![1, 2, 1, 0, 0, 1, 0, 1].into_iter().map(Scalar::from);
        let expect_poly = Polynomial::new(expect_coeffs);

        let result_poly = polynomial_divide(&dividend, &divisor);
        assert_eq!(result_poly, expect_poly);
    }

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

        let comm_p = commit(&setup, &polynomial);
        let quotient = polynomial_divide(&dividend, &divisor);
        let comm_q = commit(&setup, &quotient);
        let res = verify_pairing(&comm_p, &comm_q, z_point, y_point, &setup);
        assert!(res == true);
    }
}

fn main() {
}
