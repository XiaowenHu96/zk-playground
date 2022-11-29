use bls12_381::Scalar;
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
        for i in 0..=self.degree() as usize {
            if self.coefficients[i] != other.coefficients[i] {
                return false;
            }
        }
        return true;
    }
}

impl Polynomial {
    pub fn new(coefficients: impl Iterator<Item = Scalar>) -> Self {
        Self {
            coefficients: coefficients.collect(),
        }
    }

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

    // See long-division: https://mathworld.wolfram.com/LongDivision.html
    // Remainder is not returned here as it is not important to our use case.
    pub fn find_quotient(dividend: &Polynomial, divisor: &Polynomial) -> Polynomial {
        let mut res_coeffs: Vec<Scalar> = vec![];
        let mut dividend_coeffs = dividend.coefficients.clone();

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
}

// A domain for fast evalulation of polynomials using root of unity
pub struct Domain {
    pub generator: Scalar,
    pub invert_generator: Scalar,
    pub log_size: u32,
    pub size: usize,
    pub invert_size: Scalar,
}

impl Domain {
    pub fn new(degree: usize) -> Domain {
        let padded_size = degree.next_power_of_two();
        let log_size = padded_size.trailing_zeros(); // n in log^{n}_2
        let mut generator = bls12_381::ROOT_OF_UNITY;
        // calcualte w^{2^{log_size}}
        for _ in log_size..32 {
            generator = generator.square();
        }
        Self {
            generator,
            invert_generator: generator.invert().unwrap(),
            log_size,
            size: padded_size,
            invert_size: Scalar::from(padded_size as u64).invert().unwrap(),
        }
    }

    pub fn fft(&self, sequence: &mut Vec<Scalar>) {
        assert!(sequence.len() <= (1 << self.log_size));
        // pad sequence with zeros so that it has len which is a power of two
        sequence.resize(self.size, Scalar::zero());
        *sequence = actual_fft(self.generator, sequence)
    }

    // Fast interpolation with inverse Fast Fourier Transform
    // Input must be points from domain D
    pub fn invert_fft(&self, sequence: &mut Vec<Scalar>) {
        assert!(sequence.len() <= (1 << self.log_size));
        // pad sequence with zeros so that it has len which is a power of two
        sequence.resize(self.size, Scalar::zero());
        *sequence = actual_fft(self.invert_generator, sequence);
        for i in sequence {
            *i *= self.invert_size
        }
    }
}

// Number Theory Transform, a more general name is Fast Fourier Transform.
// It calculates the list of values of P(x) evalulate at the domian defined
// on some primitive root. I.e:
// Given D={w^0, w^1, w^2, ..., w^(2^k)}, compute (P(1), P(w^1), P(w^2), ...)
// TODO: Should transform in-place
fn actual_fft(omega: Scalar, sequence: &Vec<Scalar>) -> Vec<Scalar> {
    let x = sequence.len();
    if x <= 1 {
        return sequence.clone();
    }
    assert!(
        (x & (x - 1)) == 0,
        "sequence must have a power-of-two coeffs (fix by padding zeros)"
    );

    let even = actual_fft(
        omega.square(),
        &(sequence.clone().into_iter().step_by(2).collect()),
    );
    let odd = actual_fft(
        omega.square(),
        &(sequence.clone().into_iter().skip(1).step_by(2).collect()),
    );

    // merging results
    let mut res = vec![];
    let mut tmp = Scalar::one();
    for i in 0..x {
        res.push(even[i % (x / 2)] + tmp * odd[i % (x / 2)]);
        tmp *= omega;
    }
    return res;
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;

    #[test]
    fn test_eval_polynomial() {
        let coefficients = vec![42, 1, 1, 0, 1].into_iter().map(Scalar::from);
        let point = Scalar::from(2);
        let result_in_fr = Polynomial::new(coefficients).evalulate_at(point);
        assert_eq!(result_in_fr, Scalar::from(64));
    }

    #[test]
    fn test_find_quotient() {
        let dividend_coeffs = vec![6, 15, 14, 7, 2, 6, 3, 8, 3, 2]
            .into_iter()
            .map(Scalar::from);
        let dividend = Polynomial::new(dividend_coeffs);

        let divisor_coeffs = vec![6, 3, 2].into_iter().map(Scalar::from);
        let divisor = Polynomial::new(divisor_coeffs);

        let expect_coeffs = vec![1, 2, 1, 0, 0, 1, 0, 1].into_iter().map(Scalar::from);
        let expect_poly = Polynomial::new(expect_coeffs);

        let result_poly = Polynomial::find_quotient(&dividend, &divisor);
        assert_eq!(result_poly, expect_poly);
    }

    #[test]
    fn test_root_of_unity() {
        let mut t = bls12_381::ROOT_OF_UNITY;
        for _ in 0..32 {
            t = t.square();
        }
        assert_eq!(t, Scalar::one());
    }

    #[test]
    fn test_fft() {
        // generate a random coeffs with degree 64
        let mut rng = thread_rng();
        let mut coeffs = vec![];
        for _ in 0..64 {
            coeffs.push(Scalar::from(rng.gen::<u64>()));
        }

        // fft
        let domain = Domain::new(coeffs.len());
        let mut fft_values = coeffs.clone();
        domain.fft(&mut fft_values);

        // naive solution
        let poly = Polynomial::new(coeffs.clone().into_iter());
        let mut naive_values = vec![];
        let mut tmp = Scalar::one();
        for _ in 0..poly.coefficients.len() {
            naive_values.push(poly.evalulate_at(tmp));
            tmp *= domain.generator;
        }
        assert_eq!(
            Polynomial::new(fft_values.into_iter()),
            Polynomial::new(naive_values.into_iter())
        );
    }

    #[test]
    fn test_invert_fft() {
        // generate a random coeffs with degree 32 < d <=  64
        let mut rng = thread_rng();
        let mut coeffs = vec![];
        for _ in 0..(rng.gen::<i32>() % 32 + 32) {
            coeffs.push(Scalar::from(rng.gen::<u64>()));
        }
        // fft result
        let domain = Domain::new(coeffs.len());
        let mut fft_values = coeffs.clone();
        domain.fft(&mut fft_values);
        // invert_fft result, using fft_values
        let mut invert_fft = fft_values.clone();
        domain.invert_fft(&mut invert_fft);

        assert_eq!(
            Polynomial::new(coeffs.into_iter()),
            Polynomial::new(invert_fft.into_iter())
        );
    }
}
