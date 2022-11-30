use bls12_381::Scalar;
use rand::prelude::*;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};
/**
 * Polynomial representation
 * [a_0, a_1, ..., a_n] -> y = a_0x^0 + a_1x^1 + ... + a_nx^n
 */
#[derive(Debug, Clone)]
pub struct Polynomial {
    pub coefficients: Vec<Scalar>,
}

impl PartialEq for Polynomial {
    fn eq(&self, other: &Self) -> bool {
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

impl<'a, 'b> Div<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;
    fn div(self, other: &'b Polynomial) -> Polynomial {
        let (q, _) = Polynomial::divide(self, other);
        return q;
    }
}

impl<'a, 'b> Rem<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;
    fn rem(self, other: &'b Polynomial) -> Polynomial {
        let (_, rem) = Polynomial::divide(self, other);
        return rem;
    }
}

impl<'a> Neg for &'a Polynomial {
    type Output = Polynomial;
    fn neg(self) -> Self::Output {
        let coeffs: Vec<Scalar> = self
            .coefficients
            .clone()
            .iter_mut()
            .map(|x| x.neg())
            .collect();
        Polynomial::new(coeffs.into_iter())
    }
}

impl<'a, 'b> Add<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;
    fn add(self, other: &'b Polynomial) -> Polynomial {
        if self.degree() < 0 {
            return other.clone();
        }
        if other.degree() < 0 {
            return self.clone();
        }
        if self.degree() >= other.degree() {
            let mut result = self.clone();
            for (a, b) in result.coefficients.iter_mut().zip(&other.coefficients) {
                *a += b;
            }
            return result;
        } else {
            let mut result = other.clone();
            for (a, b) in result.coefficients.iter_mut().zip(&self.coefficients) {
                *a += b;
            }
            return result;
        }
    }
}

impl<'a, 'b> Sub<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;
    fn sub(self, other: &'b Polynomial) -> Polynomial {
        self + (&other.neg())
    }
}

// Note: This is naive multiplication
impl<'a, 'b> Mul<&'b Polynomial> for &'a Polynomial {
    type Output = Polynomial;
    fn mul(self, other: &'b Polynomial) -> Polynomial {
        if self.degree() < 0 || other.degree() < 0 {
            return Polynomial::zero();
        }
        let mut res = vec![Scalar::zero(); 1 + (self.degree() + other.degree()) as usize];
        for i in 0..=self.degree() as usize {
            for j in 0..=other.degree() as usize {
                res[i + j] += self.coefficients[i] * other.coefficients[j];
            }
        }
        Polynomial::new(res.into_iter())
    }
}

impl Polynomial {
    pub fn new(coefficients: impl Iterator<Item = Scalar>) -> Self {
        Self {
            coefficients: coefficients.collect(),
        }
    }

    fn zero() -> Self {
        Polynomial::new(vec![].into_iter())
    }

    fn one() -> Self {
        Polynomial::new(vec![Scalar::one()].into_iter())
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
    pub fn divide(dividend: &Polynomial, divisor: &Polynomial) -> (Polynomial, Polynomial) {
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

            for i in (0..=divisor_pos as usize).rev() {
                let x = divisor.coefficients[i] * quotient;
                dividend_coeffs[pos as usize + i] -= x;
            }

            dividend_pos -= 1;
            pos -= 1;
        }
        res_coeffs.reverse();
        // dividend_coeffs.reverse();
        // Quotient, Remainder
        (
            Polynomial::new(res_coeffs.into_iter()),
            Polynomial::new(dividend_coeffs.into_iter()),
        )
    }

    // Fast multiplication using FFT
    // TODO: threshold to fallback to regular multiplication
    pub fn fast_multiply(lhs: &Polynomial, rhs: &Polynomial) -> Polynomial {
        if lhs.degree() < 0 || rhs.degree() < 0 {
            return Polynomial::zero();
        }

        let final_degree = lhs.degree() + rhs.degree() + 1;
        let domain = Domain::new(final_degree as usize);
        let mut lhs_fft = lhs.coefficients.clone();
        let mut rhs_fft = rhs.coefficients.clone();
        domain.fft(&mut lhs_fft);
        domain.fft(&mut rhs_fft);

        let mut point_products = vec![];
        for i in 0..lhs_fft.len() {
            point_products.push(lhs_fft[i] * rhs_fft[i]);
        }
        domain.invert_fft(&mut point_products);

        return Polynomial::new(point_products.into_iter());
    }

    // Fast zerofier produces a polynomial that
    // evalulates to zero at the given set of points
    pub fn fast_zerofier(points: &[Scalar]) -> Polynomial {
        if points.len() == 0 {
            return Polynomial::one();
        }
        if points.len() == 1 {
            return Polynomial::new(vec![points[0].neg(), Scalar::one()].into_iter());
        }
        let lhs = Polynomial::fast_zerofier(&points[..points.len() / 2]);
        let rhs = Polynomial::fast_zerofier(&points[points.len() / 2..]);
        Polynomial::fast_multiply(&lhs, &rhs)
    }

    // Fast Evalulate by using zerofiler (Saw that in Anatomy of Stark)
    //
    // Basic idea is that, to evaluate f(x) on x_1,
    // write f(x) as p(x) = (x-x_1)P(x) + R(x)
    // Where P(x) R(X) are the quotient and remainder of f(x) / (x-x_1)
    // Clearly, if we want to evaluate f(x_1), it is the same as evaluate R(x_1)
    pub fn fast_evalulate(&self, points: &[Scalar]) -> Vec<Scalar> {
        if points.len() == 0 {
            return vec![];
        }
        if points.len() == 1 {
            return vec![self.evalulate_at(points[0])];
        }

        let left_zerofier = Polynomial::fast_zerofier(&points[..points.len() / 2]);
        let right_zerofier = Polynomial::fast_zerofier(&points[points.len() / 2..]);
        let left_poly = self % &left_zerofier;
        let right_poly = self % &right_zerofier;
        let mut left_res = left_poly.fast_evalulate(&points[..points.len() / 2]);
        let mut right_res = right_poly.fast_evalulate(&points[points.len() / 2..]);
        left_res.append(&mut right_res);
        return left_res;
    }

    // Fast interpolation.
    // Split domain xs and target ys into left and right.
    // Calulate the right zerofiler R'(X)
    // Calulate the value of R'(X) on the left half of the domain
    // Scale the left ys by those value
    pub fn fast_interpolate(xs: &[Scalar], ys: &[Scalar]) -> Polynomial {
        assert!(xs.len() == ys.len());

        if xs.len() == 0 {
            return Polynomial::zero();
        }
        if xs.len() == 1 {
            return Polynomial::new(vec![Scalar::from(ys[0])].into_iter());
        }

        let half = xs.len() / 2;
        let left_zerofier = Polynomial::fast_zerofier(&xs[..half]);
        let right_zerofier = Polynomial::fast_zerofier(&xs[half..]);

        let left_scales = right_zerofier.fast_evalulate(&xs[..half]);
        let right_scales = left_zerofier.fast_evalulate(&xs[half..]);

        let left_targets = ys[..half]
            .iter()
            .zip(left_scales)
            .map(|(a, b)| *a * b.invert().unwrap())
            .collect::<Vec<_>>();
        let right_targets = ys[half..]
            .iter()
            .zip(right_scales)
            .map(|(a, b)| *a * b.invert().unwrap())
            .collect::<Vec<_>>();

        let left = Polynomial::fast_interpolate(&xs[..half], left_targets.as_slice());
        let right = Polynomial::fast_interpolate(&xs[half..], right_targets.as_slice());

        &Polynomial::fast_multiply(&left, &right_zerofier)
            + &Polynomial::fast_multiply(&right, &left_zerofier)
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

pub fn rand_scalars(size: usize) -> Vec<Scalar> {
    let mut rng = thread_rng();
    (0..size)
        .map(|_| Scalar::from(rng.gen::<u64>()))
        .collect::<Vec<_>>()
}

#[cfg(test)]
pub mod tests {
    use super::*;

    #[test]
    fn test_eval_polynomial() {
        let coefficients = vec![42, 1, 1, 0, 1].into_iter().map(Scalar::from);
        let point = Scalar::from(2);
        let result_in_fr = Polynomial::new(coefficients).evalulate_at(point);
        assert_eq!(result_in_fr, Scalar::from(64));
    }

    #[test]
    fn test_multiply_and_fast_multiply() {
        let lhs_coeffs = rand_scalars(32);
        let rhs_coeffs = rand_scalars(32);
        let lhs = Polynomial::new(lhs_coeffs.into_iter());
        let rhs = Polynomial::new(rhs_coeffs.into_iter());
        assert_eq!(Polynomial::fast_multiply(&lhs, &rhs), &lhs * &rhs);
    }

    #[test]
    fn test_fast_zerofier() {
        // (x-1)(x-2)...(x-32)
        let mut res = Polynomial::one();
        let mut points = vec![];
        for i in 1..=32 {
            res = &res * &Polynomial::new(vec![Scalar::from(i).neg(), Scalar::one()].into_iter());
            points.push(Scalar::from(i));
        }
        let zerofier_res = Polynomial::fast_zerofier(&points);
        assert_eq!(res, zerofier_res);
    }

    #[test]
    fn test_fast_evalulate() {
        // generate a random coeffs with degree 32 and 32 points to evaluate
        let coeffs = rand_scalars(32);
        let points = rand_scalars(32);
        let poly = Polynomial::new(coeffs.into_iter());
        let fast_res = poly.fast_evalulate(points.as_slice());
        // naive evaluate
        let mut naive_res = vec![];
        for i in points {
            naive_res.push(poly.evalulate_at(i));
        }
        assert_eq!(fast_res, naive_res);
    }

    #[test]
    fn test_fast_interpolate() {
        // generate a random domain and values of size 32
        let domains = rand_scalars(32);
        let values = rand_scalars(32);
        let poly = Polynomial::fast_interpolate(domains.as_slice(), values.as_slice());

        // check that domain evaluate to value
        let res = poly.fast_evalulate(domains.as_slice());
        assert_eq!(res, values);
    }

    #[test]
    fn test_polynomial_divide() {
        // a random dividend and divisor with degree of 32 and 5
        let dividend_coeffs = rand_scalars(32);
        let dividend = Polynomial::new(dividend_coeffs.into_iter());

        let divisor_coeffs = rand_scalars(5);
        let divisor = Polynomial::new(divisor_coeffs.into_iter());

        let result_poly = &dividend / &divisor;
        let remainder = &dividend % &divisor;
        assert_eq!(&(&result_poly * &divisor) + &remainder, dividend);
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
        let coeffs = rand_scalars(64);

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
        let coeffs = rand_scalars(rng.gen::<usize>() % 32 + 32);

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
