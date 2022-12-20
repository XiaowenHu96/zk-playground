/**
 * This file implements a non-interactive proof stream (fiat_shamir)
 *
 * TODO:
 * 1. hash return u64, we need random sample over Fp
 * 2. Does the stream need nonce, in case prover needs to sample two random values consecutively
 */
use bls12_381::{G1Affine, G1Projective, Scalar};
use rand::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const G1_AFFINE_SIZE: usize = 48;
const SCALAR_SIZE: usize = 32;

// FIFO stream fiat_shamir
#[derive(Clone)]
pub struct ProofStream {
    stream: Vec<u8>,
    read_index: usize,
    base: u8,
    prover_nonce: usize,
    verifier_nonce: usize,
}

impl ProofStream {
    pub fn new() -> Self {
        let mut rng = thread_rng();
        Self {
            stream: vec![],
            read_index: 0,
            base: rng.gen(),
            prover_nonce: 0,
            verifier_nonce: 0,
        }
    }

    pub fn read_g1_affine(&mut self) -> G1Affine {
        let mut bytes = [0; G1_AFFINE_SIZE];
        bytes.copy_from_slice(&self.stream[self.read_index..(self.read_index + G1_AFFINE_SIZE)]);
        let res = G1Affine::from_compressed(&bytes).unwrap();
        self.read_index += G1_AFFINE_SIZE;
        res
    }

    // Auto convert from affine to projective
    pub fn read_g1_projective(&mut self) -> G1Projective {
        G1Projective::from(self.read_g1_affine())
    }

    pub fn write_g1_affine(&mut self, val: G1Affine) {
        let bytes = val.to_compressed();
        self.stream.extend(bytes.into_iter());
    }

    pub fn read_scalar(&mut self) -> Scalar {
        let mut bytes = [0; SCALAR_SIZE];
        bytes.copy_from_slice(&self.stream[self.read_index..(self.read_index + SCALAR_SIZE)]);
        let res = Scalar::from_bytes(&bytes).unwrap();
        self.read_index += SCALAR_SIZE;
        res
    }

    pub fn write_scalar(&mut self, val: Scalar) {
        let bytes = val.to_bytes();
        self.stream.extend(bytes.into_iter());
    }

    // TODO how to sample over Fp
    pub fn prover_sample(&mut self) -> Scalar {
        let mut hasher = DefaultHasher::new();
        self.base.hash(&mut hasher);
        self.prover_nonce.hash(&mut hasher);
        self.prover_nonce += 1;
        self.stream.hash(&mut hasher);
        Scalar::from(hasher.finish())
    }

    pub fn verifier_sample(&mut self) -> Scalar {
        let mut hasher = DefaultHasher::new();
        self.base.hash(&mut hasher);
        self.verifier_nonce.hash(&mut hasher);
        self.verifier_nonce += 1;
        self.stream[..self.read_index].hash(&mut hasher);
        Scalar::from(hasher.finish())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra;
    use crate::algebra::{Domain, Polynomial};
    use crate::prover::*;
    use crate::setup::Setup;
    use crate::verifier::*;
    use bls12_381::{G1Affine, Scalar};

    #[test]
    fn test_fiat_shamir() {
        let mut proofstream = ProofStream::new();
        let mut prover_samples = vec![];
        let mut verifier_samples = vec![];
        let scalars = algebra::rand_scalars(32);
        let g1_affines = algebra::rand_scalars(32)
            .into_iter()
            .map(|x| G1Affine::from(G1Affine::generator() * x))
            .collect::<Vec<_>>();
        for i in 0..32 {
            proofstream.write_scalar(scalars[i]);
            proofstream.write_g1_affine(g1_affines[i]);
            prover_samples.push(proofstream.prover_sample());
        }
        for i in 0..32 {
            assert_eq!(proofstream.read_scalar(), scalars[i]);
            assert_eq!(proofstream.read_g1_affine(), g1_affines[i]);
            verifier_samples.push(proofstream.verifier_sample());
        }
        assert_eq!(verifier_samples, prover_samples);
    }

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
            .map(|x| VerifierProofUnit {
                z: x.z,
                comm_ps: x
                    .ps
                    .into_iter()
                    .map(|p| setup.commit(&p))
                    .collect::<Vec<_>>(),
            })
            .collect::<Vec<_>>();
        let (res, _) = verify_multiple_poly_mulitple_points_open(&setup, &mut stream, &vproofs);
        assert_eq!(res, true);
    }

    #[test]
    fn test_positive_permutation_argument() {
        let degree = 32;
        let mut rng = thread_rng();
        let domain = algebra::Domain::new(degree);
        // generate random polynomial f with degree 32
        let f_ys = algebra::rand_scalars(32);
        let mut g_ys = f_ys.clone();
        g_ys.shuffle(&mut rng);

        let f = domain.invert_fft_interpolate(&f_ys);
        let g = domain.invert_fft_interpolate(&g_ys);
        // Now we have f, g with f(D) and g(D) being permutation of each other

        let setup = Setup::new(degree);
        let mut stream = ProofStream::new();
        // prover work
        prove_permutation_argument(&setup, &mut stream, &f, &g, &f_ys, &g_ys, &domain);
        // Verifier work
        let res = verify_permutation_argument(
            &setup,
            &mut stream,
            setup.commit(&f),
            setup.commit(&g),
            &domain,
        );
        assert!(res == true)
    }

    #[test]
    fn test_negative_permutation_argument() {
        let degree = 32;
        let mut rng = thread_rng();
        let domain = algebra::Domain::new(degree);
        // generate random polynomial f with degree 32
        let f_ys = algebra::rand_scalars(32);
        let mut g_ys = f_ys.clone();
        g_ys[0] = Scalar::one();
        g_ys.shuffle(&mut rng);

        let f = domain.invert_fft_interpolate(&f_ys);
        let g = domain.invert_fft_interpolate(&g_ys);

        let setup = Setup::new(degree);
        let mut stream = ProofStream::new();
        // prover work
        prove_permutation_argument(&setup, &mut stream, &f, &g, &f_ys, &g_ys, &domain);
        // Verifier work
        let res = verify_permutation_argument(
            &setup,
            &mut stream,
            setup.commit(&f),
            setup.commit(&g),
            &domain,
        );
        assert!(res == false)
    }

    #[test]
    fn test_positive_permutation_argument_2n() {
        let n = 32;
        let domain = Domain::new(n);
        let mut rng = thread_rng();
        let f_ys = algebra::rand_scalars(2 * n);
        let mut g_ys = f_ys.clone();
        g_ys.shuffle(&mut rng);
        let f1_ys = f_ys[0..n].to_vec();
        let f2_ys = f_ys[n..].to_vec();
        let g1_ys = g_ys[0..n].to_vec();
        let g2_ys = g_ys[n..].to_vec();
        let f1 = domain.invert_fft_interpolate(&f1_ys);
        let f2 = domain.invert_fft_interpolate(&f2_ys);
        let g1 = domain.invert_fft_interpolate(&g1_ys);
        let g2 = domain.invert_fft_interpolate(&g2_ys);

        let mut stream = ProofStream::new();
        // Make sure we supprot polynomial of degree 2n (for the quotient polynomial)
        let setup = Setup::new(2 * n);
        // prover work
        prove_permutation_argument_2n(
            &setup,
            &mut stream,
            &f1,
            &f2,
            &g1,
            &g2,
            &f1_ys,
            &f2_ys,
            &g1_ys,
            &g2_ys,
            &domain,
        );
        // Verifier work
        let res = verify_permutation_argument_2n(
            &setup,
            &mut stream,
            setup.commit(&f1),
            setup.commit(&f2),
            setup.commit(&g1),
            setup.commit(&g2),
            &domain,
        );
        assert!(res == true)
    }

    #[test]
    fn test_lookup() {
        let n = 64;
        let domain = Domain::new(n);
        let t_y = algebra::rand_scalars(n);
        let mut f_y = t_y[0..n / 2].to_vec();
        for v in f_y.clone() {
            f_y.push(v);
        }

        let f = domain.invert_fft_interpolate(&f_y);
        let t = domain.invert_fft_interpolate(&t_y);
        let mut stream = ProofStream::new();
        let setup = Setup::new(2 * n);

        prove_lookup(&setup, &mut stream, &f, &f_y, &t, &t_y, &domain);
        let comm_f = setup.commit(&f);
        let comm_t = setup.commit(&t);
        let res = verify_lookup(&setup, &mut stream, comm_f, comm_t, &domain);
        assert!(res == true);
    }

    #[test]
    fn test_negative_lookup() {
        let n = 64;
        let domain = Domain::new(n);
        let t_y = algebra::rand_scalars(n);
        let mut f_y = t_y[0..n / 2].to_vec();
        for v in f_y.clone() {
            f_y.push(v);
        }
        f_y.pop();
        f_y.push(Scalar::one()); // one of the element is not in t

        let f = domain.invert_fft_interpolate(&f_y);
        let t = domain.invert_fft_interpolate(&t_y);
        let mut stream = ProofStream::new();
        let setup = Setup::new(2 * n);

        prove_lookup(&setup, &mut stream, &f, &f_y, &t, &t_y, &domain);
        let comm_f = setup.commit(&f);
        let comm_t = setup.commit(&t);
        let res = verify_lookup(&setup, &mut stream, comm_f, comm_t, &domain);
        assert!(res == false);
    }

    #[test]
    fn test_lookup_8bits() {
        // 8 bits range proof is the same as regular lookup with t = [0..2^8-1]
        let n = 1 << 8;
        let domain = Domain::new(n);
        let t_y = (0..1 << 8).map(|x| Scalar::from(x)).collect::<Vec<_>>();
        let mut rng = thread_rng();
        let mut f_y = (0..1 << 8)
            .map(|_| Scalar::from(rng.gen::<u8>() as u64))
            .collect::<Vec<_>>();
        let setup = Setup::new(2 * n);
        {
            let f = domain.invert_fft_interpolate(&f_y);
            let t = domain.invert_fft_interpolate(&t_y);
            let mut stream = ProofStream::new();

            prove_lookup(&setup, &mut stream, &f, &f_y, &t, &t_y, &domain);
            let comm_f = setup.commit(&f);
            let comm_t = setup.commit(&t);
            let res = verify_lookup(&setup, &mut stream, comm_f, comm_t, &domain);
            assert!(res == true);
        }
        // negative
        {
            f_y.pop();
            f_y.push(Scalar::from(1 << 16));
            let f = domain.invert_fft_interpolate(&f_y);
            let t = domain.invert_fft_interpolate(&t_y);
            let mut stream = ProofStream::new();

            prove_lookup(&setup, &mut stream, &f, &f_y, &t, &t_y, &domain);
            let comm_f = setup.commit(&f);
            let comm_t = setup.commit(&t);
            let res = verify_lookup(&setup, &mut stream, comm_f, comm_t, &domain);
            assert!(res == false);
        }
    }

    #[test]
    fn test_range_proof_16bits() {
        // 16 bits range proof

        // construct a 8bits table
        let n = 1 << 8;
        let domain = Domain::new(n);
        let setup = Setup::new(2 * n);
        let t_y = (0..1 << 8).map(|x| Scalar::from(x)).collect::<Vec<_>>();

        // construct random vector in 16bits
        let mut rng = thread_rng();
        let mut f_y = (0..1 << 8)
            .map(|_| Scalar::from(rng.gen::<u16>() as u64))
            .collect::<Vec<_>>();
        {
            let f = domain.invert_fft_interpolate(&f_y);
            let t = domain.invert_fft_interpolate(&t_y);
            let mut stream = ProofStream::new();
            let comm_f = setup.commit(&f);
            let comm_t = setup.commit(&t);
            prove_range_proof_16bits(&setup, &mut stream, &f, &f_y, &t, &t_y, &domain);
            let res = verify_range_proof_16bits(&setup, &mut stream, comm_f, comm_t, &domain);
            assert!(res == true);
        }
        // negative
        {
            f_y.pop();
            f_y.push(Scalar::from(1 << 32));
            let f = domain.invert_fft_interpolate(&f_y);
            let t = domain.invert_fft_interpolate(&t_y);
            let mut stream = ProofStream::new();

            prove_lookup(&setup, &mut stream, &f, &f_y, &t, &t_y, &domain);
            let comm_f = setup.commit(&f);
            let comm_t = setup.commit(&t);
            let res = verify_lookup(&setup, &mut stream, comm_f, comm_t, &domain);
            assert!(res == false);
        }
    }
}
