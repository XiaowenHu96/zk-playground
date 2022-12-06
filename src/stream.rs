/**
 * This file implements a non-interactive proof stream (fiat_shamir)
 *
 * TODO: 
 * 1. hash return u64, we need random sample over Fp
 * 2. Does the stream need nounce, in case prover needs to sample two random values consecutively
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
    prover_nounce: usize,
    verifier_nounce: usize,
}

impl ProofStream {
    pub fn new() -> Self {
        let mut rng = thread_rng();
        Self {
            stream: vec![],
            read_index: 0,
            base: rng.gen(),
            prover_nounce: 0,
            verifier_nounce: 0,
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
        self.prover_nounce.hash(&mut hasher);
        self.prover_nounce += 1;
        self.stream.hash(&mut hasher);
        Scalar::from(hasher.finish())
    }

    pub fn verifier_sample(&mut self) -> Scalar {
        let mut hasher = DefaultHasher::new();
        self.base.hash(&mut hasher);
        self.verifier_nounce.hash(&mut hasher);
        self.verifier_nounce += 1;
        self.stream[..self.read_index].hash(&mut hasher);
        Scalar::from(hasher.finish())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra;
    use crate::algebra::Polynomial;
    use crate::setup::Setup;
    use crate::prover::*;
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
        // generate domain
        let d = algebra::Domain::new(degree);
        let mut domain = vec![];
        let mut v = Scalar::one();
        for _ in 0..degree {
            domain.push(v);
            v = v * d.generator;
        }
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
        let d = algebra::Domain::new(degree);
        let mut domain = vec![];
        let mut v = Scalar::one();
        for _ in 0..degree {
            domain.push(v);
            v = v * d.generator;
        }
        let f = Polynomial::new(algebra::rand_scalars(degree).into_iter());
        let f_ys = Polynomial::fast_evalulate(&f, &domain);
        let mut g_ys = f_ys.clone();
        // one value differs
        g_ys[0] = Scalar::one();
        g_ys.shuffle(&mut rng);
        let g = Polynomial::fast_interpolate(&domain, &g_ys);

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
}
