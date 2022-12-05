use bls12_381::{G1Affine, G1Projective, Scalar};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const G1_AFFINE_SIZE: usize = 48;
const SCALAR_SIZE: usize = 32;

// FIFO stream fiat_shamir
#[derive(Clone)]
pub struct ProofStream {
    stream: Vec<u8>,
    read_index: usize,
}

impl ProofStream {
    pub fn new() -> Self {
        Self {
            stream: vec![],
            read_index: 0,
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
    pub fn prover_sample(&self) -> Scalar {
        let mut hasher = DefaultHasher::new();
        self.stream.hash(&mut hasher);
        Scalar::from(hasher.finish())
    }

    pub fn verifier_sample(&self) -> Scalar {
        let mut hasher = DefaultHasher::new();
        self.stream[..self.read_index].hash(&mut hasher);
        Scalar::from(hasher.finish())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra;

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
}
