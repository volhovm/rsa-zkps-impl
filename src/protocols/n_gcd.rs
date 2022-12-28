/// Implementation of the protocol that proves
/// gcd(N,phi(N)) != 1 for any integer N, directly in the Fiat-Shamir model.
///
/// Taken from from Section 3.2 ("Paillier-N" protocol) of
/// "Efficient Noninteractive Certification of RSA Moduli and Beyond"
/// https://par.nsf.gov/servlets/purl/10189824

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, Converter};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;


/// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct ProofParams {
    /// Bitlength of the RSA modulus
    pub n_bitlen: usize,
    /// Security parameter
    pub lambda: u32,
    /// Small number up to which N shouldn't have divisors.
    pub pmax: u64,
}

impl ProofParams {
    pub fn reps(&self) -> u32 {
        (self.lambda as f64 / (self.pmax as f64).log2()).ceil() as u32
    }
}

impl fmt::Display for ProofParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ProofParams ( lambda: {}, n_bitlen: {}, pmax: {} )",
               self.lambda,
               self.n_bitlen,
               self.pmax)
    }
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Inst {
    pub n: BigInt
}

#[derive(Clone, PartialEq, Debug)]
pub struct Wit {
    pub p: BigInt,
    pub q: BigInt,
}

/// Contains \phi(N)
#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct VerifierPrecomp(BigInt);

pub fn sample_inst_wit(params: &ProofParams) -> (Inst,Wit) {
    let (pk,sk) = Paillier::keypair_with_modulus_size(params.n_bitlen).keys();
    let p = sk.p;
    let q = sk.q;
    let n = pk.n;

    let inst = Inst { n };
    let wit = Wit { p, q };

    return (inst,wit);
}

#[derive(Clone,Debug)]
pub struct Proof(Vec<BigInt>);

fn fs_compute_challenge(params: &ProofParams, inst: &Inst) -> Vec<BigInt> {
    use blake2::*;
    let b = (0 .. params.reps()).map(|i:u32| {
        // adding lambda for the random to be uniform.
        let slices_n = (params.n_bitlen + params.lambda as usize) / 8 + 1;
        let hash_calls = slices_n / 64 + 1;

        let mut hash_results: Vec<u8> = Vec::new();
        for call_n in 0..hash_calls {
            let x: Vec<u8> = rmp_serde::to_vec(&(call_n, params, inst, i)).unwrap();
            // Use Digest::digest, but it asks for a fixed-sized slice?
            let mut hasher: Blake2b = Digest::new();
            hasher.update(&x);
            let r0 = hasher.finalize();
            hash_results.append(&mut r0.as_slice().to_vec());
        }

        // this bigint is random, but it's at least 2^lambda bigger than N
        let raw_bn : BigInt = Converter::from_bytes(&hash_results.as_slice()[..slices_n]);
        raw_bn.modulus(&inst.n)
    }).collect();
    b
}

pub fn prove(params: &ProofParams, inst: &Inst, wit: &Wit) -> Proof {
    let chs = fs_compute_challenge(params,inst);
    let phi_n = (&wit.p-1)*(&wit.q-1);
    let n_inv = BigInt::mod_inv(&inst.n,&phi_n).expect("sample_inst inv");
    let sigmas = chs.iter().map(|ch| BigInt::mod_pow(ch,&n_inv, &inst.n)).collect();
    Proof(sigmas)
}

pub fn verify(params: &ProofParams, inst: &Inst, proof: &Proof) -> bool {
    if !super::utils::check_small_primes(params.pmax, &inst.n) { return false; }
    let chs = fs_compute_challenge(params,inst);
    for (sigma,ch) in (&proof.0).iter().zip(chs.iter()) {
        if sigma <= &BigInt::from(0) { return false; }
        if BigInt::mod_pow(sigma,&inst.n,&inst.n) != *ch { return false; }
    }
    return true
}


#[cfg(test)]
mod tests {
    #[test]
    fn test_correctness() {
        use crate::protocols::n_gcd::*;
        let params = ProofParams{ n_bitlen: 2048, lambda: 128, pmax: 64000 };
        let (inst,wit) = sample_inst_wit(&params);

        let proof = prove(&params,&inst,&wit);
        assert!(verify(&params,&inst,&proof));
    }
}
