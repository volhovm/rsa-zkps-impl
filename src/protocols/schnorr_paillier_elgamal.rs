/// Schnorr for Paillier-Elgamal.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;

use super::schnorr_generic::*;
use super::paillier_elgamal as pe;


#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct PELang {
    /// Bitlength of the RSA modulus
    pub n_bitlen: u32,
    /// Public key that is used to generate instances.
    pub pk: pe::PEPublicKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<pe::PESecretKey>,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PELangDom {
    /// Message to be encrypted
    pub m: BigInt,
    /// Encryption randomness
    pub r: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PELangCoDom {
    /// The encryption ciphertext
    pub ct: pe::PECiphertext
}

impl Lang for PELang {
    type LangParams = u32;
    type Dom = PELangDom;
    type CoDom = PELangCoDom;

    fn sample_lang(n_bitlen: &Self::LangParams) -> Self {
        let (pk,sk) = pe::keygen(*n_bitlen as usize);
        PELang { n_bitlen: *n_bitlen, pk, sk: Some(sk) }
    }

    fn to_public(&self) -> Self {
        let mut other = self.clone();
        other.sk = None;
        return other
    }

    fn verify(&self, params: &ProofParams) -> bool {
        if params.ch_space_bitlen > 32 {
            panic!("schnorr_paillier_elgamal: verify0: ch_space is too big: {:?} bits",
                   params.ch_space_bitlen)
        }
        super::utils::check_small_primes(2u64.pow(params.ch_space_bitlen),&self.pk.n)
    }

    fn sample_wit(&self) -> Self::Dom {
        let m = BigInt::sample_below(&self.pk.n);
        let r = BigInt::sample_below(&self.pk.n);
        PELangDom { m, r }
    }

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let ct = pe::encrypt_with_randomness_opt(&self.pk, self.sk.as_ref(), &wit.m, &wit.r);
        PELangCoDom { ct }
    }

    fn sample_com_rand(&self, params: &ProofParams) -> Self::Dom {
        // Response is mod N
        let m = BigInt::sample_below(&self.pk.n);
        // Response is over integers
        let r = BigInt::sample((self.n_bitlen + params.ch_space_bitlen + params.lambda) as usize);
        PELangDom { m, r }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        let n = &self.pk.n;
        let m = BigInt::mod_add(&BigInt::mod_mul(&wit.m, ch, n), &rand.m, n);
        let r = &wit.r * ch + &rand.r;
        PELangDom { m, r }
    }

    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom {
        let n2 = &self.pk.n2;
        let ct1 = BigInt::mod_mul(&BigInt::mod_pow(&inst.ct.ct1, ch, n2), &com.ct.ct1, n2);
        let ct2 = BigInt::mod_mul(&BigInt::mod_pow(&inst.ct.ct2, ch, n2), &com.ct.ct2, n2);
        PELangCoDom { ct: pe::PECiphertext{ ct1, ct2 } }
    }

    fn check_resp_range(&self, _: &ProofParams, _: &Self::Dom) -> bool {
        panic!("schnorr_paillier_elgamal does not run in the range mode");
    }
}


#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier_elgamal::*;
    use crate::protocols::schnorr_generic::*;

    #[test]
    fn test_correctness() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness::<PELang>(&params,&1024);
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness_fs::<PELang>(&params,&1024);
    }
}
