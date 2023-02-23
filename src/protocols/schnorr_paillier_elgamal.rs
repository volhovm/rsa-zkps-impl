/// Schnorr for Paillier-Elgamal.

use get_size::GetSize;
use get_size_derive::*;
use serde::{Serialize};
use std::fmt;

use crate::bigint::*;
use crate::utils as u;
use super::schnorr_generic::*;
use super::paillier_elgamal as pe;

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PELangParams {
    pub n_bitlen: u32,
    pub range: Option<BigInt>,
}

#[derive(Clone, PartialEq, Debug, Serialize, GetSize)]
pub struct PELang {
    /// Params of the language
    pub lparams: PELangParams,
    /// Public key that is used to generate instances.
    pub pk: pe::PublicKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<pe::SecretKey>,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PELangDom {
    /// Message to be encrypted
    pub m: BigInt,
    /// Encryption randomness
    pub r: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PELangCoDom {
    /// The encryption ciphertext
    pub ct: pe::Ciphertext
}

impl SchnorrLang for PELang {
    type LangParams = PELangParams;
    type Dom = PELangDom;
    type CoDom = PELangCoDom;

    fn sample_lang(lparams: &Self::LangParams) -> Self {
        let (pk,sk) = pe::keygen(lparams.n_bitlen as usize);
        PELang { lparams:lparams.clone(), pk, sk: Some(sk) }
    }

    fn to_public(&self) -> Self {
        let mut other = self.clone();
        other.sk = None;
        return other
    }

    fn pre_verify(&self, params: &ProofParams) -> bool {
        if params.ch_space_bitlen > 32 {
            panic!("schnorr_paillier_elgamal: verify0: ch_space is too big: {:?} bits",
                   params.ch_space_bitlen)
        }
        u::check_small_primes(2u64.pow(params.ch_space_bitlen),&self.pk.n)
    }

    fn sample_wit(&self) -> Self::Dom {
        let m = match &self.lparams.range {
            // Full message range N
            None => BigInt::sample_below(&self.pk.n),
            // [-R/2,R/2]
            Some(r) => u::bigint_sample_below_sym(r),
        };

        let r = BigInt::sample_below(&self.pk.n);
        PELangDom { m, r }
    }

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let ct = pe::encrypt_with_randomness_opt(&self.pk, self.sk.as_ref(), &wit.m, &wit.r);
        PELangCoDom { ct }
    }

    fn sample_com_rand(&self, params: &ProofParams) -> Self::Dom {
        let m = match &self.lparams.range {
            // Perfect blinding, because response is computed mod N
            None => BigInt::sample_below(&self.pk.n),
            // Statistical blinding, rand_range has (range * ch + lambda) bits, and in range
            // proof setting challenges are binary
            Some(r) => {
                let rand_range = r * BigInt::pow(&BigInt::from(2), params.lambda - 1);
                BigInt::sample_below(&rand_range)
            },
        };

        // Response is additive over integers
        let r = BigInt::sample((self.lparams.n_bitlen + params.ch_space_bitlen + params.lambda) as usize);
        PELangDom { m, r }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        let n = &self.pk.n;
        let m = BigInt::mod_add(&BigInt::mod_mul(&wit.m, ch, n), &rand.m, n);
        let r = &wit.r * ch + &rand.r;
        PELangDom { m, r }
    }

    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom {
        let nn = &self.pk.nn;
        let ct1 = BigInt::mod_mul(&BigInt::mod_pow(&inst.ct.ct1, ch, nn), &com.ct.ct1, nn);
        let ct2 = BigInt::mod_mul(&BigInt::mod_pow(&inst.ct.ct2, ch, nn), &com.ct.ct2, nn);
        PELangCoDom { ct: pe::Ciphertext{ ct1, ct2 } }
    }

    fn check_resp_range(&self, params: &ProofParams, resp: &Self::Dom) -> bool {
        let r = self.lparams.range.as_ref().expect("schnorr_paillier_elgamal_batched, check_resp_range: range is None!");

        let rand_range = r * BigInt::pow(&BigInt::from(2), params.lambda - 1);

        &resp.m < &rand_range
    }
}


#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier_elgamal::*;
    use crate::protocols::schnorr_generic::*;

    #[test]
    fn test_correctness() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness::<PELang>(&params,&PELangParams{n_bitlen:1024,range:None});
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness_fs::<PELang>(&params,&PELangParams{n_bitlen:1024,range:None});
    }

    #[test]
    fn test_correctness_range() {
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = ProofParams::new_range(128);
        generic_test_correctness::<PELang>(&params,&PELangParams{n_bitlen:1024,range:Some(range)});
    }

    #[test]
    fn test_correctness_range_fs() {
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = ProofParams::new_range(128);
        generic_test_correctness_fs::<PELang>(&params,&PELangParams{n_bitlen:1024,range:Some(range)});
    }
}
