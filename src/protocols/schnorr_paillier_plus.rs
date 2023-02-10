/// A tailored variant of schnorr_paillier for knowledge-of-ciphertext
/// specifically for the DVRange protocol. It is very similar to
/// super::schnorr_paillier, except that (1) it is for a slightly
/// different 3-ary relation S = Enc(w_1,w_2)*C^{w_3} mod N^2; (2) and that it
/// does not support range check functionality.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;

use super::paillier::paillier_enc_opt;
use super::schnorr_generic::*;


#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct PPLang {
    /// Bit size of the RSA modulus
    pub n_bitlen: u32,
    /// Public key that is used to generate instances.
    pub pk: EncryptionKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<DecryptionKey>,
    /// The encryption ciphertext C, corresponding to the DVRange challenge
    pub ch_ct: BigInt,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PPLangDom {
    pub m: BigInt,
    pub r: BigInt,
    /// exponent of ct
    pub cexp: BigInt,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PPLangCoDom {
    /// The encryption ciphertext S_i = Enc(w1,w2)
    pub si: BigInt
}


/// Computes Enc_pk(enc_arg,rand)*Ct^{ct_exp}
pub fn compute_si(pk: &EncryptionKey,
                  sk: Option<&DecryptionKey>,
                  ch_ct: &BigInt, m: &BigInt, r: &BigInt, cexp: &BigInt) -> BigInt {
    // TODO This can be further optimised when N^2 is known.
    BigInt::mod_mul(
        &paillier_enc_opt(pk,sk,m,r),
        // TODO Can we avoid inverting here?
        &super::utils::bigint_mod_pow(ch_ct, cexp, &pk.nn),
        &pk.nn)
}

impl Lang for PPLang {
    type LangParams = u32;
    type Dom = PPLangDom;
    type CoDom = PPLangCoDom;

    fn sample_lang(n_bitlen: &Self::LangParams) -> Self {
        let (pk,sk) = Paillier::keypair_with_modulus_size(*n_bitlen as usize).keys();
        let ch_ct = BigInt::sample_below(&pk.nn);
        PPLang { n_bitlen: *n_bitlen, pk, sk: Some(sk), ch_ct  }
    }

    fn to_public(&self) -> Self {
        let mut other = self.clone();
        other.sk = None;
        return other
    }

    fn verify(&self, params: &ProofParams) -> bool {
        if params.ch_space_bitlen > 32 {
            panic!("schnorr_paillier_plus: verify0: ch_space is too big: {:?} bits",
                   params.ch_space_bitlen)
        }
        super::utils::check_small_primes(2u64.pow(params.ch_space_bitlen),&self.pk.n)
    }

    fn sample_wit(&self) -> Self::Dom {
        let m = BigInt::sample_below(&self.pk.n);
        let r = BigInt::sample_below(&self.pk.n);
        // Most generally this is N^2. However in DVRange, this number can be
        // range-limited to smaller different numbers depending on the step.
        // TODO probably can be optimised
        let cexp = BigInt::sample_below(&self.pk.nn);

        PPLangDom { m, r, cexp }
    }

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let si = compute_si(&self.pk, self.sk.as_ref(), &self.ch_ct, &wit.m, &wit.r, &wit.cexp);
        PPLangCoDom { si }
    }

    fn sample_com_rand(&self, _params: &ProofParams) -> Self::Dom {
        // Perfect blinding since response is computed mod N
        let m = BigInt::sample_below(&self.pk.n);
        // Perfect multiplicative blinding
        let r = BigInt::sample_below(&self.pk.n);
        // Must additively blind anything over N^2.
        // TODO can be optimised if we know the witness is smaller.
        let cexp = BigInt::sample_below(&self.pk.nn);

        PPLangDom { m, r, cexp }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        let n = &self.pk.n;

        let m = BigInt::mod_add(&rand.m, &BigInt::mod_mul(&wit.m, ch, n), n);
        // TODO This can be optimised when factorization of n is known
        let r = BigInt::mod_mul(&rand.r, &BigInt::mod_pow(&wit.r, ch, n), n);
        let cexp = &wit.cexp * ch + &rand.cexp;

        PPLangDom { m, r, cexp }
    }

    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom {
        let nn = &self.pk.nn;
        let si = BigInt::mod_mul(&BigInt::mod_pow(&inst.si, ch, nn), &com.si, nn);
        PPLangCoDom { si }
    }

    fn check_resp_range(&self, _: &ProofParams, _: &Self::Dom) -> bool {
        panic!("schnorr_paillier_plus does not run in the range mode");
    }
}


#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier_plus::*;
    use crate::protocols::schnorr_generic::*;

    #[test]
    fn test_correctness() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness::<PPLang>(&params,&1024);
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness_fs::<PPLang>(&params,&1024);
    }
}
