/// A tailored variant of schnorr_paillier for knowledge-of-ciphertext
/// specifically for the DVRange protocol. It is very similar to
/// super::schnorr_paillier, except that (1) it is for a slightly
/// different 3-ary relation S = Enc(w_1;1)*C^{w_2} mod N^2; (2) and that it
/// does not support range check functionality.

use get_size::GetSize;
use get_size_derive::*;
use serde::{Serialize};
use std::fmt;

use crate::bigint::*;
use crate::utils as u;
use super::paillier as p;
use super::paillier::encrypt;
use super::schnorr_generic::*;


#[derive(Clone, PartialEq, Debug, Serialize, GetSize)]
pub struct PPLang {
    /// Bit size of the RSA modulus
    pub n_bitlen: u32,
    /// Public key that is used to generate instances.
    pub pk: p::PublicKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<p::SecretKey>,
    /// The encryption ciphertext C, corresponding to the DVRange challenge
    pub ch_ct: BigInt,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PPLangDom {
    /// Blinding message
    pub m: BigInt,
    /// exponent of ct
    pub cexp: BigInt,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PPLangCoDom {
    /// The encryption ciphertext S_i = Enc(w1,w2)
    pub si: BigInt
}


/// Computes Enc_pk(enc_arg,1)*Ct^{ct_exp}
pub fn compute_si(pk: &p::PublicKey,
                  sk: Option<&p::SecretKey>,
                  ch_ct: &BigInt, m: &BigInt, cexp: &BigInt) -> BigInt {
    let ct = p::encrypt(pk,sk,m,&BigInt::from(1));

    match sk.as_ref() {
        None => BigInt::mod_mul(&ct, &u::bigint_mod_pow(ch_ct, cexp, &pk.nn),&pk.nn),
        Some(sk) => {
            let pp = &sk.p * &sk.p;
            let qq = &sk.q * &sk.q;
            let pp_inv_qq = BigInt::mod_inv(&pp, &qq).unwrap();

            let res_pp = BigInt::mod_mul(&ct, &u::bigint_mod_pow(ch_ct, cexp, &pp), &pp);
            let res_qq = BigInt::mod_mul(&ct, &u::bigint_mod_pow(ch_ct, cexp, &qq), &qq);
            u::crt_recombine(&res_pp, &res_qq, &pp, &qq, &pp_inv_qq)
        }
    }
}

impl SchnorrLang for PPLang {
    type LangParams = u32;
    type Dom = PPLangDom;
    type CoDom = PPLangCoDom;

    fn sample_lang(n_bitlen: &Self::LangParams) -> Self {
        let (pk,sk) = p::keygen(*n_bitlen as usize);
        let ch_ct = BigInt::sample_below(&pk.nn);
        PPLang { n_bitlen: *n_bitlen, pk, sk: Some(sk), ch_ct  }
    }

    fn to_public(&self) -> Self {
        let mut other = self.clone();
        other.sk = None;
        return other
    }

    fn pre_verify(&self, params: &ProofParams) -> bool {
        if params.ch_space_bitlen > 32 {
            panic!("schnorr_paillier_plus: verify0: ch_space is too big: {:?} bits",
                   params.ch_space_bitlen)
        }
        u::check_small_primes(2u64.pow(params.ch_space_bitlen),&self.pk.n)
    }

    fn sample_wit(&self) -> Self::Dom {
        let m = BigInt::sample_below(&self.pk.n);
        // Most generally this is N^2. However in DVRange, this number can be
        // range-limited to smaller different numbers depending on the step.
        // TODO probably can be optimised
        let cexp = BigInt::sample_below(&self.pk.nn);

        PPLangDom { m, cexp }
    }

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let si = compute_si(&self.pk, self.sk.as_ref(), &self.ch_ct, &wit.m, &wit.cexp);
        PPLangCoDom { si }
    }

    fn sample_com_rand(&self, _params: &ProofParams) -> Self::Dom {
        // Perfect blinding since response is computed mod N
        let m = BigInt::sample_below(&self.pk.n);
        // Must additively blind anything over N^2.
        // TODO can be optimised if we know the witness is smaller.
        let cexp = BigInt::sample_below(&self.pk.nn);

        PPLangDom { m, cexp }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        let n = &self.pk.n;

        let m = BigInt::mod_add(&rand.m, &BigInt::mod_mul(&wit.m, ch, n), n);
        let cexp = &wit.cexp * ch + &rand.cexp;

        PPLangDom { m, cexp }
    }

    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom {
        let nn = &self.pk.nn;

        let si = match self.sk.as_ref() {
            None => BigInt::mod_mul(&BigInt::mod_pow(&inst.si, ch, nn), &com.si, nn),
            Some(sk) => {
                let pp = &sk.p * &sk.p;
                let qq = &sk.q * &sk.q;
                let pp_inv_qq = BigInt::mod_inv(&pp, &qq).unwrap();

                let si_pp = BigInt::mod_mul(&BigInt::mod_pow(&inst.si, ch, &pp), &com.si, &pp);
                let si_qq = BigInt::mod_mul(&BigInt::mod_pow(&inst.si, ch, &qq), &com.si, &qq);
                u::crt_recombine(&si_pp, &si_qq, &pp, &qq, &pp_inv_qq)
            }
        };
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
