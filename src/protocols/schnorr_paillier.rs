/// This is an implementation of the basic Schnorr protocol for
/// Paillier homomorphism with untrusted modulus N, with the optional
/// range check functionality. It uses the p_max optimisation -- that is,
/// verifier manually checks that there are no p<p_max divisors of N, which
/// allows to use log(p_max) challenge space instead of the binary one.

use serde::{Serialize};
use std::fmt;

use crate::bigint::*;
use crate::utils as u;
use super::paillier as p;
use super::schnorr_generic::*;


#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PLangParams {
    pub n_bitlen: u32,
    pub range: Option<BigInt>,
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct PLang {
    /// Params of the language
    pub lparams: PLangParams,
    /// Public key that is used to generate instances.
    pub pk: p::EncryptionKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<p::DecryptionKey>,
}


#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PLangDom {
    pub m: BigInt,
    pub r: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct PLangCoDom {
    /// The encryption ciphertext
    pub ct: BigInt
}


impl Lang for PLang {
    type LangParams = PLangParams;
    type Dom = PLangDom;
    type CoDom = PLangCoDom;

    fn sample_lang(lparams: &Self::LangParams) -> Self {
        let (pk,sk) = p::keygen(lparams.n_bitlen as usize);
        PLang { lparams: lparams.clone(), pk, sk: Some(sk)  }
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
        u::check_small_primes(2u64.pow(params.ch_space_bitlen),&self.pk.n)
    }

    fn sample_wit(&self) -> Self::Dom {
        let m = match &self.lparams.range {
            // Full message range N
            None => BigInt::sample_below(&self.pk.n),
            // [-R/2,R/2]
            Some(r) => u::bigint_sample_below_sym(r),
        };
        // The order of r^N will be less than N, so it is fine
        // to sample this not from N^2
        let r = BigInt::sample_below(&self.pk.n);

        PLangDom { m, r }
    }


    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let ct = p::paillier_enc_opt(&self.pk, self.sk.as_ref(), &wit.m, &wit.r);
        PLangCoDom { ct }
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
        // Perfect blinding, response is mod N
        let r = BigInt::sample_below(&self.pk.n);

        PLangDom { m, r }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        let n = &self.pk.n;
        let m = BigInt::mod_add(&BigInt::mod_mul(&wit.m, ch, n), &rand.m, n);

        // TODO This can be optimised when factorization of n is known
        let r = BigInt::mod_mul(&BigInt::mod_pow(&wit.r, ch, n), &rand.r, n);
        PLangDom { m, r }
    }

    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom {
        let nn = &self.pk.nn;
        let ct = BigInt::mod_mul(&BigInt::mod_pow(&inst.ct, ch, nn), &com.ct, nn);
        PLangCoDom { ct }
    }

    fn check_resp_range(&self, params: &ProofParams, resp: &Self::Dom) -> bool {
        let r = self.lparams.range.as_ref().expect("schnorr_paillier, check_resp_range: range is None!");
        let rand_range = r * BigInt::pow(&BigInt::from(2), params.lambda - 1);

        &resp.m < &rand_range
    }
}



#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier::*;
    use crate::protocols::schnorr_generic::*;

    #[test]
    fn test_correctness() {
        let lparams = PLangParams{ n_bitlen: 1024, range: None };
        generic_test_correctness::<PLang>(&ProofParams::new(128, 16),&lparams);
        generic_test_correctness::<PLang>(&ProofParams::new(128, 1),&lparams);
    }

    #[test]
    fn test_correctness_fs() {
        let lparams = PLangParams{ n_bitlen: 1024, range: None };
        generic_test_correctness_fs::<PLang>(&ProofParams::new(128, 16),&lparams);
        generic_test_correctness_fs::<PLang>(&ProofParams::new(128, 1),&lparams);
    }

    #[test]
    fn test_correctness_range_fs() {
        let range = BigInt::pow(&BigInt::from(2), 256);
        let lparams = PLangParams{ n_bitlen: 1024, range: Some(range) };
        generic_test_correctness_fs::<PLang>(&ProofParams::new_range(128),&lparams);
        generic_test_correctness_fs::<PLang>(&ProofParams::new_range(128),&lparams);
    }

//    #[test]
//    fn test_soundness_trivial() {
//        let params = ProofParams::new(2048, 128, 15);
//
//        let lang = sample_lang(&params);
//        let (inst,_) = sample_inst(&params,&lang);
//        let (_,wit2) = sample_inst(&params,&lang);
//
//
//        let res = verify0(&params,&lang);
//        assert!(res);
//
//        let (com,cr) = prove1(&params,&lang);
//        let ch = verify1(&params);
//
//        // with wit2
//        let resp = prove2(&params,&lang,&wit2,&ch,&cr);
//        assert!(verify2(&params,&lang,&inst,&com,&ch,&resp) == false);
//    }
//


}
