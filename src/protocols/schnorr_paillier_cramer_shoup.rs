use get_size::GetSize;
use get_size_derive::*;
use serde::{Serialize};
use std::fmt;

use crate::bigint::*;
use crate::utils as u;

use super::paillier_cramer_shoup as pcs;
use super::schnorr_batched_generic as schb;

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PCSLangParams {
    pub n_bitlen: u32,
    pub range_bitlen: u32,
}

#[derive(Clone, PartialEq, Debug, Serialize, GetSize)]
pub struct PCSLang {
    /// Params of the language
    pub lparams: PCSLangParams,
    /// Public key that is used to generate instances.
    pub pk: pcs::PublicKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<pcs::SecretKey>,
}


#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PCSLangDom {
    pub m: BigInt,
    pub r: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PCSLangCoDom {
    /// The encryption ciphertext
    pub ct: BigInt
}



impl schb::SchnorrBatchedLang for PCSLang {
    type LangParams = PCSLangParams;
    type Dom = PCSLangDom;
    type CoDom = PCSLangCoDom;

    fn sample_lang(lparams: &Self::LangParams) -> Self {
        let (pk,sk) = pcs::keygen(lparams.n_bitlen as usize);
        PCSLang { lparams: lparams.clone(), pk, sk: Some(sk)  }
    }

    fn to_public(&self) -> Self {
        let mut other = self.clone();
        other.sk = None;
        return other
    }

    fn sample_wit(&self) -> Self::Dom {
        let m = u::bigint_sample_sym(self.lparams.range_bitlen);
        // The order of r^N will be less than N, so it is fine
        // to sample this not from N^2
        let r = BigInt::sample_below(&self.pk.n);

        PCSLangDom { m, r }
    }


    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let ct = pcs::encrypt(&self.pk, self.sk.as_ref(), &wit.m, &wit.r);
        PCSLangCoDom { ct }
    }

    fn sample_com_rand(&self, params: &schb::ProofParams) -> Self::Dom {
        let rand_range_bitlen =
            &self.lparams.range_bitlen +
            (params.lambda - 1) +
            ((params.reps_n as f64).log2().ceil() as u32);
        let m = BigInt::sample(rand_range_bitlen as usize);
        let r = BigInt::sample(
            (self.lparams.n_bitlen +
             (params.lambda - 1) +
             ((params.reps_n as f64).log2().ceil() as u32)) as usize);

        PCSLangDom { m, r }
    }

    fn compute_resp(&self, params: &schb::ProofParams, wit: &Vec<Self::Dom>, e_mat_i: &Vec<BigInt>, rand: &Self::Dom) -> Self::Dom {
        // No need to take modulo N because this computation does not overflow
        // in the range mode.
        let m =
            &rand.m +
            (0..params.reps_n as usize)
            .map(|j| &e_mat_i[j] * &wit[j].m)
            .fold(BigInt::from(0), |acc,x| acc + x );

        // For cramer-shoup variant, it's additive over integers
        let r =
            &rand.r +
            (0..params.reps_n as usize)
            .map(|j| &e_mat_i[j] * &wit[j].r)
            .fold(BigInt::from(0), |acc,x| acc + x );

        PCSLangDom { m, r }
    }

    fn resp_lhs(&self, params: &schb::ProofParams, inst: &Vec<Self::CoDom>, e_mat_i: &Vec<BigInt>, com: &Self::CoDom) -> Self::CoDom {

        let ct =
            BigInt::mod_mul(
                &com.ct,
                &(0..params.reps_n as usize)
                    .map(|j| BigInt::mod_pow(&inst[j].ct, &e_mat_i[j], &self.pk.nn))
                    .fold(BigInt::from(1), |acc,x| BigInt::mod_mul(&acc, &x, &self.pk.nn)),
                &self.pk.nn);

        PCSLangCoDom { ct }
    }

    fn check_resp_range(&self, params: &schb::ProofParams, resp: &Self::Dom) -> bool {
        let rand_range_bitlen =
            &self.lparams.range_bitlen +
            (params.lambda - 1) +
            ((params.reps_n as f64).log2().ceil() as u32);

        let rand_range = BigInt::pow(&BigInt::from(2), rand_range_bitlen);

        &resp.m < &rand_range
    }
}



////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////


#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier_cramer_shoup::*;
    use crate::protocols::schnorr_batched_generic as schb;

    #[test]
    fn test_correctness_batched_range() {
        for _i in 0..10 {
            let range_bitlen = 256;
            let lparams = PCSLangParams{ n_bitlen: 1024, range_bitlen };
            schb::generic_test_correctness::<PCSLang>(&schb::ProofParams::new(128,128),&lparams);
        }
    }

    #[test]
    fn test_correctness_batched_range_fs() {
        for _i in 0..10 {
            let range_bitlen = 256;
            let lparams = PCSLangParams{ n_bitlen: 1024, range_bitlen };
            schb::generic_test_correctness_fs::<PCSLang>(&schb::ProofParams::new(128,128),&lparams);
        }
    }
}
