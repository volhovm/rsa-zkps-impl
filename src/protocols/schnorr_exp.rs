/// A simple Schnorr variant for knowledge-of-discrete-logarithm (`x = g^w`)
/// in Z_N where N might be subverted.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;

use crate::protocols::schnorr_generic::*;


#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct ExpNLang {
    /// Bitlength of the RSA modulus
    pub n_bitlen: u32,
    /// RSA modulus
    pub n: BigInt,
    /// Randomly sampled from Z_N
    pub h: BigInt,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct ExpNLangDom {
    /// x | g = h^x mod N
    pub x: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct ExpNLangRange {
    /// g = h^x mod N
    pub g: BigInt,
}

impl ExpNLang {
    pub fn sample_lang(n_bitlen: u32) -> Self {
        use paillier::*;
        let n = Paillier::keypair_with_modulus_size(n_bitlen as usize).keys().0.n;
        let h = BigInt::sample_below(&n);
        ExpNLang { n_bitlen, n, h }
    }
}

impl Lang for ExpNLang {
    type Dom = ExpNLangDom;
    type Range = ExpNLangRange;

    fn sample_wit(&self) -> Self::Dom {
        ExpNLangDom { x: BigInt::sample_below(&self.n) }
    }

    fn eval(&self, wit: &Self::Dom) -> Self::Range {
        ExpNLangRange { g: BigInt::mod_pow(&self.h, &wit.x, &self.n) }
    }

    fn sample_com_rand(&self, params: &ProofParams) -> Self::Dom {
        let x = BigInt::sample((self.n_bitlen + params.ch_space_bitlen + params.lambda) as usize); 
        ExpNLangDom { x }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        ExpNLangDom { x: &wit.x * ch + &rand.x }
    }

    fn resp_lhs(&self, inst: &Self::Range, ch: &BigInt, com: &Self::Range) -> Self::Range {
        let g = BigInt::mod_mul(&BigInt::mod_pow(&inst.g, ch, &self.n), &com.g, &self.n);
        ExpNLangRange { g }
    }
}



#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_exp::*;
    use crate::protocols::schnorr_generic::*;

    #[test]
    fn test_correctness_expN() {
        let params = ProofParams::new(128, 16);
        let lang = ExpNLang::sample_lang(1024);
        generic_test_correctness(&params,&lang);
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(128, 16);
        let lang = ExpNLang::sample_lang(1024);
        generic_test_correctness_fs(&params,&lang);
    }
}
