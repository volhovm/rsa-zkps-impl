/// A simple Schnorr variant for knowledge-of-discrete-logarithm (`x = g^w`)
/// in Z_N where N might be subverted.

use get_size::GetSize;
use get_size_derive::*;
use serde::{Serialize};
use std::fmt;

use crate::bigint::*;
use crate::utils as u;
use crate::protocols::schnorr_generic::*;
use crate::protocols::paillier as p;


#[derive(Clone, PartialEq, Debug, Serialize, GetSize)]
pub struct ExpNLang {
    /// Bitlength of the RSA modulus
    pub n_bitlen: u32,
    /// RSA modulus
    pub n: BigInt,
    /// Randomly sampled from Z_N
    pub h: BigInt,

    pub p: Option<BigInt>,
    pub q: Option<BigInt>,
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct ExpNLangDom {
    /// x | g = h^x mod N
    pub x: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct ExpNLangCoDom {
    /// g = h^x mod N
    pub g: BigInt,
}


impl Lang for ExpNLang {
    type LangParams = u32;
    type Dom = ExpNLangDom;
    type CoDom = ExpNLangCoDom;

    fn sample_lang(n_bitlen: &Self::LangParams) -> Self {
        let (pk,sk) = p::keygen(*n_bitlen as usize);
        let n = pk.n;
        let h = BigInt::sample_below(&n);
        ExpNLang { n_bitlen: *n_bitlen, n, h, p: Some(sk.p.clone()), q: Some(sk.q.clone())
        }
    }

    fn to_public(&self) -> Self {
        let mut other = self.clone();
        other.p = None;
        other.q = None;
        return other
    }

    fn pre_verify(&self, params: &ProofParams) -> bool {
        if params.ch_space_bitlen > 32 {
            panic!("schnorr_exp: verify0: ch_space is too big: {:?} bits",
                   params.ch_space_bitlen)
        }
        u::check_small_primes(2u64.pow(params.ch_space_bitlen),&self.n)
    }

    fn sample_wit(&self) -> Self::Dom {
        ExpNLangDom { x: BigInt::sample_below(&self.n) }
    }

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom {
        let g = match self.p.as_ref() {
            None => BigInt::mod_pow(&self.h, &wit.x, &self.n),
            Some(p) => {
                let q = self.q.as_ref().expect("schnorr_exp: p is Some, q is not!");
                let p_inv_q = BigInt::mod_inv(p, q).unwrap();
                let g_p = BigInt::mod_pow(&self.h, &wit.x, p);
                let g_q = BigInt::mod_pow(&self.h, &wit.x, q);
                u::crt_recombine(&g_p, &g_q, p, q, &p_inv_q)
            },
        };

        ExpNLangCoDom { g }
    }

    fn sample_com_rand(&self, params: &ProofParams) -> Self::Dom {
        let x = BigInt::sample((self.n_bitlen + params.ch_space_bitlen + params.lambda) as usize);
        ExpNLangDom { x }
    }

    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom {
        ExpNLangDom { x: &wit.x * ch + &rand.x }
    }

    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom {
        let g = BigInt::mod_mul(&BigInt::mod_pow(&inst.g, ch, &self.n), &com.g, &self.n);
        ExpNLangCoDom { g }
    }

    fn check_resp_range(&self, _: &ProofParams, _: &Self::Dom) -> bool {
        panic!("schnorr_exp does not run in the range mode");
    }
}



#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_exp::*;
    use crate::protocols::schnorr_generic::*;

    use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Roots, Converter};
    use curv::BigInt;

    #[test]
    fn test_correctness() {
        let params = ProofParams::new(128, 16);
        generic_test_correctness::<ExpNLang>(&params,&1024);
    }


    #[test]
    fn test_correctness_fs() {
        for _i in [0..10] {
            let params = ProofParams::new(128, 16);
            generic_test_correctness_fs::<ExpNLang>(&params,&1024);
        }
    }
}
