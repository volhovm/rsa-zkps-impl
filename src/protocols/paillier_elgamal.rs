/// Paillier-Elgamal encryption scheme, which is a variant of Paillier
/// that is additively homomorphic in both message and randomness.
///
/// For the reference, see:
/// "A Simple Public-Key Cryptosystem with a Double Trapdoor Decryption Mechanism and Its Applications"
/// Section 3.
///
/// https://link.springer.com/chapter/10.1007/978-3-540-40061-5_3

use serde::{Serialize};
use get_size::GetSize;
use get_size_derive::*;

use super::paillier as p;

use crate::bigint::*;
use crate::utils as u;


#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct SecretKey {
    pub a: BigInt,
    pub ordg: BigInt,
    pub p: BigInt,
    pub q: BigInt,

    pub pp: BigInt,
    pub qq: BigInt,
    pub pp_inv_qq: BigInt,
    pub g_inv_pp: BigInt, // g^{-1} mod p^2
    pub g_inv_qq: BigInt, // g^{-1} mod q^2
    pub h_inv_pp: BigInt, // h^{-1} mod p^2
    pub h_inv_qq: BigInt, // h^{-1} mod q^2
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct PublicKey {
    pub n: BigInt,
    pub nn: BigInt,
    pub g: BigInt,
    pub h: BigInt,
    pub g_inv_nn: BigInt, // g^{-1} mod N^2
    pub h_inv_nn: BigInt, // h^{-1} mod N^2
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct Ciphertext {
    // g^r
    pub ct1: BigInt,
    // h^r (1+mN)^r
    pub ct2: BigInt
}

pub fn keygen(n_bitlen: usize) -> (PublicKey,SecretKey) {
    let (pk,sk) = p::keygen(n_bitlen);
    let p = &sk.p;
    let q = &sk.q;
    let n = &pk.n;
    let nn = &pk.nn;

    let pp = p * p;
    let qq = q * q;
    let pp_inv_qq = BigInt::mod_inv(&pp, &qq).unwrap();

    let ordg = (p*(p-1)).lcm(&(q*(q-1)));
    let alpha = BigInt::sample_below(n);
    let a = BigInt::sample_below(&ordg);
    let g = BigInt::mod_pow(&alpha,&BigInt::from(2),nn);
    let h = BigInt::mod_pow(&g,&alpha,nn);
    let g_inv_nn = BigInt::mod_inv(&g,nn).unwrap();
    let h_inv_nn = BigInt::mod_inv(&h,nn).unwrap();

    let g_inv_pp = BigInt::mod_inv(&g,&pp).unwrap();
    let g_inv_qq = BigInt::mod_inv(&g,&qq).unwrap();
    let h_inv_pp = BigInt::mod_inv(&h,&pp).unwrap();
    let h_inv_qq = BigInt::mod_inv(&h,&qq).unwrap();

    (PublicKey{n: pk.n, nn: pk.nn, g, h, g_inv_nn, h_inv_nn},
     SecretKey{a, ordg, p: sk.p, q: sk.q, pp, qq, pp_inv_qq, g_inv_pp, g_inv_qq, h_inv_pp, h_inv_qq})
}

pub fn encrypt_with_randomness(pk: &PublicKey,
                               m: &BigInt,
                               r: &BigInt) -> Ciphertext{
    let ct1 = u::bigint_mod_pow_explicit(&pk.g, &pk.g_inv_nn, &r, &pk.nn);
    let ct2 =
        BigInt::mod_mul(
            &u::bigint_mod_pow_explicit(&pk.h, &pk.h_inv_nn, &r, &pk.nn),
            &(1 + m * &pk.n),
            &pk.nn);

    Ciphertext{ ct1, ct2 }
}



pub fn encrypt_with_randomness_sk(pk: &PublicKey,
                                  sk: &SecretKey,
                                  m: &BigInt,
                                  r: &BigInt) -> Ciphertext {

    let pp = &sk.pp;
    let qq = &sk.qq;
    let pp_inv_qq = &sk.pp_inv_qq;

    let m_p = m % pp;
    let m_q = m % qq;

    let ct1_p = u::bigint_mod_pow_explicit(&pk.g, &sk.g_inv_pp, &r, &pp);
    let ct1_q = u::bigint_mod_pow_explicit(&pk.g, &sk.g_inv_qq, &r, &qq);

    let ct2_p =
        BigInt::mod_mul(
            &u::bigint_mod_pow_explicit(&pk.h, &sk.h_inv_pp, &r, &pp),
            &(1 + m_p * &pk.n),
            &pp);

    let ct2_q =
        BigInt::mod_mul(
            &u::bigint_mod_pow_explicit(&pk.h, &sk.h_inv_qq, &r, &qq),
            &(1 + m_q * &pk.n),
            &qq);

    Ciphertext{ ct1: u::crt_recombine(&ct1_p, &ct1_q, &pp, &qq, &pp_inv_qq),
                  ct2: u::crt_recombine(&ct2_p, &ct2_q, &pp, &qq, &pp_inv_qq) }

}

pub fn encrypt_with_randomness_opt(
    pk: &PublicKey,
    sk_m: Option<&SecretKey>,
    m: &BigInt,
    r: &BigInt) -> Ciphertext {

    if r == &BigInt::from(0) {
        return Ciphertext {
            ct1: BigInt::from(1),
            ct2: 1 + (BigInt::modulus(m,&pk.n)) * &pk.n
        };
    }

    match sk_m {
        Some(sk) => encrypt_with_randomness_sk(pk,sk,m,r),
        None => encrypt_with_randomness(pk,m,r),
    }
}


pub fn encrypt(pk: &PublicKey, m: &BigInt) -> Ciphertext {
    let r = BigInt::sample_below(&pk.nn);
    encrypt_with_randomness(pk,m,&r)
}



#[cfg(test)]
mod tests {

    use crate::protocols::paillier_elgamal::*;

    #[test]
    fn test_correctness() {
        let (pk,_sk) = keygen(1024);
        let m = BigInt::from(12345);
        let _ct = encrypt(&pk, &m);
        //unimplemented!()
        // TODO
    }

}
