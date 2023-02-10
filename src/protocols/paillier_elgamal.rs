/// Paillier-Elgamal encryption scheme, which is a variant of Paillier
/// that is additively homomorphic in both message and randomness.
///
/// For the reference, see:
/// "A Simple Public-Key Cryptosystem with a Double Trapdoor Decryption Mechanism and Its Applications"
/// Section 3.
///
/// https://link.springer.com/chapter/10.1007/978-3-540-40061-5_3

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, Integer};
use curv::{BigInt};
use serde::{Serialize};
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};

use super::utils::bigint_mod_pow_explicit;


#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct PESecretKey {
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

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct PEPublicKey {
    pub n: BigInt,
    pub nn: BigInt,
    pub g: BigInt,
    pub h: BigInt,
    pub g_inv_nn: BigInt, // g^{-1} mod N^2
    pub h_inv_nn: BigInt, // h^{-1} mod N^2
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct PECiphertext {
    // g^r
    pub ct1: BigInt,
    // h^r (1+mN)^r
    pub ct2: BigInt
}

pub fn keygen(n_bitlen: usize) -> (PEPublicKey,PESecretKey) {
    let (pk,sk) = Paillier::keypair_with_modulus_size(n_bitlen).keys();
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

    (PEPublicKey{n: pk.n, nn: pk.nn, g, h, g_inv_nn, h_inv_nn},
     PESecretKey{a, ordg, p: sk.p, q: sk.q, pp, qq, pp_inv_qq, g_inv_pp, g_inv_qq, h_inv_pp, h_inv_qq})
}

pub fn encrypt_with_randomness(pk: &PEPublicKey,
                               m: &BigInt,
                               r: &BigInt) -> PECiphertext{
    let ct1 = bigint_mod_pow_explicit(&pk.g, &pk.g_inv_nn, &r, &pk.nn);
    let ct2 =
        BigInt::mod_mul(
            &bigint_mod_pow_explicit(&pk.h, &pk.h_inv_nn, &r, &pk.nn),
            &(1 + m * &pk.n),
            &pk.nn);

    PECiphertext{ ct1, ct2 }
}

fn crt_recombine(vp: &BigInt,
                 vq: &BigInt,
                 p: &BigInt,
                 q: &BigInt,
                 pinv: &BigInt) -> BigInt {
    let diff = BigInt::mod_sub(vq, vp, q);
    let u = (&diff * pinv) % q;
    vp + &u * p
}

pub fn encrypt_with_randomness_sk(pk: &PEPublicKey,
                                  sk: &PESecretKey,
                                  m: &BigInt,
                                  r: &BigInt) -> PECiphertext {

    let pp = &sk.pp;
    let qq = &sk.qq;
    let pp_inv_qq = &sk.pp_inv_qq;

    let m_p = m % pp;
    let m_q = m % qq;

    let ct1_p = bigint_mod_pow_explicit(&pk.g, &sk.g_inv_pp, &r, &pp);
    let ct1_q = bigint_mod_pow_explicit(&pk.g, &sk.g_inv_qq, &r, &qq);

    let ct2_p =
        BigInt::mod_mul(
            &bigint_mod_pow_explicit(&pk.h, &sk.h_inv_pp, &r, &pp),
            &(1 + m_p * &pk.n),
            &pp);

    let ct2_q =
        BigInt::mod_mul(
            &bigint_mod_pow_explicit(&pk.h, &sk.h_inv_qq, &r, &qq),
            &(1 + m_q * &pk.n),
            &qq);

    PECiphertext{ ct1: crt_recombine(&ct1_p, &ct1_q, &pp, &qq, &pp_inv_qq),
                  ct2: crt_recombine(&ct2_p, &ct2_q, &pp, &qq, &pp_inv_qq) }

}

pub fn encrypt_with_randomness_opt(
    pk: &PEPublicKey,
    sk_m: Option<&PESecretKey>,
    m: &BigInt,
    r: &BigInt) -> PECiphertext {
    match sk_m {
        Some(sk) => encrypt_with_randomness_sk(pk,sk,m,r),
        None => encrypt_with_randomness(pk,m,r),
    }
}


pub fn encrypt(pk: &PEPublicKey, m: &BigInt) -> PECiphertext {
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
