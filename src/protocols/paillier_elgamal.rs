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


#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct PESecretKey {
    pub a: BigInt,
    pub ordg: BigInt,
    pub p: BigInt,
    pub q: BigInt
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize)]
pub struct PEPublicKey {
    pub n: BigInt,
    pub n2: BigInt,
    pub g: BigInt,
    pub h: BigInt
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
    let n2 = &pk.nn;

    let ordg = (p*(p-1)).lcm(&(q*(q-1)));
    let alpha = BigInt::sample_below(n);
    let a = BigInt::sample_below(&ordg);
    let g = BigInt::mod_pow(&alpha,&BigInt::from(2),n2);
    let h = BigInt::mod_pow(&g,&alpha,n2);

    (PEPublicKey{n: pk.n, n2: pk.nn, g, h},
     PESecretKey{a, ordg, p: sk.p, q: sk.q})
}

pub fn encrypt_with_randomness(pk: &PEPublicKey,
                               m: &BigInt,
                               r: &BigInt) -> PECiphertext{
    let ct1 = super::utils::bigint_mod_pow(&pk.g, &r, &pk.n2);
    let ct2 =
        BigInt::mod_mul(
            &super::utils::bigint_mod_pow(&pk.h, &r, &pk.n2),
            &(1 + m * &pk.n),
            &pk.n2);

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

    let pp = &sk.p * &sk.p;
    let qq = &sk.q * &sk.q;
    let ppinv = BigInt::mod_inv(&pp, &qq).unwrap();

    let m_p = m % &pp;
    let m_q = m % &qq;

    let ct1_p = super::utils::bigint_mod_pow(&pk.g, &r, &pp);
    let ct1_q = super::utils::bigint_mod_pow(&pk.g, &r, &qq);

    let ct2_p =
        BigInt::mod_mul(
            &super::utils::bigint_mod_pow(&pk.h, &r, &pp),
            &(1 + m_p * &pk.n),
            &pp);

    let ct2_q =
        BigInt::mod_mul(
            &super::utils::bigint_mod_pow(&pk.h, &r, &qq),
            &(1 + m_q * &pk.n),
            &qq);

    PECiphertext{ ct1: crt_recombine(&ct1_p, &ct1_q, &pp, &qq, &ppinv),
                  ct2: crt_recombine(&ct2_p, &ct2_q, &pp, &qq, &ppinv) }

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
    let r = BigInt::sample_below(&pk.n2);
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
