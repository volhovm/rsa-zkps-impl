use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, Integer};
use curv::{BigInt};
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};

// "A Simple Public-Key Cryptosystem with a Double Trapdoor Decryption Mechanism and Its Applications"
// Section 3.
// https://link.springer.com/chapter/10.1007/978-3-540-40061-5_3

#[derive(Clone, Debug)]
pub struct PESecretKey {
    pub a: BigInt,
    pub ordg: BigInt,
    pub p: BigInt,
    pub q: BigInt
}

#[derive(Clone, Debug)]
pub struct PEPublicKey {
    pub n: BigInt,
    pub n2: BigInt,
    pub g: BigInt,
    pub h: BigInt
}

#[derive(Clone, Debug)]
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
    let ct1 = BigInt::mod_pow(&pk.g, &r, &pk.n2);
    let ct2 =
        BigInt::mod_mul(
            &BigInt::mod_pow(&pk.h, &r, &pk.n2),
            &(1 + m * &pk.n),
            &pk.n2);

    PECiphertext{ ct1, ct2 }
}

pub fn encrypt(pk: &PEPublicKey, m: &BigInt) -> PECiphertext {
    let r = BigInt::sample_below(&pk.n2);
    encrypt_with_randomness(pk,m,&r)
}
