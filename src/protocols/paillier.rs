/// Implementation of Paillier encryption scheme, basically
/// copying kzen_paillier library, but without parallelism.

use get_size::GetSize;
use get_size_derive::*;

use serde::{Serialize};
use paillier::Paillier;
use paillier::{Randomness, RawPlaintext, Keypair, Encrypt, Decrypt, RawCiphertext,
               KeyGeneration, EncryptWithChosenRandomness};
use paillier;

use crate::utils as u;
use crate::bigint::*;


#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct PublicKey {
    pub n: BigInt,
    pub nn: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize, GetSize)]
pub struct SecretKey {
    pub p: BigInt,
    pub q: BigInt
}

pub fn keygen(n_bitlen: usize) -> (PublicKey,SecretKey) {
    let (pk,sk) = Paillier::keypair_with_modulus_size(n_bitlen).keys();
    return (PublicKey { n: pk.n.wrap(), nn: pk.nn.wrap() },
            SecretKey { p: sk.p.wrap(), q: sk.q.wrap() });
}

pub fn encrypt(pk: &PublicKey,
               sk_m: Option<&SecretKey>,
               m: &BigInt,
               r: &BigInt) -> BigInt {
    if r == &BigInt::from(1) {
        return 1 + (BigInt::modulus(m,&pk.n)) * &pk.n;
    }

    match sk_m {
        None => {
            let gm: BigInt = (1 + m * &pk.n) % &pk.nn;
            let c = (gm * BigInt::mod_pow(&r,&pk.n,&pk.nn)) % &pk.nn;
            c
        },
        Some(sk) => {
            let pp = &sk.p * &sk.p;
            let qq = &sk.q * &sk.q;
            let pp_inv_qq = BigInt::mod_inv(&pp, &qq).unwrap();

            let rnp = BigInt::mod_pow(&r, &pk.n, &pp);
            let cp = BigInt::mod_mul(&(1 + m * &pk.n), &rnp, &pp);

            let rnq = BigInt::mod_pow(&r, &pk.n, &qq);
            let cq = BigInt::mod_mul(&(1 + m * &pk.n), &rnq, &qq);

            let c = u::crt_recombine(&cp, &cq, &pp, &qq, &pp_inv_qq) % &pk.nn;
            c
        },
    }
}

pub fn decrypt(sk: &SecretKey,
               ct: &BigInt) -> BigInt {
    let qq = &sk.q * &sk.q;
    let pp = &sk.p * &sk.p;
    let n = &sk.p * &sk.q;
    let p_inv_q = BigInt::mod_inv(&sk.p, &sk.q).unwrap();
    let qminusone = &sk.q - 1;
    let pminusone = &sk.p - 1;
    let hp = h(&sk.p, &pp, &n);
    let hq = h(&sk.q, &qq, &n);
    let (cp, cq) = u::crt_decompose(ct, &pp, &qq);
    let mp = {
        let dp = BigInt::mod_pow(&cp, &pminusone, &pp);
        let lp = (&dp - 1) / &sk.p;
        (&lp * &hp) % &sk.p
    };
    let mq = {
        let dq = BigInt::mod_pow(&cq, &qminusone, &qq);
        let lq = (&dq - 1) / &sk.q;
        (&lq * &hq) % &sk.q
    };
    let m = u::crt_recombine(&mp, &mq, &sk.p, &sk.q, &p_inv_q);
    m
}


fn h(p: &BigInt, pp: &BigInt, n: &BigInt) -> BigInt {
    // here we assume:
    //  - p \in {P, Q}
    //  - n = P * Q
    //  - g = 1 + n

    // compute g^{p-1} mod p^2
    let gp = (1 - n) % pp;
    // compute L_p(.)
    let lp = (&gp - 1) / p;
    // compute L_p(.)^{-1}
    BigInt::mod_inv(&lp, p).unwrap()
}


#[cfg(test)]
mod tests {

    use crate::protocols::paillier::*;
    use crate::bigint::*;

    #[test]
    fn test_correctness() {
        for _i in 0..100 {
            let (pk,sk) = keygen(1024);
            let m = BigInt::sample_below(&pk.n);
            let r = BigInt::sample_below(&pk.n);
            assert!(decrypt(&sk,&encrypt(&pk, None, &m, &r)) == m);
            assert!(decrypt(&sk,&encrypt(&pk, Some(&sk), &m, &r)) == m);
        }
    }

}
