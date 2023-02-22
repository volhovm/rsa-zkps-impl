/// Second-message Paillier-Elgamal encryption scheme variant, or "lite"
/// Cramer-Shoup variant, as explained here (Sec 2.4)
///
/// "A Simple Public-Key Cryptosystem with a Double Trapdoor Decryption
/// Mechanism and its Applications"
/// By Emmanuel Bresson, Dario Catalano, and David Pointcheval
///
/// ct = (1+mN)*h^r mod N^2

use serde::{Serialize};
use get_size::GetSize;
use get_size_derive::*;

use super::paillier as p;
use super::paillier_elgamal as pe;

use crate::bigint::*;
use crate::utils as u;



#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct SecretKey {
    pub p: BigInt,
    pub q: BigInt,
    pub p_inv_q: BigInt,

    pub pp: BigInt,
    pub qq: BigInt,
    pub pp_inv_qq: BigInt,

    pub lambda: BigInt,
    pub pi: BigInt,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct PublicKey {
    pub n: BigInt,
    pub nn: BigInt,
    pub h: BigInt,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct Ciphertext {
    // (1+mN) h^r mod N^2
    pub ct: BigInt,
}

pub fn keygen(n_bitlen: usize) -> (PublicKey,SecretKey) {
    let (pk,sk) = p::keygen(n_bitlen);
    let p = &sk.p;
    let q = &sk.q;
    let n = &pk.n;
    let nn = &pk.nn;

    let p_inv_q = BigInt::mod_inv(p, q).unwrap();
    let pp = p * p;
    let qq = q * q;
    let pp_inv_qq = BigInt::mod_inv(&pp, &qq).unwrap();

    let mu = BigInt::sample_below(nn);
    let g = -BigInt::mod_pow(&mu,&(&BigInt::from(2)*n),nn);
    let z = BigInt::sample_below(&(nn / &BigInt::from(2)));
    let h = BigInt::mod_pow(&g,&z,nn);


    let lambda = BigInt::lcm(&(p - &BigInt::from(1)),
                             &(q - &BigInt::from(1)));

    let pi = BigInt::mod_inv(&lambda, &n).unwrap();


    (PublicKey{n: pk.n, nn: pk.nn, h },
     SecretKey{p: sk.p, q: sk.q, p_inv_q, pp, qq, pp_inv_qq, lambda, pi })
}


pub fn encrypt(pk: &PublicKey,
               sk_m: Option<&SecretKey>,
               m: &BigInt,
               r: &BigInt) -> Ciphertext {
    let ct = match sk_m {
        None => {
            BigInt::mod_mul(&(1 + m * &pk.n),
                            &BigInt::mod_pow(&pk.h, &r, &pk.nn),
                            &pk.nn)
        },
        Some(sk) => {
            let ct_pp = BigInt::mod_mul(&(1 + m * &pk.n),
                                        &BigInt::mod_pow(&pk.h, &r, &sk.pp),
                                        &sk.pp);
            let ct_qq = BigInt::mod_mul(&(1 + m * &pk.n),
                                        &BigInt::mod_pow(&pk.h, &r, &sk.qq),
                                        &sk.qq);
            u::crt_recombine(&ct_pp, &ct_qq, &sk.pp, &sk.qq, &sk.pp_inv_qq)
        }
    };

    Ciphertext{ ct }
}

pub fn decrypt(pk: &PublicKey,
               sk: &SecretKey,
               ct: &Ciphertext) -> BigInt {

    let p_inv_q = BigInt::mod_inv(&sk.p, &sk.q).unwrap();
    let qminusone = &sk.q - 1;
    let pminusone = &sk.p - 1;
    let hp = h(&sk.p, &sk.pp, &pk.n);
    let hq = h(&sk.q, &sk.qq, &pk.n);
    let (cp, cq) = u::crt_decompose(&ct.ct, &sk.pp, &sk.qq);
    let mp = {
        let dp = BigInt::mod_pow(&cp, &pminusone, &sk.pp);
        let lp = (&dp - 1) / &sk.p;
        (&lp * &hp) % &sk.p
    };
    let mq = {
        let dq = BigInt::mod_pow(&cq, &qminusone, &sk.qq);
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

    use crate::protocols::paillier_cramer_shoup::*;
    use crate::bigint::*;

    #[test]
    fn test_correctness() {
        for _i in 0..100 {
            let (pk,sk) = keygen(1024);
            let m = BigInt::sample_below(&pk.n);
            let r = BigInt::sample_below(&pk.n);
            assert!(decrypt(&pk,&sk,&encrypt(&pk, None, &m, &r)) == m);
            assert!(decrypt(&pk,&sk,&encrypt(&pk, Some(&sk), &m, &r)) == m);
        }
    }

}
