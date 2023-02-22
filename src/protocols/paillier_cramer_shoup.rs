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
pub struct PCSSecretKey {
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
pub struct PCSPublicKey {
    pub n: BigInt,
    pub nn: BigInt,
    pub h: BigInt,
}

#[derive(PartialEq, Eq, Clone, Debug, Serialize, GetSize)]
pub struct PCSCiphertext {
    // (1+mN) h^r mod N^2
    pub ct: BigInt,
}

pub fn keygen(n_bitlen: usize) -> (PCSPublicKey,PCSSecretKey) {
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


    (PCSPublicKey{n: pk.n, nn: pk.nn, h },
     PCSSecretKey{p: sk.p, q: sk.q, p_inv_q, pp, qq, pp_inv_qq, lambda, pi })
}


pub fn encrypt(pk: &PCSPublicKey,
               sk_m: Option<&PCSSecretKey>,
               m: &BigInt,
               r: &BigInt) -> PCSCiphertext {
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

    PCSCiphertext{ ct }
}

pub fn decrypt(pk: &PCSPublicKey,
               sk: &PCSSecretKey,
               ct: &PCSCiphertext) -> BigInt {

    // We use parallelism here because the original Paillier library does.
    // Maybe we should disable it in both places though.
    // We can use p-1 as an exponent here, which makes things faster.
    // See paillier implementation.
    let m1_pp = BigInt::mod_pow(&ct.ct,&sk.lambda,&sk.pp);
    let m1_qq = BigInt::mod_pow(&ct.ct,&sk.lambda,&sk.qq);
    let m1 = u::crt_recombine(&m1_pp, &m1_qq, &sk.pp, &sk.qq, &sk.pp_inv_qq);

    let m2 = &m1 / &pk.n;

    let m3_p = BigInt::mod_mul(&m2, &sk.pi, &sk.p);
    let m3_q = BigInt::mod_mul(&m2, &sk.pi, &sk.q);
    let m3 = u::crt_recombine(&m3_p, &m3_q, &sk.p, &sk.q, &sk.p_inv_q);

    m3
}


#[cfg(test)]
mod tests {

    use crate::protocols::paillier_cramer_shoup::*;
    use crate::bigint::*;

    #[test]
    fn test_correctness() {
        for _i in 0..10 {
            let (pk,sk) = keygen(1024);
            let m = BigInt::sample_below(&pk.n);
            let r = BigInt::sample_below(&pk.n);
            assert!(decrypt(&pk,&sk,&encrypt(&pk, None, &m, &r)) == m);
            assert!(decrypt(&pk,&sk,&encrypt(&pk, Some(&sk), &m, &r)) == m);
        }
    }

}
