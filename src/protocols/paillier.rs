/// Small wrapper around Paillier implementation by kzen_paillier.


use serde::{Serialize};
use paillier::Paillier;
use paillier::{Randomness, RawPlaintext, Keypair, Encrypt, Decrypt, RawCiphertext,
               KeyGeneration, EncryptWithChosenRandomness};
use paillier;

use crate::bigint::*;

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct EncryptionKey {
    pub n: BigInt,
    pub nn: BigInt
}

#[derive(Clone, PartialEq, Eq, Debug, Serialize)]
pub struct DecryptionKey {
    pub p: BigInt,
    pub q: BigInt
}

pub fn keygen(n_bitlen: usize) -> (EncryptionKey,DecryptionKey) {
    let (pk,sk) = Paillier::keypair_with_modulus_size(n_bitlen).keys();
    return (EncryptionKey { n: pk.n.wrap(), nn: pk.nn.wrap() },
            DecryptionKey { p: sk.p.wrap(), q: sk.q.wrap() });
}

pub fn paillier_enc_opt(pk: &EncryptionKey,
                        sk_m: Option<&DecryptionKey>,
                        m: &BigInt,
                        r: &BigInt) -> BigInt {
    if r == &BigInt::from(1) {
        return 1 + (BigInt::modulus(m,&pk.n)) * &pk.n;
    }
    match sk_m {
        Some(sk) => {
            Paillier::encrypt_with_chosen_randomness(
                &paillier::DecryptionKey{p: sk.p.v.clone(),
                                        q: sk.q.v.clone()},
                RawPlaintext::from(&m.v),
                &Randomness::from(&r.v)).0.into_owned().wrap()
        }
        None =>
            Paillier::encrypt_with_chosen_randomness(
                &paillier::EncryptionKey{n: pk.n.v.clone(),
                                        nn: pk.nn.v.clone()},
                RawPlaintext::from(&m.v),
                &Randomness::from(&r.v)).0.into_owned().wrap()
    }
}

pub fn decrypt(sk: &DecryptionKey,
               ct: &BigInt) -> BigInt {
    Paillier::decrypt(&paillier::DecryptionKey{p: sk.p.v.clone(),
                                               q: sk.q.v.clone()},
                      RawCiphertext::from(&ct.v)).0.into_owned().wrap()
}
