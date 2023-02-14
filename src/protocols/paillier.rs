/// Small wrapper around Paillier implementation by kzen_paillier.

use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, DecryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, Integer};
use curv::{BigInt};


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
                sk,
                RawPlaintext::from(m),
                &Randomness::from(r)).0.into_owned()
        }
        None =>
            Paillier::encrypt_with_chosen_randomness(
                pk,
                RawPlaintext::from(m),
                &Randomness::from(r)).0.into_owned()
    }
}
