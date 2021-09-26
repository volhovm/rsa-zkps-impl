use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use std::fmt;
use std::iter;

use super::schnorr_paillier as sp;


pub struct DVParams {
    pub n_bitlen: usize,
    pub lambda: u32,
    pub two_lambda: BigInt,
    pub nizk_params: sp::ProofParams
}

impl DVParams {
    pub fn new(n_bitlen: usize, lambda: u32) -> DVParams {
        let two_lambda = BigInt::pow(&BigInt::from(2), lambda);
        let nizk_params = sp::ProofParams::new_range(n_bitlen,lambda,two_lambda.clone());
        DVParams{n_bitlen, lambda, two_lambda, nizk_params}
    }
}

pub struct VSK{
    sk: DecryptionKey
}

pub struct VPK{
    pk: EncryptionKey,
    cts: Vec<BigInt>,
    nizks: Vec<sp::FSProof>
}


pub fn keygen(params: DVParams) -> (VPK, VSK) {
    // This can be more effective in terms of move/copy
    // e.g. Instance/Witness could contain references inside?
    let (pk,sk) = Paillier::keypair_with_modulus_size(params.n_bitlen).keys();

    let chs: Vec<BigInt> =
        iter::repeat(BigInt::sample_below(&params.two_lambda)).take(2*params.lambda as usize).collect();

    let cts_rs: Vec<(BigInt,BigInt)> =
        chs.iter().map( |ch| {
            let r = BigInt::sample_below(&pk.n);
            let ct = Paillier::encrypt_with_chosen_randomness(
                &pk,
                RawPlaintext::from(ch),
                &Randomness::from(&r)).0.into_owned();
            (r, ct)
        }).collect();

    let lang = sp::Language{pk:pk.clone()};
    let nizks:Vec<sp::FSProof> =
        chs.iter().zip(cts_rs.iter()).map(|(m,(r,ct))| {
            sp::fs_prove(&params.nizk_params,
                         &lang,
                         &(sp::Instance{ct:ct.clone()}),
                         &(sp::Witness{m:m.clone(),r:r.clone()}))
        }).collect();

    // Ciphertexts only
    let cts: Vec<BigInt> = cts_rs.iter().map(|x| x.1.clone()).collect();

    (VPK{pk,cts,nizks},VSK{sk})
}

pub fn verify_vpk(params: &DVParams, vpk: &VPK) -> bool {
    let lang = sp::Language{ pk: vpk.pk.clone() };
    let (res0,precomp) = sp::fs_verify0(&params.nizk_params, &lang);
    if !res0 { return false; };

    for (ct,nizk) in vpk.cts.iter().zip(vpk.nizks.iter()) {
        let res = sp::fs_verify(&params.nizk_params,
                                &lang,
                                &(sp::Instance{ct:ct.clone()}),
                                &precomp,
                                &nizk);
        if !res { return false; }
    }

    return true;
}

pub fn prover1() {
}
pub fn verifier1() {
}
pub fn prover2() {
}
pub fn verifier2() {
}
