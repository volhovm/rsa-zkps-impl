#![allow(dead_code)]

use serde::{Serialize};
use curv::BigInt;
use curv::arithmetic::traits::BasicOps;
use paillier::*;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};

use rsazkps::protocols::schnorr_paillier as sp;
use rsazkps::protocols::designated as dv;
use rsazkps::protocols::designated_range as dvr;

fn estimate_size<T: Serialize>(x: &T) -> usize {
    let x: Vec<u8> = rmp_serde::to_vec(x).unwrap();
    x.len()
}

fn estimate_size_designated(params: &dv::DVParams) {
    print!("DV FS, malicious {:?}, GGM {:?}. ",
             params.malicious_setup, params.ggm_mode);

    let (vpk,vsk) = dv::keygen(&params);
    dv::verify_vpk(&params, &vpk);
    let (lang,inst,wit) = dv::sample_liw(params);
    let proof = dv::fs_prove(params,&vpk,&lang,&inst,&wit,0);
    println!("VPK: {} B, VSK: {} B, proof: {} B",
             estimate_size(&vpk),
             estimate_size(&vsk),
             estimate_size(&proof))
}

fn estimate_size_designated_range(params: &dvr::DVRParams) {
    print!("DVRange FS, malicious {:?}, GGM {:?}. ",
             params.malicious_setup, params.ggm_mode);

    let (vpk,vsk) = dvr::keygen(&params);
    let (lang,inst,wit) = dvr::sample_liw(params);
    let proof = dvr::fs_prove(params,&vpk,&lang,&inst,&wit,0);

    println!("VPK: {} B, VSK: {} B, proof: {} B",
             estimate_size(&vpk),
             estimate_size(&vsk),
             estimate_size(&proof))
}

fn estimate_size_schnorr_paillier(params: &sp::ProofParams) {
    print!("Schnorr-Pailler FS, range {:?}. ", !params.range_params.is_none());

    let (lang,inst,wit) = sp::sample_liw(&params);
    let proof = sp::fs_prove(&params,&lang,&inst,&wit);

    println!("proof: {} B",
             estimate_size(&proof))
}

fn estimate_proof_sizes() {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries = 32;
    let range_bitlen = 256;
    let range = BigInt::pow(&BigInt::from(2), range_bitlen);

    println!("Estimating proof sizes; log(N) = {}, lambda = {}, queries = {}, log(Range) = {}",
             n_bitlen, lambda, queries, range_bitlen);


    estimate_size_schnorr_paillier(&sp::ProofParams::new(n_bitlen, lambda, 22));
    estimate_size_schnorr_paillier(&sp::ProofParams::new_range(n_bitlen, lambda, range.clone()));

    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, false, true));
    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, true, true));
    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, false, false));
    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, true, false));

    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries as u32, false, true));
    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries as u32, true, true));
    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries as u32, false, false));
    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries as u32, true, false));

}


fn check_correct_ciphertext_proof() {
    let kp:Keypair = Paillier::keypair();
    let (pk,_) = kp.keys();

    let m = BigInt::from(1u32);
    let r = BigInt::from(2u32);

    let ct = Paillier::encrypt_with_chosen_randomness(
             &pk,
             RawPlaintext::from(m.clone()),
             &Randomness(r.clone())).0.into_owned();

    let w = CiphertextWitness{ x: m.clone(), r: r };
    let w_false = CiphertextWitness{x:m,r:BigInt::from(3)};
    let x = CiphertextStatement{ ek: pk, c: ct };

    let res1 = CiphertextProof::prove(&w,&x).verify(&x);
    println!("Honest proof verifies: {:?}", res1);

    let res2 = CiphertextProof::prove(&w_false,&x).verify(&x);
    println!("Bogus proof verification gives: {:?}", res2);
}

fn test_dv_crs() {
    let params = dv::DVParams::new(2048, 128, 32, false, false);
    println!("{:?}", params);
    let (vpk,_vsk) = dv::keygen(&params);
    assert!(dv::verify_vpk(&params,&vpk));
}


fn main() {
    //rsazkps::protocols::designated_range::test_keygen_correctness();
    //test_dv_crs();
    estimate_proof_sizes();
}
