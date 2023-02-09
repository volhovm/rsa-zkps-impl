#![allow(dead_code)]

use serde::{Serialize};
use curv::BigInt;
use curv::arithmetic::traits::BasicOps;
use paillier::*;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};
use std::time::{SystemTime};

use rsazkps::protocols::schnorr_generic as sch;
use rsazkps::protocols::schnorr_paillier as sp;
use rsazkps::protocols::schnorr_paillier_elgamal as spe;

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

fn estimate_size_schnorr<L: sch::Lang>(params: &sch::ProofParams, lparams: &L::LangParams) {
    print!("Schnorr FS, {:?} {:?}. ", params, lparams);

    let (lang,inst,wit) = L::sample_liw(lparams);
    let proof = sch::fs_prove(&params,&lang,&inst,&wit);

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

    estimate_size_schnorr::<sp::PLang>(
        &sch::ProofParams::new(lambda, 1),
        &sp::PLangParams{ n_bitlen, range: None });
    estimate_size_schnorr::<sp::PLang>(
        &sch::ProofParams::new(lambda, 22),
        &sp::PLangParams{ n_bitlen, range: None });
    estimate_size_schnorr::<sp::PLang>(
        &sch::ProofParams::new_range(lambda),
        &sp::PLangParams{ n_bitlen, range: Some(range.clone()) });

    estimate_size_schnorr::<spe::PELang>(
        &sch::ProofParams::new(lambda, 1),
        &n_bitlen);
    estimate_size_schnorr::<spe::PELang>(
        &sch::ProofParams::new(lambda, 22),
        &n_bitlen);


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

fn test_dv() {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries: usize = 32;
    let malicious_setup = true;
    let ggm_mode = true;
    let params = dv::DVParams::new(n_bitlen, lambda, queries as u32, malicious_setup, ggm_mode);

    let (vpk,vsk) = dv::keygen(&params);


    for query_ix in 0..1 {
    let (lang,inst,wit) = dv::sample_liw(&params);

    let t_1 = SystemTime::now();
    let (com,cr) = dv::prove1(&params,&lang);
    let t_2 = SystemTime::now();
    let ch1 = dv::verify1(&params);
    let t_3 = SystemTime::now();
    let resp1 = dv::prove2(&params,&vpk,&cr,&wit,&ch1,query_ix);
    let t_4 = SystemTime::now();
    let ch2 = dv::verify2(&params);
    let t_5 = SystemTime::now();
    let resp2 = dv::prove3(&params,&vpk,&cr,&wit,ch2.as_ref());
    let t_6 = SystemTime::now();

    dv::verify3(&params,&vsk,&vpk,&lang,&inst,
            &com,&ch1,ch2.as_ref(),&resp1,resp2.as_ref(),query_ix);
    let t_7 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_delta5 = t_6.duration_since(t_5).unwrap();
    let t_delta6 = t_7.duration_since(t_6).unwrap();
    let t_total = t_7.duration_since(t_1).unwrap();
    println!("DV (total {:?}):
prove1   {:?}
verify1  {:?}
prove2   {:?}
verify2  {:?}
prove3   {:?}
verify3  {:?}",
             t_total,t_delta1, t_delta2, t_delta3, t_delta4, t_delta5, t_delta6);

    }
}


fn main() {
    //rsazkps::protocols::designated_range::test_keygen_correctness();
    //test_dv_crs();
    //estimate_proof_sizes();
    test_dv();
}
