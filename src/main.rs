#![allow(dead_code)]

use curv::BigInt;
use paillier::*;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};


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
    use rsazkps::protocols::designated as dv;
    let params = dv::DVParams::new(2048, 128, 1, false);
    let (vpk,_vsk) = dv::keygen(&params);
    assert!(dv::verify_vpk(&params,&vpk));
}

fn main() {
//    rsazkps::protocols::snark_paillier::test();
//    rsazkps::protocols::schnorr_paillier_batched::tests::test_correctness();
    test_dv_crs();
    //    rsazkps::protocols::n_gcd::test();
}
