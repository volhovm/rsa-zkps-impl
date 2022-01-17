use curv::BigInt;
use paillier::*;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};
use rand::distributions::{Distribution, Uniform};
use rand::thread_rng;
use rand::seq::SliceRandom;

fn test_lemma() {
    let mut rng = rand::thread_rng();
//    let gen = Uniform::from(0..(2 * (params.lambda as usize)));

    for lambda in [14,16,18,20] {
    let m = lambda; // should be < 2*lambda
    let two_lambda = 1 << lambda;
    let attempts1 = 100;
    let attempts2 = 10000;

    //let mut dx = vec![0; 2*lambda];
    let mut dx: Vec<i128> = vec![0;2*lambda];
    let mut jx: Vec<i128> = vec![0;m-1];

    let mut totalcount = 0;
    for _i in 0..attempts1 {
        let mut count = 0;
        for j in 0..2*lambda {
            let v: i128 = Uniform::from(-two_lambda..two_lambda).sample(&mut rng);
            dx[j] = v;
        }
        for _i in 0..attempts2 {
            dx.shuffle(&mut rng);
            for j in 0..m-1 {
                jx[j] = dx[j+1] - dx[0];
            }
            //println!("Numbers: {:?}",jx);

            for i in 1..m-1 {
                jx[0] = num::integer::gcd::<i128>(jx[0],jx[i]);
            }

            if jx[0] != 1 {
                count += 1;
                totalcount +=1;
            }
        }
        //println!("Number of nonzero: {:?}/{:?}",count,attempts2);
    }
    println!("lambda = {:?}: {:?}/{:?}",lambda,totalcount,attempts1*attempts2);
    }
}

fn _check_correct_ciphertext_proof() {
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

fn main() {
    test_lemma();
//    rsazkps::protocols::snark_paillier::test();
//    rsazkps::protocols::schnorr_paillier_batched::tests::test_correctness();
}
