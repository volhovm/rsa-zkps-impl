use curv::BigInt;
use curv::arithmetic::traits::Modulo;
use paillier::*;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};

mod protocols;


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

fn main() {
    check_correct_ciphertext_proof();

    use protocols::utils::check_small_primes;
    println!("Small primes check for N = 5, up to 1000: {}", check_small_primes(&(1000u64), &BigInt::from(5)));
    println!("Small primes check for N = 1217, up to first 20 primes: {}", check_small_primes(&20, &BigInt::from(1217)));
}
