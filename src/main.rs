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

fn main() {
    check_correct_ciphertext_proof();

    use rsazkps::protocols::utils::check_small_primes;
    println!("Small primes check for (prime) N = 5, up to 1000: {}", check_small_primes(1000, &BigInt::from(5)));
    println!("Small primes check for (prime) N = 6180283, up to 6*10^7: {}", check_small_primes(6000000, &BigInt::from(6180283)));
    println!("Small primes check for (prod of 2 primes) N = 6180283 * 1217, up to 6*10^7: {}", check_small_primes(6000000, &BigInt::from(6180283u64*1217)));
}
