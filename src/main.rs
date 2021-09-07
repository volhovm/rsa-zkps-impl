use curv::BigInt;
use curv::arithmetic::traits::Modulo;
use paillier::*;
use zk_paillier::zkproofs::{CiphertextProof,CiphertextWitness,CiphertextStatement};


/// Checks whether n is divisible by any prime p <= upto.
fn check_small_primes(upto: &u64, n: BigInt) -> bool {
    use primes::{Sieve, PrimeSet};

    // This should be precomputed during compile-time.
    for p in Sieve::new().iter().take_while(|x| x <= upto) {
        let rem = Modulo::modulus(&n,&BigInt::from(p));
        if rem == BigInt::from(0) {
            println!("rem = 0 mod prime {:?}", p);
            return false;
        };
    }
    return true;
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

fn main() {
    check_correct_ciphertext_proof();

    println!("Small primes check for N = 5, up to 1000: {}", check_small_primes(&1000, BigInt::from(5)));
    println!("Small primes check for N = 1217, up to first 20 primes: {}", check_small_primes(&20, BigInt::from(1217)));
}
