use curv::BigInt;
use curv::arithmetic::traits::Modulo;


/// Checks whether n is divisible by any prime p <= upto.
pub fn check_small_primes(upto: &u64, n: &BigInt) -> bool {
    use primes::{Sieve, PrimeSet};

    // This should be precomputed during compile-time.
    for p in Sieve::new().iter().take_while(|x| x <= upto) {
        let rem = Modulo::modulus(n,&BigInt::from(p));
        if rem == BigInt::from(0) { return false; };
    }
    return true;
}
