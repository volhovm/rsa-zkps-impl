use curv::BigInt;
use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, NumberTests};


/// Checks whether n is divisible by any prime p <= upto.
pub fn check_small_primes(upto: u64, n: &BigInt) -> bool {
    use primes::{Sieve, PrimeSet};

    // This should be precomputed during compile-time.
    for p in Sieve::new().iter().take_while(|&x| x <= upto) {
        let rem = Modulo::modulus(n,&BigInt::from(p));
        if rem == BigInt::from(0) { return false; };
    }
    return true;
}

pub fn bigint_sample_below_sym(r: &BigInt) -> BigInt {
    BigInt::sample_below(r) - r / 2
}

pub fn bigint_in_range_sym(r: &BigInt, x: &BigInt, n: &BigInt) -> bool {
    let r2 = r / BigInt::from(2);
    if x < &r2 || x >= &(n-&r2) { return true; }
    false
}

/// Mod_pow but allowing exponents to be negative.
pub fn bigint_mod_pow(a: &BigInt, exponent: &BigInt, modulus: &BigInt) -> BigInt {
    if BigInt::is_negative(exponent) {
        let inv: Option<BigInt> = BigInt::mod_inv(a, modulus);
        BigInt::mod_pow(&inv.unwrap(),&-exponent,modulus)
    } else {
        BigInt::mod_pow(a,exponent,modulus)
    }
}

pub fn log2ceil(x: u32) -> u32 {
   (x as f64).log2().ceil() as u32
}

#[cfg(test)]
mod tests {

    use curv::BigInt;
    use crate::protocols::utils::check_small_primes;

    #[test]
    pub fn test_check_small_primes() {
        let res1 = check_small_primes(1000, &BigInt::from(5));
        println!("Small primes check for (prime) N = 5, up to 1000, should be f: {}", res1);
        assert!(res1 == false);

        let res2 = check_small_primes(6000000, &BigInt::from(6180283));
        println!("Small primes check for (prime) N = 6180283, up to 6*10^7, should be t: {}", res2);
        assert!(res2 == true);

        let res3 = check_small_primes(6000000, &BigInt::from(6180283u64*1217));
        println!("Small primes check for (prod of 2 primes) N = 6180283 * 1217, up to 6*10^7, should be f: {}", res3);
        assert!(res3 == false);
    }
}
