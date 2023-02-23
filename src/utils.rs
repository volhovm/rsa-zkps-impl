/// Collection of helpers and utility functions.

use std::borrow::{Borrow, Cow};

use super::bigint::*;

pub const PROFILE_SPB: bool = false;
pub const PROFILE_DV: bool = false;
pub const PROFILE_DVR: bool = false;


/// Samples N = p*q
pub fn sample_modulus(n_bitlen: usize) -> ((BigInt,BigInt),BigInt) {
    let p = crate::primes::sample_prime(n_bitlen / 2);
    let q = crate::primes::sample_prime(n_bitlen / 2);
    let n = &p * &q;
    ((p,q),n)
}

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

/// Takes a byte slice (hash output) and returns
/// a bigint of the bit_size from its prefix.
pub fn extract_bits(input: &[u8], bit_size: usize) -> BigInt {
    let r = bit_size / 8;
    let q = bit_size % 8;
    assert!(input.len() >= r + 1);
    if q == 0 {
        BigInt::from_bytes(&input[0..r])
    } else {
        let last = input[r] & (((1 as u8) << q) - 1); // FIXME check
        BigInt::from_bytes(&[&input[0..r], &[last]].concat())
    }
}

/// Given r_b, samples integer in the range [-r/2,r/2) = [0,r) - r/2, for r = 2^{r_b}
pub fn bigint_sample_sym(bitlen: u32) -> BigInt {
    &BigInt::sample(bitlen as usize) - &BigInt::pow(&BigInt::from(2),bitlen-1)
}

/// Samples integer in the range [-r/2,r/2) = [0,r) - r/2
pub fn bigint_sample_below_sym(r: &BigInt) -> BigInt {
    BigInt::sample_below(r) - r / 2
}

/// Checks that x \in [-r/2,r/2).
pub fn bigint_in_range_sym(r: &BigInt, x: &BigInt) -> bool {
    let r2 = r / BigInt::from(2);
    if (!BigInt::is_negative(x) && x < &r2) ||
        (BigInt::is_negative(x) && x >= &-&r2) { return true; }
    false
}

/// Mod_pow which allows exponents to be negative.
pub fn bigint_mod_pow_explicit(a: &BigInt, a_inv: &BigInt, exponent: &BigInt, modulus: &BigInt) -> BigInt {
    if BigInt::is_negative(exponent) {
        BigInt::mod_pow(a_inv,&-exponent,modulus)
    } else {
        BigInt::mod_pow(a,exponent,modulus)
    }
}

// TODO This should not be used thoughtlessly: consider precomputing the inverse exponent
// if possible. However this is cheap, so maybe using this thoughtlessly is not too bad.
/// Same as bigint_mod_pow, but computing the inverse on the fly.
pub fn bigint_mod_pow(a: &BigInt, exponent: &BigInt, modulus: &BigInt) -> BigInt {
    bigint_mod_pow_explicit(a, &BigInt::mod_inv(a, modulus).unwrap(), exponent, modulus)
}


/// Computes a crt decomposition.
pub fn crt_decompose<X, M1, M2>(x: X, m1: M1, m2: M2) -> (BigInt, BigInt)
where
    X: Borrow<BigInt>,
    M1: Borrow<BigInt>,
    M2: Borrow<BigInt>,
{
    (x.borrow() % m1.borrow(), x.borrow() % m2.borrow())
}

/// Computes m such that m = vp mod p & m = vq mod q.
pub fn crt_recombine(vp: &BigInt,
                     vq: &BigInt,
                     p: &BigInt,
                     q: &BigInt,
                     p_inv_q: &BigInt) -> BigInt {
    let diff = BigInt::mod_sub(vq, vp, q);
    let u = (&diff * p_inv_q) % q;
    vp + (&u) * p
}


/// Log2, ceiled.
pub fn log2ceil(x: u32) -> u32 {
   (x as f64).log2().ceil() as u32
}

#[cfg(test)]
mod tests {

    use crate::utils::check_small_primes;
    use crate::bigint::*;

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
