use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Zero, Roots, Integer, Primes};
use curv::BigInt;
use rand::distributions::{Distribution, Uniform};

// BigInt::is_probable_prime returns a probable prime with
// prob. 4^reps, so reps = 40 should do to achieve a 80 bit error prob.
static miller_rabin_reps: u32 = 40;

pub fn two_squares_decompose(n: &BigInt) -> (BigInt, BigInt) {
    unimplemented!()
}

// From "Randomized Algorithms in Number Theory" by Rabin and Shallit
pub fn three_squares_decompose(n: &BigInt) -> (BigInt, BigInt, BigInt) {
    // if n % 4 == 0, then do smth with n/4
    let (n_over_4,r) = BigInt::div_rem(n, &BigInt::from(4));
    if BigInt::is_zero(&r) {
        let (a,b,c) = three_squares_decompose(&n_over_4);
        return (2*a, 2*b, 2*c)
    }
    let n_mod8 = BigInt::modulus(n, &BigInt::from(8));
    if n_mod8 == BigInt::from(7) {
        assert!(false);
    }

    let d = BigInt::sqrt(n);
    if n_mod8 == BigInt::from(3) {
        let mut x: BigInt;
        let mut p: BigInt;
        loop {
            x = BigInt::sample_below(&d);
            p = (n - &x*&x) / &BigInt::from(2);
            if BigInt::is_probable_prime(&p, miller_rabin_reps) { break; }
        }
        let (y,z) = two_squares_decompose(&p);
        return (x, y.clone()+z.clone(), y-z)
    }

    if &(&d * &d) == n {
        return (d, BigInt::from(0), BigInt::from(0));
    }

    // Else n is 1 or 2 mod 4

    let mut x: BigInt;
    let mut p: BigInt;
    loop {
        x = BigInt::sample_below(&d);
        p = n - &x*&x;
        if BigInt::is_probable_prime(&p, miller_rabin_reps) { break; }
    }
    let (y,z) = two_squares_decompose(&p);
    return (x, y, z)
}
