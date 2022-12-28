/// Implements three-square decomposition algorithm, necessary for the
/// DVRange protocol.
///
/// Sources:
/// 1. "Randomized Algorithms in Number Theory" by Rabin and Shallit.
/// 2. https://math.stackexchange.com/questions/5877/efficiently-finding-two-squares-which-sum-to-a-prime

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Zero, Roots, Integer, Primes, Converter};
use curv::BigInt;
use rand::distributions::{Distribution, Uniform};

use num_bigint as nb;
use algebraics as alg;

// BigInt::is_probable_prime returns a probable prime with
// prob. 4^reps, so reps = 40 should do to achieve a 80 bit error prob.
static MILLER_RABIN_REPS: u32 = 40;


fn mods(a: &BigInt, n: &BigInt) -> BigInt {
    if n <= &BigInt::from(0) { panic!("Mods: negative modulus"); }
    a % n
}

fn quos(a: &BigInt, n: &BigInt) -> BigInt {
    if n <= &BigInt::from(0) { panic!("Negative modulus"); }
    a / n
}

fn powmods(a0: &BigInt, r0: &BigInt, n: &BigInt) -> BigInt {
    let mut out: BigInt = BigInt::from(1);
    let mut a = a0.clone();
    let mut r = r0.clone();
    while &r > &BigInt::from(0) {
        if &r % &BigInt::from(2) == BigInt::from(1) {
            r = &r - &BigInt::from(1);
            out = mods(&(&out * &a), n);
        }
        r = &r / &BigInt::from(2);
        a = mods(&(&a * &a), n);
    }
    out
}


// Remainder in Gaussian integers when dividing w by z
fn grem(w: &(BigInt,BigInt), z: &(BigInt,BigInt)) -> (BigInt, BigInt) {
    let (w0, w1) = w;
    let (z0, z1) = z;
    let n = z0 * z0 + z1 * z1;
    if &n == &BigInt::from(0) { panic!("division by zero"); }
    let u0 = quos(&(w0 * z0 + w1 * z1), &n);
    let u1 = quos(&(w1 * z0 - w0 * z1), &n);

    return (w0 - z0 * &u0 + z1 * &u1,
            w1 - z0 * &u1 - z1 * &u0);
}

fn ggcd(w0: &(BigInt,BigInt), z0: &(BigInt,BigInt)) -> (BigInt,BigInt) {
    let mut w = w0.clone();
    let mut z = z0.clone();
    while z != (BigInt::from(0),BigInt::from(0)) {
        //let (w, z) = (z, grem(w, z));
        let z1 = z.clone();
        z = grem(&w,&z1);
        w = z1;
    }
    w
}

fn root4(p: &BigInt) -> BigInt {
    // 4th root of 1 modulo p
    if p <= &BigInt::from(1) { panic!("too small"); }
    if (p % &BigInt::from(4)) != BigInt::from(1) { panic!("not congruent to 1"); }
    let k = p / &BigInt::from(4);
    let mut j = BigInt::from(2);
    loop {
        let a = powmods(&j, &k, p);
        let b = mods(&(&a * &a), p);
        if &b == &BigInt::from(p-1) {
            return a;
        }
        if b != BigInt::from(1) {
            panic!("not prime");
        }
        j = &j + BigInt::from(1);
    }
}

pub fn two_squares_decompose(p: &BigInt) -> (BigInt,BigInt) {
    let a = root4(p);
    ggcd(&(p.clone(),BigInt::from(0)),&(a,BigInt::from(1)))
}



fn three_squares_decompose_raw(n: &BigInt) -> Option<(BigInt, BigInt, BigInt)> {
    // if n % 4 == 0, then do smth with n/4
    let (n_over_4,r) = BigInt::div_rem(n, &BigInt::from(4));
    if BigInt::is_zero(&r) {
        let (a,b,c) = three_squares_decompose_raw(&n_over_4)?;
        return Some((2*a, 2*b, 2*c))
    }
    let n_mod8 = n % &BigInt::from(8);
    if n_mod8 == BigInt::from(7) {
        println!("three squares decompose: n = 7 mod 8");
        return None;
    }

    let d = BigInt::sqrt(n); // This fails sometimes? with "self.mpz._mp_size >= 0"
    if n_mod8 == BigInt::from(3) {
        let mut x: BigInt;
        let mut p: BigInt;
        loop {
            x = BigInt::sample_below(&d);
            p = (n - &x*&x) / &BigInt::from(2);
            if (&p % &BigInt::from(4)) == BigInt::from(1) &&
                BigInt::is_probable_prime(&p, MILLER_RABIN_REPS) { break; }
        }
        let (y,z) = two_squares_decompose(&p);
        return Some((x, y.clone()+z.clone(), y-z));
    }

    if &(&d * &d) == n {
        return Some((d, BigInt::from(0), BigInt::from(0)));
    }

    // Else n is 1 or 2 mod 4

    let mut x: BigInt;
    let mut p: BigInt;
    loop {
        x = BigInt::sample_below(&d);
        p = n - &x*&x;
        if (&p % &BigInt::from(4)) == BigInt::from(1) &&
            BigInt::is_probable_prime(&p, MILLER_RABIN_REPS) { break; }
    }
    let (y,z) = two_squares_decompose(&p);
    return Some((x, y, z));
}


pub fn three_squares_decompose(n: &BigInt) -> (BigInt, BigInt, BigInt) {
    for _i in 0..100 {
        match three_squares_decompose_raw(n) {
            Some((a,b,c)) => { if &(&a * &a + &b * &b + &c * &c) == n { return (a,b,c) }; },
            None => { println!("three_squares_decompose: got None"); },
        }
    }
    panic!("three squares decompose: I give up");
}

////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {

    use crate::protocols::squares_decomp::*;
    use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Zero, Roots, Integer, Primes, Converter};
    use curv::BigInt;

    #[test]
    fn test_two_squares() {
        let mut p: BigInt;

        for _i in 0..100 {
            loop {
                p = BigInt::sample(1024);
                if (&p % &BigInt::from(4)) == BigInt::from(1) &&
                    BigInt::is_probable_prime(&p, MILLER_RABIN_REPS) { break; }
            }

            let (a,b) = two_squares_decompose(&p);
            assert!(&a * &a + &b * &b == p);
        }
    }

    #[test]
    fn test_three_squares() {
        for _i in 0..100 {
            let n0 = BigInt::sample(1024);
            let n = &BigInt::from(4) * &n0 + &BigInt::from(1);

            let (a,b,c) = three_squares_decompose(&n);
            assert!(&a * &a + &b * &b + &c * &c == n);
        }
    }

}
