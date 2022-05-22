use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Zero, Roots, Integer, Primes, Converter};
use curv::BigInt;
use rand::distributions::{Distribution, Uniform};

use num_bigint as nb;
use algebraics as alg;

// BigInt::is_probable_prime returns a probable prime with
// prob. 4^reps, so reps = 40 should do to achieve a 80 bit error prob.
static MILLER_RABIN_REPS: u32 = 40;

type PolyCoeff = alg::mod_int::ModularInteger<
                    nb::BigInt,
                    alg::mod_int::KnownPrime<nb::BigInt>>;
type Poly = alg::polynomial::Polynomial<PolyCoeff>;

pub fn bigint_to_bi(n: &BigInt) -> nb::BigInt {
    nb::BigInt::from_bytes_be(nb::Sign::Plus,&(BigInt::to_bytes(n))[..])
}

pub fn bigint_to_bui(n: &BigInt) -> nb::BigUint {
    nb::BigUint::from_bytes_be(&(BigInt::to_bytes(n))[..])
}

pub fn two_squares_decompose_wip(p: &BigInt) -> (BigInt, BigInt) {
    use num_bigint::{BigInt, ToBigInt, RandBigInt};
    use core::ops::Rem;

    let p_nb = bigint_to_bui(p);
    let p_nb_signed: nb::BigInt = nb::ToBigInt::to_bigint(&p_nb).unwrap();
    let modulus = alg::mod_int::KnownPrime::new_unsafe(p_nb_signed.clone());

    let to_coeff = |e: &nb::BigInt| -> PolyCoeff {
        alg::mod_int::ModularInteger::from_bigint(e,modulus.clone())
    };

    let one: nb::BigInt = From::from(1);
    let two: nb::BigInt = From::from(2);
    let step1: nb::BigInt = &p_nb_signed - &one;
    let (k,krem) = step1.div_mod_floor(&From::from(4));
    assert!(krem.is_zero());

    let (_,two_k_bytes) = nb::BigInt::to_bytes_be(&(&two * &k));


    let mut rng = rand::thread_rng();
    let b = RandBigInt::gen_biguint_below(&mut rng,&p_nb).to_bigint().unwrap();
//    (1+b^2) + (-2b) * t + 1 * t^2
    let fb: Poly = From::from([to_coeff(&From::from(1)) + to_coeff(&b)*to_coeff(&b),
                               -to_coeff(&From::from(2)) * to_coeff(&b),
                               to_coeff(&From::from(1))]);

    let mut h: Poly = From::from([to_coeff(&From::from(1))]);
    let mut g: Poly =
        From::from([to_coeff(&From::from(0)),to_coeff(&From::from(1))]);

    for i in 0..two_k_bytes.len() {
        let mut mask: u8 = 1;
        for _j in 0..8 {
            g = (&g * &g) % &fb;
            if two_k_bytes[i] & mask != 0u8 {
                h = &h * &g;
            }
            mask <<= 1;
        }
    }

    let one_poly: Poly = From::from([to_coeff(&From::from(1))]);
    let hfinal: Poly = &h - &one_poly;
    let gcd = alg::traits::GCD::gcd(&hfinal,&fb);


    unimplemented!()
}



// Taken from https://math.stackexchange.com/questions/5877/efficiently-finding-two-squares-which-sum-to-a-prime

pub fn mods(a: &BigInt, n: &BigInt) -> BigInt {
    if n <= &BigInt::from(0) {
        panic!("Mods: negative modulus");
    }
    let mut b = a % n;
//    if &(&BigInt::from(2) * a) > n {
//        b = b - n;
//    }
    b
}

pub fn powmods(a0: &BigInt, r0: &BigInt, n: &BigInt) -> BigInt {
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

pub fn quos(a: &BigInt, n: &BigInt) -> BigInt {
    if n <= &BigInt::from(0) {
        panic!("Negative modulus");
    }
    a / n
}

// remainder in Gaussian integers when dividing w by z
pub fn grem(w: &(BigInt,BigInt), z: &(BigInt,BigInt)) -> (BigInt, BigInt) {
    let (w0, w1) = w;
    let (z0, z1) = z;
    let n = z0 * z0 + z1 * z1;
    if &n == &BigInt::from(0) { panic!("division by zero"); }
    let u0 = quos(&(w0 * z0 + w1 * z1), &n);
    let u1 = quos(&(w1 * z0 - w0 * z1), &n);

    return (w0 - z0 * &u0 + z1 * &u1,
            w1 - z0 * &u1 - z1 * &u0);
}

pub fn ggcd(w0: &(BigInt,BigInt), z0: &(BigInt,BigInt)) -> (BigInt,BigInt) {
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

pub fn root4(p: &BigInt) -> BigInt {
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



// From "Randomized Algorithms in Number Theory" by Rabin and Shallit.
// @volhovm: only works with numbers of form 4n+1 reliably. Otherwise
// fails for no good reason sometimes.
pub fn three_squares_decompose_raw(n: &BigInt) -> Option<(BigInt, BigInt, BigInt)> {
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

    let d = BigInt::sqrt(n);
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


// @volhovm: I will be properly ashamed of this code next time I work
// on this project.
pub fn three_squares_decompose(n: &BigInt) -> (BigInt, BigInt, BigInt) {
    for i in 0..100 {
        match three_squares_decompose_raw(n) {
            Some((a,b,c)) => { if &(&a * &a + &b * &b + &c * &c) == n { return (a,b,c) }; },
            None => { println!("I hate myself"); },
        }
    }
    panic!("three squares decompose: I give up");
}

////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////

pub fn test_two_squares() {
    let mut p: BigInt;

    for _i in 0..1000 {
        loop {
            p = BigInt::sample(128);
            if (&p % &BigInt::from(4)) == BigInt::from(1) &&
                BigInt::is_probable_prime(&p, MILLER_RABIN_REPS) { break; }
        }

        println!("Computing decomposition");
        let (a,b) = two_squares_decompose(&p);
        assert!(&a * &a + &b * &b == p);
    }
}

pub fn test_three_squares() {
    let mut n: BigInt;
    for i in 0..100 {
//        loop {
//            //if &n % BigInt::from(8) != BigInt::from(7) { break; }
//        }
        let n0 = BigInt::sample(1024);
        n = &BigInt::from(4) * &n0 + &BigInt::from(1);
        println!("Computing 3sq decomposition");
        let (a,b,c) = three_squares_decompose(&n);
        assert!(&a * &a + &b * &b + &c * &c == n);
        println!("Computing 3sq decomposition DONE");
    }
}


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
        let n = BigInt::sample(128);

        let (a,b,c) = three_squares_decompose(&n);
        assert!(&a * &a + &b * &b + &c * &c == n);
    }

}
