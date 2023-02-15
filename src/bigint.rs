/// Wrapper around BigInt that gets rid of the inefficient Serde implementation.
/// I wish I could declare an orphan impl.

use std::{ops,fmt};

use derive_more::Display;
use serde::{Serialize};

use curv as c;
pub use curv::arithmetic::traits::{Modulo, Samplable, NumberTests,
                                   BasicOps, BitManipulation, Converter, Integer,
                                   Roots, Primes};
use curv::arithmetic::{ParseBigIntError, Zero, One};


#[derive(PartialOrd,PartialEq,Ord,Eq,Clone,Serialize)]
pub struct BigInt { pub v: curv::BigInt }


/// Internal helper trait. Creates short-hand for wrapping Mpz into BigInt.
pub trait Wrap {
    fn wrap(self) -> BigInt;
}

impl Wrap for curv::BigInt {
    fn wrap(self) -> BigInt {
        BigInt { v: self }
    }
}

impl Wrap for &curv::BigInt {
    fn wrap(self) -> BigInt {
        BigInt { v: self.clone() }
    }
}

impl BigInt {
    pub fn inner_ref(&self) -> &curv::BigInt {
        &self.v
    }
    pub fn into_inner(self) -> curv::BigInt {
        self.v
    }
}

////////////////////////////////////////////////////////////////////////////
// Boilerplate
////////////////////////////////////////////////////////////////////////////

#[doc(hidden)]
#[macro_export]
macro_rules! __bigint_impl_from {
    ($($type:ty),*$(,)?) => {
        $(
        impl From<$type> for BigInt {
            fn from(x: $type) -> Self {
                curv::BigInt::from(x).wrap()
            }
        }
        )*
    };
}


__bigint_impl_from! { u32, i32, u64 }


#[macro_export]
macro_rules! __bigint_impl_ops {
    () => {};
    ($op: ident $func:ident, $($rest:tt)*) => {
        impl std::ops::$op for &BigInt {
            type Output = BigInt;
            fn $func(self, rhs: Self) -> Self::Output {
                std::ops::$op::$func(self.inner_ref(),rhs.inner_ref()).wrap()
            }
        }
        impl std::ops::$op for BigInt {
            type Output = BigInt;
            fn $func(self, rhs: Self) -> Self::Output {
                std::ops::$op::$func(self.into_inner(),rhs.into_inner()).wrap()
            }
        }
        impl std::ops::$op<BigInt> for &BigInt {
            type Output = BigInt;
            fn $func(self, rhs: BigInt) -> Self::Output {
                std::ops::$op::$func(self.inner_ref(),rhs.into_inner()).wrap()
            }
        }
        impl std::ops::$op<&BigInt> for BigInt {
            type Output = BigInt;
            fn $func(self, rhs: &BigInt) -> Self::Output {
                std::ops::$op::$func(self.into_inner(),rhs.inner_ref()).wrap()
            }
        }
        $crate::__bigint_impl_ops!{ $($rest)* }
    };
    ($op: ident $func:ident $primitive:ty, $($rest:tt)*) => {
        impl std::ops::$op<$primitive> for BigInt {
            type Output = BigInt;
            fn $func(self, rhs: $primitive) -> Self::Output {
                std::ops::$op::$func(self.into_inner(),rhs).wrap()
            }
        }
        impl std::ops::$op<$primitive> for &BigInt {
            type Output = BigInt;
            fn $func(self, rhs: $primitive) -> Self::Output {
                std::ops::$op::$func(self.inner_ref(),rhs).wrap()
            }
        }
        $crate::__bigint_impl_ops!{ $($rest)* }
    };
    ($op: ident $func:ident $primitive:ty [swap], $($rest:tt)*) => {
        impl std::ops::$op<$primitive> for BigInt {
            type Output = BigInt;
            fn $func(self, rhs: $primitive) -> Self::Output {
                std::ops::$op::$func(self.into_inner(),rhs).wrap()
            }
        }
        impl std::ops::$op<$primitive> for &BigInt {
            type Output = BigInt;
            fn $func(self, rhs: $primitive) -> Self::Output {
                std::ops::$op::$func(self.inner_ref(),rhs).wrap()
            }
        }
        impl std::ops::$op<BigInt> for $primitive {
            type Output = BigInt;
            fn $func(self, rhs: BigInt) -> Self::Output {
                std::ops::$op::$func(self,rhs.into_inner()).wrap()
            }
        }
        impl std::ops::$op<&BigInt> for $primitive {
            type Output = BigInt;
            fn $func(self, rhs: &BigInt) -> Self::Output {
                std::ops::$op::$func(self,rhs.inner_ref()).wrap()
            }
        }
        $crate::__bigint_impl_ops!{ $($rest)* }
    };
}


__bigint_impl_ops! {
    Add add,
    Sub sub,
    Mul mul,
    Div div,
    Rem rem,
    BitAnd bitand,
    BitXor bitxor,
    Shl shl usize,
    Shr shr usize,

    Add add u64 [swap],
    Sub sub u64 [swap],
    Mul mul u64 [swap],
    Div div u64,
    Rem rem u64,
}

impl ops::Neg for BigInt {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        self.v.neg().wrap()
    }
}
impl ops::Neg for &BigInt {
    type Output = BigInt;
    fn neg(self) -> Self::Output {
        (&self.v).neg().wrap()
    }
}

impl curv::arithmetic::traits::BasicOps for BigInt {
    fn pow(&self, exponent: u32) -> Self {
        self.v.pow(exponent).wrap()
    }

    fn mul(&self, other: &Self) -> Self {
        self.v.mul(&other.v).wrap()
    }

    fn sub(&self, other: &Self) -> Self {
        self.v.sub(&other.v).wrap()
    }

    fn add(&self, other: &Self) -> Self {
        self.v.add(&other.v).wrap()
    }

    fn abs(&self) -> Self {
        self.v.abs().wrap()
    }
}

impl Modulo for BigInt {
    fn mod_pow(base: &Self, exponent: &Self, modulus: &Self) -> Self {
        curv::BigInt::mod_pow(&base.v,&exponent.v,&modulus.v).wrap()
    }

    fn mod_mul(a: &Self, b: &Self, modulus: &Self) -> Self {
        curv::BigInt::mod_mul(&a.v,&b.v,&modulus.v).wrap()
    }

    fn mod_sub(a: &Self, b: &Self, modulus: &Self) -> Self {
        curv::BigInt::mod_sub(&a.v,&b.v,&modulus.v).wrap()
    }

    fn mod_add(a: &Self, b: &Self, modulus: &Self) -> Self {
        curv::BigInt::mod_add(&a.v,&b.v,&modulus.v).wrap()
    }

    fn mod_inv(a: &Self, modulus: &Self) -> Option<Self> {
        curv::BigInt::mod_inv(&a.v,&modulus.v).map(|x| x.wrap())
    }

    fn modulus(&self, modulus: &Self) -> Self {
        curv::BigInt::modulus(&self.v,&modulus.v).wrap()
    }
}

impl NumberTests for BigInt {
    fn is_zero(me: &Self) -> bool {
        <curv::BigInt as curv::arithmetic::NumberTests>::is_zero(&me.v)
    }
    fn is_negative(me: &Self) -> bool {
        <curv::BigInt as curv::arithmetic::NumberTests>::is_negative(&me.v)
    }
}


impl Samplable for BigInt {
    fn sample_below(upper: &Self) -> Self {
        curv::BigInt::sample_below(&upper.v).wrap()
    }

    fn sample_range(lower: &Self, upper: &Self) -> Self {
        curv::BigInt::sample_range(&lower.v, &upper.v).wrap()
    }

    fn strict_sample_range(lower: &Self, upper: &Self) -> Self {
        curv::BigInt::strict_sample_range(&lower.v, &upper.v).wrap()
    }

    fn sample(bit_size: usize) -> Self {
        curv::BigInt::sample(bit_size).wrap()
    }

    fn strict_sample(bit_size: usize) -> Self {
        curv::BigInt::strict_sample(bit_size).wrap()
    }
}

impl BitManipulation for BigInt {
    fn set_bit(&mut self, bit: usize, bit_val: bool) {
        self.v.set_bit(bit,bit_val)
    }

    fn test_bit(&self, bit: usize) -> bool {
        self.v.test_bit(bit)
    }

    fn bit_length(&self) -> usize {
        self.v.bit_length()
    }
}

impl Converter for BigInt {
    fn to_bytes(&self) -> Vec<u8> {
        self.v.to_bytes()
    }

    fn from_bytes(bytes: &[u8]) -> Self {
        curv::BigInt::from_bytes(bytes).wrap()
    }

    fn to_hex(&self) -> String {
        self.v.to_hex()
    }

    fn from_hex(value: &str) -> Result<BigInt, ParseBigIntError> {
        curv::BigInt::from_hex(value).map(|x| x.wrap())
    }

    fn to_str_radix(&self, radix: u8) -> String {
        self.v.to_str_radix(radix)
    }

    fn from_str_radix(str: &str, radix: u8) -> Result<Self, ParseBigIntError> {
        curv::BigInt::from_str_radix(str, radix).map(|x| x.wrap())
    }
}


impl Zero for BigInt {
    fn zero() -> Self {
        curv::BigInt::zero().wrap()
    }

    fn is_zero(&self) -> bool {
        self.v.is_zero()
    }
}

impl One for BigInt {
    fn one() -> Self {
        curv::BigInt::one().wrap()
    }
    fn is_one(&self) -> bool {
        self.v.is_one()
    }
}

impl num::Num for BigInt {
    type FromStrRadixErr = ParseBigIntError;
    fn from_str_radix(str: &str, radix: u32) -> Result<Self, ParseBigIntError> {
        <curv::BigInt as num::Num>::from_str_radix(str, radix).map(|x| x.wrap())
    }
}

impl Integer for BigInt {
    fn div_floor(&self, other: &Self) -> Self {
        self.v.div_floor(&other.v).wrap()
    }

    fn mod_floor(&self, other: &Self) -> Self {
        self.v.mod_floor(&other.v).wrap()
    }

    fn gcd(&self, other: &Self) -> Self {
        self.v.gcd(&other.v).wrap()
    }

    fn lcm(&self, other: &Self) -> Self {
        self.v.lcm(&other.v).wrap()
    }

    fn divides(&self, other: &Self) -> bool {
        self.v.divides(&other.v)
    }

    fn is_multiple_of(&self, other: &Self) -> bool {
        self.v.is_multiple_of(&other.v)
    }

    fn is_even(&self) -> bool {
        self.v.is_even()
    }

    fn is_odd(&self) -> bool {
        self.v.is_odd()
    }

    fn div_rem(&self, other: &Self) -> (Self, Self) {
        let (d,r) = self.v.div_rem(&other.v);
        (d.wrap(),r.wrap())
    }
}

impl Roots for BigInt {
    fn nth_root(&self, n: u32) -> Self {
        self.v.nth_root(n).wrap()
    }

    fn sqrt(&self) -> Self {
        self.v.sqrt().wrap()
    }
}

impl fmt::Display for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.v.fmt(f)
    }
}

impl fmt::Debug for BigInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.v.fmt(f)
    }
}

impl Primes for BigInt {
    fn next_prime(&self) -> Self {
        self.v.next_prime().wrap()
    }

    fn is_probable_prime(&self, n: u32) -> bool {
        self.v.is_probable_prime(n)
    }
}
