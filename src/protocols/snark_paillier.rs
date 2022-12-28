#[macro_use]

/// Produces the circuit for knowledge-of-plaintext of the Paillier
/// encryption scheme. Provides two versions: the naive one, and
/// optimised one, that uses CRT (Chinese remainder theorem) to
/// perform computations in the smaller fields before recombining
/// them. The intention is to illustrate that the resulting circuit,
/// because of the non-native field arithmetic, is beyond the size
/// that is practical to work with.

/*
I was following:
- https://github.com/matter-labs/bellman/blob/master/tests/mimc.rs#L92
- https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/set/rsa.rs#L523
*/

pub use sapling_crypto::bellman as bellman;
pub use bellman::pairing as pairing;

use std::convert::From;
use std::fmt::Debug;
use std::cmp::{min, Eq, PartialEq};
use std::marker::PhantomData;
use std::collections::HashMap;

use rug::{integer::Order, Integer, Complete};
use either::Either;

use bellman::{ConstraintSystem, LinearCombination, SynthesisError, Circuit};
use bellman_bignat::mp::bignat::{BigNat,BigNatParams,nat_to_limbs};
use bellman_bignat::util::convert::{nat_to_f};
use bellman_bignat::util::num::Num;
use bellman_bignat::util::gadget::Gadget;
use bellman_bignat::util::bench::{ConstraintCounter};
use bellman_bignat::group::{CircuitSemiGroup};
use pairing::bn256::{Bn256,Fr};
use pairing::{Engine};
use pairing::ff::{Field};
use sapling_crypto::circuit::boolean::Boolean;
use sapling_crypto::circuit::test::TestConstraintSystem;
use sapling_crypto::circuit::num::AllocatedNum;

use lazy_static::lazy_static;


////////////////////////////////////////////////////////////////////////////////////
// Standard Paillier
////////////////////////////////////////////////////////////////////////////////////


/// Circuit that proves knowledge of the preimage for Paillier encryption, naively
pub struct PailCorrect {
    /// Bit length of the N being proven
    n_bitlen: usize,
    /// Limb width for the non-native arithmetic conversion
    limb_width: usize,
    /// The modulus N itself
    n: Integer,
    /// Paillier base, typically n + 1
    g: Integer,
    /// Ciphertext randomness
    r: Integer,
    /// Ciphertext message
    m: Integer,
    /// The ciphertext
    ct: Integer,
}


impl<E: Engine> Circuit<E> for PailCorrect {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(),SynthesisError>
    {
        let n2_bitlen = self.n_bitlen * 2;
        let n_limbs = ((n2_bitlen as f64) / (self.limb_width as f64)).ceil() as usize;
        //let bignum_params_def = BigNatParams::new(self.limb_width, n_limbs);

        let mut alloc_bn = |var: Integer,name: &'static str| -> Result<BigNat<E>,SynthesisError>
        { BigNat::alloc_from_nat(cs.namespace(|| name), || Ok(var), self.limb_width, n_limbs) };

        // Allocate the bignums
        let m_bn = alloc_bn(self.m, "m")?;
        let r_bn = alloc_bn(self.r, "r")?;
        let g_bn = alloc_bn(self.g, "g")?;
        let n_bn = alloc_bn(self.n.clone(), "n")?;
        let n2_bn = alloc_bn(self.n.clone() * self.n.clone(), "n2")?;
        let ct_bn = alloc_bn(self.ct, "ct")?;

        g_bn.inputize(cs.namespace(|| "g pub"))?;
        n_bn.inputize(cs.namespace(|| "n pub"))?;
        n2_bn.inputize(cs.namespace(|| "n2 pub"))?;
        ct_bn.inputize(cs.namespace(|| "ct pub"))?;

        cs.namespace(|| "calculation");

        let tmp1 = g_bn.pow_mod(cs.namespace(|| "g^m"), &m_bn, &n2_bn)?;
        let tmp2 = r_bn.pow_mod(cs.namespace(|| "r^N"), &n_bn, &n2_bn)?;
        tmp1.assert_product_mod(cs.namespace(|| "g^m * r^N == ct"), &tmp2, &n2_bn, &ct_bn)?;

        Ok(())
    }
}

////////////////////////////////////////////////////////////////////////////////////
// Optimized Paillier
////////////////////////////////////////////////////////////////////////////////////


/// Optimised circuit that proves knowledge of the preimage for
/// Paillier encryption, using knowledge of its factors and CRT. See
/// `PailCorrect` for the repeated fields.
pub struct PailCorrectOpt {
    limb_width: usize,
    /// Bit length of p, must be equal to the bit length of q.
    p_bitlen: usize,
    p: Integer,
    q: Integer,
    /// N, must fit into 2*pq_bitlen bits
    n: Integer,
    g: Integer,
    r: Integer,
    m: Integer,
    ct: Integer
}

impl<E: Engine> Circuit<E> for PailCorrectOpt {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(),SynthesisError>
    {
        let p_limbs = ((self.p_bitlen as f64) / (self.limb_width as f64)).ceil() as usize;
        let n_limbs = p_limbs * 2;
        let n2_limbs = n_limbs * 2;


        let mut alloc_bn = |var: Integer,name: &'static str, limbs:usize| -> Result<BigNat<E>,SynthesisError>
        { BigNat::alloc_from_nat(cs.namespace(|| format!("alloc {}",name)), || Ok(var), self.limb_width, limbs) };

        let m_bn = alloc_bn(self.m, "m", n_limbs)?;
        let r_bn = alloc_bn(self.r, "r", n_limbs)?;

        let g_bn = alloc_bn(self.g, "g", n_limbs)?;
        let ct_bn = alloc_bn(self.ct, "ct", n2_limbs)?;
        let n_bn = alloc_bn(self.n.clone(), "n", n_limbs)?;
        let n2_bn = alloc_bn(self.n.clone() * self.n.clone(), "n2", n2_limbs)?;

        let p_bn = alloc_bn(self.p.clone(), "p", p_limbs)?;
        let q_bn = alloc_bn(self.q.clone(), "q", p_limbs)?;
        p_bn.enforce_coprime(cs.namespace(|| "coprime"), &q_bn)?;
        //println!("p limbs number: {}", p_bn.limbs.len());

        g_bn.inputize(cs.namespace(|| "g pub"))?;
        ct_bn.inputize(cs.namespace(|| "ct pub"))?;
        n_bn.inputize(cs.namespace(|| "n pub"))?;
        n2_bn.inputize(cs.namespace(|| "n2 pub"))?;

        // Allocate all bignums
        let p2_bn = p_bn.mult(cs.namespace(|| "p2"), &p_bn)?;
        //println!("p2 limbs number: {}", p2_bn.limbs.len());
        let q2_bn = q_bn.mult(cs.namespace(|| "q2"), &q_bn)?;

        let n2_tmp_bn = p2_bn.mult(cs.namespace(|| "n2 check"), &q2_bn)?;
        BigNat::assert_equal(cs.namespace(|| "checking n2 validity"), &n2_bn, &n2_tmp_bn)?;

        // otherwise cs is mutably shared
        let mut alloc_bn = |var: Integer,name: &'static str, limbs:usize| -> Result<BigNat<E>,SynthesisError>
        { BigNat::alloc_from_nat(cs.namespace(|| format!("alloc {}",name)), || Ok(var), self.limb_width, limbs) };


        let p2 = self.p.clone() * self.p.clone();
        let q2 = self.q.clone() * self.q.clone();
        let p2inv = p2.clone().invert(&q2).unwrap();
        let q2inv = q2.clone().invert(&p2).unwrap();
        let p2inv_bn = alloc_bn(p2inv, "p2inv", n2_limbs)?;
        let q2inv_bn = alloc_bn(q2inv, "q2inv", n2_limbs)?;

        // Comparisons should be done between BigNat s of the same limbs length
        let one_long_bn = BigNat::one::<CS>(self.limb_width).with_n_limbs::<CS>(n_limbs);
        let p2_mul_p2inv = p2_bn.mult_mod(cs.namespace(|| "p2 mul p2inv % q2"), &p2inv_bn, &q2_bn)?.1;
        BigNat::assert_equal(cs.namespace(|| "checking p2inv validity"), &p2_mul_p2inv, &one_long_bn)?;
        let q2_mul_q2inv = q2_bn.mult_mod(cs.namespace(|| "q2 mul q2inv % p2"), &q2inv_bn, &p2_bn)?.1;
        BigNat::assert_equal(cs.namespace(|| "checking q2inv validity"), &q2_mul_q2inv, &one_long_bn)?;


        // Computations mod p2
        let p_tmp1 = g_bn.pow_mod(cs.namespace(|| "g^m mod p2"), &m_bn, &p2_bn)?;
        let p_tmp2 = r_bn.pow_mod(cs.namespace(|| "r^N mod p2"), &n_bn, &p2_bn)?;
        let p_res = p_tmp1.mult_mod(cs.namespace(|| "g^m * r^N mod p2"), &p_tmp2, &p2_bn)?.1;

        // Computations mod q2
        let q_tmp1 = g_bn.pow_mod(cs.namespace(|| "g^m mod q2"), &m_bn, &q2_bn)?;
        let q_tmp2 = r_bn.pow_mod(cs.namespace(|| "r^N mod q2"), &n_bn, &q2_bn)?;
        let q_res = q_tmp1.mult_mod(cs.namespace(|| "g^m * r^N mod q2"), &q_tmp2, &q2_bn)?.1;


        // CRT mod n2
        let mut mult_mod_n2 = |ns: &str, a: &BigNat<E>, b: &BigNat<E>| -> BigNat<E> {
            a.mult_mod(cs.namespace(|| format!("mult_mod_n2: {}", ns)), b, &n2_bn).unwrap().1
        };

        //// Extend to n2_limbs?

        let fin_tmp1 = mult_mod_n2("fin mul 1", &p_res, &q2_bn);
        let fin_tmp2 = mult_mod_n2("fin mul 2", &fin_tmp1, &q2inv_bn);
        let fin_tmp3 = mult_mod_n2("fin mul 3", &q_res, &p2_bn);
        let fin_tmp4 = mult_mod_n2("fin mul 4", &fin_tmp3, &p2inv_bn);

        ////BigNat::assert_equal(cs.namespace(|| "tmp check"), &fin_tmp2, &tmp_bn)?;

        let lhs =
            fin_tmp2.add::<CS>(&fin_tmp4)?.
            red_mod(cs.namespace(|| "last red"), &n2_bn)?;

        BigNat::assert_equal(cs.namespace(|| "last assert_eq check"), &lhs,&ct_bn)?;

        Ok(())
    }
}


////////////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////////////


// Taken from https://asecuritysite.com/encryption/random3?val=256

const RSA_80_P: &'static str = "1036290781";
const RSA_80_Q: &'static str = "878851969";

const RSA_512_P: &'static str = "67913768407298188679966852928456126752604535230759869929745089490467957985039";
const RSA_512_Q: &'static str = "49192928480432640539205900174531479322565920828724827008219103747527267700743";

const RSA_1024_P: &str = "2139242324751964981487368157318443342292065064597582554156390123944943204976475663670392405681846258899349931591750147107606739898928419150872150577877431";
const RSA_1024_Q: &str = "3767988990528002581812997974750268500702903415741627650701515837167668220564772553809538981300271959025651451181360142724278681204729734081009240231091113";

const RSA_2048_P: &str = "143822471615987551108285575326610654873105502425051106785945055365643861664898580552088892029310749816972080047171460449564169917735739186980510479142505041664307359997486476880621544015292571404224350147608910493202630826673453787102774704431949054698968594138703573370678243344323507423214559298663065508351";
const RSA_2048_Q: &str = "125089148898302683888991836902266045298248521010716318301113754496571950682912995474071548842056568440005323384259343285990121389690794592984430971947003129853123591745683625799124368978738088675958620714511504800865096907087713183366666078248613760907178781257935473791620521578712801629425324569108785191333";


lazy_static! {
    static ref test_moduli_pq: HashMap<usize,(Integer,Integer)> = {
        let mut m = HashMap::new();
        let parse = |p,q| { (Integer::parse(p).unwrap().complete(),
                             Integer::parse(q).unwrap().complete()) };
        m.insert(80, parse(RSA_80_P, RSA_80_Q));
        m.insert(512, parse(RSA_512_P, RSA_512_Q));
        m.insert(1024, parse(RSA_1024_P, RSA_1024_Q));
        m.insert(2048, parse(RSA_2048_P, RSA_2048_Q));
        m
    };
}


pub trait PailCircuit<E: Engine>: Circuit<E> {
    fn compute_circuit(n_bitlen: usize) -> Self;
    fn namedesc() -> &'static str;
}

pub fn compute_circuit(n_bitlen: usize, opt: bool) -> Either<PailCorrect,PailCorrectOpt> {
    let (p,q) = test_moduli_pq.get(&n_bitlen).unwrap();

    let n: Integer = p.clone() * q.clone();

    let n2 = n.clone() * n.clone();
    let g = n.clone() + Integer::from(1);
    let r = n.clone() - Integer::from(12312512421i64);
    let m = n.clone() - Integer::from(12473251335i64);
    let tmp1 = g.clone().pow_mod(&m, &n2).unwrap();
    let tmp2 = r.clone().pow_mod(&n, &n2).unwrap();
    let ct = (tmp1 * tmp2) % n2.clone();


    let p2 = p.clone() * p.clone();
    let q2 = q.clone() * q.clone();
    let p2inv = p2.clone().invert(&q2).unwrap();
    let q2inv = q2.clone().invert(&p2).unwrap();
    // g^m r^n mod p^2
    let tmp = ((ct.clone() % p2.clone()) * q2.clone() * q2inv.clone() +
               (ct.clone() % q2.clone()) * p2.clone() * p2inv.clone()) % n2.clone();
    assert!(tmp == ct);

    if opt { Either::Right(PailCorrectOpt { p_bitlen: n_bitlen/2, limb_width: 32,
                                            p: p.clone(), q: q.clone(), n, g, r, m, ct }) }
    else { Either::Left(PailCorrect {n_bitlen: n_bitlen, limb_width: 32,
                                     n, g, r, m, ct }) }
}

impl<E:Engine> PailCircuit<E> for PailCorrect {
    fn compute_circuit(n_bitlen: usize) -> Self {
        return compute_circuit(n_bitlen,false).left().unwrap();
    }
    fn namedesc() -> &'static str { "unoptimized" }
}

impl<E:Engine> PailCircuit<E> for PailCorrectOpt {
    fn compute_circuit(n_bitlen: usize) -> Self {
        return compute_circuit(n_bitlen,true).right().unwrap();
    }
    fn namedesc() -> &'static str { "optimized" }
}


pub fn estimate_num_constraints<C: PailCircuit<Bn256>>(n_bitlen: usize) {
    let circuit = C::compute_circuit(n_bitlen);
    let mut cs = ConstraintCounter::new();
    (Circuit::<Bn256>::synthesize(circuit, &mut cs)).expect("synthesis failed");
    let constr = cs.num_constraints();

    println!("Num Constraints for {} bits, {}: {:.2} M (*10^6)", n_bitlen, C::namedesc(), (constr as f64 / 1000000f64));
}


pub fn test_completeness<C: PailCircuit<Bn256>>(n_bitlen: usize) {
    println!("Completeness test for {} bits, {}", n_bitlen, C::namedesc());

    let circuit = C::compute_circuit(n_bitlen);
    let mut cs = TestConstraintSystem::<Bn256>::new();

    circuit.synthesize(&mut cs).expect("synthesis failed");
    println!(concat!("Constraints number: {}"), cs.num_constraints());
    if !cs.is_satisfied() {
        println!("UNSAT: {:#?}", cs.which_is_unsatisfied())
    }
    let unconstrained = cs.find_unconstrained();
    if unconstrained.len() > 0 {
        println!(concat!("Unconstrained: {}"), cs.find_unconstrained());
    }

    assert_eq!(cs.is_satisfied(), true);
    println!("Completeness test passed");
}

pub fn test() {
    test_completeness::<PailCorrectOpt>(80);

    for &n in test_moduli_pq.keys() {
        estimate_num_constraints::<PailCorrect>(n);
        estimate_num_constraints::<PailCorrectOpt>(n);
    }
}
