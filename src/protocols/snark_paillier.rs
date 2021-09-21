pub use sapling_crypto::bellman as bellman;
pub use bellman::pairing as pairing;

use std::convert::From;
use std::fmt::Debug;
use std::cmp::{min, Eq, PartialEq};
use std::marker::PhantomData;

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


// Trying to follow
// - https://github.com/matter-labs/bellman/blob/master/tests/mimc.rs#L92
// - https://github.com/alex-ozdemir/bellman-bignat/blob/master/src/set/rsa.rs#L523


////////////////////////////////////////////////////////////////////////////////////
// Standard Paillier
////////////////////////////////////////////////////////////////////////////////////


/// Circuit that proves knowledge of the preimage for Paillier encryption.
pub struct PailCorrect {
    n_bitlen: usize,
    limb_width: usize,
    n: Integer,
    /// Paillier base, typically n + 1
    g: Integer,
    r: Integer,
    m: Integer,
    ct: Integer
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

        // Allocate all bignums
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

        // TODO Inputize public inputs?

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


/// Circuit that proves knowledge of the preimage for Paillier encryption.
pub struct PailCorrectOpt {
    limb_width: usize,
    p_bitlen: usize, // q bitlen should be the same
    p: Integer,
    q: Integer,
    n: Integer, // Must be 2*pq_bitlen bits
    /// Paillier base, typically n + 1
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
        let n_bitlen = self.p_bitlen * 2;
        // *TODO* Perhaps optimize?
        // We add 1 limb because it may be that p^2 < N + 1, so N+1 wouldn't fit in n_limbs
        let n_limbs = (((n_bitlen as f64) / (self.limb_width as f64)).ceil() as usize) + 1;
        let n2_limbs = n_limbs * 2;
        //let bignum_params_def = BigNatParams::new(self.limb_width, n_limbs);


        let mut alloc_bn = |var: Integer,name: &'static str, limbs:usize| -> Result<BigNat<E>,SynthesisError>
        { BigNat::alloc_from_nat(cs.namespace(|| format!("alloc {}",name)), || Ok(var), self.limb_width, limbs) };

        // FIXME we might need to have some constraints making sure numbers are related,
        // e.g. n = pq etc

        // Allocate all bignums
        let p2_bn = alloc_bn(self.p.clone() * self.p.clone(), "p2", n_limbs)?;
        let q2_bn = alloc_bn(self.q.clone() * self.q.clone(), "q2", n_limbs)?;
        let n_bn = alloc_bn(self.n.clone(), "n", n_limbs)?;
        let n2_bn = alloc_bn(self.n.clone() * self.n.clone(), "n2", n2_limbs)?;

        let g_bn = alloc_bn(self.g, "g", n_limbs)?;
        let m_bn = alloc_bn(self.m, "m", n_limbs)?;
        let r_bn = alloc_bn(self.r, "r", n_limbs)?;
        let ct_bn = alloc_bn(self.ct, "ct", n2_limbs)?;

        let p_bn = alloc_bn(self.p.clone(), "p", n2_limbs)?;
        let q_bn = alloc_bn(self.q.clone(), "q", n2_limbs)?;

        let pinv = self.p.clone().invert(&self.q).unwrap();
        let qinv = self.q.clone().invert(&self.p).unwrap();
        let pinv_bn = alloc_bn(pinv, "pinv", n2_limbs)?;
        let qinv_bn = alloc_bn(qinv, "qinv", n2_limbs)?;

        drop(alloc_bn);


        g_bn.inputize(cs.namespace(|| "g pub"))?;
        n_bn.inputize(cs.namespace(|| "n pub"))?;
        n2_bn.inputize(cs.namespace(|| "n2 pub"))?;
        ct_bn.inputize(cs.namespace(|| "ct pub"))?;


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

        let fin_tmp1 = mult_mod_n2("fin add 1", &p_res, &q_bn);
        let fin_tmp2 = mult_mod_n2("fin add 2", &fin_tmp1, &qinv_bn);
        let fin_tmp3 = mult_mod_n2("fin add 3", &q_res, &p_bn);
        let fin_tmp4 = mult_mod_n2("fin add 4", &fin_tmp3, &pinv_bn);
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


// https://asecuritysite.com/encryption/random3?val=256

const RSA_80_P: &'static str = "1036290781";
const RSA_80_Q: &'static str = "878851969";

const RSA_512_P: &'static str = "67913768407298188679966852928456126752604535230759869929745089490467957985039";
const RSA_512_Q: &'static str = "49192928480432640539205900174531479322565920828724827008219103747527267700743";

const RSA_1024_P: &str = "2139242324751964981487368157318443342292065064597582554156390123944943204976475663670392405681846258899349931591750147107606739898928419150872150577877431";
const RSA_1024_Q: &str = "3767988990528002581812997974750268500702903415741627650701515837167668220564772553809538981300271959025651451181360142724278681204729734081009240231091113";

const RSA_2048_P: &str = "143822471615987551108285575326610654873105502425051106785945055365643861664898580552088892029310749816972080047171460449564169917735739186980510479142505041664307359997486476880621544015292571404224350147608910493202630826673453787102774704431949054698968594138703573370678243344323507423214559298663065508351";
const RSA_2048_Q: &str = "125089148898302683888991836902266045298248521010716318301113754496571950682912995474071548842056568440005323384259343285990121389690794592984430971947003129853123591745683625799124368978738088675958620714511504800865096907087713183366666078248613760907178781257935473791620521578712801629425324569108785191333";

// Too lazy to figure out how static maps work

pub fn select_modulus_pq(n_bitlen: usize) -> (&'static str,&'static str) {
    match n_bitlen {
        80 => (RSA_80_P, RSA_80_Q),
        512 => (RSA_512_P, RSA_512_Q),
        1024 => (RSA_1024_P, RSA_1024_Q),
        2048 => (RSA_2048_P, RSA_2048_Q),
        _ => panic!("select_modulus_pq is not implemented for bitlength {}", n_bitlen),
    }
}


pub trait PailCircuit<E: Engine>: Circuit<E> {
    fn compute_circuit(n_bitlen: usize) -> Self;
    fn namedesc() -> &'static str;
}

pub fn compute_circuit(n_bitlen: usize, opt: bool) -> Either<PailCorrect,PailCorrectOpt> {
    let (p_str,q_str) = select_modulus_pq(n_bitlen);

    let p: Integer = Integer::parse(p_str).unwrap().complete();
    let q: Integer = Integer::parse(q_str).unwrap().complete();
    let n: Integer = p.clone() * q.clone();

    let n2 = n.clone() * n.clone();
    let g = n.clone() + Integer::from(1);
    let r = n.clone() - Integer::from(12312512421i64);
    let m = n.clone() - Integer::from(12473251335i64);
    //let ct = n - Integer::from(12312312512i64) // doesn't matter that it's not computed correctly
    let tmp1 = g.clone().pow_mod(&m, &n2).unwrap();
    let tmp2 = r.clone().pow_mod(&n, &n2).unwrap();
    let ct = (tmp1 * tmp2) % n2.clone();

    if opt { Either::Right(PailCorrectOpt { p_bitlen: n_bitlen/2, limb_width: 32,
                                            p, q, n, g, r, m, ct }) }
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

    println!("Num Constraints for {} bits, {}: {}", n_bitlen, C::namedesc(), constr);
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
    //    test_completeness_opt(80);
    for n in [80,512,1024,2048] {
        estimate_num_constraints::<PailCorrect>(n);
        estimate_num_constraints::<PailCorrectOpt>(n);
    }
//    estimate_num_constraints_opt(80);
//    estimate_num_constraints(512);
//    estimate_num_constraints_opt(512);
//    estimate_num_constraints(1024);
//    estimate_num_constraints_opt(1024);
//    estimate_num_constraints(2048);
//    estimate_num_constraints_opt(2048);

//    test_completeness(80);
//    test_completeness(330);
//
////    estimate_num_constraints(330);
//    estimate_num_constraints(1024);
//    estimate_num_constraints(2048);
}

// From set_proof.rs in bellman bignat examples
//
//    let mut circuit = SetBench::<_, ExpSet<_, ParExpComb>> {
//        inputs: Some(inputs),
//        params: params.clone(),
//    };
// create_random_proof(circuit, &params, rng).unwrap();
// let prover = prepare_prover(circuit)
// let proof = prover.create_proof(params, r, s)?;

// They implement Circuit trait for SetBench in rsa.rs
//
// examples/rollup_bench.rs has number of constraints calculation:
//    let circuit = rsa::RollupBench::<Bls12, Poseidon<Bls12>>::from_counts(
//        t, // Use `t` in place of `c` for sparse-ness.
//        t,
//        JubjubBls12::new(),
//        Poseidon::default(),
//    );
//
//    let mut cs = ConstraintCounter::new();
//    circuit.synthesize(&mut cs).expect("synthesis failed");
//    cs.num_constraints()
//
// Here RollupBench implements circuit, so it has synthesize.

// pocklington/mod.rs has computation of pow_mod from base and extension.

// wesolowski.rs has something very similar to paillier: proof that "q^l base^r = res"

// pow_mod for bignats is only used in pocklington and in PowMod circuit (tests).

// Pocklington criterion is used for "challenge" in set/rsa.rs and rollup/rsa.rs

// group.rs defines semigroup, which only has power wrt integer exponent.
// This doesn't work for us.
// But at the same time CircuitSemiGroup::power can take a bignat as exponent,
// and this is used in wesolowski::proof_of_exp
// In turn this is ued in CircuitIntSet::insert, and ::remove, which are used
// in rsa.rs. This matches what's claimed in the paper: RSA proofs are batched with
// wesolowski proofs.

// I could implement semigroup and CircuitSemiGroup for Paillier, but isn't this an overkill?
// why not use directly bignat::pow?
// "Bauer" is probably "Brauer"

// Why are there two different exp algorithms? One in bignat used for Pocklington,
// another in group.rs used for wesolowski proofs?
// Bc it's the same code, just copy-pasted!
