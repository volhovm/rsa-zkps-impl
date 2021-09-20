pub use sapling_crypto::bellman as bellman;
pub use bellman::pairing as pairing;

use std::convert::From;
use std::fmt::Debug;
use std::cmp::{min, Eq, PartialEq};
use std::marker::PhantomData;

use rug::{integer::Order, Integer, Complete};

use bellman::{ConstraintSystem, LinearCombination, SynthesisError, Circuit};
use bellman_bignat::mp::bignat::{BigNat,BigNatParams,nat_to_limbs};
use bellman_bignat::util::convert::{nat_to_f};
use bellman_bignat::util::num::Num;
use bellman_bignat::util::gadget::Gadget;
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


/// Circuit that proves knowledge of the preimage for Paillier encryption.
struct PailCorrect<E> {
    n_bitlen: usize,
    limb_width: usize,
    n: Integer,
    /// n^2
    n2: Integer,
    /// Paillier base, typically n + 1
    g: Integer,
    r: Integer,
    m: Integer,
    ct: Integer,
    phantom: PhantomData<E>
}

impl<E: Engine> Circuit<E> for PailCorrect<E> {
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(),SynthesisError>
    {
        let n2_bitlen = self.n_bitlen * 2;
        let n_limbs = ((n2_bitlen as f64) / (self.limb_width as f64)).ceil() as usize;
        let bignum_params_def = BigNatParams::new(self.limb_width, n_limbs);

        let mut alloc_bn = |var: Integer,name: &'static str| -> Result<BigNat<E>,SynthesisError>
        { BigNat::alloc_from_nat(cs.namespace(|| name), || Ok(var), self.limb_width, n_limbs) };

        // Allocate all bignums
        let r_bn = alloc_bn(self.r, "r")?;
        let m_bn = alloc_bn(self.m, "m")?;
        let g_bn = alloc_bn(self.g, "g")?;
        let n_bn = alloc_bn(self.n, "n")?;
        let n2_bn = alloc_bn(self.n2, "n2")?;
        let ct_bn = alloc_bn(self.ct, "ct")?;


        cs.namespace(|| "calculation");

        let tmp1 = g_bn.pow_mod(cs.namespace(|| "g^m"), &m_bn, &n2_bn)?;
        let tmp2 = r_bn.pow_mod(cs.namespace(|| "r^N"), &n_bn, &n2_bn)?;
        tmp1.assert_product_mod(cs.namespace(|| "g^m * r^N == ct"), &tmp2, &n2_bn, &ct_bn)?;

        // Compute helper values for pocklington's criterion
        //let n_less_one = extension.mult(cs.namespace(|| "n - 1"), &prime)?;
        //let n = n_less_one.shift::<CS>(E::Fr::one());
        //let part = base.pow_mod(cs.namespace(|| "a^r"), &extension, &n)?;
        //let one = BigNat::one::<CS>(prime.params().limb_width);
        //let part_less_one = part.sub(cs.namespace(|| "a^r - 1"), &one)?;

        //// Check coprimality
        //part_less_one.enforce_coprime(cs.namespace(|| "coprime"), &n)?;
        //let power = part.pow_mod(cs.namespace(|| "a^r^p"), &prime, &n)?;

        //// Check fermat's little theorem
        //power.equal_when_carried(cs.namespace(|| "a^r^p == 1"), &one)?;

        Ok(())
    }
}


// https://en.wikipedia.org/wiki/RSA_numbers#RSA-1024
const RSA_1024: &str = "135066410865995223349603216278805969938881475605667027524485143851526510604859533833940287150571909441798207282164471551373680419703964191743046496589274256239341020864383202110372958725762358509643110564073501508187510676594629205563685529475213500852879416377328533906109750544334999811150056977236890927563";



pub fn test() {
//    let num: Num<Bn256> = Num::new(Some(Field::one()), LinearCombination::zero());
//    let cs = TestConstraintSystem::<Bn256>::new();
//    let bignat = BigNat::from_num(num, BigNatParams::new(10, 12));
    //    let Result::Ok(t) = BigNat::alloc_from_nat(cs, None);

    use bellman_bignat::util::bench::{ConstraintCounter};

    let rsa_num: Integer = Integer::parse(RSA_1024).unwrap().complete();
    let pailcorr: PailCorrect<Bn256> = PailCorrect {
                     n_bitlen: 1024,
                     limb_width: 32,
                     n: rsa_num.clone(),
                     n2: rsa_num.clone() * rsa_num.clone(),
                     g: rsa_num.clone() + Integer::from(1),
                     r: Integer::from(12312512421i64),
                     m: Integer::from(12473251335i64),
        ct: Integer::from(12312312512i64),
        phantom: PhantomData
                 };


    let mut cs = ConstraintCounter::new();
    (pailcorr.synthesize(&mut cs)).expect("synthesis failed");
    let constr = cs.num_constraints();

    println!("Num Constraints: {}", constr);
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
