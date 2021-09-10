use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::traits::{Add, Mul};
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawCiphertext, RawPlaintext, Keypair};
use paillier::*;


// Common parameters for the proof system.
pub struct ProofParams {
    /// Small number up to which N shouldn't have divisors.
    pub q: u64,
}

pub struct Instance {
    pub n: BigInt,
    /// N^2
    pub n2: BigInt,
    pub ct: BigInt
}

pub struct Witness {
    pub m: BigInt,
    pub r: BigInt
}

pub struct Commitment(BigInt);
pub struct ComRand(BigInt,BigInt);
pub struct Challenge(bool);
pub struct Response(BigInt,BigInt);

pub fn lang_sample() -> (Instance,Witness) {
    let kp:Keypair = Paillier::keypair();
    let (pk,_) = kp.keys();
    let m = BigInt::sample_below(&pk.n);
    let r = BigInt::sample_below(&pk.n);
    let ct = Paillier::encrypt_with_chosen_randomness(
             &pk,
             RawPlaintext::from(m.clone()),
             &Randomness(r.clone())).0.into_owned();

    let n2 = BigInt::mul(&pk.n,&pk.n);

    let inst = Instance { n: pk.n.clone(), n2: n2, ct: ct };
    let wit = Witness { m: m, r:r };

    return (inst,wit);
}


pub fn verifier0(params: ProofParams, x: Instance) -> bool {
    return super::utils::check_small_primes(&params.q,&x.n);
}

pub fn prove1(params: ProofParams, inst: Instance) -> (Commitment,ComRand) {
    let rm = BigInt::sample_below(&inst.n);
    let rr = BigInt::sample_below(&inst.n);
    let ek = EncryptionKey::from(&inst.n);
    let alpha = Paillier::encrypt_with_chosen_randomness(
                &ek,
                RawPlaintext::from(rm.clone()),
                &Randomness(rr.clone())).0.into_owned();

    return (Commitment(alpha),ComRand(rm,rr));
}

pub fn verify1() -> Challenge {
    let b: bool = rand::random();
    return Challenge(b);
}

pub fn prove2(params: ProofParams,
              inst: Instance,
              wit: Witness,
              ch: Challenge,
              cr: ComRand) -> Response {
    let Challenge(b) = ch;
    let ComRand(rm,rr) = cr;

    let t1 = if b { wit.m } else { BigInt::from(0) };
    let s1 = BigInt::mod_add(&rm,&t1,&inst.n);
    let t2 = if b { wit.r } else { BigInt::from(1) };
    let s2 = BigInt::mod_mul(&rr,&t2,&inst.n2);

    return Response(s1,s2);
}

pub fn verify2(params: ProofParams,
               inst: Instance,
               com: Commitment,
               ch: Challenge,
               resp: Response) -> bool {
    let Challenge(b) = ch;
    let Response(s1,s2) = resp;

    let ec = if b {inst.ct} else {BigInt::from(1)};
    let lhs = BigInt::mod_mul(&ec,&com.0,&inst.n2);

    let rhs = BigInt::mod_mul(
        &BigInt::mod_pow(&(&inst.n + 1),&s1,&inst.n2),
        &BigInt::mod_pow(&s2,&inst.n,&inst.n2),
        &inst.n2);

    return lhs == rhs;
}
