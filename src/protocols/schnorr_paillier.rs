use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;


// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Small number up to which N shouldn't have divisors.
    pub q: u64,
    /// Number of repeats of the basic protocol.
    pub reps: usize
}

#[derive(Clone, PartialEq, Debug)]
pub struct Instance {
    pub n: BigInt,
    /// N^2
    pub n2: BigInt,
    pub ct: BigInt
}

#[derive(Clone, PartialEq, Debug)]
pub struct Witness {
    pub m: BigInt,
    pub r: BigInt
}

#[derive(Clone, PartialEq, Debug)]
pub struct Commitment(Vec<BigInt>);
#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<(BigInt,BigInt)>);
#[derive(Clone, PartialEq, Debug)]
pub struct Challenge(Vec<bool>);
#[derive(Clone, PartialEq, Debug)]
pub struct Response(Vec<(BigInt,BigInt)>);


pub fn lang_sample(big_length: usize) -> (Instance,Witness) {
    let kp:Keypair = Paillier::keypair_with_modulus_size(big_length);
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


pub fn verify0(params: &ProofParams, x: &Instance) -> bool {
    return super::utils::check_small_primes(params.q,&x.n);
}

pub fn prove1(params: &ProofParams, inst: &Instance) -> (Commitment,ComRand) {
    // TODO What's the difference between (a..b) and [a..b]?.. The second one gives unexpected results.
    // apparently a..b is already a range I need, so [a..b] is a singleton array?
    let rand_v: Vec<_> = (0..params.reps).map(|_| {
                            let rm = BigInt::sample_below(&inst.n);
                            let rr = BigInt::sample_below(&inst.n);
                            return (rm,rr);
                        }).collect();
    let alpha_v: Vec<_> = rand_v.iter().map(|(rm,rr)| {
                             let ek = EncryptionKey::from(&inst.n);
                             return Paillier::encrypt_with_chosen_randomness(
                                 &ek,
                                 RawPlaintext::from(rm.clone()),
                                 &Randomness(rr.clone())).0.into_owned();
                         }).collect();
    return (Commitment(alpha_v),ComRand(rand_v));
}

pub fn verify1(params: &ProofParams) -> Challenge {
    let b: Vec<bool> = (0..params.reps).map(|_| rand::random()).collect();
    return Challenge(b);
}

pub fn prove2(params: &ProofParams,
              inst: &Instance,
              wit: &Witness,
              ch: &Challenge,
              cr: &ComRand) -> Response {
    let resp_v: Vec<_> = (0..params.reps).map(|i| {
        let b: bool = (&ch.0)[i];
        let rm:&BigInt = &(&cr.0)[i].0;
        let rr:&BigInt = &(&cr.0)[i].1;

        let t1 = if b { wit.m.clone() } else { BigInt::from(0) };
        let s1 = BigInt::mod_add(rm,&t1,&inst.n);
        let t2 = if b { wit.r.clone() } else { BigInt::from(1) };
        let s2 = BigInt::mod_mul(rr,&t2,&inst.n2);
        return (s1,s2);
    }).collect();
    return Response(resp_v);
}

pub fn verify2(params: &ProofParams,
               inst: &Instance,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    for i in 0..params.reps {
        let b:bool = ch.0[i];
        let s1 = &resp.0[i].0;
        let s2 = &resp.0[i].1;
        let alpha = &com.0[i];

        let ec = if b { inst.ct.clone() } else { BigInt::from(1) };
        let lhs = BigInt::mod_mul(&ec,alpha,&inst.n2);

        let rhs = BigInt::mod_mul(
            &BigInt::mod_pow(&(&inst.n + 1),s1,&inst.n2),
            &BigInt::mod_pow(s2,&inst.n,&inst.n2),
            &inst.n2);

        if lhs != rhs { return false; }
    }
    return true;
}

#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier::*;

    #[test]
    fn test_correctness() {
        // This gives about log33k * 17 = 15 * 17 ~= 256 bits security.
        let params = ProofParams { q: 33000 , reps: 17 };
        let (inst,wit) = lang_sample(2048);

        assert!(verify0(&params,&inst));

        let (com,cr) = prove1(&params,&inst);
        let ch = verify1(&params);

        let resp = prove2(&params,&inst,&wit,&ch,&cr);
        assert!(verify2(&params,&inst,&com,&ch,&resp));
    }

    #[test]
    fn test_soundness_trivial() {
        let params = ProofParams { q: 33000 , reps: 17 };
        let (inst,_) = lang_sample(2048);
        let (_,wit2) = lang_sample(2048);

        assert!(verify0(&params,&inst));

        let (com,cr) = prove1(&params,&inst);
        let ch = verify1(&params);

        // with wit2
        let resp = prove2(&params,&inst,&wit2,&ch,&cr);
        assert!(verify2(&params,&inst,&com,&ch,&resp) == false);
    }

}
