use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use std::fmt;


// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Small number up to which N shouldn't have divisors.
    pub q: u64,
    /// Number of repeats of the basic protocol.
    pub reps: usize,
    /// Bitlength of the RSA modulus.
    pub n_bitlen: usize,
    /// Size of the challenge space, upper bound.
    pub ch_space: BigInt
}

impl ProofParams {
    pub fn calc_proof_params(n_bitlen: usize, sec_level: u32, repbits: u32) -> Self {
        let ch_space = BigInt::pow(&BigInt::from(2), repbits);
        return ProofParams { q: 2u64.pow(repbits),
                             reps: (sec_level as f64 / repbits as f64).ceil() as usize,
                             n_bitlen: n_bitlen,
                             ch_space: ch_space };
    }
}

impl fmt::Display for ProofParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ProofParams ( q: {}, reps: {}, n_bitlen: {}, ch_space: {} )",
               self.q,
               self.reps,
               self.n_bitlen,
               self.ch_space)
    }
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
pub struct Challenge(Vec<BigInt>);
#[derive(Clone, PartialEq, Debug)]
pub struct Response(Vec<(BigInt,BigInt)>);


pub fn lang_sample(params: &ProofParams) -> (Instance,Witness) {
    let kp:Keypair = Paillier::keypair_with_modulus_size(params.n_bitlen);
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
    let b = (0..params.reps).map(|_| BigInt::sample_below(&params.ch_space)).collect();
    return Challenge(b);
}

pub fn prove2(params: &ProofParams,
              inst: &Instance,
              wit: &Witness,
              ch: &Challenge,
              cr: &ComRand) -> Response {
    let resp_v: Vec<_> = (0..params.reps).map(|i| {
        let ch = &(&ch.0)[i];
        let rm = &(&cr.0)[i].0;
        let rr = &(&cr.0)[i].1;

        let t1 = BigInt::mod_mul(ch, &(wit.m), &inst.n);
        let s1 = BigInt::mod_add(rm,&t1,&inst.n);
        let t2 = BigInt::mod_pow(&(wit.r), ch, &inst.n2);
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
        let ch = &(&ch.0)[i];
        let s1 = &resp.0[i].0;
        let s2 = &resp.0[i].1;
        let alpha = &com.0[i];

        let ec = BigInt::mod_pow(&inst.ct, ch, &inst.n2);
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
        let ch_space = BigInt::pow(&BigInt::from(2), 15);
        let params = ProofParams { q: 2u64.pow(15),
                                   reps: 17,
                                   n_bitlen: 2048,
                                   ch_space: ch_space };
        let (inst,wit) = lang_sample(&params);

        assert!(verify0(&params,&inst));

        let (com,cr) = prove1(&params,&inst);
        let ch = verify1(&params);

        let resp = prove2(&params,&inst,&wit,&ch,&cr);
        assert!(verify2(&params,&inst,&com,&ch,&resp));
    }

    #[test]
    fn test_soundness_trivial() {
        let ch_space = BigInt::pow(&BigInt::from(2), 15);
        let params = ProofParams { q: 2u64.pow(15),
                                   reps: 17,
                                   n_bitlen: 2048,
                                   ch_space: ch_space};
        let (inst,_) = lang_sample(&params);
        let (_,wit2) = lang_sample(&params);

        assert!(verify0(&params,&inst));

        let (com,cr) = prove1(&params,&inst);
        let ch = verify1(&params);

        // with wit2
        let resp = prove2(&params,&inst,&wit2,&ch,&cr);
        assert!(verify2(&params,&inst,&com,&ch,&resp) == false);
    }

}
