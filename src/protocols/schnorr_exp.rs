use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;


#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Secparam
    pub lambda: u32,
    /// Small number up to which N shouldn't have divisors.
    pub q: u64,
    /// Number of repetitions of the protocol.
    pub reps: usize,
    /// Bitlength of the RSA modulus.
    pub n_bitlen: u32,
    /// Size of the challenge space, upper bound.
    pub ch_space: BigInt,
}

impl ProofParams {
    // Rep bits is bitlength of the smallest prime in N.
    pub fn new(n_bitlen: u32,
           lambda: u32,
           repbits: u32) -> Self {
        let ch_space = BigInt::pow(&BigInt::from(2), repbits);
        let reps = (lambda as f64 / repbits as f64).ceil() as usize;
        let q = 2u64.pow(repbits);
        return ProofParams { q, reps, n_bitlen, lambda, ch_space };
    }

}


////////////////////////////////////////////////////////////////////////////
// Language
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Lang {
    /// RSA modulus
    pub n: BigInt,
    /// Randomly sampled from Z_N
    pub h: BigInt,
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Inst {
    /// g = h^x
    pub g: BigInt,
}

#[derive(Clone, PartialEq, Debug)]
pub struct Wit {
    /// x | g = h^x
    pub x: BigInt
}


pub fn sample_lang(params: &ProofParams) -> Lang {
    let pk = Paillier::keypair_with_modulus_size(params.n_bitlen as usize).keys().0;
    let h = BigInt::sample_below(&pk.n);
    Lang{n: pk.n.clone(), h: h.clone()}
}

pub fn sample_inst(_params: &ProofParams, lang: &Lang) -> (Inst,Wit) {
    let x = BigInt::sample_below(&lang.n);
    let g = BigInt::mod_pow(&lang.h, &x, &lang.n);

    (Inst{g}, Wit{x})
}

pub fn sample_liw(params: &ProofParams) -> (Lang,Inst,Wit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(params, &lang);
    (lang,inst,wit)
}


////////////////////////////////////////////////////////////////////////////
// Protocol
////////////////////////////////////////////////////////////////////////////


/// Contains N-2^{λ+1} R
#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct VerifierPrecomp(pub Option<BigInt>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct Challenge(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct Response(Vec<BigInt>);



pub fn verify0(params: &ProofParams, lang: &Lang) -> (bool,VerifierPrecomp) {
    if !super::utils::check_small_primes(params.q,&lang.n) {
        return (false,VerifierPrecomp(None));
    };

    (true, VerifierPrecomp(None))
}

pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    let mut rand_v = vec![];
    let mut com_v = vec![];
    for _i in 0..params.reps {
        let r = BigInt::sample_below(&lang.n);
        com_v.push(BigInt::mod_pow(&lang.h, &r, &lang.n));
        rand_v.push(r);
    }
    return (Commitment(com_v),ComRand(rand_v));
}

pub fn verify1(params: &ProofParams) -> Challenge {
    let b = (0..params.reps).map(|_| BigInt::sample_below(&params.ch_space)).collect();
    return Challenge(b);
}

pub fn prove2(params: &ProofParams,
              lang: &Lang,
              wit: &Wit,
              ch: &Challenge,
              cr: &ComRand) -> Response {
    //let n: &BigInt = &lang.n;
    let resp_v: Vec<_> = (0..params.reps).map(|i| {
        &cr.0[i] + &wit.x * &ch.0[i]
    }).collect();
    return Response(resp_v);
}

pub fn verify2(params: &ProofParams,
               lang: &Lang,
               inst: &Inst,
               _precomp: &VerifierPrecomp,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    let n = &lang.n;

    for i in 0..params.reps {
        println!("Verifying...");
        let lhs = BigInt::mod_mul(&BigInt::mod_pow(&inst.g, &ch.0[i], n), &com.0[i], n);
        let rhs = BigInt::mod_pow(&lang.h, &resp.0[i], n);

        if lhs != rhs { return false; }
    }
    true
}



#[derive(Clone, Debug)]
pub struct FSProof {
    fs_com : Commitment,
    fs_ch : Challenge,
    fs_resp : Response
}

fn fs_compute_challenge(lang: &Lang, inst:&Inst, fs_com: &Commitment) -> Challenge {
    use blake2::*;
    let b = fs_com.0.iter().map(|com:&BigInt| {
        let x: Vec<u8> = rmp_serde::to_vec(&(com, inst, lang)).unwrap();
        // Use Digest::digest, but it asks for a fixed-sized slice?
        let mut hasher: Blake2b = Digest::new();
        hasher.update(&x);
        let r0 = hasher.finalize();
        BigInt::from((&(r0.as_slice())[0] & 0b0000001) as u32)
    }).collect();
    Challenge(b)
}


pub fn fs_prove(params: &ProofParams,
                lang: &Lang,
                inst: &Inst,
                wit: &Wit) -> FSProof {
    let (fs_com,cr) = prove1(&params,&lang);
    let fs_ch = fs_compute_challenge(lang,inst,&fs_com);
    let fs_resp = prove2(&params,&lang,&wit,&fs_ch,&cr);

    FSProof{ fs_com, fs_ch, fs_resp }
}

pub fn fs_verify0(params: &ProofParams,
                  lang: &Lang) -> (bool, VerifierPrecomp) {
    verify0(params,lang)
}

pub fn fs_verify(params: &ProofParams,
                 lang: &Lang,
                 inst: &Inst,
                 precomp: &VerifierPrecomp,
                 proof: &FSProof) -> bool {
    let (res0, _) = fs_verify0(params,lang);
    if !res0 { return false; }

    let fs_ch_own = fs_compute_challenge(lang,inst,&proof.fs_com);
    if fs_ch_own != proof.fs_ch { return false; }

    verify2(&params,&lang,&inst,precomp,
            &proof.fs_com,&proof.fs_ch,&proof.fs_resp)
}




#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_exp::*;

    #[test]
    fn test_correctness() {
        let params = ProofParams::new(2048, 128, 15);
        let (lang,inst,wit) = sample_liw(&params);

        let (res,precomp) = verify0(&params,&lang);
        assert!(res);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        let resp = prove2(&params,&lang,&wit,&ch,&cr);
        assert!(verify2(&params,&lang,&inst,&precomp,&com,&ch,&resp));
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(2048, 128, 15);
        let (lang,inst,wit) = sample_liw(&params);

        let proof = fs_prove(&params,&lang,&inst,&wit);
        let (res0,precomp) = fs_verify0(&params,&lang);
        assert!(res0);
        let res = fs_verify(&params,&lang,&inst,&precomp,&proof);
        assert!(res);
    }
}
