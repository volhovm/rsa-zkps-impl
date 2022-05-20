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
    /// Bitlength of the RSA modulus.
    pub n_bitlen: u32,
    /// Size of the challenge space, upper bound.
    pub ch_space: BigInt,
}


#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Lang {
    /// RSA modulus
    pub n: BigInt,
    /// Randomly sampled from Z_N
    pub h: BigInt
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

/// Contains N-2^{λ+1} R
#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct VerifierPrecomp(Option<BigInt>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(BigInt);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(BigInt);

#[derive(Clone, PartialEq, Debug)]
pub struct Challenge(BigInt);

#[derive(Clone, PartialEq, Debug)]
pub struct Response(BigInt);


pub fn verify0(params: &ProofParams, lang: &Lang) -> (bool,VerifierPrecomp) {
    if !super::utils::check_small_primes(params.q,&lang.n) {
        return (false,VerifierPrecomp(None));
    };

    (true, VerifierPrecomp(None))
}

pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    let n = &lang.n;
    let r = BigInt::sample_below(n);
    let com = BigInt::mod_pow(&lang.h, &r, n);
    return (Commitment(com),ComRand(r));
}

pub fn verify1(params: &ProofParams) -> Challenge {
    let b = BigInt::sample_below(&params.ch_space);
    return Challenge(b);
}

pub fn prove2(params: &ProofParams,
              lang: &Lang,
              wit: &Wit,
              ch: &Challenge,
              cr: &ComRand) -> Response {
    let n: &BigInt = &lang.n;
    let resp = BigInt::mod_add(&cr.0, &BigInt::mod_mul(&wit.x,&ch.0, n), n);
    return Response(resp);
}

pub fn verify2(params: &ProofParams,
               lang: &Lang,
               inst: &Inst,
               _precomp: &VerifierPrecomp,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    let n = &lang.n;

    let lhs = BigInt::mod_mul(&BigInt::mod_pow(&inst.g, &ch.0, n), &com.0, n);
    let rhs = BigInt::mod_pow(&lang.h, &resp.0, n);

    lhs == rhs
}



#[derive(Clone, Debug)]
pub struct FSProof {
    fs_com : Commitment,
    fs_ch : Challenge,
    fs_resp : Response
}

fn fs_compute_challenge(lang: &Lang, inst:&Inst, com: &Commitment) -> Challenge {
    use blake2::*;
    let x: Vec<u8> = rmp_serde::to_vec(&(com, inst, lang)).unwrap();
    // Use Digest::digest, but it asks for a fixed-sized slice?
    let mut hasher: Blake2b = Digest::new();
    hasher.update(&x);
    let r0 = hasher.finalize();
    let b = BigInt::from((&(r0.as_slice())[0] & 0b0000001) as u32);
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

    let fs_ch_own = fs_compute_challenge(lang,inst,&proof.fs_com);
    if fs_ch_own != proof.fs_ch { return false; }

    verify2(&params,&lang,&inst,precomp,
            &proof.fs_com,&proof.fs_ch,&proof.fs_resp)
}


//#[cfg(test)]
//mod tests {
//
//    use crate::protocols::schnorr_paillier::*;
//
//    #[test]
//    fn test_correctness() {
//        let params = ProofParams::new(2048, 128, 15);
//        let (lang,inst,wit) = sample_liw(&params);
//
//        let (res,precomp) = verify0(&params,&lang);
//        assert!(res);
//
//        let (com,cr) = prove1(&params,&lang);
//        let ch = verify1(&params);
//
//        let resp = prove2(&params,&lang,&wit,&ch,&cr);
//        assert!(verify2(&params,&lang,&inst,&precomp,&com,&ch,&resp));
//    }
//
//}
