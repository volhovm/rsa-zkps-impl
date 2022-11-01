// variant of schnorr_paillier for knowledge-of-ciphertext for the DVRange protocol

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;

// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Small number up to which N shouldn't have divisors.
    pub q: u64,
    /// Number of repeats of the basic protocol.
    pub reps: usize,
    /// Bitlength of the RSA modulus.
    pub n_bitlen: u32,
    /// Size of the challenge space, upper bound.
    pub ch_space: BigInt,
}

impl ProofParams {
    fn calc_proof_params(n_bitlen: u32,
                         lambda: u32,
                         repbits: u32) -> Self {
        let ch_space = BigInt::pow(&BigInt::from(2), repbits);
        return ProofParams { q: 2u64.pow(repbits),
                             reps: (lambda as f64 / repbits as f64).ceil() as usize,
                             n_bitlen, ch_space };
    }
    pub fn new(n_bitlen: u32, lambda: u32, repbits: u32) -> Self {
        Self::calc_proof_params(n_bitlen,lambda,repbits)
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

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Lang {
    /// Public key that is used to generate instances.
    pub pk: EncryptionKey,
    /// The encryption ciphertext C, corresponding to the DVRange challenge
    pub ch_ct: BigInt,
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Inst {
    /// The encryption ciphertext S_i = Enc(w1,w2)
    pub si: BigInt
}

#[derive(Clone, PartialEq, Debug)]
pub struct Wit {
    pub m: BigInt,
    pub r: BigInt,
    /// exponent of ct
    pub cexp: BigInt, 
}

pub fn sample_lang(params: &ProofParams) -> Lang {
    let pk = Paillier::keypair_with_modulus_size(params.n_bitlen as usize).keys().0;
    let ch_ct = BigInt::sample_below(&pk.nn);
    Lang { pk, ch_ct }
}

// Computes Enc_pk(enc_arg,rand)*Ct^{ct_exp}
pub fn compute_si(pk: &EncryptionKey, ch_ct: &BigInt, m: &BigInt, r: &BigInt, cexp: &BigInt) -> BigInt {
    BigInt::mod_mul(
        &Paillier::encrypt_with_chosen_randomness(
            pk,
            RawPlaintext::from(m),
            &Randomness::from(r)).0.into_owned(),
        &super::utils::bigint_mod_pow(ch_ct, cexp, &pk.nn),
        &pk.nn)
}

pub fn sample_inst(params: &ProofParams, lang: &Lang) -> (Inst,Wit) {
    let m =  BigInt::sample_below(&lang.pk.n);
    let r = BigInt::sample_below(&lang.pk.n);
    let cexp = BigInt::sample_below(&lang.pk.n);
    let si = compute_si(&lang.pk, &lang.ch_ct, &m, &r, &cexp);

    let inst = Inst { si };
    let wit = Wit { m, r, cexp };

    return (inst,wit);
}

pub fn sample_liw(params: &ProofParams) -> (Lang,Inst,Wit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(params, &lang);
    (lang,inst,wit)
}


////////////////////////////////////////////////////////////////////////////
// Interactive protocol
////////////////////////////////////////////////////////////////////////////


/// Contains N-2^{λ+1} R
#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct VerifierPrecomp(Option<BigInt>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<(BigInt,BigInt,BigInt)>);

#[derive(Clone, PartialEq, Debug)]
pub struct Challenge(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct Response(Vec<(BigInt,BigInt,BigInt)>);

pub fn verify0(params: &ProofParams, lang: &Lang) -> (bool,VerifierPrecomp) {
    if !super::utils::check_small_primes(params.q,&lang.pk.n) {
        return (false,VerifierPrecomp(None));
    };

    (true, VerifierPrecomp(None))
}

pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    let n: &BigInt = &lang.pk.n;
    let rand_v: Vec<_> = (0..params.reps).map(|_| {
        let rm =  BigInt::sample_below(n);
        let rr = BigInt::sample_below(n);
        // FIXME should be just enough to blind c*wit.cexp, but wit.cexp is small.
        let rcexp = BigInt::sample_below(n); 
        (rm,rr,rcexp)
    }).collect();
    let alpha_v: Vec<_> = rand_v.iter().map(|(rm,rr,rcexp)| {
        compute_si(&lang.pk, &lang.ch_ct,&rm,&rr,&rcexp)
    }).collect();
    return (Commitment(alpha_v),ComRand(rand_v));
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
    let n: &BigInt = &lang.pk.n;
    let n2: &BigInt = &lang.pk.nn;
    let resp_v: Vec<_> = (0..params.reps).map(|i| {
        let ch = &(&ch.0)[i];
        let rm = &(&cr.0)[i].0;
        let rr = &(&cr.0)[i].1;
        let rcexp = &(&cr.0)[i].2;

        let s1 = BigInt::mod_add(rm, &BigInt::mod_mul(&wit.m, ch, n), n);
        let s2 = BigInt::mod_mul(rr, &BigInt::mod_pow(&wit.r, ch, n2), n2);
        let s3 = &wit.cexp * ch + rcexp;
        return (s1,s2,s3);
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
    let n: &BigInt = &lang.pk.n;
    let n2: &BigInt = &lang.pk.nn;
    for i in 0..params.reps {
        let ch = &(&ch.0)[i];
        let s1 = &resp.0[i].0;
        let s2 = &resp.0[i].1;
        let s3 = &resp.0[i].2;

        let alpha = &com.0[i];

        let lhs = BigInt::mod_mul(&BigInt::mod_pow(&inst.si, ch, n2), alpha, n2);
        let rhs = compute_si(&lang.pk, &lang.ch_ct, s1, s2, s3);

        if lhs != rhs { return false; }
    }
    return true;
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

    let fs_ch_own = fs_compute_challenge(lang,inst,&proof.fs_com);
    if fs_ch_own != proof.fs_ch { return false; }

    verify2(&params,&lang,&inst,precomp,
            &proof.fs_com,&proof.fs_ch,&proof.fs_resp)
}


#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier_plus::*;

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

//
//    #[test]
//    fn test_soundness_trivial() {
//        let params = ProofParams::new(2048, 128, 15);
//
//        let lang = sample_lang(&params);
//        let (inst,_) = sample_inst(&params,&lang);
//        let (_,wit2) = sample_inst(&params,&lang);
//
//
//        let (res,precomp) = verify0(&params,&lang);
//        assert!(res);
//
//        let (com,cr) = prove1(&params,&lang);
//        let ch = verify1(&params);
//
//        // with wit2
//        let resp = prove2(&params,&lang,&wit2,&ch,&cr);
//        assert!(verify2(&params,&lang,&inst,&precomp,&com,&ch,&resp) == false);
//    }

}
