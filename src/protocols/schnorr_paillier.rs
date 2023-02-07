/// This is an implementation of the basic Schnorr protocol for
/// Paillier homomorphism with untrusted modulus N, with the optional
/// range check functionality. It uses the p_max optimisation -- that is,
/// verifier manually checks that there are no p<p_max divisors of N, which
/// allows to use log(p_max) challenge space instead of the binary one.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;

use super::paillier::paillier_enc_opt;

#[derive(Clone, PartialEq, Debug)]
pub struct RangeProofParams {
    /// Range of the original message value.
    pub r: BigInt,
    /// R 2^{λ-1}
    pub rand_range: BigInt,
}

impl RangeProofParams {
    /// Generates new range proof params, precomputes range values
    /// that are used in the actual proof.
    pub fn new(lambda: u32, r: BigInt) -> Self {
        let two_lambda_min1 = BigInt::pow(&BigInt::from(2), lambda - 1);
        // R 2^{λ-1}
        let rand_range = &r * two_lambda_min1;

        RangeProofParams{ r, rand_range }
    }
}

// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Security parameter
    pub lambda: u32,
    /// Bitlength of the RSA modulus.
    pub n_bitlen: u32,
    /// Bitsize of the challenge space
    pub ch_space_bitlen: u32,
    /// Number of repeats of the basic protocol.
    pub reps: usize,
    /// Whether to run in a range-proof mode.
    pub range_params: Option<RangeProofParams>,
}

impl ProofParams {
    fn calc_proof_params(n_bitlen: u32,
                         lambda: u32,
                         ch_space_bitlen: u32,
                         range_params: Option<RangeProofParams>) -> Self {
        let reps = (lambda as f64 / ch_space_bitlen as f64).ceil() as usize;
        return ProofParams { lambda, n_bitlen, ch_space_bitlen, reps, range_params };
    }

    pub fn new(n_bitlen: u32, lambda: u32, ch_space_bitlen: u32) -> Self {
        Self::calc_proof_params(n_bitlen,lambda,ch_space_bitlen,None)
    }

    pub fn new_range(n_bitlen: u32,
                     lambda: u32,
                     r: BigInt) -> Self {
        let range_params = RangeProofParams::new(lambda,r);
        Self::calc_proof_params(n_bitlen,lambda,1,Some(range_params))
    }
}

impl fmt::Display for ProofParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ProofParams ( ch_space_bitlen: {}, reps: {}, n_bitlen: {},  )",
               self.ch_space_bitlen,
               self.reps,
               self.n_bitlen)
    }
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Lang {
    /// Public key that is used to generate instances.
    pub pk: EncryptionKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<DecryptionKey>,
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Inst {
    /// The encryption ciphertext
    pub ct: BigInt
}

#[derive(Clone, PartialEq, Debug)]
pub struct Wit {
    pub m: BigInt,
    pub r: BigInt
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<(BigInt,BigInt)>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Challenge(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Response(Vec<(BigInt,BigInt)>);

pub fn sample_lang(params: &ProofParams) -> Lang {
    let (pk,sk) = Paillier::keypair_with_modulus_size(params.n_bitlen as usize).keys();
    Lang { pk, sk: Some(sk) }
}

pub fn sample_inst(params: &ProofParams, lang: &Lang) -> (Inst,Wit) {
    let m = match &params.range_params {
        // [-R/2,R/2]
        Some(RangeProofParams{r,..}) => {
            let x = BigInt::sample_below(&(r));
            x - r/2
        }
        None => BigInt::sample_below(&lang.pk.n),
    };
    let r = BigInt::sample_below(&lang.pk.n);
    let ct = paillier_enc_opt(&lang.pk, lang.sk.as_ref(), &m, &r);

    let inst = Inst { ct };
    let wit = Wit { m, r };

    return (inst,wit);
}

pub fn sample_liw(params: &ProofParams) -> (Lang,Inst,Wit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(params, &lang);
    (lang,inst,wit)
}


pub fn verify0(params: &ProofParams, lang: &Lang) -> bool {
    if params.ch_space_bitlen > 32 {
        panic!("schnorr_paillier: verify0: ch_space is too big: {:?} bits",
               params.ch_space_bitlen)
    }
    let q:u64 = 2u64.pow(params.ch_space_bitlen);
    if !super::utils::check_small_primes(q,&lang.pk.n) {
        return false
    };

    true
}

pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    let n: &BigInt = &lang.pk.n;
    let rand_v: Vec<_> = (0..params.reps).map(|_| {
        let rm = match &params.range_params {
            // Perfect blinding, because response is computed mod N for Paillier
            None => BigInt::sample_below(n),
            // Statistical blinding, rand_range has (range * ch + lambda) bits, and in range
            // proof setting challenges are binary
            Some(RangeProofParams{ rand_range, .. }) => BigInt::sample_below(&rand_range),
        };
        // Statistical blinding, this must blind (r * ch) modulo n^2
        let rr = BigInt::sample(
            (params.n_bitlen + params.ch_space_bitlen + params.lambda) as usize);
        (rm,rr)
    }).collect();
    let alpha_v: Vec<_> = rand_v.iter().map(|(rm,rr)| {
        paillier_enc_opt(&lang.pk, lang.sk.as_ref(), rm, rr)
    }).collect();
    return (Commitment(alpha_v),ComRand(rand_v));
}

pub fn verify1(params: &ProofParams) -> Challenge {
    let b = (0..params.reps).map(|_| BigInt::sample(params.ch_space_bitlen as usize)).collect();
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

        let s1 = BigInt::mod_add(rm, &BigInt::mod_mul(ch, &wit.m , n), n);
        let s2 = BigInt::mod_mul(rr, &BigInt::mod_pow(&(wit.r), ch, n2), n2);
        return (s1,s2);
    }).collect();
    return Response(resp_v);
}

pub fn verify2(params: &ProofParams,
               lang: &Lang,
               inst: &Inst,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    let n2: &BigInt = &lang.pk.nn;
    for i in 0..params.reps {
        let ch = &(&ch.0)[i];
        let s1 = &resp.0[i].0;
        let s2 = &resp.0[i].1;
        let alpha = &com.0[i];
        let ct = &inst.ct;

        if let Some(RangeProofParams{rand_range,..}) = &params.range_params {
            if s1 >= rand_range  { return false; }
        };

        let lhs = BigInt::mod_mul(&BigInt::mod_pow(&ct, ch, n2), alpha, n2);
        let rhs = paillier_enc_opt(&lang.pk, None, s1, s2);

        if lhs != rhs { return false; }
    }
    return true;
}



#[derive(Clone, Debug, Serialize)]
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
                  lang: &Lang) -> bool {
    verify0(params,lang)
}

pub fn fs_verify(params: &ProofParams,
                 lang: &Lang,
                 inst: &Inst,
                 proof: &FSProof) -> bool {

    let fs_ch_own = fs_compute_challenge(lang,inst,&proof.fs_com);
    if fs_ch_own != proof.fs_ch { return false; }

    verify2(&params,&lang,&inst,
            &proof.fs_com,&proof.fs_ch,&proof.fs_resp)
}


#[cfg(test)]
mod tests {

    use crate::protocols::schnorr_paillier::*;

    #[test]
    fn test_correctness() {
        let params = ProofParams::new(2048, 128, 15);
        let (lang,inst,wit) = sample_liw(&params);

        let res = verify0(&params,&lang);
        assert!(res);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        let resp = prove2(&params,&lang,&wit,&ch,&cr);
        assert!(verify2(&params,&lang,&inst,&com,&ch,&resp));
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(2048, 128, 15);
        let (lang,inst,wit) = sample_liw(&params);

        let proof = fs_prove(&params,&lang,&inst,&wit);
        let res0 = fs_verify0(&params,&lang);
        assert!(res0);
        let res = fs_verify(&params,&lang,&inst,&proof);
        assert!(res);
    }


    #[test]
    fn test_correctness_range() {
        let lambda = 128;
        let range = BigInt::pow(&BigInt::from(2), 200);
        let params = ProofParams::new_range(512, lambda, range);
        let (lang,inst,wit) = sample_liw(&params);

        println!("Debug: Inst {:?}", inst);

        let res = verify0(&params,&lang);
        assert!(res);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        let resp = prove2(&params,&lang,&wit,&ch,&cr);
        assert!(verify2(&params,&lang,&inst,&com,&ch,&resp));
    }


    #[test]
    fn test_soundness_trivial() {
        let params = ProofParams::new(2048, 128, 15);

        let lang = sample_lang(&params);
        let (inst,_) = sample_inst(&params,&lang);
        let (_,wit2) = sample_inst(&params,&lang);


        let res = verify0(&params,&lang);
        assert!(res);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        // with wit2
        let resp = prove2(&params,&lang,&wit2,&ch,&cr);
        assert!(verify2(&params,&lang,&inst,&com,&ch,&resp) == false);
    }

}
