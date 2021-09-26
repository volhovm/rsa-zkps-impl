use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;


#[derive(Clone, PartialEq, Debug)]
pub struct RangeProofParams {
    /// Security parameter
    pub lambda: u32,
    /// Range of the original message value.
    pub r: BigInt,
    /// R 2^λ
    pub rand_range: BigInt,
    /// R 2^{λ+1}
    pub rand_range2: BigInt,
}

impl RangeProofParams {
    /// Generates new range proof params, precomputes range values
    /// that are used in the actual proof.
    pub fn new(lambda: u32, r: BigInt) -> Self {
        let two_lambda = BigInt::pow(&BigInt::from(2), lambda);
        // R 2^λ
        let rand_range = &r * two_lambda;
        // R 2^{λ+1}
        let rand_range2 = &rand_range * &BigInt::from(2);

        RangeProofParams{ lambda, r, rand_range, rand_range2 }
    }
}

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
    pub ch_space: BigInt,
    /// Whether to run in a range-proof mode.
    pub range_params: Option<RangeProofParams>,
}

impl ProofParams {
    fn calc_proof_params(n_bitlen: usize,
                         lambda: u32,
                         repbits: u32,
                         range_params: Option<RangeProofParams>) -> Self {
        let ch_space = BigInt::pow(&BigInt::from(2), repbits);
        return ProofParams { q: 2u64.pow(repbits),
                             reps: (lambda as f64 / repbits as f64).ceil() as usize,
                             n_bitlen, ch_space, range_params };
    }
    pub fn new(n_bitlen: usize, lambda: u32, repbits: u32) -> Self {

        Self::calc_proof_params(n_bitlen,lambda,repbits,None)
    }
    pub fn new_range(n_bitlen: usize,
                     lambda: u32,
                     r: BigInt) -> Self {
        let range_params = RangeProofParams::new(lambda,r);
        Self::calc_proof_params(n_bitlen,lambda,1,Some(range_params))
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
    pub pk: EncryptionKey
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

/// Contains (optionally) ciphertext encrypting -2^{λ+1} R, in case
/// we're in range proof mode
#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct VerifierPrecomp(Option<BigInt>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<(BigInt,BigInt)>);

#[derive(Clone, PartialEq, Debug)]
pub struct Challenge(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct Response(Vec<(BigInt,BigInt)>);

pub fn sample_lang(params: &ProofParams) -> Lang {
    let pk = Paillier::keypair_with_modulus_size(params.n_bitlen).keys().0;
    Lang { pk }
}

pub fn sample_inst(params: &ProofParams, lang: &Lang) -> (Inst,Wit) {
    let m = match &params.range_params {
        Some(RangeProofParams{r,..}) => BigInt::sample_below(&r),
        None => BigInt::sample_below(&lang.pk.n),
    };
    let r = BigInt::sample_below(&lang.pk.n);
    let ct = Paillier::encrypt_with_chosen_randomness(
             &lang.pk,
             RawPlaintext::from(m.clone()),
             &Randomness(r.clone())).0.into_owned();

    let inst = Inst { ct };
    let wit = Wit { m, r };

    return (inst,wit);
}

pub fn sample_liw(params: &ProofParams) -> (Lang,Inst,Wit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(params, &lang);
    (lang,inst,wit)
}


pub fn verify0(params: &ProofParams, lang: &Lang) -> (bool,VerifierPrecomp) {
    if !super::utils::check_small_primes(params.q,&lang.pk.n) {
        return (false,VerifierPrecomp(None));
    };

    let precomp = params.range_params.as_ref().map(|RangeProofParams{rand_range2,..}| {
//            let rnd = BigInt::sample_below(&inst.pk.n);
            let rnd = BigInt::from(1);
            let m = &lang.pk.n - rand_range2;
            let neg_ct = Paillier::encrypt_with_chosen_randomness(
                &lang.pk,
                RawPlaintext::from(m),
                &Randomness(rnd)).0.into_owned();
            neg_ct
        });

    (true, VerifierPrecomp(precomp))
}

pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    // TODO What's the difference between (a..b) and [a..b]?.. The second one gives unexpected results.
    // apparently a..b is already a range I need, so [a..b] is a singleton array?
    let n: &BigInt = &lang.pk.n;
    let rand_v: Vec<_> = (0..params.reps).map(|_| {
        let rm = match &params.range_params {
            Some(RangeProofParams{ rand_range, .. }) =>
                BigInt::sample_below(&rand_range),
            None => BigInt::sample_below(n),
        };
        let rr = BigInt::sample_below(n);
        (rm,rr)
    }).collect();
    let alpha_v: Vec<_> = rand_v.iter().map(|(rm,rr)| {
        let ek = EncryptionKey::from(n);
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

//        let m_shifted = None;
        let m_shifted = params.range_params.as_ref().map(|RangeProofParams{rand_range2,..}| {
            // Is this the most efficient way?..
            (n - rand_range2 + &wit.m) % n
        });
        // I can't create this inside map because of referencing issues
        let mm = if m_shifted.is_some() { m_shifted.as_ref().unwrap() } else { &wit.m };

        let t1 = BigInt::mod_mul(ch, mm, n);
        let s1 = BigInt::mod_add(rm, &t1, n);
        let t2 = BigInt::mod_pow(&(wit.r), ch, n2);
        let s2 = BigInt::mod_mul(rr, &t2, n2);
        return (s1,s2);
    }).collect();
    return Response(resp_v);
}

pub fn verify2(params: &ProofParams,
               lang: &Lang,
               inst: &Inst,
               precomp: &VerifierPrecomp,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    let n: &BigInt = &lang.pk.n;
    let n2: &BigInt = &lang.pk.nn;
    for i in 0..params.reps {
        let ch = &(&ch.0)[i];
        let s1 = &resp.0[i].0;
        let s2 = &resp.0[i].1;
        let alpha = &com.0[i];
        let mut ct = inst.ct.clone();

        if let Some(RangeProofParams{rand_range2,..}) = &params.range_params {
            let neg_ct = precomp.0.as_ref().unwrap();
//            println!("Before challenge size check");
            if s1 >= rand_range2 || s1 < &BigInt::from(0) { return false; }
//            println!("Passed challenge size check");
            ct = BigInt::mod_mul(&ct, &neg_ct, n2);
        };

        let ec = BigInt::mod_pow(&ct, ch, n2);
        let lhs = BigInt::mod_mul(&ec, alpha, n2);

        let rhs = BigInt::mod_mul(
            &BigInt::mod_pow(&(n + 1), s1, n2),
            &BigInt::mod_pow(s2, n, n2),
            &n2);

        if lhs != rhs { return false; }

//        println!("Attempt {}, successful!", i);
    }
    return true;
}

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

    use crate::protocols::schnorr_paillier::*;

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


    #[test]
    fn test_correctness_range() {
        let lambda = 128;
        let range = BigInt::pow(&BigInt::from(2), 200);
        let params = ProofParams::new_range(512, lambda, range);
        let (lang,inst,wit) = sample_liw(&params);

        println!("Debug: Inst {:?}", inst);

        let (res,precomp) = verify0(&params,&lang);
        println!("Debug: Precomp {:?}", precomp);
        assert!(res);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        let resp = prove2(&params,&lang,&wit,&ch,&cr);
        assert!(verify2(&params,&lang,&inst,&precomp,&com,&ch,&resp));
    }


    #[test]
    fn test_soundness_trivial() {
        let params = ProofParams::new(2048, 128, 15);

        let lang = sample_lang(&params);
        let (inst,_) = sample_inst(&params,&lang);
        let (_,wit2) = sample_inst(&params,&lang);


        let (res,precomp) = verify0(&params,&lang);
        assert!(res);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        // with wit2
        let resp = prove2(&params,&lang,&wit2,&ch,&cr);
        assert!(verify2(&params,&lang,&inst,&precomp,&com,&ch,&resp) == false);
    }

}
