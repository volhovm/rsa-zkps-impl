/// Schnorr for Paillier-Elgamal.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::fmt;

use super::paillier_elgamal as pe;


// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Security parameter
    pub lambda: u32,
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
    pub fn new(n_bitlen: u32, lambda: u32, repbits: u32) -> Self {
        let ch_space = BigInt::pow(&BigInt::from(2), repbits);
        return ProofParams { q: 2u64.pow(repbits),
                             reps: (lambda as f64 / repbits as f64).ceil() as usize,
                             n_bitlen, ch_space, lambda };
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
    pub pk: pe::PEPublicKey,
    /// Optional decryption key that speeds up Paillier
    pub sk: Option<pe::PESecretKey>,
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Inst {
    /// The encryption ciphertext
    pub ct: pe::PECiphertext
}

#[derive(Clone, PartialEq, Debug)]
pub struct Wit {
    pub m: BigInt,
    pub r: BigInt
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(Vec<Inst>);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<Wit>);

#[derive(Clone, PartialEq, Debug)]
pub struct Challenge(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct Response(Vec<Wit>);

pub fn sample_lang(params: &ProofParams) -> Lang {
    let (pk,sk) = pe::keygen(params.n_bitlen as usize);
    Lang { pk, sk: Some(sk) }
}

pub fn sample_inst(_params: &ProofParams, lang: &Lang) -> (Inst,Wit) {
    let m = BigInt::sample_below(&lang.pk.n);
    let r = BigInt::sample_below(&lang.pk.n);
    let ct = pe::encrypt_with_randomness_opt(&lang.pk, lang.sk.as_ref(), &m, &r);

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
    if !super::utils::check_small_primes(params.q,&lang.pk.n) {
        return false
    };

    true
}

pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    let n: &BigInt = &lang.pk.n;
    let rand_v: Vec<_> = (0..params.reps).map(|_| {
        let rm = BigInt::sample_below(&(n + &BigInt::pow(&BigInt::from(2), params.lambda)));
        let rr = BigInt::sample_below(&(n + &BigInt::pow(&BigInt::from(2), params.lambda)));
        Wit{ m: rm, r: rr }
    }).collect();
    let alpha_v: Vec<_> = rand_v.iter().map(|rand| {
        Inst{ ct: pe::encrypt_with_randomness_opt(&lang.pk, lang.sk.as_ref(), &rand.m, &rand.r) }
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
    let resp_v: Vec<_> = (0..params.reps).map(|i| {
        let ch = &(&ch.0)[i];
        let rm = &(&cr.0)[i].m;
        let rr = &(&cr.0)[i].r;

        let s1 = BigInt::mod_add(rm, &BigInt::mod_mul(ch, &wit.m , n), n);
        let s2 = BigInt::add(rr, &BigInt::mul(ch, &wit.r));
        //let s2 = BigInt::mod_mul(rr, &BigInt::mod_pow(&(wit.r), ch, n2), n2);
        return Wit{ m: s1, r: s2 };
    }).collect();
    return Response(resp_v);
}

pub fn verify2(params: &ProofParams,
               lang: &Lang,
               inst: &Inst,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    let n2: &BigInt = &lang.pk.n2;
    for i in 0..params.reps {
        let ch = &(&ch.0)[i];
        let s1 = &resp.0[i].m;
        let s2 = &resp.0[i].r;
        let alpha = &com.0[i].ct;
        let ct = &inst.ct;

        let lhs_1 = BigInt::mod_mul(&BigInt::mod_pow(&ct.ct1, ch, n2), &alpha.ct1, n2);
        let lhs_2 = BigInt::mod_mul(&BigInt::mod_pow(&ct.ct2, ch, n2), &alpha.ct2, n2);

        let rhs = pe::encrypt_with_randomness_opt(&lang.pk, None, &s1, &s2);

        if lhs_1 != rhs.ct1 {
            // println!("First equation failed.");
            return false;
        }
        if lhs_2 != rhs.ct2 {
            // println!("Second equation failed.");
            return false;
        }
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
    let b = fs_com.0.iter().map(|com:&Inst| {
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

    use crate::protocols::schnorr_paillier_elgamal::*;

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


//    #[test]
//    fn test_correctness_range() {
//        let lambda = 128;
//        let range = BigInt::pow(&BigInt::from(2), 200);
//        let params = ProofParams::new_range(512, lambda, range);
//        let (lang,inst,wit) = sample_liw(&params);
//
//        println!("Debug: Inst {:?}", inst);
//
//        let (res,precomp) = verify0(&params,&lang);
//        println!("Debug: Precomp {:?}", precomp);
//        assert!(res);
//
//        let (com,cr) = prove1(&params,&lang);
//        let ch = verify1(&params);
//
//        let resp = prove2(&params,&lang,&wit,&ch,&cr);
//        assert!(verify2(&params,&lang,&inst,&precomp,&com,&ch,&resp));
//    }
//
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
