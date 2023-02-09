/// A generic Schnorr implementation for any homomorphisms.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use serde::{Serialize, Serializer};
use std::fmt;
use std::fmt::Debug;

////////////////////////////////////////////////////////////////////////////
// Params
////////////////////////////////////////////////////////////////////////////

#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Security parameter
    pub lambda: u32,
    /// Bit size of the challenge space
    pub ch_space_bitlen: u32,
    /// Number of repetitions of the protocol
    pub reps: usize,
    /// Whether to run in a range mode
    pub range_mode: bool
}

impl ProofParams {
    pub fn new(lambda: u32,
               ch_space_bitlen: u32) -> Self {
        let reps = (lambda as f64 / ch_space_bitlen as f64).ceil() as usize;
        return ProofParams { lambda, ch_space_bitlen, reps, range_mode: false };
    }
    pub fn new_range(lambda: u32) -> Self {
        // Binary challenges for the range mode
        return ProofParams { lambda,
                             ch_space_bitlen: 1,
                             reps: lambda as usize,
                             range_mode: true };
    }
}

////////////////////////////////////////////////////////////////////////////
// Language
////////////////////////////////////////////////////////////////////////////

pub trait Lang: Serialize {
    type LangParams: Clone + Debug;
    type Dom: Serialize + Eq + Clone + Debug;
    type CoDom: Serialize + Eq + Clone + Debug;

    fn sample_lang(lparams: &Self::LangParams) -> Self;
    fn to_public(&self) -> Self;
    fn verify(&self, params: &ProofParams) -> bool;

    fn sample_wit(&self) -> Self::Dom;

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom;

    fn sample_com_rand(&self, params: &ProofParams) -> Self::Dom;
    fn compute_resp(&self, wit: &Self::Dom, ch: &BigInt, rand: &Self::Dom) -> Self::Dom;
    fn resp_lhs(&self, inst: &Self::CoDom, ch: &BigInt, com: &Self::CoDom) -> Self::CoDom;

    fn check_resp_range(&self, params: &ProofParams, resp: &Self::Dom) -> bool;

    fn sample_liw(lparams: &Self::LangParams) -> (Self,Self::CoDom,Self::Dom) where Self: Sized {
        let lang = Self::sample_lang(lparams);
        let wit = lang.sample_wit();
        let inst = lang.eval(&wit);
        (lang,inst,wit)
    }
}

////////////////////////////////////////////////////////////////////////////
// Protocol
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug)]
pub struct Commitment<L:Lang>(Vec<L::CoDom>);

#[derive(Clone, Debug, )]
pub struct ComRand<L:Lang>(Vec<L::Dom>);

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Challenge(pub Vec<BigInt>);

#[derive(Clone, Debug)]
pub struct Response<L:Lang>(Vec<L::Dom>);



pub fn prove1<L:Lang>(params: &ProofParams, lang: &L) -> (Commitment<L>,ComRand<L>) {
    let mut rand_v = vec![];
    let mut com_v = vec![];
    for _i in 0..params.reps {
        let wit = lang.sample_com_rand(params);
        let inst = lang.eval(&wit);
        rand_v.push(wit);
        com_v.push(inst);
    }
    return (Commitment(com_v),ComRand(rand_v));
}

pub fn verify1(params: &ProofParams) -> Challenge {
    let b = (0..params.reps).map(|_| BigInt::sample(params.ch_space_bitlen as usize)).collect();
    return Challenge(b);
}

pub fn prove2<L:Lang>(params: &ProofParams,
                      lang: &L,
                      wit: &L::Dom,
                      ch: &Challenge,
                      cr: &ComRand<L>) -> Response<L> {
    let resp_v: Vec<_> = (0..params.reps).map(|i| {
        lang.compute_resp(wit,&ch.0[i],&cr.0[i])
    }).collect();
    return Response(resp_v);
}

pub fn verify2<L:Lang>(params: &ProofParams,
                       lang: &L,
                       inst: &L::CoDom,
                       com: &Commitment<L>,
                       ch: &Challenge,
                       resp: &Response<L>) -> bool {
    for i in 0..params.reps {
        if params.range_mode && !lang.check_resp_range(params,&resp.0[i]) { return false; }

        let lhs = lang.resp_lhs(inst, &ch.0[i], &com.0[i]);
        let rhs = lang.eval(&resp.0[i]);

        if lhs != rhs { return false; }
    }
    true
}


////////////////////////////////////////////////////////////////////////////
// Fiat-Shamir variant
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Serialize, Debug)]
pub struct FSProof<L: Lang> {
    fs_com: Commitment<L>,
    fs_resp: Response<L>
}

fn fs_compute_challenge<L: Lang>(lang: &L,
                                 inst:&L::CoDom,
                                 fs_com: &Commitment<L>) -> Challenge {
    use blake2::*;
    let b = fs_com.0.iter().map(|com:&L::CoDom| {
        let x: Vec<u8> = rmp_serde::to_vec(&(com, inst, lang.to_public())).unwrap();
        // Use Digest::digest, but it asks for a fixed-sized slice?
        let mut hasher: Blake2b = Digest::new();
        hasher.update(&x);
        let r0 = hasher.finalize();
        BigInt::from((&(r0.as_slice())[0] & 0b0000001) as u32)
    }).collect();
    Challenge(b)
}

pub fn fs_prove<L:Lang>(params: &ProofParams,
                        lang: &L,
                        inst: &L::CoDom,
                        wit: &L::Dom) -> FSProof<L> {
    let (fs_com,cr) = prove1(params,lang);
    let fs_ch = fs_compute_challenge(lang,inst,&fs_com);
    let fs_resp = prove2(params,lang,wit,&fs_ch,&cr);

    FSProof{ fs_com, fs_resp }
}

pub fn fs_verify<L:Lang>(params: &ProofParams,
                         lang: &L,
                         inst: &L::CoDom,
                         proof: &FSProof<L>) -> bool {
    let fs_ch = fs_compute_challenge(lang,inst,&proof.fs_com);
    verify2(params,lang,inst,&proof.fs_com,&fs_ch,&proof.fs_resp)
}


////////////////////////////////////////////////////////////////////////////
// Tests (Generic)
////////////////////////////////////////////////////////////////////////////


pub fn generic_test_correctness<L: Lang>(params: &ProofParams, lparams: &L::LangParams) {
    let (lang,inst,wit) = L::sample_liw(lparams);

    let (com,cr) = prove1(params,&lang);
    let ch = verify1(params);

    let resp = prove2(params,&lang,&wit,&ch,&cr);
    assert!(verify2(params,&lang,&inst,&com,&ch,&resp));
    assert!(verify2(params,&lang.to_public(),&inst,&com,&ch,&resp));
}

pub fn generic_test_correctness_fs<L: Lang>(params: &ProofParams, lparams: &L::LangParams) {
    let (lang,inst,wit) = L::sample_liw(lparams);

    let proof = fs_prove(params,&lang,&inst,&wit);
    assert!(fs_verify(params,&lang,&inst,&proof));
    assert!(fs_verify(params,&lang.to_public(),&inst,&proof));
}

////////////////////////////////////////////////////////////////////////////
// Trait implementations for our types
////////////////////////////////////////////////////////////////////////////


// #derive is a bit broken for associated types

impl <L:Lang> PartialEq for Commitment<L> { fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) } }
impl <L:Lang> Eq for Commitment<L> {}
impl <L:Lang> PartialEq for ComRand<L> { fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) } }
impl <L:Lang> Eq for ComRand<L> {}
impl <L:Lang> PartialEq for Response<L> { fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) } }
impl <L:Lang> Eq for Response<L> {}

impl <L:Lang> Serialize for Commitment<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>
    { self.0.serialize(serializer) }
}
impl <L:Lang> Serialize for ComRand<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>
    { self.0.serialize(serializer) }
}
impl <L:Lang> Serialize for Response<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>
    { self.0.serialize(serializer) }
}
