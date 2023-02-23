use get_size::GetSize;
use get_size_derive::*;
use std::fmt;
use std::fmt::Debug;
use serde::{Serialize, Serializer};

use crate::bigint::*;
use crate::utils as u;

use super::schnorr_generic as sch;

////////////////////////////////////////////////////////////////////////////
// Params
////////////////////////////////////////////////////////////////////////////


// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Security parameter
    pub lambda: u32,
    /// Number of repeats n, equal to the number of instances, usually =lambda
    pub reps_n: u32,
}

impl ProofParams {
    pub fn new(lambda: u32, reps_n: u32 ) -> Self {
        return ProofParams { lambda, reps_n };
    }

    pub fn reps_m(&self) -> u32 { 2 * self.reps_n + 1 }
}

impl fmt::Display for ProofParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ProofParams ( lambda: {}, reps: {} )",
               self.lambda,
               self.reps_n)
    }
}


////////////////////////////////////////////////////////////////////////////
// Language
////////////////////////////////////////////////////////////////////////////

pub trait SchnorrBatchedLang: Serialize + GetSize {
    type LangParams: Clone + Debug;
    type Dom: Serialize + GetSize + Eq + Clone + Debug;
    type CoDom: Serialize + GetSize + Eq + Clone + Debug;

    fn sample_lang(lparams: &Self::LangParams) -> Self;
    fn to_public(&self) -> Self;

    fn sample_wit(&self) -> Self::Dom;

    fn eval(&self, wit: &Self::Dom) -> Self::CoDom;

    fn sample_com_rand(&self, params: &ProofParams) -> Self::Dom;
    fn compute_resp(&self,
                    params: &ProofParams,
                    wit: &Vec<Self::Dom>,
                    e_mat_i: &Vec<BigInt>,
                    rand: &Self::Dom) -> Self::Dom;

    fn resp_lhs(&self, params: &ProofParams, inst: &Vec<Self::CoDom>, e_mat_i: &Vec<BigInt>, com: &Self::CoDom) -> Self::CoDom;

    fn check_resp_range(&self, params: &ProofParams, resp: &Self::Dom) -> bool;

    fn sample_liw(params: &ProofParams,
                  lparams: &Self::LangParams) -> (Self,Vec<Self::CoDom>,Vec<Self::Dom>) where Self: Sized {
        let lang = Self::sample_lang(lparams);

        let mut insts:Vec<Self::CoDom> = vec![];
        let mut wits:Vec<Self::Dom> = vec![];
        for _i in 0..params.reps_n as usize {
            let wit = lang.sample_wit();
            let inst = lang.eval(&wit);
            insts.push(inst);
            wits.push(wit);
        }

        (lang,insts,wits)
    }
}

////////////////////////////////////////////////////////////////////////////
// Protocol
////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Debug)]
pub struct Commitment<L:SchnorrBatchedLang>(Vec<L::CoDom>);

#[derive(Clone, Debug)]
pub struct ComRand<L:SchnorrBatchedLang>(Vec<L::Dom>);

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Challenge(pub BigInt);

#[derive(Clone, Debug)]
pub struct Response<L:SchnorrBatchedLang>(Vec<L::Dom>);

pub fn prove1<L:SchnorrBatchedLang>(params: &ProofParams, lang: &L) -> (Commitment<L>,ComRand<L>) {
    let mut rand_v = vec![];
    let mut com_v = vec![];
    for _i in 0..params.reps_m() {
        let wit = lang.sample_com_rand(params);
        let inst = lang.eval(&wit);
        rand_v.push(wit);
        com_v.push(inst);
    }
    return (Commitment(com_v),ComRand(rand_v));
}

pub fn verify1(params: &ProofParams) -> Challenge {
    let b = BigInt::sample(params.reps_n as usize);
    return Challenge(b);
}

fn challenge_e_mat(reps_m: usize, reps_n: usize, e: &BigInt) -> Vec<Vec<BigInt>> {
    let mut e_mat: Vec<Vec<BigInt>> =
        vec![vec![BigInt::from(0);reps_n];reps_m];
    for i in 0..reps_m {
        for j in 0..reps_n {
            if (i < reps_n && j <= i) ||
               (i >= reps_n && j >= i - reps_n) {
                e_mat[i][j] = BigInt::from(e.test_bit(reps_n - 1 + i - j) as u32);
            }
        }
    }
    e_mat
}

pub fn prove2<L:SchnorrBatchedLang>(params: &ProofParams,
                                    lang: &L,
                                    wit: &Vec<L::Dom>,
                                    ch: &Challenge,
                                    cr: &ComRand<L>) -> Response<L> {
    let e_mat = challenge_e_mat(params.reps_m() as usize,
                                params.reps_n as usize,
                                &ch.0);

    let resp_v: Vec<_> = (0..params.reps_m() as usize).map(|i| {
        lang.compute_resp(params,wit,&e_mat[i],&cr.0[i])
    }).collect();

    Response(resp_v)
}

pub fn verify2<L:SchnorrBatchedLang>(params: &ProofParams,
                                     lang: &L,
                                     inst: &Vec<L::CoDom>,
                                     com: &Commitment<L>,
                                     ch: &Challenge,
                                     resp: &Response<L>) -> bool {
    let e_mat = challenge_e_mat(params.reps_m() as usize,
                                params.reps_n as usize,
                                &ch.0);

    for i in 0..params.reps_m() as usize {
        if !lang.check_resp_range(params,&resp.0[i]) { return false; }

        let lhs = lang.resp_lhs(params, inst, &e_mat[i], &com.0[i]);
        let rhs = lang.eval(&resp.0[i]);

        if lhs != rhs { return false; }
    }
    true
}

////////////////////////////////////////////////////////////////////////////
// Fiat-Shamir variant
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Serialize, GetSize, Debug)]
pub struct FSProof<L: SchnorrBatchedLang> {
    fs_com: Commitment<L>,
    fs_resp: Response<L>
}

fn fs_compute_challenge<L: SchnorrBatchedLang>(
    params: &ProofParams,
    lang: &L,
    inst:&Vec<L::CoDom>,
    fs_com: &Commitment<L>) -> Challenge
{
    use blake2::*;
    let x: Vec<u8> = rmp_serde::to_vec(&(fs_com, inst, lang.to_public())).unwrap();
    // Use Digest::digest, but it asks for a fixed-sized slice?
    let mut hasher: Blake2b = Digest::new();
    hasher.update(&x);
    let r0 = hasher.finalize();
    let b = u::extract_bits(&r0.as_slice(),params.reps_n as usize);
    Challenge(b)
}

pub fn fs_prove<L:SchnorrBatchedLang>(
    params: &ProofParams,
    lang: &L,
    inst: &Vec<L::CoDom>,
    wit: &Vec<L::Dom>) -> FSProof<L>
{
    let (fs_com,cr) = prove1(params,lang);
    let fs_ch = fs_compute_challenge(params,lang,inst,&fs_com);
    let fs_resp = prove2(params,lang,wit,&fs_ch,&cr);

    FSProof{ fs_com, fs_resp }
}

pub fn fs_verify<L:SchnorrBatchedLang>(params: &ProofParams,
                         lang: &L,
                         inst: &Vec<L::CoDom>,
                         proof: &FSProof<L>) -> bool {
    let fs_ch = fs_compute_challenge(params,lang,inst,&proof.fs_com);
    verify2(params,lang,inst,&proof.fs_com,&fs_ch,&proof.fs_resp)
}



////////////////////////////////////////////////////////////////////////////
// Tests (Generic)
////////////////////////////////////////////////////////////////////////////


pub fn generic_test_correctness<L: SchnorrBatchedLang>(params: &ProofParams, lparams: &L::LangParams) {
    let (lang,inst,wit) = L::sample_liw(params,lparams);

    let (com,cr) = prove1(params,&lang);
    let ch = verify1(params);

    let resp = prove2(params,&lang,&wit,&ch,&cr);
    assert!(verify2(params,&lang,&inst,&com,&ch,&resp));
    assert!(verify2(params,&lang.to_public(),&inst,&com,&ch,&resp));
}

pub fn generic_test_correctness_fs<L: SchnorrBatchedLang>(params: &ProofParams, lparams: &L::LangParams) {
    let (lang,inst,wit) = L::sample_liw(params,lparams);

    let proof = fs_prove(params,&lang,&inst,&wit);
    assert!(fs_verify(params,&lang,&inst,&proof));
    assert!(fs_verify(params,&lang.to_public(),&inst,&proof));
}

////////////////////////////////////////////////////////////////////////////
// Trait implementations for our types
////////////////////////////////////////////////////////////////////////////


// #derive is a bit broken for associated types

impl <L:SchnorrBatchedLang> PartialEq for Commitment<L> { fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) } }
impl <L:SchnorrBatchedLang> Eq for Commitment<L> {}
impl <L:SchnorrBatchedLang> PartialEq for ComRand<L> { fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) } }
impl <L:SchnorrBatchedLang> Eq for ComRand<L> {}
impl <L:SchnorrBatchedLang> PartialEq for Response<L> { fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) } }
impl <L:SchnorrBatchedLang> Eq for Response<L> {}

impl <L:SchnorrBatchedLang> Serialize for Commitment<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>
    { self.0.serialize(serializer) }
}
impl <L:SchnorrBatchedLang> Serialize for ComRand<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>
    { self.0.serialize(serializer) }
}
impl <L:SchnorrBatchedLang> Serialize for Response<L> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error>
    { self.0.serialize(serializer) }
}

impl <L:SchnorrBatchedLang> GetSize for Commitment<L> {
    fn get_stack_size() -> usize { panic!("I don't know how to implement this"); }
    fn get_heap_size(&self) -> usize { self.0.get_heap_size() }
    fn get_size(&self) -> usize { self.0.get_size() }
}

impl <L:SchnorrBatchedLang> GetSize for ComRand<L> {
    fn get_stack_size() -> usize { panic!("I don't know how to implement this"); }
    fn get_heap_size(&self) -> usize { self.0.get_heap_size() }
    fn get_size(&self) -> usize { self.0.get_size() }
}

impl <L:SchnorrBatchedLang> GetSize for Response<L> {
    fn get_stack_size() -> usize { panic!("I don't know how to implement this"); }
    fn get_heap_size(&self) -> usize { self.0.get_heap_size() }
    fn get_size(&self) -> usize { self.0.get_size() }
}

impl GetSize for Challenge {
    fn get_stack_size() -> usize { panic!("I don't know how to implement this"); }
    fn get_heap_size(&self) -> usize { self.0.get_heap_size() }
    fn get_size(&self) -> usize { self.0.get_size() }
}
