use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration, Encrypt, Decrypt, RawCiphertext,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};
use std::fmt;
use std::iter;
use rand::distributions::{Distribution, Uniform};

use super::schnorr_paillier as sp;
use super::paillier_elgamal as pe;


#[derive(Clone, Debug)]
pub struct DVParams {
    pub n_bitlen: usize,
    pub lambda: u32,
    pub nizk_params: sp::ProofParams
}

impl DVParams {
    pub fn new(n_bitlen: usize, lambda: u32) -> DVParams {
        let two_lambda = BigInt::pow(&BigInt::from(2), lambda);
        let nizk_params = sp::ProofParams::new_range(n_bitlen,lambda,two_lambda.clone());
        DVParams{n_bitlen, lambda, nizk_params}
    }
}

#[derive(Clone, Debug)]
pub struct VSK {
    /// Verifier's Paillier secret key
    pub sk: DecryptionKey,
    /// Original challenge values
    pub chs: Vec<BigInt>
}

#[derive(Clone, Debug)]
pub struct VPK {
    /// Verifier's Paillier public key
    pub pk: EncryptionKey,
    /// Challenges, encrypted under Verifier's key
    pub cts: Vec<BigInt>,
    /// Proofs of correctness+range of cts
    pub nizks: Vec<sp::FSProof>
}


pub fn keygen(params: &DVParams) -> (VPK, VSK) {
    // This can be more effective in terms of move/copy
    // e.g. Inst/Wit could contain references inside?
    let (pk,sk) =
        Paillier::keypair_with_modulus_size(params.n_bitlen * 2 + 4 * (params.lambda as usize)).keys();

    let chs: Vec<BigInt> =
        (0..2*params.lambda)
        .map(|_| BigInt::sample(params.lambda as usize))
        .collect();

    let cts_rs: Vec<(BigInt,BigInt)> =
        chs.iter().map( |ch| {
            let r = BigInt::sample_below(&pk.n);
            let ct = Paillier::encrypt_with_chosen_randomness(
                &pk,
                RawPlaintext::from(ch),
                &Randomness::from(&r)).0.into_owned();
            (r, ct)
        }).collect();

    let lang = sp::Lang{pk:pk.clone()};
    let nizks:Vec<sp::FSProof> =
        chs.iter().zip(cts_rs.iter()).map(|(m,(r,ct))| {
            sp::fs_prove(&params.nizk_params,
                         &lang,
                         &(sp::Inst{ct:ct.clone()}),
                         &(sp::Wit{m:m.clone(),r:r.clone()}))
        }).collect();

    // Ciphertexts only
    let cts: Vec<BigInt> = cts_rs.iter().map(|x| x.1.clone()).collect();

    (VPK{pk,cts,nizks},VSK{sk, chs})
}

pub fn verify_vpk(params: &DVParams, vpk: &VPK) -> bool {
    let lang = sp::Lang{ pk: vpk.pk.clone() };
    let (res0,precomp) = sp::fs_verify0(&params.nizk_params, &lang);
    if !res0 { return false; };

    for (ct,nizk) in vpk.cts.iter().zip(vpk.nizks.iter()) {
        let res = sp::fs_verify(&params.nizk_params,
                                &lang,
                                &(sp::Inst{ct:ct.clone()}),
                                &precomp,
                                &nizk);
        if !res { return false; }
    }

    return true;
}


#[derive(Clone, Debug)]
pub struct Commitment(Vec<BigInt>);

#[derive(Clone, Debug)]
pub struct ComRand(Vec<(BigInt,BigInt)>);

#[derive(Clone, Debug)]
pub struct Challenge(Vec<BigInt>);

#[derive(Clone, Debug)]
pub struct Response(Vec<(BigInt,BigInt)>);


#[derive(Clone, Debug)]
pub struct DVLang { pub pk: pe::PEPublicKey }
#[derive(Clone, Debug)]
pub struct DVInst { pub ct: pe::PECiphertext }
#[derive(Clone, Debug)]
pub struct DVWit { pub m: BigInt, pub r: BigInt }

pub fn sample_lang(params: &DVParams) -> DVLang {
    let (pk,_sk) = pe::keygen(params.n_bitlen);
    DVLang{pk}
}

pub fn sample_inst(lang: &DVLang) -> (DVInst,DVWit) {
//    let m = BigInt::from(5);
//    let r = BigInt::from(10);
    let m = BigInt::sample_below(&lang.pk.n);
    let r = BigInt::sample_below(&lang.pk.n2);
    let ct = pe::encrypt_with_randomness(&lang.pk,&m,&r);
    (DVInst{ct}, DVWit{m, r})
}

pub fn sample_liw(params: &DVParams) -> (DVLang,DVInst,DVWit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(&lang);
    (lang,inst,wit)
}



#[derive(Clone, Debug)]
pub struct DVCom{ pub a: pe::PECiphertext }

#[derive(Clone, Debug)]
pub struct DVComRand{ pub rr: BigInt, pub rm: BigInt }

#[derive(Clone, Debug)]
pub struct DVChallenge(Vec<usize>);

#[derive(Clone, Debug)]
pub struct DVResp{ pub s_m: BigInt, pub s_r: BigInt }


pub fn prove1(params: &DVParams, lang: &DVLang) -> (DVCom,DVComRand) {
    let rm = BigInt::sample(params.n_bitlen + 3 * (params.lambda as usize));
    let rr = BigInt::sample(2 * params.n_bitlen + 3 * (params.lambda as usize));

    let a = pe::encrypt_with_randomness(&lang.pk,&rm,&rr);

    (DVCom{a}, DVComRand{rr, rm})
}

pub fn verify1(params: &DVParams) -> DVChallenge {
    let mut rng = rand::thread_rng();
    let gen = Uniform::from(0..(2 * (params.lambda as usize)));

    // There is a better way to do it.
    use std::collections::HashSet;
    let mut ix: HashSet<usize> = HashSet::new();

    while ix.len() < params.lambda as usize {
        let i = gen.sample(&mut rng);
        if !ix.contains(&i) { ix.insert(i); }
    }

    DVChallenge(ix.into_iter().collect())
}

pub fn prove2(vpk: &VPK,
               cr: &DVComRand,
               wit: &DVWit,
               ch: &DVChallenge) -> DVResp {
    let n2: &BigInt = &vpk.pk.nn;

    let ct =
        ch.0.iter()
        .map(|&i| &vpk.cts[i])
        .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, n2));

    let rr_ct = Paillier::encrypt(&vpk.pk,RawPlaintext::from(&cr.rr)).0.into_owned();
    let s_r = BigInt::mod_mul(&BigInt::mod_pow(&ct, &wit.r, n2),
                             &rr_ct,
                             n2);

    let rm_ct = Paillier::encrypt(&vpk.pk,RawPlaintext::from(&cr.rm)).0.into_owned();
    let s_m = BigInt::mod_mul(&BigInt::mod_pow(&ct, &wit.m, n2),
                             &rm_ct,
                             n2);

    DVResp{s_m,s_r}
}

pub fn verify2(vsk: &VSK,
               lang: &DVLang,
               inst: &DVInst,
               com: &DVCom,
               ch: &DVChallenge,
               resp: &DVResp) -> bool {
    let ch_raw: BigInt =
        ch.0.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );

    let s_r = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.s_r)).0.into_owned();
    let s_m = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.s_m)).0.into_owned();

    let pe::PECiphertext{ct1:x1,ct2:x2} =
        pe::encrypt_with_randomness(&lang.pk, &s_m, &s_r);

    let tmp1 =
        BigInt::mod_mul(
            &BigInt::mod_pow(&inst.ct.ct1, &ch_raw, &lang.pk.n2),
            &com.a.ct1,
            &lang.pk.n2);
    if tmp1 != x1 { return false; }

    let tmp2 =
        BigInt::mod_mul(
            &BigInt::mod_pow(&inst.ct.ct2, &ch_raw, &lang.pk.n2),
            &com.a.ct2,
            &lang.pk.n2);

    if tmp2 != x2 { return false; }

    true
}


#[cfg(test)]
mod tests {

    use crate::protocols::designated::*;

//    #[test]
//    fn test_correctness_keygen() {
//        let params = DVParams::new(1024, 32);
//
//        let (vpk,_vsk) = keygen(&params);
//        assert!(verify_vpk(&params,&vpk));
//    }

    #[test]
    fn test_correctness() {
        let params = DVParams::new(256, 16);

        let (vpk,vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));

        let (lang,inst,wit) = sample_liw(&params);

        let (com,cr) = prove1(&params,&lang);
        let ch = verify1(&params);

        let resp = prove2(&vpk,&cr,&wit,&ch);
        assert!(verify2(&vsk,&lang,&inst,&com,&ch,&resp));
    }
}