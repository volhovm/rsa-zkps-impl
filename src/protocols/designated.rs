use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration, Encrypt, Decrypt, RawCiphertext,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};
use std::fmt;
use std::iter;
use std::time::{SystemTime, UNIX_EPOCH};
use rand::distributions::{Distribution, Uniform};

use super::utils as utils;
use super::schnorr_paillier_batched as spb;
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;


#[derive(Clone, Debug)]
pub struct DVParams {
    pub n_bitlen: usize,
    pub lambda: u32,
    pub crs_uses: u32,
    pub trusted_setup: bool
}

impl DVParams {
    pub fn new(n_bitlen: usize, lambda: u32, crs_uses: u32, trusted_setup: bool) -> DVParams {
        DVParams{n_bitlen, lambda, crs_uses, trusted_setup}
    }
    pub fn vpk_n_bitlen(&self) -> usize {
        // N + 2λ + log λ + 1
        self.n_bitlen + 2 * (self.lambda as usize) +
            ((self.lambda as f64).log2().ceil() as usize) + 1
    }

    pub fn nizk_ct_params(&self) -> spb::ProofParams {
        spb::ProofParams::new(self.n_bitlen,self.lambda,self.lambda,self.lambda)
    }

    pub fn nizk_gcd_params(&self) -> n_gcd::ProofParams {
        n_gcd::ProofParams{n_bitlen: self.n_bitlen,
                           lambda: self.lambda,
                           pmax: 10000}
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
    /// Proof of N' having gcd(N,phi(N)) = 1.
    pub nizk_gcd: n_gcd::Proof,
    /// Proofs of correctness+range of cts.
    pub nizks_ct: Vec<spb::FSProof>,
}


pub fn keygen(params: &DVParams) -> (VPK, VSK) {
    let t_start = SystemTime::now();
    // This can be more effective in terms of move/copy
    // e.g. Inst/Wit could contain references inside?
    let (pk,sk) =
        //Paillier::keypair_with_modulus_size(params.n_bitlen * 2 + 4 * (params.lambda as usize)).keys();
        Paillier::keypair_with_modulus_size(params.vpk_n_bitlen()).keys();

    let ch_range_1 = BigInt::pow(&BigInt::from(2), params.lambda);
    let ch_range_2 = &ch_range_1 * &ch_range_1 * BigInt::from(params.lambda);

    let mut chs: Vec<BigInt> = vec![];
    for _i in 0..params.lambda {
        chs.push(utils::bigint_sample_below_sym(&ch_range_1)); }
    for _i in 0..params.crs_uses {
        chs.push(utils::bigint_sample_below_sym(&ch_range_2)); }

    let rs: Vec<BigInt> =
        (0..(params.lambda + params.crs_uses))
        .map(|_| BigInt::sample_below(&pk.n))
        .collect();

    let cts: Vec<BigInt> =
        chs.iter().zip(rs.iter()).map(|(ch,r)|
            Paillier::encrypt_with_chosen_randomness(
                &pk,
                RawPlaintext::from(ch),
                &Randomness::from(r)).0.into_owned())
        .collect();

    let lang = spb::Lang{pk:pk.clone()};

    let t_p1 = SystemTime::now();
    let nizk_gcd: n_gcd::Proof =
        n_gcd::prove(
            &params.nizk_gcd_params(),
            &n_gcd::Inst{ n: pk.n.clone() },
            &n_gcd::Wit{ p: sk.p.clone(), q: sk.q.clone() }
            );

    let t_p2 = SystemTime::now();
    let mut nizks_ct: Vec<spb::FSProof> = vec![];
    let nizk_batches =
        if params.crs_uses == 0
           { 1 } else { 2 + (params.crs_uses - 1) / params.lambda };
    for i in 0..nizk_batches {
        let batch_from = (i*params.lambda) as usize;
        let batch_to = std::cmp::min((i+1)*params.lambda,
                                     params.lambda + params.crs_uses) as usize;
        println!("Proving batch from {:?} to {:?}", batch_from, batch_to);
        let mut cts_inst = (&cts[batch_from..batch_to]).to_vec();
        let mut ms_wit = (&chs[batch_from..batch_to]).to_vec();
        let mut rs_wit = (&rs[batch_from..batch_to]).to_vec();

        let pad_last_batch = params.crs_uses > 0 && i == nizk_batches - 1;
        if pad_last_batch {
            for _j in 0..(params.lambda - (params.crs_uses % params.lambda)) {
                ms_wit.push(BigInt::from(0));
                rs_wit.push(BigInt::from(1));
                cts_inst.push(Paillier::encrypt_with_chosen_randomness(
                    &pk,
                    RawPlaintext::from(BigInt::from(0)),
                    &Randomness::from(BigInt::from(1))).0.into_owned());
            }
        }

        let inst = spb::Inst{cts: cts_inst};
        let wit = spb::Wit{ms: ms_wit, rs: rs_wit};

        nizks_ct.push(spb::fs_prove(&params.nizk_ct_params(), &lang, &inst, &wit));
    }
    println!("Proving done");
        
    let t_p3 = SystemTime::now();

    let t_delta1 = t_p1.duration_since(t_start).expect("error1");
    let t_delta2 = t_p2.duration_since(t_p1).expect("error2");
    let t_delta3 = t_p3.duration_since(t_p2).expect("error2");
    let t_total = t_p3.duration_since(t_start).expect("error2");
    println!("Keygen prove time (total {:?}): cts: {:?}, nizk_gcd {:?}; nizk_ct: {:?}",t_total, t_delta1, t_delta2, t_delta3);

    (VPK{pk, cts, nizk_gcd, nizks_ct},VSK{sk, chs})
}

pub fn verify_vpk(params: &DVParams, vpk: &VPK) -> bool {

    let t_start = SystemTime::now();

    let res1 = n_gcd::verify(
        &params.nizk_gcd_params(),
        &n_gcd::Inst{ n: vpk.pk.n.clone() },
        &vpk.nizk_gcd);
    if !res1 { return false; }

    let t_p1 = SystemTime::now();

    for i in 0..(vpk.nizks_ct.len() as u32) {
        let batch_from = (i*params.lambda) as usize;
        let batch_to = std::cmp::min((i+1)*params.lambda,
                                     params.lambda + params.crs_uses) as usize;

        let mut cts_w = (&vpk.cts[batch_from..batch_to]).to_vec();

        let pad_last_batch = params.crs_uses > 0 && i == (vpk.nizks_ct.len() as u32) - 1;
        if pad_last_batch {
            for _j in 0..(params.lambda - (params.crs_uses % params.lambda)) {
                cts_w.push(Paillier::encrypt_with_chosen_randomness(
                    &vpk.pk,
                    RawPlaintext::from(BigInt::from(0)),
                    &Randomness::from(BigInt::from(1))).0.into_owned());
            }
        }

        let inst = spb::Lang{ pk: vpk.pk.clone() };
        let wit = spb::Inst{ cts: cts_w };

        let res2 = spb::fs_verify(
            &params.nizk_ct_params(), &inst, &wit,
            &vpk.nizks_ct[i as usize]);
        if !res2 { return false; }

        println!("Verified nizk batch #{:?}", i);
    }

    let t_p2 = SystemTime::now();
    let t_delta1 = t_p1.duration_since(t_start).expect("error1");
    let t_delta2 = t_p2.duration_since(t_p1).expect("error2");
    let t_total = t_p2.duration_since(t_start).expect("error3");
    println!("Keygen verify time (total {:?}): nizk_gcd {:?}; nizk_ct: {:?}", t_total,t_delta1, t_delta2);

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
    // TODO it's broken here
    let rm = BigInt::sample(params.vpk_n_bitlen() +
                            2 * (params.lambda as usize) +
                            ((params.lambda as f64).log2().ceil() as usize));
    let rr = BigInt::sample(params.vpk_n_bitlen());

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

pub fn test_correctness_keygen() {
    let params = DVParams::new(1024, 32, 32, false);
    let (vpk,_vsk) = keygen(&params);
    assert!(verify_vpk(&params,&vpk));
}


#[cfg(test)]
mod tests {

    use crate::protocols::designated::*;

    #[test]
    fn test_correctness_keygen() {
        let params = DVParams::new(1024, 32, 5, false);

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }

//    #[test]
//    fn test_correctness() {
//        let params = DVParams::new(256, 16);
//
//        let (vpk,vsk) = keygen(&params);
//        assert!(verify_vpk(&params,&vpk));
//
//        let (lang,inst,wit) = sample_liw(&params);
//
//        let (com,cr) = prove1(&params,&lang);
//        let ch = verify1(&params);
//
//        let resp = prove2(&vpk,&cr,&wit,&ch);
//        assert!(verify2(&vsk,&lang,&inst,&com,&ch,&resp));
//    }
}
