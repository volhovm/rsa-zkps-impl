/// The main DV (designated verifier) protocol, which proves knowledge
/// of plaintext for the Paillier-Elgamal encryption scheme (see
/// `super::paillier_elgamal`), assuming its modulus can be subverted.

use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation,Converter};
use curv::{BigInt};
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration, Encrypt, Decrypt, RawCiphertext,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};
use std::fmt;
use std::iter;
use std::time::{SystemTime, UNIX_EPOCH};
use serde::{Serialize};
use rand::distributions::{Distribution, Uniform};

use super::paillier::paillier_enc_opt;
use super::utils as u;
use super::schnorr_paillier_batched as spb;
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;


////////////////////////////////////////////////////////////////////////////
// Params
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug)]
pub struct DVParams {
    /// N of the prover (of the homomorphism psi), bit length
    pub psi_n_bitlen: u32,
    /// Security parameter
    pub lambda: u32,
    /// The number of CRS reuses
    pub crs_uses: u32,
    /// Whether malicious setup (that introduces VPK proofs) is enabled
    pub malicious_setup: bool,
    /// Whether the GGM mode is enabled, which omits certain proof parts
    pub ggm_mode: bool,
}

impl DVParams {
    pub fn new(psi_n_bitlen: u32,
               lambda: u32,
               crs_uses: u32,
               malicious_setup: bool,
               ggm_mode: bool) -> DVParams {
        DVParams{psi_n_bitlen, lambda, crs_uses, malicious_setup, ggm_mode}
    }

    /// Range slack of the batched range proof.
    pub fn range_slack_bitlen(&self) -> u32 {
        2 * self.lambda + u::log2ceil(self.lambda) - 1
    }

    /// The size of honestly generated challenges (first λ).
    fn ch_small_bitlen(&self) -> u32 { self.lambda }

    /// The size of honestly generated challenges (λ+1 ... λ+Q) for Q number of queries.
    fn ch_big_bitlen(&self) -> u32 { 2 * self.lambda + u::log2ceil(self.lambda) }

    /// Maximum size of the summed-up challenge, real.
    pub fn max_ch_bitlen(&self) -> u32 {
        if self.crs_uses == 0 {
            self.lambda + u::log2ceil(self.lambda)
        } else {
            2 * self.lambda + u::log2ceil(self.lambda)
        }
    }

    /// Maximum size of the summed-up challenge
    pub fn max_ch_proven_bitlen(&self) -> u32 {
        let slack = if self.malicious_setup { self.range_slack_bitlen() } else { 0 };
        if self.crs_uses == 0 {
            // sum of lambda (small challenges with slack)
            (self.ch_small_bitlen() + slack)
                + u::log2ceil(self.lambda)
        } else {
            // a single big challenge with slack
            self.ch_big_bitlen() + slack + 1
        }
    }

    pub fn rand_m_bitlen(&self) -> u32 {
        // r should be lambda bits more than c * w, where c is maximum
        // sum-challenge according to what is known (in the trusted
        // case) or proven by the batched protocol (in the malicious
        // setup case).
        self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda
    }

    pub fn rand_r_bitlen(&self) -> u32 {
        self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda
        //2 * self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda
    }

    // M should be bigger than r + cw, but r should hide cw perfectly;
    // so cw is always negligibly smaller than r. We could just take M
    // to be n and achieve statistical completeness in this respect,
    // but adding one extra bit will give us perfect completeness,
    // because now r + cw < 2 r.
    pub fn vpk_n_bitlen(&self) -> u32 {
        // It should be max(x,y)
        // + 1, not +2. Maybe this has to do with the symmetric range.
        // But the difference does not affect the performance anyway.
        std::cmp::max(self.rand_m_bitlen(),self.rand_r_bitlen()) + 2
    }

    /// Params for the first batch, for challenges of lambda bits.
    pub fn nizk_ct_params_1(&self) -> spb::ProofParams {
        spb::ProofParams::new(self.vpk_n_bitlen(),
                              self.lambda,
                              self.lambda,
                              self.lambda)
    }

    /// Params for the second+ batches, for challenges of 2 * lambda +
    /// log lambda bits.
    pub fn nizk_ct_params_2(&self) -> spb::ProofParams {
        spb::ProofParams::new(self.vpk_n_bitlen(),
                              self.lambda,
                              self.lambda,
                              2 * self.lambda + u::log2ceil(self.lambda))
    }

    /// Parameters for the GCD NIZK proof.
    pub fn nizk_gcd_params(&self) -> n_gcd::ProofParams {
        n_gcd::ProofParams{ n_bitlen: self.psi_n_bitlen as usize,
                            lambda: self.lambda,
                            pmax: 10000 }
    }
}


////////////////////////////////////////////////////////////////////////////
// Keygen
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct VSK {
    /// Verifier's Paillier secret key
    pub sk: DecryptionKey,
    /// Original challenge values
    pub chs: Vec<BigInt>
}

#[derive(Clone, Debug, Serialize)]
pub struct VPK {
    /// Verifier's Paillier public key
    pub pk: EncryptionKey,
    /// Challenges, encrypted under Verifier's key
    pub cts: Vec<BigInt>,
    /// Proof of N = pk.n having gcd(N,phi(N)) = 1.
    pub nizk_gcd: Option<n_gcd::Proof>,
    /// Proofs of correctness+range of cts.
    pub nizks_ct: Option<Vec<spb::FSProof>>,
}


pub fn keygen(params: &DVParams) -> (VPK, VSK) {
    //let t_start = SystemTime::now();

    // This can be more effective in terms of move/copy
    // e.g. Inst/Wit could contain references inside?
    let (pk,sk) =
        Paillier::keypair_with_modulus_size(params.vpk_n_bitlen() as usize).keys();

    let ch_range_1 = BigInt::pow(&BigInt::from(2), params.ch_small_bitlen());
    let ch_range_2 = BigInt::pow(&BigInt::from(2), params.ch_big_bitlen());
    let mut chs: Vec<BigInt> = vec![];
    for _i in 0..params.lambda {
        chs.push(u::bigint_sample_below_sym(&ch_range_1)); }
    for _i in 0..params.crs_uses {
        chs.push(u::bigint_sample_below_sym(&ch_range_2)); }

    let rs: Vec<BigInt> =
        (0..(params.lambda + params.crs_uses))
        .map(|_| BigInt::sample_below(&pk.n))
        .collect();

    let cts: Vec<BigInt> =
        chs.iter().zip(rs.iter())
        .map(|(ch,r)| paillier_enc_opt(&pk,Some(&sk),ch,r))
        .collect();

    let (nizk_gcd,nizks_ct) = if !params.malicious_setup {
        (None,None)
    } else {
        
        //let t_p1 = SystemTime::now();
        let nizk_gcd: n_gcd::Proof =
            n_gcd::prove(
                &params.nizk_gcd_params(),
                &n_gcd::Inst{ n: pk.n.clone() },
                &n_gcd::Wit{ p: sk.p.clone(), q: sk.q.clone() }
            );
        
        //let t_p2 = SystemTime::now();
        let mut nizks_ct: Vec<spb::FSProof> = vec![];
        let nizk_batches =
            if params.crs_uses == 0 { 1 }
        else { 2 + (params.crs_uses - 1) / params.lambda };
        
        let lang = spb::Lang{pk:pk.clone(), sk: Some(sk.clone())};
        
        for i in 0..nizk_batches {
            let batch_from = (i*params.lambda) as usize;
            let batch_to = std::cmp::min((i+1)*params.lambda,
                                         params.lambda + params.crs_uses) as usize;
            let mut cts_inst = (&cts[batch_from..batch_to]).to_vec();
            let mut ms_wit = (&chs[batch_from..batch_to]).to_vec();
            let mut rs_wit = (&rs[batch_from..batch_to]).to_vec();
            
            let pad_last_batch = params.crs_uses > 0 && i == nizk_batches - 1;
            if pad_last_batch {
                for _j in 0..(params.lambda - (params.crs_uses % params.lambda)) {
                    ms_wit.push(BigInt::from(0));
                    rs_wit.push(BigInt::from(1));
                    cts_inst.push(paillier_enc_opt(&pk,Some(&sk),
                                                   &BigInt::from(0),
                                                   &BigInt::from(1)));
                }
            }
            
            let params = if i == 0 { params.nizk_ct_params_1() }
            else { params.nizk_ct_params_2() };
            let inst = spb::Inst{cts: cts_inst};
            let wit = spb::Wit{ms: ms_wit, rs: rs_wit};
            
            nizks_ct.push(spb::fs_prove(&params, &lang, &inst, &wit));
        }

        (Some(nizk_gcd), Some(nizks_ct))
    };

    //let t_p3 = SystemTime::now();

    //let _t_delta1 = t_p1.duration_since(t_start).expect("error1");
    //let _t_delta2 = t_p2.duration_since(t_p1).expect("error2");
    //let _t_delta3 = t_p3.duration_since(t_p2).expect("error2");
    //let _t_total = t_p3.duration_since(t_start).expect("error2");
    //println!("Keygen prove time (total {:?}): cts: {:?}, nizk_gcd {:?}; nizk_ct: {:?}",t_total, t_delta1, t_delta2, t_delta3);

    (VPK{pk, cts, nizk_gcd, nizks_ct},VSK{sk, chs})
}

pub fn verify_vpk(params: &DVParams, vpk: &VPK) -> bool {

    if !params.malicious_setup {
        return true
    }

    let t_start = SystemTime::now();

    let res1 = n_gcd::verify(
        &params.nizk_gcd_params(),
        &n_gcd::Inst{ n: vpk.pk.n.clone() },
        vpk.nizk_gcd.as_ref().expect("dv#verify_vpk: no nizk_gcd"));
    if !res1 { return false; }

    let t_p1 = SystemTime::now();

    let nizks_ct = vpk.nizks_ct.as_ref().expect("dv#verify_vpk: no nizk_gcd");
    for i in 0..(nizks_ct.len() as u32) {
        let batch_from = (i*params.lambda) as usize;
        let batch_to = std::cmp::min((i+1)*params.lambda,
                                     params.lambda + params.crs_uses) as usize;

        let mut cts_w = (&vpk.cts[batch_from..batch_to]).to_vec();

        let pad_last_batch = params.crs_uses > 0 && i == (nizks_ct.len() as u32) - 1;
        if pad_last_batch {
            for _j in 0..(params.lambda - (params.crs_uses % params.lambda)) {
                cts_w.push(
                    paillier_enc_opt(&vpk.pk, None, &BigInt::from(0), &BigInt::from(1)));
            }
        }

        let params =
            if i == 0 { params.nizk_ct_params_1() }
            else { params.nizk_ct_params_2() };
        let inst = spb::Lang{ pk: vpk.pk.clone(), sk: None };
        let wit = spb::Inst{ cts: cts_w };

        let res2 = spb::fs_verify(&params, &inst, &wit, &nizks_ct[i as usize]);
        if !res2 { return false; }
    }

    let t_p2 = SystemTime::now();
    let _t_delta1 = t_p1.duration_since(t_start).expect("error1");
    let _t_delta2 = t_p2.duration_since(t_p1).expect("error2");
    let _t_total = t_p2.duration_since(t_start).expect("error3");
    //println!("Keygen verify time (total {:?}): nizk_gcd {:?}; nizk_ct: {:?}", t_total,t_delta1, t_delta2);

    return true;
}


////////////////////////////////////////////////////////////////////////////
// Language
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct DVLang {
    pub pk: pe::PEPublicKey,
    pub sk: Option<pe::PESecretKey>
}

#[derive(Clone, Debug, Serialize)]
pub struct DVInst {
    pub ct: pe::PECiphertext
}

#[derive(Clone, Debug)]
pub struct DVWit {
    pub m: BigInt,
    pub r: BigInt,
}


pub fn sample_lang(params: &DVParams) -> DVLang {
    let (pk,sk) = pe::keygen(params.psi_n_bitlen as usize);
    DVLang{pk,sk:Some(sk)}
}

pub fn sample_inst(lang: &DVLang) -> (DVInst,DVWit) {
    let m = BigInt::sample_below(&lang.pk.n);
    let r = BigInt::sample_below(&lang.pk.n);
    let ct = pe::encrypt_with_randomness_opt(&lang.pk,lang.sk.as_ref(),&m,&r);
    (DVInst{ct}, DVWit{m, r})
}

pub fn sample_liw(params: &DVParams) -> (DVLang,DVInst,DVWit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(&lang);
    (lang,inst,wit)
}


////////////////////////////////////////////////////////////////////////////
// Interactive part
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct DVCom{ pub a: pe::PECiphertext }

#[derive(Clone, Debug, Serialize)]
pub struct DVComRand {
    pub rm_m: BigInt,
    pub rm_r: BigInt,
    pub rr_m: BigInt,
    pub rr_r: BigInt,
    pub tm1: Option<BigInt>,
    pub tm2: Option<BigInt>,
    pub tm3: Option<BigInt>,
    pub tr1: Option<BigInt>,
    pub tr2: Option<BigInt>,
    pub tr3: Option<BigInt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVChallenge1(BigInt);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DVChallenge2(BigInt);

#[derive(Clone, Debug, Serialize)]
pub struct DVResp1 {
    pub sm: BigInt,
    pub sr: BigInt,
    pub tm: Option<BigInt>,
    pub tr: Option<BigInt>,
}

#[derive(Clone, Debug, Serialize)]
pub struct DVResp2 {
    pub um1: BigInt,
    pub um2: BigInt,
    pub um3: BigInt,
    pub ur1: BigInt,
    pub ur2: BigInt,
    pub ur3: BigInt,
}


pub fn prove1(params: &DVParams, lang: &DVLang) -> (DVCom,DVComRand) {
    let rm_m = BigInt::sample(params.rand_m_bitlen() as usize);
    let rm_r = BigInt::sample(params.vpk_n_bitlen() as usize);

    let rr_m = BigInt::sample(params.rand_r_bitlen() as usize);
    let rr_r = BigInt::sample(params.vpk_n_bitlen() as usize);

    let a = pe::encrypt_with_randomness_opt(&lang.pk,lang.sk.as_ref(),&rm_m,&rr_m);

    if params.ggm_mode {
        (DVCom{a}, DVComRand{rm_m, rm_r, rr_m, rr_r,
                             tm1: None, tm2: None, tm3: None,
                             tr1: None, tr2: None, tr3: None})
    } else {
        let tm1 = BigInt::sample(params.vpk_n_bitlen() as usize);
        let tm2 = BigInt::sample(params.vpk_n_bitlen() as usize);
        let tm3 = BigInt::sample(params.vpk_n_bitlen() as usize);

        let tr1 = BigInt::sample(params.vpk_n_bitlen() as usize);
        let tr2 = BigInt::sample(params.vpk_n_bitlen() as usize);
        let tr3 = BigInt::sample(params.vpk_n_bitlen() as usize);


        (DVCom{a}, DVComRand{rm_m, rm_r, rr_m, rr_r,
                             tm1: Some(tm1), tm2: Some(tm2), tm3: Some(tm3),
                             tr1: Some(tr1), tr2: Some(tr2), tr3: Some(tr3)})
    }
}

pub fn verify1(params: &DVParams) -> DVChallenge1 {
    let b = BigInt::sample(params.lambda as usize);
    DVChallenge1(b)
}

pub fn prove2(params: &DVParams,
              vpk: &VPK,
              cr: &DVComRand,
              wit: &DVWit,
              ch1: &DVChallenge1,
              query_ix: usize) -> DVResp1 {
    let n2: &BigInt = &vpk.pk.nn;

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, n2)),
                        n2);

    let sm_ct = paillier_enc_opt(&vpk.pk, None, &cr.rm_m, &cr.rm_r);
    let sm = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, &wit.m, n2),
                             &sm_ct,
                             n2);

    let sr_ct = paillier_enc_opt(&vpk.pk, None, &cr.rr_m, &cr.rr_r);
    let sr = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, &wit.r, n2),
                             &sr_ct,
                             n2);

    if params.ggm_mode {
        DVResp1{sm, sr, tm: None, tr: None}
    } else {
        let tm1 = cr.tm1.as_ref().expect("designated#prove2: tm1 must be Some");
        let tm2 = cr.tm2.as_ref().expect("designated#prove2: tm2 must be Some");
        let tm3 = cr.tm3.as_ref().expect("designated#prove2: tm3 must be Some");
        let tr1 = cr.tr1.as_ref().expect("designated#prove2: tr1 must be Some");
        let tr2 = cr.tr2.as_ref().expect("designated#prove2: tr2 must be Some");
        let tr3 = cr.tr3.as_ref().expect("designated#prove2: tr3 must be Some");

        let tm_ct = paillier_enc_opt(&vpk.pk, None, tm2, tm3);
        let tm = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, tm1, n2),
                                 &tm_ct,
                                 n2);

        let tr_ct = paillier_enc_opt(&vpk.pk, None, tr2, tr3);
        let tr = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, tr1, n2),
                                 &tr_ct,
                                 n2);

        DVResp1{sm, sr, tm: Some(tm), tr: Some(tr)}
    }
}

pub fn verify2(params: &DVParams) -> Option<DVChallenge2> {
    if params.ggm_mode {
        None
    } else{
        let d = BigInt::sample(params.lambda as usize);
        Some(DVChallenge2(d))
    }
}

pub fn prove3(params: &DVParams,
              vpk: &VPK,
              cr: &DVComRand,
              wit: &DVWit,
              ch2_opt: Option<&DVChallenge2>) -> Option<DVResp2> {
    if params.ggm_mode {
        None
    } else {

        let n2: &BigInt = &vpk.pk.nn;

        let ch2 = ch2_opt.expect("designated#prove3: ch2 must be Some");
        let d: &BigInt = &ch2.0;

        let tm1 = cr.tm1.as_ref().expect("designated#prove3: tm1 must be Some");
        let tm2 = cr.tm2.as_ref().expect("designated#prove3: tm2 must be Some");
        let tm3 = cr.tm3.as_ref().expect("designated#prove3: tm3 must be Some");
        let tr1 = cr.tr1.as_ref().expect("designated#prove3: tr1 must be Some");
        let tr2 = cr.tr2.as_ref().expect("designated#prove3: tr2 must be Some");
        let tr3 = cr.tr3.as_ref().expect("designated#prove3: tr3 must be Some");

        let um1 = BigInt::mod_add(&BigInt::mod_mul(&wit.m, d, n2), tm1, n2);
        let um2 = BigInt::mod_add(&BigInt::mod_mul(&cr.rm_m, d, n2), tm2, n2);
        let um3 = BigInt::mod_mul(&BigInt::mod_pow(&cr.rm_r, d, n2), tm3, n2);

        let ur1 = BigInt::mod_add(&BigInt::mod_mul(&wit.r, d, n2), tr1, n2);
        let ur2 = BigInt::mod_add(&BigInt::mod_mul(&cr.rr_m, d, n2), tr2, n2);
        let ur3 = BigInt::mod_mul(&BigInt::mod_pow(&cr.rr_r, d, n2), tr3, n2);

        Some(DVResp2{um1, um2, um3, ur1, ur2, ur3})
    }
}

pub fn verify3(params: &DVParams,
               vsk: &VSK,
               vpk: &VPK,
               lang: &DVLang,
               inst: &DVInst,
               com: &DVCom,
               ch1: &DVChallenge1,
               ch2_opt: Option<&DVChallenge2>,
               resp1: &DVResp1,
               resp2_opt: Option<&DVResp2>,
               query_ix: usize) -> bool {

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let ch1_raw: BigInt =
        &vsk.chs[(params.lambda as usize) + query_ix] +
        ch1_active_bits.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );

    let sr = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp1.sr)).0.into_owned();
    let sm = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp1.sm)).0.into_owned();

    // a Y^c = Enc_psi(s_m,s_r)
    {
        let pe::PECiphertext{ct1:x1,ct2:x2} =
            pe::encrypt_with_randomness_opt(&lang.pk, None, &sm, &sr);

        let tmp1 =
            BigInt::mod_mul(
                &u::bigint_mod_pow(&inst.ct.ct1, &ch1_raw, &lang.pk.n2),
                &com.a.ct1,
                &lang.pk.n2);
        if tmp1 != x1 { return false; }

        let tmp2 =
            BigInt::mod_mul(
                &u::bigint_mod_pow(&inst.ct.ct2, &ch1_raw, &lang.pk.n2),
                &com.a.ct2,
                &lang.pk.n2);
        if tmp2 != x2 { return false; }
    }


    if !params.ggm_mode {
        let ch2: &DVChallenge2 = ch2_opt.expect("designated#verify3: ch2 must be Some");
        let resp2: &DVResp2 = resp2_opt.expect("designated#verify3: resp2 must be Some");
        let ch1_ct =
            BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                            &ch1_active_bits.iter()
                              .map(|&i| &vpk.cts[i])
                              .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, &vpk.pk.nn)),
                            &vpk.pk.nn);

        {
            let ct = paillier_enc_opt(&vpk.pk, Some(&vsk.sk), &resp2.um2, &resp2.um3);
            let tm = resp1.tm.as_ref().expect("designated#verify3: tm must be Some");
            let rhs = &BigInt::mod_mul(&BigInt::mod_pow(&ch1_ct, &resp2.um1, &vpk.pk.nn), &ct, &vpk.pk.nn);
            let lhs = &BigInt::mod_mul(&BigInt::mod_pow(&resp1.sm, &ch2.0, &vpk.pk.nn), tm, &vpk.pk.nn);
            if lhs != rhs { return false; }
        }

        {
            let ct = paillier_enc_opt(&vpk.pk, Some(&vsk.sk), &resp2.ur2, &resp2.ur3);
            let tr = resp1.tr.as_ref().expect("designated#verify3: tr must be Some");
            let rhs = &BigInt::mod_mul(&BigInt::mod_pow(&ch1_ct, &resp2.ur1, &vpk.pk.nn), &ct, &vpk.pk.nn);
            let lhs = &BigInt::mod_mul(&BigInt::mod_pow(&resp1.sr, &ch2.0, &vpk.pk.nn), tr, &vpk.pk.nn);
            if lhs != rhs { return false; }
        }
    }

    true
}


////////////////////////////////////////////////////////////////////////////
// Fiat-Shamir variant
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct FSDVProof {
    com : DVCom,
    resp1 : DVResp1,
    resp2 : Option<DVResp2>,
}

// Returns a lambda-bit bigint equal to the first bits of Blake2b(hash_input)
fn fs_to_bigint(params: &DVParams,
                hash_input: &Vec<u8>) -> BigInt {

    use blake2::*;
    let mut hasher: Blake2b = Digest::new();
    hasher.update(hash_input);
    let r0 = hasher.finalize(); // the result is u8 array of size 64
    let bigint = Converter::from_bytes(&r0[0..(params.lambda as usize) / 8 - 1]);

    bigint
}

fn fs_compute_challenge_1(params: &DVParams,
                          lang: &DVLang,
                          inst: &DVInst,
                          fs_com: &DVCom) -> DVChallenge1 {
    let x: Vec<u8> = rmp_serde::to_vec(&(fs_com, inst, lang)).unwrap();
    let ch1 = fs_to_bigint(params, &x);
    DVChallenge1(ch1)
}

fn fs_compute_challenge_2(params: &DVParams,
                          lang: &DVLang,
                          inst: &DVInst,
                          fs_com: &DVCom,
                          fs_ch1: &DVChallenge1,
                          fs_resp1: &DVResp1) -> Option<DVChallenge2> {
    if params.ggm_mode {
        None
    } else{
        let x: Vec<u8> = rmp_serde::to_vec(&(fs_com, fs_ch1, fs_resp1, inst, lang)).unwrap();
        let ch2 = fs_to_bigint(params, &x);
        Some(DVChallenge2(ch2))
    }
}


pub fn fs_prove(params: &DVParams,
                vpk: &VPK,
                lang: &DVLang,
                inst: &DVInst,
                wit: &DVWit,
                query_ix: usize) -> FSDVProof {
    let (com,cr) = prove1(params,lang);
    let ch1 = fs_compute_challenge_1(params,lang,inst,&com);
    let resp1 = prove2(params,vpk,&cr,wit,&ch1,query_ix);
    let ch2 = fs_compute_challenge_2(&params,lang,inst,&com,&ch1,&resp1);
    let resp2 = prove3(params,vpk,&cr,&wit,ch2.as_ref());

    FSDVProof{ com, resp1, resp2 }
}

pub fn fs_verify(params: &DVParams,
                 vsk: &VSK,
                 vpk: &VPK,
                 lang: &DVLang,
                 inst: &DVInst,
                 query_ix: usize,
                 proof: &FSDVProof) -> bool {

    let ch1 = fs_compute_challenge_1(&params,lang,inst,&proof.com);
    let ch2 = fs_compute_challenge_2(&params,lang,inst,&proof.com,&ch1,&proof.resp1);

    verify3(&params,&vsk,&vpk,&lang,&inst,
            &proof.com,&ch1,ch2.as_ref(),&proof.resp1,proof.resp2.as_ref(),query_ix)
}


////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////


pub fn test_keygen_correctness() {
    for ggm_mode in [true,false] {
        for malicious_vpk in [false,true] {
            let params = DVParams::new(2048, 128, 32, malicious_vpk, ggm_mode);

            let t_start = SystemTime::now();
            let (vpk,_vsk) = keygen(&params);
            let t_2 = SystemTime::now();
            if malicious_vpk { verify_vpk(&params,&vpk); };
            let t_end = SystemTime::now();

            let t_delta1 = t_2.duration_since(t_start).expect("error1");
            let t_delta2 = t_end.duration_since(t_2).expect("error2");
            println!("{:?}", params);
            println!("keygen: {:?}, verify: {:?}", t_delta1, t_delta2);
        }
    }
}


#[cfg(test)]
mod tests {

    use crate::protocols::designated::*;

    #[test]
    fn test_correctness_keygen() {
        let params = DVParams::new(1024, 32, 5, false, false);

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }

    #[test]
    fn test_correctness() {
        for ggm_mode in [false,true] {
        for _i in 0..10 {
            let queries:usize = 60;
            let params = DVParams::new(256, 16, queries as u32, true, ggm_mode);

            let (vpk,vsk) = keygen(&params);
            assert!(verify_vpk(&params,&vpk));

            for query_ix in 0..queries {
                let (lang,inst,wit) = sample_liw(&params);

                let (com,cr) = prove1(&params,&lang);
                let ch1 = verify1(&params);
                let resp1 = prove2(&params,&vpk,&cr,&wit,&ch1,query_ix);
                let ch2 = verify2(&params);
                let resp2 = prove3(&params,&vpk,&cr,&wit,ch2.as_ref());

                assert!(verify3(&params,&vsk,&vpk,&lang,&inst,
                                &com,&ch1,ch2.as_ref(),&resp1,resp2.as_ref(),query_ix));
            }
        }
        }
    }


    #[test]
    fn test_correctness_fs() {
        for ggm_mode in [false,true] {
        for _i in 0..10 {
            let queries:usize = 60;
            let params = DVParams::new(256, 16, queries as u32, true, ggm_mode);

            let (vpk,vsk) = keygen(&params);
            assert!(verify_vpk(&params,&vpk));

            for query_ix in 0..queries {
                let (lang,inst,wit) = sample_liw(&params);

                let proof = fs_prove(&params,&vpk,&lang,&inst,&wit,query_ix);
                assert!(fs_verify(&params,&vsk,&vpk,&lang,&inst,query_ix,&proof));
            }
        }
        }
    }

}
