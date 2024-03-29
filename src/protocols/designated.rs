/// The main DV (designated verifier) protocol, which proves knowledge
/// of plaintext for the Paillier-Elgamal encryption scheme (see
/// `super::paillier_elgamal`), assuming its modulus can be subverted.

use std::fmt;
use std::iter;
use std::time::{SystemTime, UNIX_EPOCH};
use serde::{Serialize};
use get_size::GetSize;
use get_size_derive::*;
use rand::distributions::{Distribution, Uniform};

use crate::bigint::*;
use crate::utils as u;
use crate::utils::PROFILE_DV;

use super::paillier_elgamal as pe;
use super::paillier_cramer_shoup as pcs;
use super::n_gcd as n_gcd;
use super::schnorr_batched_generic as schb;
use super::schnorr_paillier_cramer_shoup as spcs;

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


    /// The size of honestly generated challenges (first λ).
    fn ch_small_bitlen(&self) -> u32 { self.lambda }

    /// The size of honestly generated challenges (λ+1 ... λ+Q) for Q number of queries.
    fn ch_big_bitlen(&self) -> u32 { 2 * self.lambda + u::log2ceil(self.lambda) }

    /// Maximum size of the summed-up challenge, real.
    pub fn max_ch_bitlen(&self) -> u32 {
        if self.crs_uses == 0 {
            // sum of lambda (small challenges with slack)
            self.lambda + u::log2ceil(self.lambda)
        } else {
            // a single big challenge
            self.ch_big_bitlen()
        }
    }

    /// Maximum size of the summed-up challenge
    pub fn max_ch_proven_bitlen(&self) -> u32 {
        // Range slack of the batched range proof.
        let range_slack_bitlen =
            2 * self.lambda + u::log2ceil(self.lambda) - 1;

        self.max_ch_bitlen() +
            if self.malicious_setup { range_slack_bitlen } else { 0 } +
            1
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
        std::cmp::max(self.rand_m_bitlen(),self.rand_r_bitlen()) + 3
    }

    /// Params for the first batch, for challenges of lambda bits.
    pub fn nizk_ct_params(&self) -> schb::ProofParams {
        schb::ProofParams::new(self.lambda,
                               self.lambda)
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


#[derive(Clone, Debug, Serialize, GetSize)]
pub struct VSK {
    /// Verifier's Paillier secret key
    pub sk: pcs::SecretKey,
    /// Original challenge values
    pub chs: Vec<BigInt>
}

#[derive(Clone, Debug, Serialize, GetSize)]
pub struct VPK {
    /// Verifier's Paillier public key
    pub pk: pcs::PublicKey,
    /// Challenges, encrypted under Verifier's key
    pub cts: Vec<BigInt>,
    /// Proof of N = pk.n having gcd(N,phi(N)) = 1.
    pub nizk_gcd: Option<n_gcd::Proof>,
    /// Proofs of correctness+range of cts.
    pub nizks_ct: Option<Vec<schb::FSProof<spcs::PCSLang>>>,
}


pub fn keygen(params: &DVParams) -> (VPK, VSK) {

    let t_1 = SystemTime::now();
    // This can be more effective in terms of move/copy
    // e.g. Inst/Wit could contain references inside?
    let (pk,sk) = pcs::keygen(params.vpk_n_bitlen() as usize);

    let ch_range_1 = BigInt::pow(&BigInt::from(2), params.ch_small_bitlen());
    let ch_range_2 = BigInt::pow(&BigInt::from(2), params.ch_big_bitlen());
    let mut chs: Vec<BigInt> = vec![];
    for _i in 0..params.lambda {
        chs.push(u::bigint_sample_below_sym(&ch_range_1)); }
    for _i in 0..params.crs_uses {
        chs.push(u::bigint_sample_below_sym(&ch_range_2)); }
    let t_2 = SystemTime::now();

    let rs: Vec<BigInt> =
        (0..(params.lambda + params.crs_uses))
        .map(|_| BigInt::sample_below(&pk.n))
        .collect();

    let cts: Vec<BigInt> =
        chs.iter().zip(rs.iter())
        .map(|(ch,r)| pcs::encrypt(&pk,Some(&sk),ch,r))
        .collect();

    let t_3 = SystemTime::now();

    let mut t_4 = SystemTime::now();

    let (nizk_gcd,nizks_ct) = if !params.malicious_setup {
        (None,None)
    } else {

        let nizk_gcd: n_gcd::Proof =
            n_gcd::prove(
                &params.nizk_gcd_params(),
                &n_gcd::Inst{ n: pk.n.clone() },
                &n_gcd::Wit{ p: sk.p.clone(), q: sk.q.clone() }
            );

        t_4 = SystemTime::now();

        let mut nizks_ct: Vec<schb::FSProof<spcs::PCSLang>> = vec![];
        let nizk_batches =
            if params.crs_uses == 0 { 1 }
        else { 2 + (params.crs_uses - 1) / params.lambda };

        let lang1 = spcs::PCSLang{
            lparams: spcs::PCSLangParams { n_bitlen: params.vpk_n_bitlen(),
                                           range_bitlen: params.ch_small_bitlen() },
            pk: pk.clone(),
            sk: Some(sk.clone())};
        let lang2 = spcs::PCSLang{
            lparams: spcs::PCSLangParams { n_bitlen: params.vpk_n_bitlen(),
                                           range_bitlen: params.ch_big_bitlen() },
            pk: pk.clone(),
            sk: Some(sk.clone())};

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
                    rs_wit.push(BigInt::from(0));
                    cts_inst.push(pcs::encrypt(&pk,Some(&sk),
                                               &BigInt::from(0),
                                               &BigInt::from(0)));
                }
            }

            let params = params.nizk_ct_params();
            let lang = if i == 0 { &lang1 } else { &lang2 };

            let inst = cts_inst.iter().map(|ct| spcs::PCSLangCoDom{ct:ct.clone()}).collect();
            let wit = ms_wit.into_iter().zip(rs_wit.into_iter())
                .map(|(m,r)| spcs::PCSLangDom{m, r})
                .collect();

            nizks_ct.push(schb::fs_prove(&params, lang, &inst, &wit));
        }

        (Some(nizk_gcd), Some(nizks_ct))
    };

    let t_5 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_total = t_5.duration_since(t_1).unwrap();

    if PROFILE_DV {
        println!("Keygen prove time (total {:?}):
  keygen    {:?}
  cts       {:?}
  nizk_gcd  {:?}
  nizk_ct   {:?}",
                 t_total, t_delta1, t_delta2, t_delta3, t_delta4);
    }

    (VPK{pk, cts, nizk_gcd, nizks_ct},VSK{sk, chs})
}

pub fn verify_vpk(params: &DVParams, vpk: &VPK) -> bool {

    if !params.malicious_setup {
        return true
    }

    let t_1 = SystemTime::now();

    let res1 = n_gcd::verify(
        &params.nizk_gcd_params(),
        &n_gcd::Inst{ n: vpk.pk.n.clone() },
        vpk.nizk_gcd.as_ref().expect("dv#verify_vpk: no nizk_gcd"));
    if !res1 { return false; }

    let t_2 = SystemTime::now();

    let nizks_ct = vpk.nizks_ct.as_ref().expect("dv#verify_vpk: no nizk_gcd");

    let lang1 = spcs::PCSLang{
        lparams: spcs::PCSLangParams { n_bitlen: params.vpk_n_bitlen(),
                                       range_bitlen: params.ch_small_bitlen() },
        pk: vpk.pk.clone(),
        sk: None };
    let lang2 = spcs::PCSLang{
        lparams: spcs::PCSLangParams { n_bitlen: params.vpk_n_bitlen(),
                                       range_bitlen: params.ch_big_bitlen() },
        pk: vpk.pk.clone(),
        sk: None };

    for i in 0..(nizks_ct.len() as u32) {
        let batch_from = (i*params.lambda) as usize;
        let batch_to = std::cmp::min((i+1)*params.lambda,
                                     params.lambda + params.crs_uses) as usize;

        let mut cts_w = (&vpk.cts[batch_from..batch_to]).to_vec();

        let pad_last_batch = params.crs_uses > 0 && i == (nizks_ct.len() as u32) - 1;
        if pad_last_batch {
            for _j in 0..(params.lambda - (params.crs_uses % params.lambda)) {
                cts_w.push(
                    pcs::encrypt(&vpk.pk, None, &BigInt::from(0), &BigInt::from(0)));
            }
        }


        let params = params.nizk_ct_params();
        let lang = if i == 0 { &lang1 } else { &lang2 };
        let inst = cts_w.iter().map(|ct| spcs::PCSLangCoDom{ ct:ct.clone() }).collect();

        let res2 = schb::fs_verify(&params, lang, &inst, &nizks_ct[i as usize]);
        if !res2 { return false; }
    }

    let t_3 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_total = t_3.duration_since(t_1).unwrap();
    if PROFILE_DV {
        println!("Keygen verify time (total {:?}):
  nizk_gcd {:?}
  nizk_ct: {:?}",
                 t_total,t_delta1, t_delta2);
    }

    return true;
}


////////////////////////////////////////////////////////////////////////////
// Language
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize, GetSize)]
pub struct DVLang {
    pub pk: pe::PublicKey,
    pub sk: Option<pe::SecretKey>
}

#[derive(Clone, Debug, Serialize, GetSize)]
pub struct DVInst {
    pub ct: pe::Ciphertext
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


#[derive(Clone, Debug, Serialize, GetSize)]
pub struct DVCom{ pub a: pe::Ciphertext }

#[derive(Clone, Debug, Serialize, GetSize)]
pub struct DVComRand {
    pub rm_m: BigInt,
    pub rr_m: BigInt,
    pub tm1: Option<BigInt>,
    pub tm2: Option<BigInt>,
    pub tr1: Option<BigInt>,
    pub tr2: Option<BigInt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, GetSize)]
pub struct DVChallenge1{ inner: BigInt }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DVChallenge2{ inner: BigInt }

#[derive(Clone, Debug, Serialize, GetSize)]
pub struct DVResp1 {
    pub sm: BigInt,
    pub sr: BigInt,
    pub tm: Option<BigInt>,
    pub tr: Option<BigInt>,
}

#[derive(Clone, Debug, Serialize, GetSize)]
pub struct DVResp2 {
    pub um1: BigInt,
    pub um2: BigInt,
    pub ur1: BigInt,
    pub ur2: BigInt,
}


pub fn prove1(params: &DVParams, vpk: &VPK, lang: &DVLang) -> (DVCom,DVComRand) {
    let t_1 = SystemTime::now();
    let rm_m = BigInt::sample(params.rand_m_bitlen() as usize);
    let rr_m = BigInt::sample(params.rand_r_bitlen() as usize);

    let a = pe::encrypt_with_randomness_opt(&lang.pk,lang.sk.as_ref(),&rm_m,&rr_m);
    let t_2 = SystemTime::now();

    let (tm1, tm2, tr1, tr2) = if params.ggm_mode {
        (None, None, None, None)
    } else {
        // These must blind, over Z, the product d*w, and d*r, where d is lambda
        // bits and both w and r are n_bitlen bits.
        let tm1 = BigInt::sample((params.psi_n_bitlen + 2 * params.lambda) as usize);
        let tr1 = BigInt::sample((params.psi_n_bitlen + 2 * params.lambda) as usize);

        let tm2 = BigInt::sample_below(&vpk.pk.n);
        let tr2 = BigInt::sample_below(&vpk.pk.n);

        (Some(tm1), Some(tm2), Some(tr1), Some(tr2))
    };

    let t_3 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_total = t_3.duration_since(t_1).unwrap();

    if PROFILE_DV {
        println!("DV prove1 (total {:?}):
  sample & commit  {:?}
  GGM pre-sample   {:?}",
                 t_total,t_delta1,t_delta2);
    }

    (DVCom{a}, DVComRand{rm_m, rr_m,
                         tm1, tm2, tr1, tr2})

}

pub fn verify1(params: &DVParams) -> DVChallenge1 {
    let b = BigInt::sample(params.lambda as usize);
    DVChallenge1{ inner: b }
}

pub fn prove2(params: &DVParams,
              vpk: &VPK,
              cr: &DVComRand,
              wit: &DVWit,
              ch1: &DVChallenge1,
              query_ix: usize) -> DVResp1 {
    let nn: &BigInt = &vpk.pk.nn;

    let t_1 = SystemTime::now();
    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.inner.test_bit(i) { ch1_active_bits.push(i); }
    }
    let t_2 = SystemTime::now();

    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, nn)),
                        nn);
    let t_3 = SystemTime::now();

    let sm_ct = pcs::encrypt(&vpk.pk, None, &cr.rm_m, &BigInt::from(0));
    let t_4 = SystemTime::now();
    let sm = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, &wit.m, nn),
                             &sm_ct,
                             nn);
    let t_5 = SystemTime::now();

    let sr_ct = pcs::encrypt(&vpk.pk, None, &cr.rr_m, &BigInt::from(0));
    let t_6 = SystemTime::now();
    let sr = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, &wit.r, nn),
                             &sr_ct,
                             nn);
    let t_7 = SystemTime::now();


    let (tm,tr) = if params.ggm_mode {
        (None,None)
    } else {
        let tm1 = cr.tm1.as_ref().expect("designated#prove2: tm1 must be Some");
        let tm2 = cr.tm2.as_ref().expect("designated#prove2: tm2 must be Some");
        let tr1 = cr.tr1.as_ref().expect("designated#prove2: tr1 must be Some");
        let tr2 = cr.tr2.as_ref().expect("designated#prove2: tr2 must be Some");

        let tm_ct = pcs::encrypt(&vpk.pk, None, tm2, &BigInt::from(0));
        let tm = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, tm1, nn),
                                 &tm_ct,
                                 nn);

        let tr_ct = pcs::encrypt(&vpk.pk, None, tr2, &BigInt::from(0));
        let tr = BigInt::mod_mul(&BigInt::mod_pow(&ch_ct, tr1, nn),
                                 &tr_ct,
                                 nn);

        (Some(tm), Some(tr))
    };
    let t_8 = SystemTime::now();


    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_delta5 = t_6.duration_since(t_5).unwrap();
    let t_delta6 = t_7.duration_since(t_6).unwrap();
    let t_delta7 = t_8.duration_since(t_7).unwrap();
    let t_total = t_8.duration_since(t_1).unwrap();
    if PROFILE_DV {
        println!("DV prove2 (total {:?}):
  active bits      {:?}
  prod chall       {:?}
  enc 1            {:?}
  hom_comp 1       {:?}
  enc 2            {:?}
  hom_comp 2       {:?}
  ggm enc+resp x2  {:?}",
                 t_total,t_delta1, t_delta2, t_delta3, t_delta4, t_delta5, t_delta6, t_delta7);
    }


    DVResp1{sm, sr, tm, tr}
}

pub fn verify2(params: &DVParams) -> Option<DVChallenge2> {
    if params.ggm_mode {
        None
    } else{
        let d = BigInt::sample(params.lambda as usize);
        Some(DVChallenge2{inner: d})
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

        let n: &BigInt = &vpk.pk.n;

        let ch2 = ch2_opt.expect("designated#prove3: ch2 must be Some");
        let d: &BigInt = &ch2.inner;

        let tm1 = cr.tm1.as_ref().expect("designated#prove3: tm1 must be Some");
        let tm2 = cr.tm2.as_ref().expect("designated#prove3: tm2 must be Some");
        let tr1 = cr.tr1.as_ref().expect("designated#prove3: tr1 must be Some");
        let tr2 = cr.tr2.as_ref().expect("designated#prove3: tr2 must be Some");

        // These are over integers because we don't know the order of C.
        let um1 = &wit.m * d + tm1;
        let ur1 = &wit.r * d + tr1;

        let um2 = BigInt::mod_add(&BigInt::mod_mul(&cr.rm_m, d, n), tm2, n);
        let ur2 = BigInt::mod_add(&BigInt::mod_mul(&cr.rr_m, d, n), tr2, n);

        Some(DVResp2{um1, um2, ur1, ur2})
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

    let t_1 = SystemTime::now();
    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.inner.test_bit(i) { ch1_active_bits.push(i); }
    }

    let ch1_raw: BigInt =
        &vsk.chs[(params.lambda as usize) + query_ix] +
        ch1_active_bits.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );
    let t_2 = SystemTime::now();

    let sr = pcs::decrypt(&vpk.pk,&vsk.sk,&resp1.sr);
    let sm = pcs::decrypt(&vpk.pk,&vsk.sk,&resp1.sm);
    let t_3 = SystemTime::now();


    // a Y^c = Enc_psi(s_m,s_r)
    {

        let pe::Ciphertext{ct1:x1,ct2:x2} =
            pe::encrypt_with_randomness_opt(&lang.pk, None, &sm, &sr);

        let t_4 = SystemTime::now();
        let tmp1 =
            BigInt::mod_mul(
                &u::bigint_mod_pow(&inst.ct.ct1, &ch1_raw, &lang.pk.nn),
                &com.a.ct1,
                &lang.pk.nn);
        if tmp1 != x1 { return false; }
        let t_5 = SystemTime::now();

        let tmp2 =
            BigInt::mod_mul(
                &u::bigint_mod_pow(&inst.ct.ct2, &ch1_raw, &lang.pk.nn),
                &com.a.ct2,
                &lang.pk.nn);
        if tmp2 != x2 { return false; }
        let t_6 = SystemTime::now();

        let t_delta1 = t_2.duration_since(t_1).unwrap();
        let t_delta2 = t_3.duration_since(t_2).unwrap();
        let t_delta3 = t_4.duration_since(t_3).unwrap();
        let t_delta4 = t_5.duration_since(t_4).unwrap();
        let t_delta5 = t_6.duration_since(t_5).unwrap();
        let t_total = t_6.duration_since(t_1).unwrap();


        if PROFILE_DV {
        println!("DV verify3 (total {:?}):
  prod chal    {:?}
  decrypt      {:?}
  enc 1        {:?}
  hom_comp 1   {:?}
  hom_comp 2   {:?}",
                 t_total,t_delta1, t_delta2, t_delta3, t_delta4, t_delta5);}
    }


    if !params.ggm_mode {
        let nn = &vpk.pk.nn;
        let ch2: &DVChallenge2 = ch2_opt.expect("designated#verify3: ch2 must be Some");
        let resp2: &DVResp2 = resp2_opt.expect("designated#verify3: resp2 must be Some");
        let ch1_ct =
            BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                            &ch1_active_bits.iter()
                              .map(|&i| &vpk.cts[i])
                              .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, nn)),
                            nn);

        let tm = resp1.tm.as_ref().expect("designated#verify3: tm must be Some");
        let tr = resp1.tr.as_ref().expect("designated#verify3: tr must be Some");

        let p = &vsk.sk.p;
        let q = &vsk.sk.q;
        let pp = p * p;
        let qq = q * q;
        let pp_inv_qq = BigInt::mod_inv(&pp, &qq).unwrap();

        {
            let ct = pcs::encrypt(&vpk.pk, Some(&vsk.sk), &resp2.um2, &BigInt::from(0));
            let exp1_pp = BigInt::mod_pow(&ch1_ct, &resp2.um1, &pp);
            let exp1_qq = BigInt::mod_pow(&ch1_ct, &resp2.um1, &qq);
            let exp1 = u::crt_recombine(&exp1_pp, &exp1_qq, &pp, &qq, &pp_inv_qq);
            let rhs = &BigInt::mod_mul(&exp1, &ct, nn);


            let exp2_pp = &BigInt::mod_pow(&resp1.sm, &ch2.inner, &pp);
            let exp2_qq = &BigInt::mod_pow(&resp1.sm, &ch2.inner, &qq);
            let exp2 = u::crt_recombine(&exp2_pp, &exp2_qq, &pp, &qq, &pp_inv_qq);
            let lhs = &BigInt::mod_mul(&exp2, tm, nn);

            if lhs != rhs { return false; }
        }

        {
            let ct = pcs::encrypt(&vpk.pk, Some(&vsk.sk), &resp2.ur2, &BigInt::from(0));

            let exp1_pp = BigInt::mod_pow(&ch1_ct, &resp2.ur1, &pp);
            let exp1_qq = BigInt::mod_pow(&ch1_ct, &resp2.ur1, &qq);
            let exp1 = u::crt_recombine(&exp1_pp, &exp1_qq, &pp, &qq, &pp_inv_qq);
            let rhs = &BigInt::mod_mul(&exp1, &ct, nn);

            let exp2_pp = &BigInt::mod_pow(&resp1.sr, &ch2.inner, &pp);
            let exp2_qq = &BigInt::mod_pow(&resp1.sr, &ch2.inner, &qq);
            let exp2 = u::crt_recombine(&exp2_pp, &exp2_qq, &pp, &qq, &pp_inv_qq);
            let lhs = &BigInt::mod_mul(&exp2, tr, nn);

            if lhs != rhs { return false; }
        }
    }

    true
}


////////////////////////////////////////////////////////////////////////////
// Fiat-Shamir variant
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize, GetSize)]
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
    let bigint = Converter::from_bytes(&r0[0..(params.lambda as usize) / 8]);

    bigint
}

fn fs_compute_challenge_1(params: &DVParams,
                          lang: &DVLang,
                          inst: &DVInst,
                          fs_com: &DVCom) -> DVChallenge1 {
    let x: Vec<u8> = rmp_serde::to_vec(&(fs_com, inst, lang)).unwrap();
    let ch1 = fs_to_bigint(params, &x);
    DVChallenge1{inner: ch1}
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
        Some(DVChallenge2{ inner: ch2})
    }
}


pub fn fs_prove(params: &DVParams,
                vpk: &VPK,
                lang: &DVLang,
                inst: &DVInst,
                wit: &DVWit,
                query_ix: usize) -> FSDVProof {
    let (com,cr) = prove1(params,vpk,lang);
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



#[cfg(test)]
mod tests {

    use crate::protocols::designated::*;

    #[test]
    fn keygen_correctness() {
        for ggm_mode in [false,true] {
            let params = DVParams::new(1024, 32, 5, true, ggm_mode);
            
            let (vpk,_vsk) = keygen(&params);
            assert!(verify_vpk(&params,&vpk));
        }
    }

    #[test]
    fn correctness() {
        for malicious_setup in [false,true] {
        for ggm_mode in [false,true] {
        for _i in 0..5 {
            let queries:usize = 128;
            let params = DVParams::new(256, 16, queries as u32, malicious_setup, ggm_mode);

            let (vpk,vsk) = keygen(&params);
            assert!(verify_vpk(&params,&vpk));

            for query_ix in 0..queries {
                let (lang,inst,wit) = sample_liw(&params);

                let (com,cr) = prove1(&params,&vpk,&lang);
                let ch1 = verify1(&params);
                let resp1 = prove2(&params,&vpk,&cr,&wit,&ch1,query_ix);
                let ch2 = verify2(&params);
                let resp2 = prove3(&params,&vpk,&cr,&wit,ch2.as_ref());

                assert!(verify3(&params,&vsk,&vpk,&lang,&inst,
                                &com,&ch1,ch2.as_ref(),&resp1,resp2.as_ref(),query_ix));
            }
        }}}
    }


    #[test]
    fn fs_correctness() {
        for malicious_setup in [false,true] {
        for ggm_mode in [false,true] {
        for _i in 0..5 {
            let queries:usize = 128;
            let params = DVParams::new(256, 16, queries as u32, malicious_setup, ggm_mode);

            let (vpk,vsk) = keygen(&params);
            assert!(verify_vpk(&params,&vpk));

            for query_ix in 0..queries {
                let (lang,inst,wit) = sample_liw(&params);

                let proof = fs_prove(&params,&vpk,&lang,&inst,&wit,query_ix);
                assert!(fs_verify(&params,&vsk,&vpk,&lang,&inst,query_ix,&proof));
            }
        }}}
    }

}
