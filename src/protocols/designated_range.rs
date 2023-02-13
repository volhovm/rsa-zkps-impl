use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Roots, Converter};
use curv::BigInt;
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
use super::utils::PROFILE_DVR;
use super::schnorr_generic as sch;
use super::schnorr_paillier_batched as spb;
use super::schnorr_paillier_plus as spp;
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;
use super::schnorr_exp as se;


////////////////////////////////////////////////////////////////////////////
// Params
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct DVRParams {
    /// N of the prover (of the homomorphism psi), bit length
    pub psi_n_bitlen: u32,
    /// Security parameter
    pub lambda: u32,
    /// Bitlen of the range
    pub range_bitlen: u32,
    /// Range we're proving
    pub range: BigInt,
    /// The number of CRS reuses
    pub crs_uses: u32,
    /// Whether malicious setup (that introduces VPK proofs) is enabled
    pub malicious_setup: bool,
    /// Whether the GGM mode is enabled, which omits certain proof parts
    pub ggm_mode: bool,



    /// The size of honestly generated challenges (first λ).
    pub ch_small_bitlen: u32,
    /// The size of honestly generated challenges (λ+1 ... λ+Q) for Q number of queries.
    pub ch_big_bitlen: u32,
    /// Maximum size of the summed-up challenge, real.
    pub max_ch_bitlen: u32,
    /// Maximum size of the summed-up challenge, after considering VPK proof slack.
    pub max_ch_proven_bitlen: u32,
    /// Bit length of the third N, wrt which VPK.n is constructed.
    pub n_bitlen: u32,

    // A bunch of parameters defining how to sample in prove1
    pub t_range_bitlen: u32,
    pub r_range_bitlen: u32,
    pub sigma_range_bitlen: u32,
    pub tau_range_bitlen: u32,

    /// A parameter we check u_i range w.r.t.
    pub ui_range_bitlen: u32,

    /// Bit length of the modulus N_V used by the verifier.
    pub vpk_n_bitlen: u32,

}

impl DVRParams {

    pub fn new(psi_n_bitlen: u32,
               lambda: u32,
               range_bitlen: u32,
               crs_uses: u32,
               malicious_setup: bool,
               ggm_mode: bool) -> DVRParams {
        let range = BigInt::pow(&BigInt::from(2), range_bitlen);

        let ch_small_bitlen = lambda;
        // lambda bits more than sum of lambda small challenges
        let ch_big_bitlen = 
            ch_small_bitlen + u::log2ceil(lambda) + lambda;
        let max_ch_bitlen = 
            if crs_uses == 0 {
                // because we sum ch_small_bitlen lambda times
                ch_small_bitlen + u::log2ceil(lambda)
            } else {
                // Just ch_big_bitlen, because it masks ch_small_bitlen fully.
                ch_big_bitlen
            };
        // Range slack of the batched range proof.
        let range_slack_bitlen = 2 * lambda + u::log2ceil(lambda) - 1;
        let max_ch_proven_bitlen =
            max_ch_bitlen + 
            if malicious_setup { range_slack_bitlen } else { 0 } +
            1;
        // FIXME Double check the value
        // This length should only depend on lambda, not psi;
        // but I'm assuming psi_n_bitlen is already in sync with lambda.
        let n_bitlen = psi_n_bitlen;

        // TODO Can't this be just n_bitlen? we need lambda for uniformness?
        // 2^λ N
        let t_range_bitlen = n_bitlen + lambda;
        // r must blind c*(R-m)
        // r_i is the same -- it must blind c*x_i,
        //   where each x_i is at most R, because they decompose ~R^2
        let r_range_bitlen = max_ch_proven_bitlen + range_bitlen + lambda;
        // sigma must blind c*t
        // sigma_i must blind c*t_i, t_i are same as t
        let sigma_range_bitlen = max_ch_proven_bitlen + t_range_bitlen + lambda;
        // must blind c*(3*xi*ti-4Rt) <= c * (3 R t - 4 R t) <= c * 7 R t
        let tau_range_bitlen =
            max_ch_proven_bitlen +
            (t_range_bitlen + range_bitlen + 4) +
            lambda;

        // FIXME I need confirmation on how this value is computed.
        // for now I will just assume it is equal to the r_i blinder.
        let ui_range_bitlen = r_range_bitlen + 1;
        
        // It basically needs to hide tau, which is the biggest encrypted message.
        // FIXME why +3? Does not work with +2 but works with +3? Or sometimes with +2?
        let vpk_n_bitlen = tau_range_bitlen + 2;

        DVRParams{psi_n_bitlen, lambda, range_bitlen,
                  range, crs_uses, malicious_setup, ggm_mode,

                  ch_small_bitlen,
                  ch_big_bitlen,
                  max_ch_bitlen,
                  max_ch_proven_bitlen,
                  n_bitlen,

                  t_range_bitlen,
                  r_range_bitlen,
                  sigma_range_bitlen,
                  tau_range_bitlen,

                  ui_range_bitlen,
                  vpk_n_bitlen,
        }
    }

    /// Parameters for the Gen g/h NIZK proof.
    pub fn nizk_se_params(&self) -> sch::ProofParams {
        // This gives 7 reps, which is optimal for a 1-shot proof.
        let ch_space_bitlen = 19;
        sch::ProofParams::new(self.lambda, ch_space_bitlen)
    }


    /// Params for the first batch, for challenges of lambda bits.
    pub fn nizk_ct_params_1(&self) -> spb::ProofParams {
        spb::ProofParams::new(self.vpk_n_bitlen,
                              self.lambda,
                              self.lambda,
                              self.lambda)
    }

    /// Params for the second+ batches, for challenges of 2 * lambda +
    /// log lambda bits.
    pub fn nizk_ct_params_2(&self) -> spb::ProofParams {
        spb::ProofParams::new(self.vpk_n_bitlen,
                              self.lambda,
                              self.lambda,
                              2 * self.lambda + u::log2ceil(self.lambda))
    }

    /// Parameters for the GCD NIZK proof.
    pub fn nizk_gcd_params(&self) -> n_gcd::ProofParams {
        n_gcd::ProofParams{ n_bitlen: self.psi_n_bitlen as usize,
                            lambda: self.lambda,
                            pmax: 2_u64.pow(19) }
    }


    /// Parameters for the schnorr-paillier+ sub-protocol
    pub fn spp_params(&self) -> sch::ProofParams {
        // We can assume lambda-bit challenge space (and thus 1 repetition only)
        // because these non-GGM proofs are w.r.t. N_V controlled by the extractor,
        // which is trusted for soundness. And ZK is preserved anyway.
        sch::ProofParams::new(self.lambda, self.lambda)
    }

}


////////////////////////////////////////////////////////////////////////////
// Language
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct DVRLang {
    pub pk: pe::PEPublicKey,
    pub sk: Option<pe::PESecretKey>,
}

impl DVRLang {
    pub fn range_rand(&self) -> &BigInt {
        &self.pk.n
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct DVRInst { pub ct: pe::PECiphertext }
#[derive(Clone, Debug)]
pub struct DVRWit { pub m: BigInt, pub r: BigInt }


pub fn sample_lang(params: &DVRParams) -> DVRLang {
    let (pk,sk) = pe::keygen(params.psi_n_bitlen as usize);
    DVRLang{pk, sk: Some(sk)}
}

pub fn sample_inst(params: &DVRParams, lang: &DVRLang) -> (DVRInst,DVRWit) {
    let m = BigInt::sample(params.range_bitlen as usize);
    let r = BigInt::sample_below(&lang.pk.n);
    let ct = pe::encrypt_with_randomness_opt(&lang.pk,lang.sk.as_ref(),&m,&r);
    (DVRInst{ct}, DVRWit{m, r})
}

pub fn sample_liw(params: &DVRParams) -> (DVRLang,DVRInst,DVRWit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(params,&lang);
    (lang,inst,wit)
}


////////////////////////////////////////////////////////////////////////////
// Keygen
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct VSK {
    /// Verifier's Paillier secret key
    pub sk: DecryptionKey,
    /// Original challenge values
    pub chs: Vec<BigInt>,


    /// First factor of the VPK.n
    pub p: BigInt,
    /// Second factor of the VPK.n
    pub q: BigInt,
    /// The secret exponent
    pub f: BigInt,
    /// p^{-1} mod q, for convenience
    pub p_inv_q: BigInt
}


#[derive(Clone, Debug, Serialize)]
pub struct VPK {
    /// Verifier's Paillier public key
    pub pk: EncryptionKey,
    /// Challenges, encrypted under Verifier's key
    pub cts: Vec<BigInt>,

    /// An RSA modulus used for h/g
    pub n: BigInt,
    /// Generator w.r.t. N
    pub g: BigInt,
    /// Second generator w.r.t. N, h = g^f mod N, where f is secret.
    pub h: BigInt,

    /// Schnorr proof of g/h
    pub nizk_gen: sch::FSProof<se::ExpNLang>,
    /// Proof of N = pk.n having gcd(N,phi(N)) = 1.
    pub nizk_gcd: Option<n_gcd::Proof>,
    /// Proofs of correctness+range of cts.
    pub nizks_ct: Option<Vec<spb::FSProof>>,
}


pub fn keygen(params: &DVRParams) -> (VPK, VSK) {
    let t_1 = SystemTime::now();
    // These two are suspiciously slow, taking 300ms both for 2048 bit+
    let (pk,sk) =
        Paillier::keypair_with_modulus_size(params.vpk_n_bitlen as usize).keys();

    let (pk_,sk_) =
        Paillier::keypair_with_modulus_size(params.n_bitlen as usize).keys();
    let t_2 = SystemTime::now();


    let n = pk_.n.clone();
    let p = sk_.p.clone();
    let q = sk_.q.clone();
    let p_inv_q = BigInt::mod_inv(&p, &q).unwrap();

    let h = BigInt::sample_below(&n);
    let phi = (&p-1) * (&q-1);
    let f = BigInt::sample_below(&phi);
    let g = BigInt::mod_pow(&h, &f, &n);


    let ch_range_1 = BigInt::pow(&BigInt::from(2), params.ch_small_bitlen);
    let ch_range_2 = BigInt::pow(&BigInt::from(2), params.ch_big_bitlen);
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
        .map(|(ch,r)| paillier_enc_opt(&pk, Some(&sk), &ch, &r))
        .collect();
    let t_3 = SystemTime::now();

    let nizk_gen = sch::fs_prove(
        &params.nizk_se_params(),
        &se::ExpNLang{n_bitlen: params.n_bitlen,
                      n: n.clone(),
                      h: h.clone(),
                      p: Some(p.clone()),
                      q: Some(q.clone())},
        &se::ExpNLangCoDom{g: g.clone()},
        &se::ExpNLangDom{x: f.clone()});

    let t_4 = SystemTime::now();
    let mut t_5 = SystemTime::now();
    let (nizk_gcd,nizks_ct) = if !params.malicious_setup {
        (None,None)
    } else {
        let nizk_gcd: n_gcd::Proof =
            n_gcd::prove(
                &params.nizk_gcd_params(),
                &n_gcd::Inst{ n: pk.n.clone() },
                &n_gcd::Wit{ p: sk.p.clone(), q: sk.q.clone() }
            );
        t_5 = SystemTime::now();

        let spb_lang = spb::Lang{pk:pk.clone(), sk: Some(sk.clone())};
        let mut nizks_ct: Vec<spb::FSProof> = vec![];
        let nizk_batches =
            if params.crs_uses == 0 { 1 }
        else { 2 + (params.crs_uses - 1) / params.lambda };

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
                    cts_inst.push(
                        paillier_enc_opt(&pk,Some(&sk),&BigInt::from(0),&BigInt::from(1)));
                }
            }

            let params = if i == 0 { params.nizk_ct_params_1() }
            else { params.nizk_ct_params_2() };
            let inst = spb::Inst{cts: cts_inst};
            let wit = spb::Wit{ms: ms_wit, rs: rs_wit};

            nizks_ct.push(spb::fs_prove(&params, &spb_lang, &inst, &wit));
        }

        (Some(nizk_gcd),Some(nizks_ct))
    };

    let t_6 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_delta5 = t_6.duration_since(t_5).unwrap();
    let t_total = t_6.duration_since(t_1).unwrap();

    if PROFILE_DVR {
        println!("DVR Keygen prove time (total {:?}):
  keygen    {:?}
  cts       {:?}
  nizk_exp  {:?}
  nizk_gcd  {:?}
  nizk_ct   {:?}",
                 t_total, t_delta1, t_delta2, t_delta3, t_delta4, t_delta5);
    }



    let vsk = VSK{f, p, q, sk, chs, p_inv_q};
    let vpk = VPK{n, g, h, nizk_gen, pk, cts, nizk_gcd, nizks_ct};
    (vpk,vsk)
}


pub fn verify_vpk(params: &DVRParams, vpk: &VPK) -> bool {
    let t_1 = SystemTime::now();

    let se_params = &params.nizk_se_params();
    let se_lang = se::ExpNLang{n_bitlen: params.n_bitlen,
                               n: vpk.n.clone(), h: vpk.h.clone(),
                               p: None, q: None };
    // FIXME I'm not sure it's needed, and I'm not sure I
    // haven't missed lang. verification anywhere else
    if !sch::Lang::verify(&se_lang,&se_params) { return false; }
    if !sch::fs_verify(&se_params,
                       &se_lang,
                       &se::ExpNLangCoDom{g: vpk.g.clone()},
                       &vpk.nizk_gen) {
        return false;
    }

    if !params.malicious_setup {
        return true;
    }


    let t_2 = SystemTime::now();

    let res1 = n_gcd::verify(
        &params.nizk_gcd_params(),
        &n_gcd::Inst{ n: vpk.pk.n.clone() },
        vpk.nizk_gcd.as_ref().expect("dvr::verify_vpk: nizk_gcd must be Some"));
    if !res1 { return false; }

    let t_3 = SystemTime::now();

    let nizks_ct = vpk.nizks_ct.as_ref().expect("dvr::verify_vpk: nizks_ct must be Some");
    for i in 0..(nizks_ct.len() as u32) {
        let batch_from = (i*params.lambda) as usize;
        let batch_to = std::cmp::min((i+1)*params.lambda,
                                     params.lambda + params.crs_uses) as usize;

        let mut cts_w = (&vpk.cts[batch_from..batch_to]).to_vec();

        let pad_last_batch = params.crs_uses > 0 && i == (nizks_ct.len() as u32) - 1;
        if pad_last_batch {
            for _j in 0..(params.lambda - (params.crs_uses % params.lambda)) {
                cts_w.push(
                    paillier_enc_opt(&vpk.pk,None,&BigInt::from(0),&BigInt::from(1)));
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


    let t_4 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_total = t_3.duration_since(t_1).unwrap();

    if PROFILE_DVR {
        println!("DVR Keygen verify time (total {:?}):
  nizk_exp  {:?}
  nizk_gcd  {:?}
  nizk_ct   {:?}",
                 t_total,t_delta1, t_delta2, t_delta3);
    }


    true
}


////////////////////////////////////////////////////////////////////////////
// Interactive part
////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRCom {
    com_m: BigInt,
    com1_m: BigInt,
    com2_m: BigInt,
    com3_m: BigInt,
    beta_m: BigInt,
    beta1_m: BigInt,
    beta2_m: BigInt,
    beta3_m: BigInt,
    beta4_m: BigInt,

    com_r: BigInt,

    alpha1: BigInt,
    alpha2: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRComRand {
    r_m: BigInt,
    r1_m: BigInt,
    r2_m: BigInt,
    r3_m: BigInt,
    t_m: BigInt,
    t1_m: BigInt,
    t2_m: BigInt,
    t3_m: BigInt,
    x1_m: BigInt,
    x2_m: BigInt,
    x3_m: BigInt,
    sigma_m: BigInt,
    sigma1_m: BigInt,
    sigma2_m: BigInt,
    sigma3_m: BigInt,
    tau_m: BigInt,

    r_r: BigInt,
    t_r: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRChallenge1(BigInt);

/// Commitment for the pe+ protocol
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PlusCom {
    com_u_m: sch::Commitment<spp::PPLang>,
    com_v_m: sch::Commitment<spp::PPLang>,
    com_u1_m: sch::Commitment<spp::PPLang>,
    com_v1_m: sch::Commitment<spp::PPLang>,
    com_u2_m: sch::Commitment<spp::PPLang>,
    com_v2_m: sch::Commitment<spp::PPLang>,
    com_u3_m: sch::Commitment<spp::PPLang>,
    com_v3_m: sch::Commitment<spp::PPLang>,
    com_u4_m: sch::Commitment<spp::PPLang>,

    com_u_r: sch::Commitment<spp::PPLang>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRResp1 {
    u_m: BigInt,
    v_m: BigInt,
    u1_m: BigInt,
    v1_m: BigInt,
    u2_m: BigInt,
    v2_m: BigInt,
    u3_m: BigInt,
    v3_m: BigInt,
    u4_m: BigInt,

    u_r: BigInt,

    plus_com: Option<PlusCom>
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PlusComRand {
    comrand_u_m: sch::ComRand<spp::PPLang>,
    comrand_v_m: sch::ComRand<spp::PPLang>,
    comrand_u1_m: sch::ComRand<spp::PPLang>,
    comrand_v1_m: sch::ComRand<spp::PPLang>,
    comrand_u2_m: sch::ComRand<spp::PPLang>,
    comrand_v2_m: sch::ComRand<spp::PPLang>,
    comrand_u3_m: sch::ComRand<spp::PPLang>,
    comrand_v3_m: sch::ComRand<spp::PPLang>,
    comrand_u4_m: sch::ComRand<spp::PPLang>,

    comrand_u_r: sch::ComRand<spp::PPLang>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRResp1Rand {
    u_r_m: BigInt,
    v_r_m: BigInt,
    u1_r_m: BigInt,
    v1_r_m: BigInt,
    u2_r_m: BigInt,
    v2_r_m: BigInt,
    u3_r_m: BigInt,
    v3_r_m: BigInt,
    u4_r_m: BigInt,

    u_r_r: BigInt,

    plus_comrand: Option<PlusComRand>
}


#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRChallenge2 {
    ch_u_m: sch::Challenge,
    ch_v_m: sch::Challenge,
    ch_u1_m: sch::Challenge,
    ch_v1_m: sch::Challenge,
    ch_u2_m: sch::Challenge,
    ch_v2_m: sch::Challenge,
    ch_u3_m: sch::Challenge,
    ch_v3_m: sch::Challenge,
    ch_u4_m: sch::Challenge,

    ch_u_r: sch::Challenge,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRResp2 {
    resp_u_m: sch::Response<spp::PPLang>,
    resp_v_m: sch::Response<spp::PPLang>,
    resp_u1_m: sch::Response<spp::PPLang>,
    resp_v1_m: sch::Response<spp::PPLang>,
    resp_u2_m: sch::Response<spp::PPLang>,
    resp_v2_m: sch::Response<spp::PPLang>,
    resp_u3_m: sch::Response<spp::PPLang>,
    resp_v3_m: sch::Response<spp::PPLang>,
    resp_u4_m: sch::Response<spp::PPLang>,

    resp_u_r: sch::Response<spp::PPLang>,
}




fn pedersen_commit(vpk: &VPK, vsk: Option<&VSK>, msg: &BigInt, r: &BigInt) -> BigInt {
    match vsk.as_ref() {
        None => BigInt::mod_mul(&u::bigint_mod_pow(&vpk.g, msg, &vpk.n),
                                &u::bigint_mod_pow(&vpk.h, r, &vpk.n),
                                &vpk.n),
        Some(vsk) => {
            let res_p = BigInt::mod_mul(&u::bigint_mod_pow(&vpk.g, msg, &vsk.p),
                                        &u::bigint_mod_pow(&vpk.h, r, &vsk.p),
                                        &vsk.p);
            let res_q = BigInt::mod_mul(&u::bigint_mod_pow(&vpk.g, msg, &vsk.q),
                                        &u::bigint_mod_pow(&vpk.h, r, &vsk.q),
                                        &vsk.q);
            u::crt_recombine(&res_p,&res_q,&vsk.p,&vsk.q,&vsk.p_inv_q)
        }
    }

}


pub fn prove1(params: &DVRParams, vpk: &VPK, lang: &DVRLang, wit: &DVRWit) -> (DVRCom,DVRComRand) {

    let t_1 = SystemTime::now();

    let t_2 = SystemTime::now();
    ////// For the message, wit.m first

    // Compute com
    let t_m = u::bigint_sample_sym(params.t_range_bitlen);
    let com_m = pedersen_commit(&vpk, None, &wit.m, &t_m);

    //println!("t_m: {:?}", &t_m);
    //println!("wit_m: {:?}", &wit.m);

    // Compute beta
    let r_m = u::bigint_sample_sym(params.r_range_bitlen);
    let sigma_m = u::bigint_sample_sym(params.sigma_range_bitlen);

    //println!("r_m: {:?}", &r_m);
    //println!("sigma_m: {:?}", &sigma_m);
    let beta_m = pedersen_commit(&vpk, None, &r_m, &sigma_m);


    let t_3 = SystemTime::now();

    // Decompose 4 m (R - wit.m) + 1
    let decomp_target = &BigInt::from(4) * &wit.m * (&params.range - &wit.m) + &BigInt::from(1);
    let (x1_m,x2_m,x3_m) = super::squares_decomp::three_squares_decompose(&decomp_target);

    let t_4 = SystemTime::now();

    // Compute commitments to xi
    let t1_m = u::bigint_sample_sym(params.t_range_bitlen);
    let com1_m = pedersen_commit(&vpk, None, &x1_m, &t1_m);
    let t2_m = u::bigint_sample_sym(params.t_range_bitlen);
    let com2_m = pedersen_commit(&vpk, None, &x2_m, &t2_m);
    let t3_m = u::bigint_sample_sym(params.t_range_bitlen);
    let com3_m = pedersen_commit(&vpk, None, &x3_m, &t3_m);

    let t_5 = SystemTime::now();

    // Compute beta_i
    let r1_m = u::bigint_sample_sym(params.r_range_bitlen);
    let sigma1_m = u::bigint_sample_sym(params.sigma_range_bitlen);
    let beta1_m = pedersen_commit(&vpk, None, &r1_m, &sigma1_m);
    let r2_m = u::bigint_sample_sym(params.r_range_bitlen);
    let sigma2_m = u::bigint_sample_sym(params.sigma_range_bitlen);
    let beta2_m = pedersen_commit(&vpk, None, &r2_m, &sigma2_m);
    let r3_m = u::bigint_sample_sym(params.r_range_bitlen);
    let sigma3_m = u::bigint_sample_sym(params.sigma_range_bitlen);
    let beta3_m = pedersen_commit(&vpk, None, &r3_m, &sigma3_m);

    let t_6 = SystemTime::now();

    // Compute tau/beta_4
    let tau_m = u::bigint_sample_sym(params.tau_range_bitlen);
    let beta4_m_args: [&BigInt;5] =
        [&u::bigint_mod_pow(&vpk.h,&tau_m,&vpk.n),
         &u::bigint_mod_pow(&com_m,&(&BigInt::from(4)*&r_m),&vpk.n),
         &u::bigint_mod_pow(&com1_m,&-&r1_m,&vpk.n),
         &u::bigint_mod_pow(&com2_m,&-&r2_m,&vpk.n),
         &u::bigint_mod_pow(&com3_m,&-&r3_m,&vpk.n)
        ];
    let beta4_m: BigInt =
        beta4_m_args.iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n));


    let t_7 = SystemTime::now();

    ////// For the randomness, wit.r

    // Compute com
    let t_r = u::bigint_sample_sym(params.t_range_bitlen);
    let com_r = pedersen_commit(&vpk, None, &wit.r, &t_r);

    let r_r = u::bigint_sample_sym(params.r_range_bitlen);


    //// alpha1 and alpha_2
    let pe::PECiphertext{ct1:alpha1,ct2:alpha2} =
            pe::encrypt_with_randomness_opt(&lang.pk, lang.sk.as_ref(), &r_m, &r_r);


    // Commitment and commitment randomness
    let com = DVRCom {
        com_m, com1_m, com2_m, com3_m, beta_m, beta1_m, beta2_m, beta3_m, beta4_m,
        com_r,
        alpha1, alpha2,
    };
    let comrand = DVRComRand {
        r_m, r1_m, r2_m, r3_m, t_m, t1_m, t2_m, t3_m, x1_m, x2_m, x3_m,
        sigma_m, sigma1_m, sigma2_m, sigma3_m, tau_m,
        r_r, t_r,
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
    if PROFILE_DVR {
        println!("DVR prove1 (total {:?}):
  sample ranges    {:?}
  com & beta       {:?}
  square-decomp    {:?}
  xi coms          {:?}
  beta_i           {:?}
  tau/beta_4       {:?}
  for wit.r        {:?}",
                 t_total,t_delta1, t_delta2, t_delta3, t_delta4, t_delta5, t_delta6, t_delta7);
    }


    (com, comrand)
}

pub fn verify1(params: &DVRParams) -> DVRChallenge1 {
    let b = BigInt::sample(params.lambda as usize);
    DVRChallenge1(b)
}

pub fn prove2(params: &DVRParams,
              vpk: &VPK,
              wit: &DVRWit,
              ch1: &DVRChallenge1,
              cr: &DVRComRand,
              query_ix: usize) -> (DVRResp1,DVRResp1Rand) {
    let t_1 = SystemTime::now();

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_nn: &BigInt = &vpk.pk.nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_nn)),
                        vpk_nn);

    // Computes Enc_pk(enc_arg,rand)*Ct^{ct_exp}
    let p2_generic = |rand: &BigInt,enc_arg: &BigInt,ct_exp: &BigInt|
            super::schnorr_paillier_plus::compute_si(&vpk.pk,None,&ch_ct,enc_arg,rand,ct_exp);

    let t_2 = SystemTime::now();
    ////// For wit.m

    // u, v
    let u_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let u_m = p2_generic(&u_r_m, &cr.r_m, &(&params.range - &wit.m));
    let v_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let v_m = p2_generic(&v_r_m, &cr.sigma_m, &-&cr.t_m);

    // u_i, v_i, i = 1, 2, 3
    let u1_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let u1_m = p2_generic(&u1_r_m, &cr.r1_m, &cr.x1_m);
    let v1_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let v1_m = p2_generic(&v1_r_m, &cr.sigma1_m, &cr.t1_m);

    let u2_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let u2_m = p2_generic(&u2_r_m, &cr.r2_m, &cr.x2_m);
    let v2_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let v2_m = p2_generic(&v2_r_m, &cr.sigma2_m, &cr.t2_m);

    let u3_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let u3_m = p2_generic(&u3_r_m, &cr.r3_m, &cr.x3_m);
    let v3_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let v3_m = p2_generic(&v3_r_m, &cr.sigma3_m, &cr.t3_m);

    // u4
    let u4_r_m = BigInt::sample(params.vpk_n_bitlen as usize);
    let u4_m_exp = &cr.x1_m * &cr.t1_m +
                   &cr.x2_m * &cr.t2_m +
                   &cr.x3_m * &cr.t3_m -
                   &BigInt::from(4) * (&params.range - &wit.m) * &cr.t_m;
    let u4_m =
        p2_generic(&u4_r_m, &cr.tau_m, &u4_m_exp);

    ////// For wit.r

    // u, v
    let u_r_r = BigInt::sample(params.vpk_n_bitlen as usize);
    let u_r = p2_generic(&u_r_r, &cr.r_r, &-&wit.r);

    let t_3 = SystemTime::now();

    let (plus_com,plus_comrand) = if params.ggm_mode { (None,None) } else {
        //// Running the sub-proof
        let spp_params = params.spp_params();
        let spp_lang = spp::PPLang{ n_bitlen: params.vpk_n_bitlen,
                                    pk: vpk.pk.clone(),
                                    sk: None,
                                    ch_ct: ch_ct.clone() };

        let (com_u_m ,comrand_u_m ) = sch::prove1(&spp_params, &spp_lang);
        let (com_v_m ,comrand_v_m ) = sch::prove1(&spp_params, &spp_lang);
        let (com_u1_m,comrand_u1_m) = sch::prove1(&spp_params, &spp_lang);
        let (com_v1_m,comrand_v1_m) = sch::prove1(&spp_params, &spp_lang);
        let (com_u2_m,comrand_u2_m) = sch::prove1(&spp_params, &spp_lang);
        let (com_v2_m,comrand_v2_m) = sch::prove1(&spp_params, &spp_lang);
        let (com_u3_m,comrand_u3_m) = sch::prove1(&spp_params, &spp_lang);
        let (com_v3_m,comrand_v3_m) = sch::prove1(&spp_params, &spp_lang);
        let (com_u4_m,comrand_u4_m) = sch::prove1(&spp_params, &spp_lang);

        let (com_u_r ,comrand_u_r) = sch::prove1(&spp_params, &spp_lang);

        (Some(PlusCom {
            com_u_m ,
            com_v_m ,
            com_u1_m,
            com_v1_m,
            com_u2_m,
            com_v2_m,
            com_u3_m,
            com_v3_m,
            com_u4_m,

            com_u_r }),
         Some(PlusComRand {
             comrand_u_m,
            comrand_v_m,
            comrand_u1_m,
            comrand_v1_m,
            comrand_u2_m,
            comrand_v2_m,
            comrand_u3_m,
            comrand_v3_m,
            comrand_u4_m,
             comrand_u_r}))
    };

    let resp1 =
        DVRResp1 {
            u_m, v_m, u1_m, v1_m, u2_m, v2_m, u3_m, v3_m, u4_m,
            u_r,
            plus_com,
        };
    let resp1_rand =
        DVRResp1Rand {
            u_r_m, v_r_m, u1_r_m, v1_r_m, u2_r_m, v2_r_m, u3_r_m, v3_r_m, u4_r_m,
            u_r_r,
            plus_comrand,
                };



    let t_4 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_total = t_4.duration_since(t_1).unwrap();


    if PROFILE_DVR {
        println!("DVR prove2 (total {:?}):
  challenge      {:?}
  hom responses  {:?}
  non-ggm/prove  {:?}",
                 t_total, t_delta1, t_delta2, t_delta3);
    }



    (resp1,resp1_rand)
}

pub fn verify2(params: &DVRParams) -> Option<DVRChallenge2> {
    if params.ggm_mode { None } else {
    let spp_params = params.spp_params();

    let ch_u_m = sch::verify1(&spp_params);
    let ch_v_m = sch::verify1(&spp_params);
    let ch_u1_m = sch::verify1(&spp_params);
    let ch_v1_m = sch::verify1(&spp_params);
    let ch_u2_m = sch::verify1(&spp_params);
    let ch_v2_m = sch::verify1(&spp_params);
    let ch_u3_m = sch::verify1(&spp_params);
    let ch_v3_m = sch::verify1(&spp_params);
    let ch_u4_m = sch::verify1(&spp_params);

    let ch_u_r = sch::verify1(&spp_params);

    Some(DVRChallenge2 {
        ch_u_m,
        ch_v_m,
        ch_u1_m,
        ch_v1_m,
        ch_u2_m,
        ch_v2_m,
        ch_u3_m,
        ch_v3_m,
        ch_u4_m,

        ch_u_r })
    }
}

pub fn prove3(params: &DVRParams,
              vpk: &VPK,
              wit: &DVRWit,
              ch1: &DVRChallenge1,
              cr: &DVRComRand,
              resp1rand: &DVRResp1Rand,
              ch2: Option<&DVRChallenge2>,
              query_ix: usize) -> Option<DVRResp2> {
    if params.ggm_mode { None } else {

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_nn: &BigInt = &vpk.pk.nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_nn)),
                        vpk_nn);

    //// Running the sub-proof
    let spp_params = params.spp_params();
        let spp_lang = spp::PPLang{ n_bitlen: params.vpk_n_bitlen,
                                    pk: vpk.pk.clone(), sk: None, ch_ct: ch_ct.clone() };

    let spp_reply = |witm: &BigInt, witr: &BigInt, witcexp: &BigInt, ch: &sch::Challenge, comrand: &sch::ComRand<spp::PPLang>| {
            sch::prove2(&spp_params,&spp_lang,
                            &spp::PPLangDom{m: witm.clone(),
                                            r: witr.clone(),
                                            cexp: witcexp.clone()},
                            ch,
                            comrand)
    };

    let ch2_unwrap = ch2.expect("DVRange#prove3: ch2 must be Some");
    let plus_comrand = resp1rand.plus_comrand.clone().expect("DVRange#prove3: plus_comrand must be Some");


    let resp_u_m = spp_reply(&cr.r_m,
                                 &resp1rand.u_r_m,
                                 &(&params.range - &wit.m),
                                 &ch2_unwrap.ch_u_m,
                                 &plus_comrand.comrand_u_m);

    let resp_v_m = spp_reply(&cr.sigma_m,
                                 &resp1rand.v_r_m,
                                 &-&cr.t_m,
                                 &ch2_unwrap.ch_v_m,
                                 &plus_comrand.comrand_v_m);

    let resp_u1_m = spp_reply(&cr.r1_m,
                                  &resp1rand.u1_r_m,
                                  &cr.x1_m,
                                  &ch2_unwrap.ch_u1_m,
                                  &plus_comrand.comrand_u1_m);
    let resp_v1_m = spp_reply(&cr.sigma1_m,
                                  &resp1rand.v1_r_m,
                                  &cr.t1_m,
                                  &ch2_unwrap.ch_v1_m,
                                  &plus_comrand.comrand_v1_m);

    let resp_u2_m = spp_reply(&cr.r2_m,
                                  &resp1rand.u2_r_m,
                                  &cr.x2_m,
                                  &ch2_unwrap.ch_u2_m,
                                  &plus_comrand.comrand_u2_m);
    let resp_v2_m = spp_reply(&cr.sigma2_m,
                                  &resp1rand.v2_r_m,
                                  &cr.t2_m,
                                  &ch2_unwrap.ch_v2_m,
                                  &plus_comrand.comrand_v2_m);

    let resp_u3_m = spp_reply(&cr.r3_m,
                                  &resp1rand.u3_r_m,
                                  &cr.x3_m,
                                  &ch2_unwrap.ch_u3_m,
                                  &plus_comrand.comrand_u3_m);
    let resp_v3_m = spp_reply(&cr.sigma3_m,
                                  &resp1rand.v3_r_m,
                                  &cr.t3_m,
                                  &ch2_unwrap.ch_v3_m,
                                  &plus_comrand.comrand_v3_m);

    let resp_u4_m = spp_reply(&cr.tau_m,
                                  &resp1rand.u4_r_m,
                                  &(&cr.x1_m * &cr.t1_m +
                                    &cr.x2_m * &cr.t2_m +
                                    &cr.x3_m * &cr.t3_m -
                                    &BigInt::from(4) * (&params.range - &wit.m) * &cr.t_m),
                                  &ch2_unwrap.ch_u4_m,
                                  &plus_comrand.comrand_u4_m);


    let resp_u_r = spp_reply(&cr.r_r,
                                 &resp1rand.u_r_r,
                                 &-&wit.r,
                                 &ch2_unwrap.ch_u_r,
                                 &plus_comrand.comrand_u_r);

    Some(DVRResp2 {
        resp_u_m,
        resp_v_m,
        resp_u1_m,
        resp_v1_m,
        resp_u2_m,
        resp_v2_m,
        resp_u3_m,
        resp_v3_m,
        resp_u4_m,

        resp_u_r,
    })
    }
}

pub fn verify3(params: &DVRParams,
               vsk: &VSK,
               vpk: &VPK,
               lang: &DVRLang,
               inst: &DVRInst,
               com: &DVRCom,
               ch1: &DVRChallenge1,
               resp1: &DVRResp1,
               ch2: Option<&DVRChallenge2>,
               resp2: Option<&DVRResp2>,
               query_ix: usize) -> bool {
    let t_1 = SystemTime::now();

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_nn: &BigInt = &vpk.pk.nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_nn)),
                        vpk_nn);

    let ch_raw: BigInt =
        &vsk.chs[(params.lambda as usize) + query_ix] +
        ch1_active_bits.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );


    let paillier_decrypt = |target: &BigInt| {
        let res = Paillier::decrypt(&vsk.sk,RawCiphertext::from(target)).0.into_owned();
        if &res >= &(&vpk.pk.n / BigInt::from(2)) { &res - &vpk.pk.n } else { res }
    };


    let t_2 = SystemTime::now();
    let u_m_plain = paillier_decrypt(&resp1.u_m);
    let v_m_plain  = paillier_decrypt(&resp1.v_m);
    let u1_m_plain = paillier_decrypt(&resp1.u1_m);
    let v1_m_plain = paillier_decrypt(&resp1.v1_m);
    let u2_m_plain = paillier_decrypt(&resp1.u2_m);
    let v2_m_plain = paillier_decrypt(&resp1.v2_m);
    let u3_m_plain = paillier_decrypt(&resp1.u3_m);
    let v3_m_plain = paillier_decrypt(&resp1.v3_m);
    let u4_m_plain = paillier_decrypt(&resp1.u4_m);
    let u_r_plain = paillier_decrypt(&resp1.u_r);
    let t_3 = SystemTime::now();

    // Perform the _m checks
    {
        let ui_range = BigInt::pow(&BigInt::from(2),params.ui_range_bitlen);
        if !u::bigint_in_range_sym(&ui_range,&u1_m_plain) ||
            !u::bigint_in_range_sym(&ui_range,&u2_m_plain) ||
            !u::bigint_in_range_sym(&ui_range,&u3_m_plain) {
                println!("DVRange#verify3: range check 1 failed");
                println!("{:?}", ui_range);
                println!("{:?}", u1_m_plain);
                println!("{:?}", u2_m_plain);
                println!("{:?}", u3_m_plain);
                println!("{:?}", vpk.pk.n);
                return false;
            }

        let com_m_inv = BigInt::mod_inv(&com.com_m,&vpk.n).unwrap();
        let eq1_lhs_p =
            BigInt::mod_mul(
                &com.beta_m,
                &u::bigint_mod_pow(
                    &(&com_m_inv *
                      &u::bigint_mod_pow(&vpk.g,&params.range,&vsk.p)),
                    &ch_raw,
                    &vsk.p),
                &vsk.p);
        let eq1_lhs_q =
            BigInt::mod_mul(
                &com.beta_m,
                &u::bigint_mod_pow(
                    &(&com_m_inv *
                      &u::bigint_mod_pow(&vpk.g,&params.range,&vsk.q)),
                    &ch_raw,
                    &vsk.q),
                &vsk.q);
        let eq1_lhs = u::crt_recombine(&eq1_lhs_p,&eq1_lhs_q,&vsk.p,&vsk.q,&vsk.p_inv_q);
        let eq1_rhs = pedersen_commit(&vpk, Some(&vsk), &u_m_plain, &v_m_plain);
        if eq1_lhs != eq1_rhs {
            println!("DVRange#verify3: 1 eq1");
            return false;
        }


        let eq21_lhs_p =
            BigInt::mod_mul(&com.beta1_m,
                            &u::bigint_mod_pow(&com.com1_m,&ch_raw,&vsk.p),
                            &vsk.p);
        let eq21_lhs_q =
            BigInt::mod_mul(&com.beta1_m,
                            &u::bigint_mod_pow(&com.com1_m,&ch_raw,&vsk.q),
                            &vsk.q);
        let eq21_lhs = u::crt_recombine(&eq21_lhs_p,&eq21_lhs_q,&vsk.p,&vsk.q,&vsk.p_inv_q);
        let eq21_rhs = pedersen_commit(&vpk, Some(&vsk), &u1_m_plain, &v1_m_plain);
        if eq21_lhs != eq21_rhs {
            println!("DVRange#verify3: 1 eq21");
            return false;
        }

        let eq22_lhs_p =
            BigInt::mod_mul(&com.beta2_m,
                            &u::bigint_mod_pow(&com.com2_m,&ch_raw,&vsk.p),
                            &vsk.p);
        let eq22_lhs_q =
            BigInt::mod_mul(&com.beta2_m,
                            &u::bigint_mod_pow(&com.com2_m,&ch_raw,&vsk.q),
                            &vsk.q);
        let eq22_lhs = u::crt_recombine(&eq22_lhs_p,&eq22_lhs_q,&vsk.p,&vsk.q,&vsk.p_inv_q);
        let eq22_rhs = pedersen_commit(&vpk, Some(&vsk), &u2_m_plain, &v2_m_plain);
        if eq22_lhs != eq22_rhs {
            println!("DVRange#verify3: 1 eq22");
            return false;
        }

        let eq23_lhs_p =
            BigInt::mod_mul(&com.beta3_m,
                            &u::bigint_mod_pow(&com.com3_m,&ch_raw,&vsk.p),
                            &vsk.p);
        let eq23_lhs_q =
            BigInt::mod_mul(&com.beta3_m,
                            &u::bigint_mod_pow(&com.com3_m,&ch_raw,&vsk.q),
                            &vsk.q);
        let eq23_lhs = u::crt_recombine(&eq23_lhs_p,&eq23_lhs_q,&vsk.p,&vsk.q,&vsk.p_inv_q);
        let eq23_rhs = pedersen_commit(&vpk, Some(&vsk), &u3_m_plain, &v3_m_plain);
        if eq23_lhs != eq23_rhs {
            println!("DVRange#verify3: 1 eq23");
            return false;
        }

        let eq3_lhs_p =
            BigInt::mod_mul(
                &com.beta4_m,
                &([&u::bigint_mod_pow(&com.com1_m,&u1_m_plain,&vsk.p),
                   &u::bigint_mod_pow(&com.com2_m,&u2_m_plain,&vsk.p),
                   &u::bigint_mod_pow(&com.com3_m,&u3_m_plain,&vsk.p),
                ].iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vsk.p))),
                &vsk.p);
        let eq3_lhs_q =
            BigInt::mod_mul(
                &com.beta4_m,
                &([&u::bigint_mod_pow(&com.com1_m,&u1_m_plain,&vsk.q),
                   &u::bigint_mod_pow(&com.com2_m,&u2_m_plain,&vsk.q),
                   &u::bigint_mod_pow(&com.com3_m,&u3_m_plain,&vsk.q),
                ].iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vsk.q))),
                &vsk.q);
        let eq3_lhs = u::crt_recombine(&eq3_lhs_p,&eq3_lhs_q,&vsk.p,&vsk.q,&vsk.p_inv_q);
        let eq3_rhs = BigInt::mod_mul(
            &pedersen_commit(&vpk, Some(&vsk), &ch_raw, &u4_m_plain),
            &u::bigint_mod_pow(&com.com_m,&(BigInt::from(4) * &u_m_plain),&vpk.n),
            &vpk.n
        );
        if eq3_lhs != eq3_rhs {
            println!("DVRange#verify3: 1 eq3");
            return false;
        }

    }
    let t_4 = SystemTime::now();


    // perform the alpha check
    {
        let pe::PECiphertext{ct1:rhs_1,ct2:rhs_2} =
            pe::encrypt_with_randomness_opt(&lang.pk, None, &u_m_plain, &u_r_plain);

        // both (R,0) and (R,R) should work, depending on how u_r is constructed
        let pe::PECiphertext{ct1:psi_range_1,ct2:psi_range_2} =
            pe::encrypt_with_randomness_opt(&lang.pk, None, &params.range, &BigInt::from(0));
            //pe::encrypt_with_randomness(&lang.pk, &params.range, lang.range_rand());

        let lhs_1 =
            BigInt::mod_mul(&com.alpha1,
                            &u::bigint_mod_pow(
                                &BigInt::mod_mul(
                                    &BigInt::mod_inv(&inst.ct.ct1,&lang.pk.nn).unwrap(),
                                    &psi_range_1,
                                    &lang.pk.nn),
                                &ch_raw,
                                &lang.pk.nn),
                            &lang.pk.nn);

        if lhs_1 != rhs_1 {
            println!("DVRange#verify3: alpha 1");
            return false; }

        let lhs_2 =
            BigInt::mod_mul(&com.alpha2,
                            &u::bigint_mod_pow(
                                &BigInt::mod_mul(
                                    &BigInt::mod_inv(&inst.ct.ct2,&lang.pk.nn).unwrap(),
                                    &psi_range_2,
                                    &lang.pk.nn),
                                &ch_raw,
                                &lang.pk.nn),
                            &lang.pk.nn);

        if lhs_2 != rhs_2 {
            println!("DVRange#verify3: alpha 2");
            return false; }
    }
    let t_5 = SystemTime::now();


    // Check the sub-protocol replies, for the schnorr-paillier plus
    if !params.ggm_mode {
        let spp_params = params.spp_params();
        let spp_lang = spp::PPLang{ n_bitlen: params.vpk_n_bitlen,
                                    pk: vpk.pk.clone(),
                                    sk: Some(vsk.sk.clone()),
                                    ch_ct: ch_ct.clone() };
        let plus_com = resp1.plus_com.clone().expect("DVRange#verify3 plus_com must be Some");
        let plus_ch = ch2.expect("DVRange#verify3 ch2 must be Some");
        let plus_resp = resp2.expect("DVRange#verify3 resp2 must be Some");

        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.u_m.clone()},
                             &plus_com.com_u_m,
                             &plus_ch.ch_u_m,
                             &plus_resp.resp_u_m)
        { println!("DVRange#verify3: spp 1"); return false; }

        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.v_m.clone()},
                             &plus_com.com_v_m,
                             &plus_ch.ch_v_m,
                             &plus_resp.resp_v_m)
        { println!("DVRange#verify3: spp 2");  return false; }

        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.u1_m.clone()},
                             &plus_com.com_u1_m,
                             &plus_ch.ch_u1_m,
                             &plus_resp.resp_u1_m)
        { println!("DVRange#verify3: spp 3");  return false; }
        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.v1_m.clone()},
                             &plus_com.com_v1_m,
                             &plus_ch.ch_v1_m,
                             &plus_resp.resp_v1_m)
        { println!("DVRange#verify3: spp 4");  return false; }
        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.u2_m.clone()},
                             &plus_com.com_u2_m,
                             &plus_ch.ch_u2_m,
                             &plus_resp.resp_u2_m)
        { println!("DVRange#verify3: spp 5");  return false; }
        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.v2_m.clone()},
                             &plus_com.com_v2_m,
                             &plus_ch.ch_v2_m,
                             &plus_resp.resp_v2_m)
        { println!("DVRange#verify3: spp 6");  return false; }
        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.u3_m.clone()},
                             &plus_com.com_u3_m,
                             &plus_ch.ch_u3_m,
                             &plus_resp.resp_u3_m)
        { println!("DVRange#verify3: spp 7");  return false; }
        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.v3_m.clone()},
                             &plus_com.com_v3_m,
                             &plus_ch.ch_v3_m,
                             &plus_resp.resp_v3_m)
        { println!("DVRange#verify3: spp 8");  return false; }

        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.u4_m.clone()},
                             &plus_com.com_u4_m,
                             &plus_ch.ch_u4_m,
                             &plus_resp.resp_u4_m)
        { println!("DVRange#verify3: spp 9");  return false; }

        if !sch::verify2(&spp_params,&spp_lang,
                             &spp::PPLangCoDom{si:resp1.u_r.clone()},
                             &plus_com.com_u_r,
                             &plus_ch.ch_u_r,
                             &plus_resp.resp_u_r)
        { println!("DVRange#verify3: spp 10");  return false; }

    }


    let t_6 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_delta5 = t_6.duration_since(t_5).unwrap();
    let t_total = t_5.duration_since(t_1).unwrap();


    if PROFILE_DVR {
        println!("DVR verify3 (total {:?}):
  challenge     {:?}
  decryptions   {:?}
  com checks    {:?}
  alpha checks  {:?}
  non-ggm       {:?}",
                 t_total, t_delta1, t_delta2, t_delta3, t_delta4, t_delta5);
    }


    true
}



////////////////////////////////////////////////////////////////////////////
// Fiat-Shamir variant
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug, Serialize)]
pub struct FSDVRProof {
    com : DVRCom,
    resp1 : DVRResp1,
    resp2 : Option<DVRResp2>,
}

// Returns a lambda-bit bigint equal to the first bits of Blake2b(hash_input)
fn fs_to_bigint(params: &DVRParams,
                hash_input: &Vec<u8>) -> BigInt {

    use blake2::*;
    let mut hasher: Blake2b = Digest::new();
    hasher.update(hash_input);
    let r0 = hasher.finalize(); // the result is u8 array of size 64
    let bigint = Converter::from_bytes(&r0[0..(params.lambda as usize) / 8 - 1]);

    bigint
}

fn fs_compute_challenge_1(params: &DVRParams,
                          lang: &DVRLang,
                          inst: &DVRInst,
                          com: &DVRCom) -> DVRChallenge1 {
    let x: Vec<u8> = rmp_serde::to_vec(&(com, inst, lang)).unwrap();
    let ch1 = fs_to_bigint(params, &x);
    DVRChallenge1(ch1)
}

fn fs_compute_challenge_2(params: &DVRParams,
                          lang: &DVRLang,
                          inst: &DVRInst,
                          com: &DVRCom,
                          ch1: &DVRChallenge1,
                          resp1: &DVRResp1) -> Option<DVRChallenge2> {
    if params.ggm_mode { None } else {
    let common_prefix: Vec<u8> = rmp_serde::to_vec(
            &(params, lang, inst, com, ch1,
              &resp1.u_m,
              &resp1.v_m,
              &resp1.u1_m,
              &resp1.v1_m,
              &resp1.u2_m,
              &resp1.v2_m,
              &resp1.u3_m,
              &resp1.v3_m,
              &resp1.u4_m,
              &resp1.u_r)).unwrap();

    let get_ch = |resp: &sch::Commitment<spp::PPLang>| {
        let x: Vec<u8> = rmp_serde::to_vec(&(com, ch1, resp1, inst, lang, resp)).unwrap();
        fs_to_bigint(params, &([common_prefix.clone(),x].concat()))
    };
    let plus_com = resp1.plus_com.clone().expect("DVRange#verify3 plus_com must be Some");
    let ch_u_m  = sch::Challenge(vec![get_ch(&plus_com.com_u_m)]);
    let ch_v_m  = sch::Challenge(vec![get_ch(&plus_com.com_v_m)]);
    let ch_u1_m = sch::Challenge(vec![get_ch(&plus_com.com_u1_m)]);
    let ch_v1_m = sch::Challenge(vec![get_ch(&plus_com.com_v1_m)]);
    let ch_u2_m = sch::Challenge(vec![get_ch(&plus_com.com_u2_m)]);
    let ch_v2_m = sch::Challenge(vec![get_ch(&plus_com.com_v2_m)]);
    let ch_u3_m = sch::Challenge(vec![get_ch(&plus_com.com_u3_m)]);
    let ch_v3_m = sch::Challenge(vec![get_ch(&plus_com.com_v3_m)]);
    let ch_u4_m = sch::Challenge(vec![get_ch(&plus_com.com_u4_m)]);
    let ch_u_r  = sch::Challenge(vec![get_ch(&plus_com.com_u_r)]);

    Some(DVRChallenge2 {
        ch_u_m,
        ch_v_m,
        ch_u1_m,
        ch_v1_m,
        ch_u2_m,
        ch_v2_m,
        ch_u3_m,
        ch_v3_m,
        ch_u4_m,

        ch_u_r })}

}

pub fn fs_prove(params: &DVRParams,
                vpk: &VPK,
                lang: &DVRLang,
                inst: &DVRInst,
                wit: &DVRWit,
                query_ix: usize) -> FSDVRProof {
    let (com,cr) = prove1(params,vpk,lang,wit);
    let ch1 = fs_compute_challenge_1(params,lang,inst,&com);
    let (resp1,resp1rand) = prove2(&params,&vpk,&wit,&ch1,&cr,query_ix);
    let ch2 = fs_compute_challenge_2(&params,lang,inst,&com,&ch1,&resp1);
    let resp2 = prove3(params,vpk,wit,&ch1,&cr,&resp1rand,ch2.as_ref(),query_ix);

    FSDVRProof{ com, resp1, resp2 }
}


pub fn fs_verify(params: &DVRParams,
                 vsk: &VSK,
                 vpk: &VPK,
                 lang: &DVRLang,
                 inst: &DVRInst,
                 query_ix: usize,
                 proof: &FSDVRProof) -> bool {

    let ch1 = fs_compute_challenge_1(params,lang,inst,&proof.com);
    let ch2 = fs_compute_challenge_2(&params,lang,inst,&proof.com,&ch1,&proof.resp1);

    verify3(&params,&vsk,&vpk,&lang,&inst,
            &proof.com,&ch1,&proof.resp1,ch2.as_ref(),proof.resp2.as_ref(),query_ix)
}


////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////


pub fn test_correctness_fs() {
    let queries:usize = 32;
    let range_bitlen = 256;
    let params = DVRParams::new(1024, 128, range_bitlen, queries as u32, false, false);

    println!("keygen...");
    let (vpk,vsk) = keygen(&params);
    println!("verifying vpk...");
    assert!(verify_vpk(&params,&vpk));

    for query_ix in 0..queries {
        let (lang,inst,wit) = sample_liw(&params);

        let proof = fs_prove(&params,&vpk,&lang,&inst,&wit,query_ix);
        assert!(fs_verify(&params,&vsk,&vpk,&lang,&inst,query_ix,&proof));
    }
}


pub fn test_keygen_correctness() {
    for ggm_mode in [false,true] {
        for malicious_vpk in [false,true] {
    let range_bitlen = 256;
    let params = DVRParams::new(2048, 128, range_bitlen, 32, malicious_vpk, ggm_mode);

    let t_start = SystemTime::now();
    let (vpk,_vsk) = keygen(&params);
    let t_2 = SystemTime::now();
    if malicious_vpk { verify_vpk(&params,&vpk); };
    let t_end = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_start).expect("error1");
    let t_delta2 = t_end.duration_since(t_2).expect("error2");
    println!("{:?}", params);
            println!("keygen: {:?}, verify: {:?}", t_delta1, t_delta2);
        }}
}



#[cfg(test)]
mod tests {
    use crate::protocols::designated_range::*;
    use crate::protocols::designated as dv;
    use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation};
    use curv::BigInt;

    #[test]
    fn keygen_correctness() {
        let range_bitlen = 256;
        let n_bitlen = 1024;
        let lambda = 64;
        let crs_uses = lambda;
        let params = DVRParams::new(n_bitlen, crs_uses, range_bitlen, crs_uses, true, false);

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }

    #[test]
    fn correctness() {
        for ggm_mode in [false,true] {
        let queries:usize = 128;
        let range_bitlen = 256;
        let params = DVRParams::new(256, 32, range_bitlen, queries as u32, false, ggm_mode);

        let (vpk,vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));

        for query_ix in 0..queries {
            println!("Query #{:?}", query_ix);
            let (lang,inst,wit) = sample_liw(&params);

            println!("Prove1");
            let (com,cr) = prove1(&params,&vpk,&lang,&wit);
            println!("Verify1");
            let ch1 = verify1(&params);
            println!("Prove2");
            let (resp1,resp1rand) = prove2(&params,&vpk,&wit,&ch1,&cr,query_ix);
            println!("Verify2");
            let ch2 = verify2(&params);
            println!("Prove3");
            let resp2 = prove3(&params,&vpk,&wit,&ch1,&cr,&resp1rand,ch2.as_ref(),query_ix);

            assert!(verify3(&params,&vsk,&vpk,&lang,&inst,
                            &com,&ch1,&resp1,ch2.as_ref(),resp2.as_ref(),query_ix));
        }}
    }

    #[test]
    fn fs_correctness() {
        for ggm_mode in [false,true] {
            let queries:usize = 32;
            let range_bitlen = 256;
            let params = DVRParams::new(1024, 128, range_bitlen, queries as u32, false, ggm_mode);

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
