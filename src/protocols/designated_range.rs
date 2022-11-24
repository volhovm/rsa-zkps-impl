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

use super::utils as u;
use super::schnorr_paillier_batched as spb;
use super::schnorr_paillier_plus as sp_plus;
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;
use super::schnorr_exp as se;


#[derive(Clone, Debug, Serialize)]
pub struct DVRParams {
    /// N of the prover (of the homomorphism psi), bit length
    pub psi_n_bitlen: u32,
    /// Security parameter
    pub lambda: u32,
    /// Range we're proving
    pub range: BigInt,
    /// The number of CRS reuses
    pub crs_uses: u32,
    /// Whether malicious setup (that introduces VPK proofs) is enabled
    pub malicious_setup: bool,
    /// Whether the GGM mode is enabled, which omits certain proof parts
    pub ggm_mode: bool,
}

impl DVRParams {

    pub fn new(psi_n_bitlen: u32,
               lambda: u32,
               range: BigInt,
               crs_uses: u32,
               malicious_setup: bool,
               ggm_mode: bool
               ) -> DVRParams {
        DVRParams{psi_n_bitlen, lambda, range, crs_uses, malicious_setup, ggm_mode}
    }

    /// Parameters for the Gen g/h NIZK proof.
    pub fn nizk_se_params(&self) -> se::ProofParams {
        let repbits = 15;
        se::ProofParams::new(self.psi_n_bitlen,
                             self.lambda,
                             repbits)
    }

    /// The size of honestly generated challenges (first λ).
    fn ch_small_bitlen(&self) -> u32 { self.lambda }

    /// The size of honestly generated challenges (λ+1 ... λ+Q) for Q number of queries.
    fn ch_big_bitlen(&self) -> u32 {
        // lambda bits more than sum of lambda small challenges
        self.lambda + self.ch_small_bitlen() + u::log2ceil(self.lambda)
    }

    /// Maximum size of the summed-up challenge, real.
    pub fn max_ch_bitlen(&self) -> u32 {
        if self.crs_uses == 0 {
            // because we sum ch_small_bitlen lambda times
            self.ch_small_bitlen() + u::log2ceil(self.lambda)
        } else {
            // Just ch_big_bitlen, because it masks ch_small_bitlen fully.
            self.ch_big_bitlen()
        }
    }

    /// Maximum size of the summed-up challenge, after considering VPK proof slack.
    pub fn max_ch_proven_bitlen(&self) -> u32 {
        let slack = if self.malicious_setup { self.range_slack_bitlen() } else { 0 };
        self.max_ch_bitlen() + slack + 1
    }

    /// Bit length of the third N, wrt which VPK.n is constructed.
    pub fn n_bitlen(&self) -> u32 {
        self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda + 2
    }


    // M should be bigger than r + cw, but r should hide cw perfectly;
    // so cw is always negligibly smaller than r. We could just take M
    // to be n and achieve statistical completeness in this respect,
    // but adding one extra bit will give us perfect completeness,
    // because now r + cw < 2 r.
    pub fn vpk_n_bitlen(&self) -> u32 {
        // It basically needs to hide tau
        self.max_ch_proven_bitlen() + 2*self.lambda + self.n_bitlen() +
            (BigInt::bit_length(&(BigInt::from(7) * &self.range)) as u32)
        //u::log2ceil(self.lambda) + 5 * self.lambda + self.crs_uses - 1 +
        //    self.n_bitlen() +
        //    (BigInt::bit_length(&(&BigInt::from(3) * &Roots::sqrt(&self.range) +
        //                         &BigInt::from(4) * &self.range)) as u32)

        //std::cmp::max(self.rand_m_bitlen(),self.rand_r_bitlen()) + 2
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

    /// Range slack of the batched range proof.
    pub fn range_slack_bitlen(&self) -> u32 {
        2 * self.lambda + u::log2ceil(self.lambda) - 1
    }

    /// Parameters for the schnorr-paillier+ sub-protocol
    pub fn sp_plus_params(&self) -> sp_plus::ProofParams {
        sp_plus::ProofParams::new(self.vpk_n_bitlen(), self.lambda, self.lambda)
    }

}


#[derive(Clone, Debug, Serialize)]
pub struct DVRLang { pub pk: pe::PEPublicKey }

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
    let (pk,_sk) = pe::keygen(params.psi_n_bitlen as usize);
    DVRLang{pk}
}

pub fn sample_inst(params: &DVRParams, lang: &DVRLang) -> (DVRInst,DVRWit) {
    let m = BigInt::sample_below(&params.range);
    let r = BigInt::sample_below(&lang.pk.n);
    let ct = pe::encrypt_with_randomness(&lang.pk,&m,&r);
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


#[derive(Clone, Debug)]
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
}


#[derive(Clone, Debug)]
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

    /// Proof of N = pk.n having gcd(N,phi(N)) = 1.
    pub nizk_gcd: n_gcd::Proof,
    /// Proofs of correctness+range of cts.
    pub nizks_ct: Vec<spb::FSProof>,
    /// Schnorr proof of g/h
    pub nizk_gen: se::FSProof,
}


pub fn keygen(params: &DVRParams) -> (VPK, VSK) {
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
        chs.iter().zip(rs.iter()).map(|(ch,r)|
            Paillier::encrypt_with_chosen_randomness(
                &pk,
                RawPlaintext::from(ch),
                &Randomness::from(r)).0.into_owned())
        .collect();

    let lang = spb::Lang{pk:pk.clone()};

    let nizk_gcd: n_gcd::Proof =
        n_gcd::prove(
            &params.nizk_gcd_params(),
            &n_gcd::Inst{ n: pk.n.clone() },
            &n_gcd::Wit{ p: sk.p.clone(), q: sk.q.clone() }
            );

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
                cts_inst.push(Paillier::encrypt_with_chosen_randomness(
                    &pk,
                    RawPlaintext::from(BigInt::from(0)),
                    &Randomness::from(BigInt::from(1))).0.into_owned());
            }
        }

        let params = if i == 0 { params.nizk_ct_params_1() }
                     else { params.nizk_ct_params_2() };
        let inst = spb::Inst{cts: cts_inst};
        let wit = spb::Wit{ms: ms_wit, rs: rs_wit};

        nizks_ct.push(spb::fs_prove(&params, &lang, &inst, &wit));
    }


    let (pk_,sk_) =
        Paillier::keypair_with_modulus_size(params.n_bitlen() as usize).keys();
    let n = pk_.n.clone();
    let p = sk_.p.clone();
    let q = sk_.q.clone();

    let h = BigInt::sample_below(&n);
    let phi = (&p-1) * (&q-1);
    let f = BigInt::sample_below(&phi);
    let g = u::bigint_mod_pow(&h, &f, &n);
    let nizk_gen = se::fs_prove(
        &params.nizk_se_params(),
        &se::Lang{n: n.clone(), h: h.clone()},
        &se::Inst{g: g.clone()},
        &se::Wit{x: f.clone()});

    let vsk = VSK{f, p, q, sk, chs};
    let vpk = VPK{n, g, h, nizk_gen, pk, cts, nizk_gcd, nizks_ct};
    (vpk,vsk)
}


pub fn verify_vpk(params: &DVRParams, vpk: &VPK) -> bool {
    let res1 = n_gcd::verify(
        &params.nizk_gcd_params(),
        &n_gcd::Inst{ n: vpk.pk.n.clone() },
        &vpk.nizk_gcd);
    if !res1 { return false; }

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

        let params =
            if i == 0 { params.nizk_ct_params_1() }
            else { params.nizk_ct_params_2() };
        let inst = spb::Lang{ pk: vpk.pk.clone() };
        let wit = spb::Inst{ cts: cts_w };

        let res2 = spb::fs_verify(&params, &inst, &wit, &vpk.nizks_ct[i as usize]);
        if !res2 { return false; }
    }

    if !se::fs_verify(&params.nizk_se_params(),
                      &se::Lang{n: vpk.n.clone(), h: vpk.h.clone()},
                      &se::Inst{g: vpk.g.clone()},
                      &se::VerifierPrecomp(None),
                      &vpk.nizk_gen) { return false; }

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
    com_u_m: sp_plus::Commitment,
    com_v_m: sp_plus::Commitment,
    com_u1_m: sp_plus::Commitment,
    com_v1_m: sp_plus::Commitment,
    com_u2_m: sp_plus::Commitment,
    com_v2_m: sp_plus::Commitment,
    com_u3_m: sp_plus::Commitment,
    com_v3_m: sp_plus::Commitment,
    com_u4_m: sp_plus::Commitment,

    com_u_r: sp_plus::Commitment,
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
    comrand_u_m: sp_plus::ComRand,
    comrand_v_m: sp_plus::ComRand,
    comrand_u1_m: sp_plus::ComRand,
    comrand_v1_m: sp_plus::ComRand,
    comrand_u2_m: sp_plus::ComRand,
    comrand_v2_m: sp_plus::ComRand,
    comrand_u3_m: sp_plus::ComRand,
    comrand_v3_m: sp_plus::ComRand,
    comrand_u4_m: sp_plus::ComRand,

    comrand_u_r: sp_plus::ComRand,
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
    ch_u_m: sp_plus::Challenge,
    ch_v_m: sp_plus::Challenge,
    ch_u1_m: sp_plus::Challenge,
    ch_v1_m: sp_plus::Challenge,
    ch_u2_m: sp_plus::Challenge,
    ch_v2_m: sp_plus::Challenge,
    ch_u3_m: sp_plus::Challenge,
    ch_v3_m: sp_plus::Challenge,
    ch_u4_m: sp_plus::Challenge,

    ch_u_r: sp_plus::Challenge,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRResp2 {
    resp_u_m: sp_plus::Response,
    resp_v_m: sp_plus::Response,
    resp_u1_m: sp_plus::Response,
    resp_v1_m: sp_plus::Response,
    resp_u2_m: sp_plus::Response,
    resp_v2_m: sp_plus::Response,
    resp_u3_m: sp_plus::Response,
    resp_v3_m: sp_plus::Response,
    resp_u4_m: sp_plus::Response,

    resp_u_r: sp_plus::Response,
}




fn pedersen_commit(vpk: &VPK, msg: &BigInt, r: &BigInt) -> BigInt {
    BigInt::mod_mul(
        &u::bigint_mod_pow(&vpk.g, msg, &vpk.n),
        &u::bigint_mod_pow(&vpk.h, r, &vpk.n),
        &vpk.n)
}


pub fn prove1(params: &DVRParams, vpk: &VPK, lang: &DVRLang, wit: &DVRWit) -> (DVRCom,DVRComRand) {

    // maximum challenge possible, c
    let max_ch = BigInt::pow(&BigInt::from(2),params.max_ch_proven_bitlen());
    // 2^{λ-1}N
    let t_range = &BigInt::pow(&BigInt::from(2),params.lambda - 1) * &vpk.n;
    // must blind c*(R-m)
    let r_range = &max_ch * &params.range;
    // must blind c*t
    let sigma_range = &max_ch * &t_range;
    // must blind c*x_i, where each x_i is at most R. So it's same as r_range
    let ri_range = &r_range;
    // must blind c*t_i, but t_i is same as t
    let sigmai_range = &sigma_range;
    // must blind c*(3*xi*ti-4Rt) <= c * 7 R t
    let tau_range = &max_ch * &BigInt::from(7) * &t_range * &params.range;

    ////// For the message, wit.m first

    // Compute com
    let t_m = u::bigint_sample_below_sym(&t_range);
    let com_m = pedersen_commit(&vpk, &wit.m, &t_m);

    //println!("t_m: {:?}", &t_m);
    //println!("wit_m: {:?}", &wit.m);

    // Compute beta
    let r_m = u::bigint_sample_below_sym(&r_range);
    let sigma_m = u::bigint_sample_below_sym(&sigma_range);

    //println!("r_m: {:?}", &r_m);
    //println!("sigma_m: {:?}", &sigma_m);
    let beta_m = pedersen_commit(&vpk, &r_m, &sigma_m);

    // Decompose 4 m (R - wit.m) + 1
    let decomp_target = &BigInt::from(4) * &wit.m * (&params.range - &wit.m) + &BigInt::from(1);
    let (x1_m,x2_m,x3_m) = super::squares_decomp::three_squares_decompose(&decomp_target);

    // Compute commitments to xi
    let t1_m = u::bigint_sample_below_sym(&t_range);
    let com1_m = pedersen_commit(&vpk, &x1_m, &t1_m);
    let t2_m = u::bigint_sample_below_sym(&t_range);
    let com2_m = pedersen_commit(&vpk, &x2_m, &t2_m);
    let t3_m = u::bigint_sample_below_sym(&t_range);
    let com3_m = pedersen_commit(&vpk, &x3_m, &t3_m);

    // Compute beta_i
    let r1_m = u::bigint_sample_below_sym(&ri_range);
    let sigma1_m = u::bigint_sample_below_sym(&sigmai_range);
    let beta1_m = pedersen_commit(&vpk, &r1_m, &sigma1_m);
    let r2_m = u::bigint_sample_below_sym(&ri_range);
    let sigma2_m = u::bigint_sample_below_sym(&sigmai_range);
    let beta2_m = pedersen_commit(&vpk, &r2_m, &sigma2_m);
    let r3_m = u::bigint_sample_below_sym(&ri_range);
    let sigma3_m = u::bigint_sample_below_sym(&sigmai_range);
    let beta3_m = pedersen_commit(&vpk, &r3_m, &sigma3_m);

    // Compute tau/beta_4
    let tau_m = u::bigint_sample_below_sym(&tau_range);
    let beta4_m_args: [&BigInt;5] =
        [&u::bigint_mod_pow(&vpk.h,&tau_m,&vpk.n),
         &u::bigint_mod_pow(&com_m,&(&BigInt::from(4)*&r_m),&vpk.n),
         &u::bigint_mod_pow(&com1_m,&-&r1_m,&vpk.n),
         &u::bigint_mod_pow(&com2_m,&-&r2_m,&vpk.n),
         &u::bigint_mod_pow(&com3_m,&-&r3_m,&vpk.n)
        ];
    let beta4_m: BigInt =
        beta4_m_args.iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n));


    ////// For the randomness, wit.r

    // Compute com
    let t_r = u::bigint_sample_below_sym(&t_range);
    let com_r = pedersen_commit(&vpk, &wit.r, &t_r);

    let r_r = u::bigint_sample_below_sym(&r_range);

    //// alpha1 and alpha_2
    let pe::PECiphertext{ct1:alpha1,ct2:alpha2} =
            pe::encrypt_with_randomness(&lang.pk, &r_m, &r_r);

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

    (com, comrand)
}

pub fn verify1(params: &DVRParams) -> DVRChallenge1 {
    let b = BigInt::sample(params.lambda as usize);
    DVRChallenge1(b)
}

pub fn prove2(params: &DVRParams,
              vpk: &VPK,
              lang: &DVRLang,
              wit: &DVRWit,
              ch1: &DVRChallenge1,
              cr: &DVRComRand,
              query_ix: usize) -> (DVRResp1,DVRResp1Rand) {

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_n2: &BigInt = &vpk.pk.nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_n2)),
                        vpk_n2);

    // Computes Enc_pk(enc_arg,rand)*Ct^{ct_exp}
    let p2_generic = |rand: &BigInt,enc_arg: &BigInt,ct_exp: &BigInt|
            super::schnorr_paillier_plus::compute_si(&vpk.pk,&ch_ct,enc_arg,rand,ct_exp);

    ////// For wit.m

    // u, v
    let u_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u_m = p2_generic(&u_r_m, &cr.r_m, &(&params.range - &wit.m));
    let v_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v_m = p2_generic(&v_r_m, &cr.sigma_m, &-&cr.t_m);

    // u_i, v_i, i = 1, 2, 3
    let u1_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u1_m = p2_generic(&u1_r_m, &cr.r1_m, &cr.x1_m);
    let v1_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v1_m = p2_generic(&v1_r_m, &cr.sigma1_m, &cr.t1_m);

    let u2_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u2_m = p2_generic(&u2_r_m, &cr.r2_m, &cr.x2_m);
    let v2_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v2_m = p2_generic(&v2_r_m, &cr.sigma2_m, &cr.t2_m);

    let u3_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u3_m = p2_generic(&u3_r_m, &cr.r3_m, &cr.x3_m);
    let v3_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v3_m = p2_generic(&v3_r_m, &cr.sigma3_m, &cr.t3_m);

    // u4
    let u4_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u4_m =
        p2_generic(&u4_r_m, &cr.tau_m,
                   &(&cr.x1_m * &cr.t1_m +
                     &cr.x2_m * &cr.t2_m +
                     &cr.x3_m * &cr.t3_m -
                     &BigInt::from(4) * (&params.range - &wit.m) * &cr.t_m));


    ////// For wit.r

    // u, v
    let u_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u_r = p2_generic(&u_r_r, &cr.r_r, &-&wit.r);


    let (plus_com,plus_comrand) = if params.ggm_mode { (None,None) } else {
        //// Running the sub-proof
        let sp_plus_params = params.sp_plus_params();
        let sp_plus_lang = sp_plus::Lang{ pk: vpk.pk.clone(), ch_ct: ch_ct.clone() };

        let (com_u_m ,comrand_u_m ) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_v_m ,comrand_v_m ) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_u1_m,comrand_u1_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_v1_m,comrand_v1_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_u2_m,comrand_u2_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_v2_m,comrand_v2_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_u3_m,comrand_u3_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_v3_m,comrand_v3_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);
        let (com_u4_m,comrand_u4_m) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);

        let (com_u_r ,comrand_u_r) = sp_plus::prove1(&sp_plus_params, &sp_plus_lang);

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

    (resp1,resp1_rand)
}

pub fn verify2(params: &DVRParams) -> Option<DVRChallenge2> {
    if params.ggm_mode { None } else {
    let sp_plus_params = params.sp_plus_params();

    let ch_u_m = sp_plus::verify1(&sp_plus_params);
    let ch_v_m = sp_plus::verify1(&sp_plus_params);
    let ch_u1_m = sp_plus::verify1(&sp_plus_params);
    let ch_v1_m = sp_plus::verify1(&sp_plus_params);
    let ch_u2_m = sp_plus::verify1(&sp_plus_params);
    let ch_v2_m = sp_plus::verify1(&sp_plus_params);
    let ch_u3_m = sp_plus::verify1(&sp_plus_params);
    let ch_v3_m = sp_plus::verify1(&sp_plus_params);
    let ch_u4_m = sp_plus::verify1(&sp_plus_params);

    let ch_u_r = sp_plus::verify1(&sp_plus_params);

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
              resp1: &DVRResp1,
              resp1rand: &DVRResp1Rand,
              ch2: Option<&DVRChallenge2>,
              query_ix: usize) -> Option<DVRResp2> {
    if params.ggm_mode { None } else {

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_n2: &BigInt = &vpk.pk.nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_n2)),
                        vpk_n2);

    //// Running the sub-proof
    let sp_plus_params = params.sp_plus_params();
    let sp_plus_lang = sp_plus::Lang{ pk: vpk.pk.clone(), ch_ct: ch_ct.clone() };

    let sp_plus_reply = |witm: &BigInt, witr: &BigInt, witcexp: &BigInt, ch: &sp_plus::Challenge, comrand: &sp_plus::ComRand| {
            sp_plus::prove2(&sp_plus_params,&sp_plus_lang,
                            &sp_plus::Wit{m: witm.clone(),
                                          r: witr.clone(),
                                          cexp: witcexp.clone()},
                            ch,
                            comrand)
    };

    let ch2_unwrap = ch2.expect("DVRange#prove3: ch2 must be Some");
    let plus_comrand = resp1rand.plus_comrand.clone().expect("DVRange#prove3: plus_comrand must be Some");


    let resp_u_m = sp_plus_reply(&cr.r_m,
                                 &resp1rand.u_r_m,
                                 &(&params.range - &wit.m),
                                 &ch2_unwrap.ch_u_m,
                                 &plus_comrand.comrand_u_m);

    let resp_v_m = sp_plus_reply(&cr.sigma_m,
                                 &resp1rand.v_r_m,
                                 &-&cr.t_m,
                                 &ch2_unwrap.ch_v_m,
                                 &plus_comrand.comrand_v_m);

    let resp_u1_m = sp_plus_reply(&cr.r1_m,
                                  &resp1rand.u1_r_m,
                                  &cr.x1_m,
                                  &ch2_unwrap.ch_u1_m,
                                  &plus_comrand.comrand_u1_m);
    let resp_v1_m = sp_plus_reply(&cr.sigma1_m,
                                  &resp1rand.v1_r_m,
                                  &cr.t1_m,
                                  &ch2_unwrap.ch_v1_m,
                                  &plus_comrand.comrand_v1_m);

    let resp_u2_m = sp_plus_reply(&cr.r2_m,
                                  &resp1rand.u2_r_m,
                                  &cr.x2_m,
                                  &ch2_unwrap.ch_u2_m,
                                  &plus_comrand.comrand_u2_m);
    let resp_v2_m = sp_plus_reply(&cr.sigma2_m,
                                  &resp1rand.v2_r_m,
                                  &cr.t2_m,
                                  &ch2_unwrap.ch_v2_m,
                                  &plus_comrand.comrand_v2_m);

    let resp_u3_m = sp_plus_reply(&cr.r3_m,
                                  &resp1rand.u3_r_m,
                                  &cr.x3_m,
                                  &ch2_unwrap.ch_u3_m,
                                  &plus_comrand.comrand_u3_m);
    let resp_v3_m = sp_plus_reply(&cr.sigma3_m,
                                  &resp1rand.v3_r_m,
                                  &cr.t3_m,
                                  &ch2_unwrap.ch_v3_m,
                                  &plus_comrand.comrand_v3_m);

    let resp_u4_m = sp_plus_reply(&cr.tau_m,
                                  &resp1rand.u4_r_m,
                                  &(&cr.x1_m * &cr.t1_m +
                                    &cr.x2_m * &cr.t2_m +
                                    &cr.x3_m * &cr.t3_m -
                                    &BigInt::from(4) * (&params.range - &wit.m) * &cr.t_m),
                                  &ch2_unwrap.ch_u4_m,
                                  &plus_comrand.comrand_u4_m);


    let resp_u_r = sp_plus_reply(&cr.r_r,
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

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_n2: &BigInt = &vpk.pk.nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts[(params.lambda as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_n2)),
                        vpk_n2);

    let ch_raw: BigInt =
        &vsk.chs[(params.lambda as usize) + query_ix] +
        ch1_active_bits.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );

    // λ 2^{4λ+Q} R + λ 2^{3λ+Q} R = λ 2^{3λ+Q} R (2^λ + 1)
    let ui_range = &BigInt::from(params.lambda) *
                   &BigInt::pow(&BigInt::from(2),3 * params.lambda + params.crs_uses) *
                   &params.range *
                   &(&BigInt::pow(&BigInt::from(2),params.lambda) + &BigInt::from(1));

    let paillier_decrypt = |target: &BigInt| {
        let res = Paillier::decrypt(&vsk.sk,RawCiphertext::from(target)).0.into_owned();
        if &res >= &(&vpk.pk.n / BigInt::from(2)) { &res - &vpk.pk.n } else { res }
    };

    let u_m_plain = paillier_decrypt(&resp1.u_m);

    // Perform the _m checks
    {
        let v_m_plain  = paillier_decrypt(&resp1.v_m);
        let u1_m_plain = paillier_decrypt(&resp1.u1_m);
        let v1_m_plain = paillier_decrypt(&resp1.v1_m);
        let u2_m_plain = paillier_decrypt(&resp1.u2_m);
        let v2_m_plain = paillier_decrypt(&resp1.v2_m);
        let u3_m_plain = paillier_decrypt(&resp1.u3_m);
        let v3_m_plain = paillier_decrypt(&resp1.v3_m);
        let u4_m_plain = paillier_decrypt(&resp1.u4_m);


        //println!("ch_raw   : {:?}", &ch_raw);
        //println!("range    : {:?}", &ui_range);
        //println!("u_m      : {:?}", &u_m_plain);
        //println!("v_m      : {:?}", &v_m_plain);

        if !u::bigint_in_range_sym(&ui_range,&u1_m_plain,&vpk.pk.n) ||
            !u::bigint_in_range_sym(&ui_range,&u2_m_plain,&vpk.pk.n) ||
            !u::bigint_in_range_sym(&ui_range,&u3_m_plain,&vpk.pk.n) {
                println!("DVRange#verify3: range check 1 failed");
                return false;
            }

        let eq1_lhs =
            BigInt::mod_mul(
                &com.beta_m,
                &u::bigint_mod_pow(
                    &(&BigInt::mod_inv(&com.com_m,&vpk.n).unwrap() *
                      &u::bigint_mod_pow(&vpk.g,&params.range,&vpk.n)),
                    &ch_raw,
                    &vpk.n),
                &vpk.n);
        let eq1_rhs = pedersen_commit(&vpk, &u_m_plain, &v_m_plain);
        if eq1_lhs != eq1_rhs {
            println!("DVRange#verify3: 1 eq1");
            return false;
        }

        //println!("beta1_m   : {:?}", &com.beta1_m);
        //println!("u1_m      : {:?}", &u1_m_plain);
        //println!("v1_m      : {:?}", &v1_m_plain);

        let eq21_lhs = BigInt::mod_mul(&com.beta1_m,
                                       &u::bigint_mod_pow(&com.com1_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq21_rhs = pedersen_commit(&vpk, &u1_m_plain, &v1_m_plain);
        if eq21_lhs != eq21_rhs {
            println!("DVRange#verify3: 1 eq21");
            return false;
        }

        let eq22_lhs = BigInt::mod_mul(&com.beta2_m,
                                       &u::bigint_mod_pow(&com.com2_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq22_rhs = pedersen_commit(&vpk, &u2_m_plain, &v2_m_plain);
        if eq22_lhs != eq22_rhs {
            println!("DVRange#verify3: 1 eq22");
            return false;
        }

        let eq23_lhs = BigInt::mod_mul(&com.beta3_m,
                                       &u::bigint_mod_pow(&com.com3_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq23_rhs = pedersen_commit(&vpk, &u3_m_plain, &v3_m_plain);
        if eq23_lhs != eq23_rhs {
            println!("DVRange#verify3: 1 eq23");
            return false;
        }

        let eq3_lhs =
            BigInt::mod_mul(
                &com.beta4_m,
                &([&u::bigint_mod_pow(&com.com1_m,&u1_m_plain,&vpk.n),
                   &u::bigint_mod_pow(&com.com2_m,&u2_m_plain,&vpk.n),
                   &u::bigint_mod_pow(&com.com3_m,&u3_m_plain,&vpk.n),
                ].iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n))),
                &vpk.n);
        let eq3_rhs = BigInt::mod_mul(
            &pedersen_commit(&vpk, &ch_raw, &u4_m_plain),
            &u::bigint_mod_pow(&com.com_m,&(BigInt::from(4) * &u_m_plain),&vpk.n),
            &vpk.n
        );
        if eq3_lhs != eq3_rhs {
            println!("DVRange#verify3: 1 eq3");
            return false;
        }

    }

    let u_r_plain = paillier_decrypt(&resp1.u_r);

    // perform the alpha check
    {
        let pe::PECiphertext{ct1:rhs_1,ct2:rhs_2} =
            pe::encrypt_with_randomness(&lang.pk, &u_m_plain, &u_r_plain);

        // both (R,0) and (R,R) should work, depending on how u_r is constructed
        let pe::PECiphertext{ct1:psi_range_1,ct2:psi_range_2} =
            pe::encrypt_with_randomness(&lang.pk, &params.range, &BigInt::from(0));
            //pe::encrypt_with_randomness(&lang.pk, &params.range, lang.range_rand());

        let lhs_1 =
            BigInt::mod_mul(&com.alpha1,
                            &u::bigint_mod_pow(
                                &BigInt::mod_mul(
                                    &BigInt::mod_inv(&inst.ct.ct1,&lang.pk.n2).unwrap(),
                                    &psi_range_1,
                                    &lang.pk.n2),
                                &ch_raw,
                                &lang.pk.n2),
                            &lang.pk.n2);

        if lhs_1 != rhs_1 {
            println!("DVRange#verify3: alpha 1");
            return false; }

        let lhs_2 =
            BigInt::mod_mul(&com.alpha2,
                            &u::bigint_mod_pow(
                                &BigInt::mod_mul(
                                    &BigInt::mod_inv(&inst.ct.ct2,&lang.pk.n2).unwrap(),
                                    &psi_range_2,
                                    &lang.pk.n2),
                                &ch_raw,
                                &lang.pk.n2),
                            &lang.pk.n2);

        if lhs_2 != rhs_2 {
            println!("DVRange#verify3: alpha 2");
            return false; }
    }


    // Check the sub-protocol replies, for the schnorr-paillier plus
    if !params.ggm_mode {
        let sp_plus_params = params.sp_plus_params();
        let sp_plus_lang = sp_plus::Lang{ pk: vpk.pk.clone(), ch_ct: ch_ct.clone() };
        let plus_com = resp1.plus_com.clone().expect("DVRange#verify3 plus_com must be Some");
        let plus_ch = ch2.expect("DVRange#verify3 ch2 must be Some");
        let plus_resp = resp2.expect("DVRange#verify3 resp2 must be Some");

        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.u_m.clone()},
                             &plus_com.com_u_m,
                             &plus_ch.ch_u_m,
                             &plus_resp.resp_u_m)
        { println!("DVRange#verify3: sp_plus 1"); return false; }

        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.v_m.clone()},
                             &plus_com.com_v_m,
                             &plus_ch.ch_v_m,
                             &plus_resp.resp_v_m)
        { println!("DVRange#verify3: sp_plus 2");  return false; }

        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.u1_m.clone()},
                             &plus_com.com_u1_m,
                             &plus_ch.ch_u1_m,
                             &plus_resp.resp_u1_m)
        { println!("DVRange#verify3: sp_plus 3");  return false; }
        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.v1_m.clone()},
                             &plus_com.com_v1_m,
                             &plus_ch.ch_v1_m,
                             &plus_resp.resp_v1_m)
        { println!("DVRange#verify3: sp_plus 4");  return false; }
        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.u2_m.clone()},
                             &plus_com.com_u2_m,
                             &plus_ch.ch_u2_m,
                             &plus_resp.resp_u2_m)
        { println!("DVRange#verify3: sp_plus 5");  return false; }
        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.v2_m.clone()},
                             &plus_com.com_v2_m,
                             &plus_ch.ch_v2_m,
                             &plus_resp.resp_v2_m)
        { println!("DVRange#verify3: sp_plus 6");  return false; }
        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.u3_m.clone()},
                             &plus_com.com_u3_m,
                             &plus_ch.ch_u3_m,
                             &plus_resp.resp_u3_m)
        { println!("DVRange#verify3: sp_plus 7");  return false; }
        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.v3_m.clone()},
                             &plus_com.com_v3_m,
                             &plus_ch.ch_v3_m,
                             &plus_resp.resp_v3_m)
        { println!("DVRange#verify3: sp_plus 8");  return false; }

        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.u4_m.clone()},
                             &plus_com.com_u4_m,
                             &plus_ch.ch_u4_m,
                             &plus_resp.resp_u4_m)
        { println!("DVRange#verify3: sp_plus 9");  return false; }

        if !sp_plus::verify2(&sp_plus_params,&sp_plus_lang,
                             &sp_plus::Inst{si:resp1.u_r.clone()},
                             &plus_com.com_u_r,
                             &plus_ch.ch_u_r,
                             &plus_resp.resp_u_r)
        { println!("DVRange#verify3: sp_plus 10");  return false; }

    }

    true
}



////////////////////////////////////////////////////////////////////////////
// Fiat-Shamir variant
////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Debug)]
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

    let get_ch = |resp: &sp_plus::Commitment| {
        let x: Vec<u8> = rmp_serde::to_vec(&(com, ch1, resp1, inst, lang, resp)).unwrap();
        fs_to_bigint(params, &([common_prefix.clone(),x].concat()))
    };
    let plus_com = resp1.plus_com.clone().expect("DVRange#verify3 plus_com must be Some");
    let ch_u_m  = sp_plus::Challenge(vec![get_ch(&plus_com.com_u_m)]);
    let ch_v_m  = sp_plus::Challenge(vec![get_ch(&plus_com.com_v_m)]);
    let ch_u1_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_u1_m)]);
    let ch_v1_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_v1_m)]);
    let ch_u2_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_u2_m)]);
    let ch_v2_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_v2_m)]);
    let ch_u3_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_u3_m)]);
    let ch_v3_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_v3_m)]);
    let ch_u4_m = sp_plus::Challenge(vec![get_ch(&plus_com.com_u4_m)]);
    let ch_u_r  = sp_plus::Challenge(vec![get_ch(&plus_com.com_u_r)]);

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
    let (resp1,resp1rand) = prove2(&params,&vpk,&lang,&wit,&ch1,&cr,query_ix);
    let ch2 = fs_compute_challenge_2(&params,lang,inst,&com,&ch1,&resp1);
    let resp2 = prove3(params,vpk,wit,&ch1,&cr,&resp1,&resp1rand,ch2.as_ref(),query_ix);

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
    let range = BigInt::pow(&BigInt::from(2), 256);
    let params = DVRParams::new(1024, 128, range, queries as u32, false, false);

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
    let range = BigInt::pow(&BigInt::from(2), 256);
    let params = DVRParams::new(2048, 128, range, 32, malicious_vpk, ggm_mode);

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
    fn test_keygen_correctness() {
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams::new(1024, 32, range, 5, false, false);

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }

    #[test]
    fn test_correctness() {
        for ggm_mode in [false,true] {
        let queries:usize = 32;
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams::new(256, 32, range, queries as u32, false, ggm_mode);

        let (vpk,vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));

        for query_ix in 0..queries {
            println!("Query #{:?}", query_ix);
            let (lang,inst,wit) = sample_liw(&params);

            let (com,cr) = prove1(&params,&vpk,&lang,&wit);
            let ch1 = verify1(&params);
            let (resp1,resp1rand) = prove2(&params,&vpk,&lang,&wit,&ch1,&cr,query_ix);
            let ch2 = verify2(&params);
            let resp2 = prove3(&params,&vpk,&wit,&ch1,&cr,&resp1,&resp1rand,ch2.as_ref(),query_ix);

            assert!(verify3(&params,&vsk,&vpk,&lang,&inst,
                            &com,&ch1,&resp1,ch2.as_ref(),resp2.as_ref(),query_ix));
        }}
    }

    #[test]
    fn test_correctness_fs() {
        for ggm_mode in [false,true] {
        let queries:usize = 32;
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams::new(1024, 128, range, queries as u32, false, ggm_mode);

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
