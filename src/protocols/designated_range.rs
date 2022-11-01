use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation, Roots};
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
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;
use super::schnorr_exp as se;


#[derive(Clone, Debug)]
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

    /// Bit length of the third N, wrt which VPK.n is constructed.
    pub fn n_bitlen(&self) -> u32 {
        // @volhovm FIXME I don't know the real value. This is a stub.
        self.psi_n_bitlen * 3
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
            self.ch_big_bitlen() // FIXME, shouldn't it be a bit more?
        }
    }

    /// Maximum size of the summed-up challenge, after considering VPK proof slack.
    pub fn max_ch_proven_bitlen(&self) -> u32 {
        let slack = if self.malicious_setup { self.range_slack_bitlen() } else { 0 };
        // Plus one just in case. TODO maybe not necessary to add 1.
        self.max_ch_bitlen() + slack + 1
    }

    pub fn rand_m_bitlen(&self) -> u32 {
        // r should be lambda bits more than c * w, where c is maximum sum-challenge proven.
        self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda
        // TODO: maybe we can use range bits instead of psi_n_bitlen here. To optimise.
    }

    pub fn rand_r_bitlen(&self) -> u32 {
        // @volhovm FIXME: which randomness we use here depends on
        // what randomness is used for Paillier on Prover's side. It
        // can either be randomness from N or from N^2.

        self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda
        //2 * self.psi_n_bitlen + self.max_ch_proven_bitlen() + self.lambda
    }

    // M should be bigger than r + cw, but r should hide cw perfectly;
    // so cw is always negligibly smaller than r. We could just take M
    // to be n and achieve statistical completeness in this respect,
    // but adding one extra bit will give us perfect completeness,
    // because now r + cw < 2 r.
    pub fn vpk_n_bitlen(&self) -> u32 {
        // This crazily big value needs to be justified probably.
        u::log2ceil(self.lambda) + 5 * self.lambda + self.crs_uses - 1 + 
            self.n_bitlen() + 
            (BigInt::bit_length(&(&BigInt::from(3) * &Roots::sqrt(&self.range) +
                                 &BigInt::from(4) * &self.range)) as u32)

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

    // FIXME: not sure g in Z_N or in Z_{N^2}
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
    com1_r: BigInt,
    com2_r: BigInt,
    com3_r: BigInt,
    beta_r: BigInt,
    beta1_r: BigInt,
    beta2_r: BigInt,
    beta3_r: BigInt,
    beta4_r: BigInt,

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
    r1_r: BigInt,
    r2_r: BigInt,
    r3_r: BigInt,
    t_r: BigInt,
    t1_r: BigInt,
    t2_r: BigInt,
    t3_r: BigInt,
    x1_r: BigInt,
    x2_r: BigInt,
    x3_r: BigInt,
    sigma_r: BigInt,
    sigma1_r: BigInt,
    sigma2_r: BigInt,
    sigma3_r: BigInt,
    tau_r: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DVRChallenge(BigInt);

pub struct DVRResp {
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
    v_r: BigInt,
    u1_r: BigInt,
    v1_r: BigInt,
    u2_r: BigInt,
    v2_r: BigInt,
    u3_r: BigInt,
    v3_r: BigInt,
    u4_r: BigInt,
}

pub struct DVRRespRand {
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
    v_r_r: BigInt,
    u1_r_r: BigInt,
    v1_r_r: BigInt,
    u2_r_r: BigInt,
    v2_r_r: BigInt,
    u3_r_r: BigInt,
    v3_r_r: BigInt,
    u4_r_r: BigInt,
}



fn pedersen_commit(vpk: &VPK, msg: &BigInt, r: &BigInt) -> BigInt {
    // FIXME over Z_N, right? Or Z_N^2?
    BigInt::mod_mul(
        &u::bigint_mod_pow(&vpk.g, msg, &vpk.n),
        &u::bigint_mod_pow(&vpk.h, r, &vpk.n),
        &vpk.n)
}


pub fn prove1(params: &DVRParams, vpk: &VPK, lang: &DVRLang, wit: &DVRWit) -> (DVRCom,DVRComRand) {
    // FIXME: these ranges are taken from the basic protocol, figure 3,
    // that does not consider reusable CRS. With reusable CRS the ranges will become bigger.

    // 2^{λ-1}N
    let t_range = &BigInt::pow(&BigInt::from(2),params.lambda - 1) * &vpk.n;
    // λ 2^{4λ+Q} R
    let r_range = &BigInt::from(params.lambda) *
                  &BigInt::pow(&BigInt::from(2),4 * params.lambda + params.crs_uses) *
                  &params.range;
    // λ 2^{5λ+Q - 1} N
    let sigma_range = &BigInt::from(params.lambda) *
                      &BigInt::pow(&BigInt::from(2),5 * params.lambda + params.crs_uses - 1) *
                      &vpk.n;
    // λ 2^{5λ+Q - 1} N (3 sqrt(R) + 4 R)
    // TODO: this sqrt is floored, should we ceil?
    let tau_range = &sigma_range * (&BigInt::from(3) * &Roots::sqrt(&params.range) +
                                    &BigInt::from(4) * &params.range);

    ////// For the message, wit.m first

    // Compute com
    let t_m = u::bigint_sample_below_sym(&t_range);
    let com_m = pedersen_commit(&vpk, &wit.m, &t_m);

    // Compute beta
    let r_m = u::bigint_sample_below_sym(&r_range);
    let sigma_m = u::bigint_sample_below_sym(&sigma_range);
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
    let r1_m = u::bigint_sample_below_sym(&r_range);
    let sigma1_m = u::bigint_sample_below_sym(&sigma_range);
    let beta1_m = pedersen_commit(&vpk, &r1_m, &sigma1_m);
    let r2_m = u::bigint_sample_below_sym(&r_range);
    let sigma2_m = u::bigint_sample_below_sym(&sigma_range);
    let beta2_m = pedersen_commit(&vpk, &r2_m, &sigma2_m);
    let r3_m = u::bigint_sample_below_sym(&r_range);
    let sigma3_m = u::bigint_sample_below_sym(&sigma_range);
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

    // Compute beta
    let r_r = u::bigint_sample_below_sym(&r_range);
    let sigma_r = u::bigint_sample_below_sym(&sigma_range);
    let beta_r = pedersen_commit(&vpk, &r_r, &sigma_r);

    // Decompose 4 m (R_r - wit.r) + 1
    let decomp_target = &BigInt::from(4) * &wit.r * (lang.range_rand() - &wit.r) + &BigInt::from(1);
    println!("decomp target: {:?}", decomp_target);
    let (x1_r,x2_r,x3_r) = super::squares_decomp::three_squares_decompose(&decomp_target);

    // Compute commitments to xi
    let t1_r = u::bigint_sample_below_sym(&t_range);
    let com1_r = pedersen_commit(&vpk, &x1_r, &t1_r);
    let t2_r = u::bigint_sample_below_sym(&t_range);
    let com2_r = pedersen_commit(&vpk, &x2_r, &t2_r);
    let t3_r = u::bigint_sample_below_sym(&t_range);
    let com3_r = pedersen_commit(&vpk, &x3_r, &t3_r);

    // Compute beta_i
    let r1_r = u::bigint_sample_below_sym(&r_range);
    let sigma1_r = u::bigint_sample_below_sym(&sigma_range);
    let beta1_r = pedersen_commit(&vpk, &r1_r, &sigma1_r);
    let r2_r = u::bigint_sample_below_sym(&r_range);
    let sigma2_r = u::bigint_sample_below_sym(&sigma_range);
    let beta2_r = pedersen_commit(&vpk, &r2_r, &sigma2_r);
    let r3_r = u::bigint_sample_below_sym(&r_range);
    let sigma3_r = u::bigint_sample_below_sym(&sigma_range);
    let beta3_r = pedersen_commit(&vpk, &r3_r, &sigma3_r);

    // Compute tau/beta_4
    let tau_r = u::bigint_sample_below_sym(&tau_range);
    let beta4_r_args: [&BigInt;5] =
        [&u::bigint_mod_pow(&vpk.h,&tau_r,&vpk.n),
         &u::bigint_mod_pow(&com_r,&(&BigInt::from(4)*&r_r),&vpk.n),
         &u::bigint_mod_pow(&com1_r,&-&r1_r,&vpk.n),
         &u::bigint_mod_pow(&com2_r,&-&r2_r,&vpk.n),
         &u::bigint_mod_pow(&com3_r,&-&r3_r,&vpk.n)
        ];
    let beta4_r: BigInt =
            beta4_r_args.iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n));


    // alpha1 and alpha_2
    let pe::PECiphertext{ct1:alpha1,ct2:alpha2} =
            pe::encrypt_with_randomness(&lang.pk, &r_m, &r_r);

    // Commitment and commitment randomness
    let com = DVRCom {
        com_m, com1_m, com2_m, com3_m, beta_m, beta1_m, beta2_m, beta3_m, beta4_m,
        com_r, com1_r, com2_r, com3_r, beta_r, beta1_r, beta2_r, beta3_r, beta4_r,
        alpha1, alpha2,
    };
    let comrand = DVRComRand {
        r_m, r1_m, r2_m, r3_m, t_m, t1_m, t2_m, t3_m, x1_m, x2_m, x3_m,
        sigma_m, sigma1_m, sigma2_m, sigma3_m, tau_m,
        r_r, r1_r, r2_r, r3_r, t_r, t1_r, t2_r, t3_r, x1_r, x2_r, x3_r,
        sigma_r, sigma1_r, sigma2_r, sigma3_r, tau_r,
    };

    (com, comrand)
}

pub fn verify1(params: &DVRParams) -> DVRChallenge {
    let b = BigInt::sample(params.lambda as usize);
    DVRChallenge(b)
}

pub fn prove2(params: &DVRParams,
              vpk: &VPK,
              lang: &DVRLang,
              wit: &DVRWit,
              ch1: &DVRChallenge,
              cr: &DVRComRand,
              query_ix: usize) -> (DVRResp,DVRRespRand) {

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
            BigInt::mod_mul(
                &Paillier::encrypt_with_chosen_randomness(
                    &vpk.pk,
                    RawPlaintext::from(enc_arg),
                    &Randomness::from(rand)).0.into_owned(),
                &u::bigint_mod_pow(&ch_ct, ct_exp, vpk_n2),
                vpk_n2);


    ////// For wit.m

    // u, v
    let u_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u_m = p2_generic(&u_r_m, &cr.r_m, &(&params.range - &wit.m));
    let v_r_m = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v_m = p2_generic(&v_r_m, &cr.sigma_m, &-&cr.t_m);

    // u_i, v_i, i = 1, 2, 3
    println!("r1_m: {:?}", &cr.r1_m);
    println!("x1_m: {:?}", &cr.x1_m);
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
    let u_r = p2_generic(&u_r_r, &cr.r_r, &(&params.range - &wit.r));
    let v_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v_r = p2_generic(&v_r_r, &cr.sigma_r, &-&cr.t_r);

    // u_i, v_i, i = 1, 2, 3
    let u1_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u1_r = p2_generic(&u1_r_r, &cr.r1_r, &cr.x1_r);
    let v1_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v1_r = p2_generic(&v1_r_r, &cr.sigma1_r, &cr.t1_r);

    let u2_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u2_r = p2_generic(&u2_r_r, &cr.r2_r, &cr.x2_r);
    let v2_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v2_r = p2_generic(&v2_r_r, &cr.sigma2_r, &cr.t2_r);

    let u3_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u3_r = p2_generic(&u3_r_r, &cr.r3_r, &cr.x3_r);
    let v3_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let v3_r = p2_generic(&v3_r_r, &cr.sigma3_r, &cr.t3_r);

    // u4
    let u4_r_r = BigInt::sample(params.vpk_n_bitlen() as usize);
    let u4_r =
        p2_generic(&u4_r_r, &cr.tau_r,
                   &(&cr.x1_r * &cr.t1_r +
                     &cr.x2_r * &cr.t2_r +
                     &cr.x3_r * &cr.t3_r -
                     &BigInt::from(4) * (&params.range - &wit.r) * &cr.t_r));

    let resp1 =
        DVRResp {
            u_m, v_m, u1_m, v1_m, u2_m, v2_m, u3_m, v3_m, u4_m,
            u_r, v_r, u1_r, v1_r, u2_r, v2_r, u3_r, v3_r, u4_r,
        };
    let resp1_rand =
        DVRRespRand {
            u_r_m, v_r_m, u1_r_m, v1_r_m, u2_r_m, v2_r_m, u3_r_m, v3_r_m, u4_r_m,
            u_r_r, v_r_r, u1_r_r, v1_r_r, u2_r_r, v2_r_r, u3_r_r, v3_r_r, u4_r_r,
        };

    (resp1,resp1_rand)
}


pub fn verify2(params: &DVRParams,
               vsk: &VSK,
               vpk: &VPK,
               lang: &DVRLang,
               inst: &DVRInst,
               com: &DVRCom,
               ch: &DVRChallenge,
               resp: &DVRResp,
               query_ix: usize) -> bool {

    let mut ch_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda as usize) {
        if ch.0.test_bit(i) { ch_active_bits.push(i); }
    }

    let ch_raw: BigInt =
        &vsk.chs[(params.lambda as usize) + query_ix] +
        ch_active_bits.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );

    // λ 2^{4λ+Q} R + λ 2^{3λ+Q} R = λ 2^{3λ+Q} R (2^λ + 1)
    let ui_range = &BigInt::from(params.lambda) *
                   &BigInt::pow(&BigInt::from(2),3 * params.lambda + params.crs_uses) *
                   &params.range *
                   &(&BigInt::pow(&BigInt::from(2),params.lambda) + &BigInt::from(1));

    let u_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u_m)).0.into_owned();

    // Perform the _m checks
    {
        let v_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v_m)).0.into_owned();
        let u1_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u1_m)).0.into_owned();
        let v1_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v1_m)).0.into_owned();
        let u2_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u2_m)).0.into_owned();
        let v2_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v2_m)).0.into_owned();
        let u3_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u3_m)).0.into_owned();
        let v3_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v3_m)).0.into_owned();
        let u4_m_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u4_m)).0.into_owned();

        println!("ch_raw    : {:?}", &ch_raw);
        println!("vpk_n     : {:?}", &vpk.pk.n);
        println!("range     : {:?}", &ui_range);
        println!("u1_m      : {:?}", &u1_m_plain);
        println!("vpk_n-u1_m: {:?}", &(&vpk.pk.n - &u1_m_plain));
        println!("u1 is in range?: {:?}", u::bigint_in_range_sym(&ui_range,&u1_m_plain,&vpk.pk.n));

        if !u::bigint_in_range_sym(&ui_range,&u1_m_plain,&vpk.pk.n) ||
            !u::bigint_in_range_sym(&ui_range,&u2_m_plain,&vpk.pk.n) ||
            !u::bigint_in_range_sym(&ui_range,&u3_m_plain,&vpk.pk.n) {
                println!("DVRange#verify2: range check 1 failed");
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
            println!("DVRange#verify2: 1 eq1");
            return false;
        }

        let eq21_lhs = BigInt::mod_mul(&com.beta1_m,
                                       &u::bigint_mod_pow(&com.com_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq21_rhs = pedersen_commit(&vpk, &u1_m_plain, &v1_m_plain);
        if eq21_lhs != eq21_rhs {
            println!("DVRange#verify2: 1 eq21");
            return false;
        }

        let eq22_lhs = BigInt::mod_mul(&com.beta2_m,
                                       &u::bigint_mod_pow(&com.com_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq22_rhs = pedersen_commit(&vpk, &u2_m_plain, &v2_m_plain);
        if eq22_lhs != eq22_rhs {
            println!("DVRange#verify2: 1 eq22");
            return false;
        }

        let eq23_lhs = BigInt::mod_mul(&com.beta3_m,
                                       &u::bigint_mod_pow(&com.com_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq23_rhs = pedersen_commit(&vpk, &u3_m_plain, &v3_m_plain);
        if eq23_lhs != eq23_rhs {
            println!("DVRange#verify2: 1 eq23");
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
        let eq3_rhs = pedersen_commit(&vpk, &ch_raw, &u4_m_plain);
        if eq3_lhs != eq3_rhs {
            println!("DVRange#verify2: 1 eq3");
            return false;
        }

    }

    // Perform the _r checks
    let u_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u_r)).0.into_owned();
    {
        let v_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v_r)).0.into_owned();
        let u1_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u1_r)).0.into_owned();
        let v1_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v1_r)).0.into_owned();
        let u2_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u2_r)).0.into_owned();
        let v2_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v2_r)).0.into_owned();
        let u3_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u3_r)).0.into_owned();
        let v3_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.v3_r)).0.into_owned();
        let u4_r_plain = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp.u4_r)).0.into_owned();


        if !u::bigint_in_range_sym(&ui_range,&u1_r_plain,&vpk.pk.n) ||
            !u::bigint_in_range_sym(&ui_range,&u2_r_plain,&vpk.pk.n) ||
            !u::bigint_in_range_sym(&ui_range,&u3_r_plain,&vpk.pk.n) {
                println!("DVRange#verify2: range check 2 failed");
                return false;
            }

        let eq1_lhs =
            BigInt::mod_mul(
                &com.beta_r,
                &u::bigint_mod_pow(
                    &(&BigInt::mod_inv(&com.com_r,&vpk.n).unwrap() *
                      &u::bigint_mod_pow(&vpk.g,&params.range,&vpk.n)),
                    &ch_raw,
                    &vpk.n),
                &vpk.n);
        let eq1_rhs = pedersen_commit(&vpk, &u_r_plain, &v_r_plain);
        if eq1_lhs != eq1_rhs {
            println!("DVRange#verify2: 2 eq1");
            return false; }

        let eq21_lhs = BigInt::mod_mul(&com.beta1_r,
                                       &u::bigint_mod_pow(&com.com_r,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq21_rhs = pedersen_commit(&vpk, &u1_r_plain, &v1_r_plain);
        if eq21_lhs != eq21_rhs {
            println!("DVRange#verify2: 2 eq21");
            return false; }

        let eq22_lhs = BigInt::mod_mul(&com.beta2_r,
                                       &u::bigint_mod_pow(&com.com_r,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq22_rhs = pedersen_commit(&vpk, &u2_r_plain, &v2_r_plain);
        if eq22_lhs != eq22_rhs {
            println!("DVRange#verify2: 2 eq22");
            return false; }

        let eq23_lhs = BigInt::mod_mul(&com.beta3_r,
                                       &u::bigint_mod_pow(&com.com_r,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq23_rhs = pedersen_commit(&vpk, &u3_r_plain, &v3_r_plain);
        if eq23_lhs != eq23_rhs {
            println!("DVRange#verify2: 2 eq23");
            return false; }

        let eq3_lhs =
            BigInt::mod_mul(
                &com.beta4_r,
                &([&u::bigint_mod_pow(&com.com1_r,&u1_r_plain,&vpk.n),
                   &u::bigint_mod_pow(&com.com2_r,&u2_r_plain,&vpk.n),
                   &u::bigint_mod_pow(&com.com3_r,&u3_r_plain,&vpk.n),
                ].iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n))),
                &vpk.n);
        let eq3_rhs = pedersen_commit(&vpk, &ch_raw, &u4_r_plain);
        if eq3_lhs != eq3_rhs {
            println!("DVRange#verify2: 2 eq3");
            return false; }

    }

    // perform the alpha check

    {
        let pe::PECiphertext{ct1:rhs_1,ct2:rhs_2} =
            pe::encrypt_with_randomness(&lang.pk, &u_m_plain, &u_r_plain);

        // FIXME: what should be R for the randomness?...
        // Currently it's N but it probably won't work
        // @dimitris both (R,0) and (R,R) should work
        let pe::PECiphertext{ct1:psi_range_1,ct2:psi_range_2} =
            pe::encrypt_with_randomness(&lang.pk, &params.range, lang.range_rand());

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
            println!("DVRange#verify2: alpha 1");
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
            println!("DVRange#verify2: alpha 2");
            return false; }
    }

    true
}


////////////////////////////////////////////////////////////////////////////
// Tests
////////////////////////////////////////////////////////////////////////////

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
        let queries:usize = 32;
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams::new(256, 32, range, 5, false, false);

        let (vpk,vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));

        for query_ix in 0..queries {
            let (lang,inst,wit) = sample_liw(&params);

            let (com,cr) = prove1(&params,&vpk,&lang,&wit);
            let ch1 = verify1(&params);

            let (resp1,resp1rand) = prove2(&params,&vpk,&lang,&wit,&ch1,&cr,query_ix);
            assert!(verify2(&params,&vsk,&vpk,&lang,&inst,
                            &com,&ch1,&resp1,query_ix));
        }
    }

}
