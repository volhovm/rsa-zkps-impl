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

use super::designated as dv;
use super::utils as u;
use super::schnorr_paillier_batched as spb;
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;
use super::schnorr_exp as se;


#[derive(Clone, Debug)]
pub struct DVRParams {
    /// Internal DV Params
    pub dv_params: dv::DVParams,
    /// Range we're proving
    pub range: BigInt,
}

impl DVRParams {
    /// Parameters for the Gen g/h NIZK proof.
    pub fn nizk_se_params(&self) -> se::ProofParams {
        let repbits = 15;
        se::ProofParams::new(self.dv_params.n_bitlen,
                             self.dv_params.lambda,
                             repbits)
    }

    pub fn lambda(&self) -> u32 { self.dv_params.lambda }

    /// Bit length of the third N, wrt which VPK.n is constructed.
    pub fn n_bitlen(&self) -> u32 {
        // @volhovm FIXME I don't know the real value. This is a stub.
        self.dv_params.n_bitlen
    }
}


pub fn sample_liw(params: &DVRParams) -> (dv::DVLang,dv::DVInst,dv::DVWit) {
    let lang = dv::sample_lang(&params.dv_params);
    let (inst,wit) = dv::sample_inst(&lang,Some(&params.range));
    (lang,inst,wit)
}

////////////////////////////////////////////////////////////////////////////
// Keygen
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug)]
pub struct VSK {
    /// Internal DV VSK
    pub dv_vsk: dv::VSK,

    /// First factor of the VPK.n
    pub p: BigInt,
    /// Second factor of the VPK.n
    pub q: BigInt,
    /// The secret exponent
    pub f: BigInt,
}

impl VSK {
    pub fn sk(&self) -> &DecryptionKey { &self.dv_vsk.sk }
    pub fn chs(&self) -> &Vec<BigInt> { &self.dv_vsk.chs }
}

#[derive(Clone, Debug)]
pub struct VPK {
    /// Internal DV VPK
    pub dv_vpk: dv::VPK,

    /// An RSA modulus used for h/g
    pub n: BigInt,
    /// Generator w.r.t. N
    pub g: BigInt,
    /// Second generator w.r.t. N, h = g^f mod N, where f is secret.
    pub h: BigInt,
    /// Schnorr proof of g/h
    pub nizk_gen: se::FSProof,
}

impl VPK {
    pub fn pk(&self) -> &EncryptionKey { &self.dv_vpk.pk }
    pub fn cts(&self) -> &Vec<BigInt> { &self.dv_vpk.cts }
    pub fn nizk_gcd(&self) -> &n_gcd::Proof { &self.dv_vpk.nizk_gcd }
    pub fn nizks_ct(&self) -> &Vec<spb::FSProof> { &self.dv_vpk.nizks_ct }
}


pub fn keygen(params: &DVRParams) -> (VPK, VSK) {
    let (dv_vpk, dv_vsk) = dv::keygen(&params.dv_params);

    let (pk,sk) =
        Paillier::keypair_with_modulus_size(params.n_bitlen() as usize).keys();

    let n = pk.n;
    let p = sk.p;
    let q = sk.q;
    // FIXME: not sure g in Z_N or in Z_{N^2}
    let h = BigInt::sample_below(&n);
    let phi = (&p-1) * (&q-1);
    let f = BigInt::sample_below(&phi);
    let g = BigInt::mod_pow(&h, &f, &n);
    let nizk_gen = se::fs_prove(
        &params.nizk_se_params(),
        &se::Lang{n: n.clone(), h: h.clone()},
        &se::Inst{g: g.clone()},
        &se::Wit{x: f.clone()});

    //if !se::fs_verify(&params.nizk_se_params(),
    //                  &se::Lang{n: n.clone(), h: h.clone()},
    //                  &se::Inst{g: g.clone()},
    //                  &se::VerifierPrecomp(None),
    //                  &nizk_gen) { panic!("DVRange keygen"); }

    let vsk = VSK{dv_vsk, f, p, q};
    let vpk = VPK{dv_vpk, n, g, h, nizk_gen};
    (vpk,vsk)
}

pub fn verify_vpk(params: &DVRParams, vpk: &VPK) -> bool {
    if !dv::verify_vpk(&params.dv_params, &vpk.dv_vpk) { return false; }
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



pub fn pedersen_commit(vpk: &VPK, msg: &BigInt, r: &BigInt) -> BigInt {
    // FIXME over Z_N, right? Or Z_N^2?
    BigInt::mod_mul(
        &BigInt::mod_pow(&vpk.g, msg, &vpk.n),
        &BigInt::mod_pow(&vpk.h, r, &vpk.n),
        &vpk.n)
}


pub fn prove1(params: &DVRParams, vpk: &VPK, lang: &dv::DVLang, wit: &dv::DVWit) -> (DVRCom,DVRComRand) {
    // FIXME: these ranges are taken from the basic protocol, figure 3,
    // that does not consider reusable CRS. With reusable CRS the ranges will become bigger.

    // 2^{λ-1}N
    let t_range = &BigInt::pow(&BigInt::from(2),params.dv_params.lambda - 1) * &vpk.n;
    // λ 2^{4λ+Q} R
    let r_range = &BigInt::from(params.lambda()) *
                  &BigInt::pow(&BigInt::from(2),4 * params.lambda() + params.dv_params.crs_uses) *
                  &params.range;
    // λ 2^{5λ+Q - 1} N
    let sigma_range = &BigInt::from(params.lambda()) *
                      &BigInt::pow(&BigInt::from(2),5 * params.lambda() + params.dv_params.crs_uses - 1) *
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

    // Decompose 4 m (R - m) + 1
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
        [&BigInt::mod_pow(&vpk.h,&tau_m,&vpk.n),
         &BigInt::mod_pow(&com_m,&(&BigInt::from(4)*&r_m),&vpk.n),
         &BigInt::mod_pow(&com1_m,&-&r1_m,&vpk.n),
         &BigInt::mod_pow(&com2_m,&-&r2_m,&vpk.n),
         &BigInt::mod_pow(&com3_m,&-&r3_m,&vpk.n)
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

    // Decompose 4 m (R - m) + 1
    let decomp_target = &BigInt::from(4) * &wit.r * (&params.range - &wit.r) + &BigInt::from(1);
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
        [&BigInt::mod_pow(&vpk.h,&tau_r,&vpk.n),
         &BigInt::mod_pow(&com_r,&(&BigInt::from(4)*&r_r),&vpk.n),
         &BigInt::mod_pow(&com1_r,&-&r1_r,&vpk.n),
         &BigInt::mod_pow(&com2_r,&-&r2_r,&vpk.n),
         &BigInt::mod_pow(&com3_r,&-&r3_r,&vpk.n)
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
    let b = BigInt::sample(params.lambda() as usize);
    DVRChallenge(b)
}

pub fn prove2(params: &DVRParams,
              vpk: &VPK,
              lang: &dv::DVLang,
              wit: &dv::DVWit,
              ch1: &DVRChallenge,
              cr: &DVRComRand,
              query_ix: usize) -> (DVRResp,DVRRespRand) {

    let mut ch1_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda() as usize) {
        if ch1.0.test_bit(i) { ch1_active_bits.push(i); }
    }

    let vpk_n2: &BigInt = &vpk.pk().nn;
    let ch_ct =
        BigInt::mod_mul(&vpk.cts()[(params.lambda() as usize) + query_ix],
                        &ch1_active_bits.iter()
                          .map(|&i| &vpk.cts()[i])
                          .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, vpk_n2)),
                        vpk_n2);

    // Computes Enc_pk(enc_arg,rand)*Ct^{ct_exp}
    let p2_generic = |rand: &BigInt,enc_arg: &BigInt,ct_exp: &BigInt|
            BigInt::mod_mul(
                &Paillier::encrypt_with_chosen_randomness(
                    vpk.pk(),
                    RawPlaintext::from(enc_arg),
                    &Randomness::from(rand)).0.into_owned(),
                &BigInt::mod_pow(&ch_ct, ct_exp, vpk_n2),
                vpk_n2);


    ////// For wit.m

    // u, v
    let u_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u_m = p2_generic(&u_r_m, &cr.r_m, &(&params.range - &wit.m));
    let v_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v_m = p2_generic(&v_r_m, &cr.sigma_m, &-&cr.t_m);

    // u_i, v_i, i = 1, 2, 3
    let u1_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u1_m = p2_generic(&u1_r_m, &cr.r1_m, &cr.x1_m);
    let v1_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v1_m = p2_generic(&v1_r_m, &cr.sigma1_m, &cr.t1_m);

    let u2_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u2_m = p2_generic(&u2_r_m, &cr.r2_m, &cr.x2_m);
    let v2_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v2_m = p2_generic(&v2_r_m, &cr.sigma2_m, &cr.t2_m);

    let u3_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u3_m = p2_generic(&u3_r_m, &cr.r3_m, &cr.x3_m);
    let v3_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v3_m = p2_generic(&v3_r_m, &cr.sigma3_m, &cr.t3_m);

    // u4
    let u4_r_m = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u4_m =
        p2_generic(&u4_r_m, &cr.tau_m,
                   &(&cr.x1_m * &cr.t1_m +
                     &cr.x2_m * &cr.t2_m +
                     &cr.x3_m * &cr.t3_m -
                     &BigInt::from(4) * (&params.range - &wit.m) * &cr.t_m));


    ////// For wit.r

    // u, v
    let u_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u_r = p2_generic(&u_r_r, &cr.r_r, &(&params.range - &wit.r));
    let v_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v_r = p2_generic(&v_r_r, &cr.sigma_r, &-&cr.t_r);

    // u_i, v_i, i = 1, 2, 3
    let u1_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u1_r = p2_generic(&u1_r_r, &cr.r1_r, &cr.x1_r);
    let v1_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v1_r = p2_generic(&v1_r_r, &cr.sigma1_r, &cr.t1_r);

    let u2_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u2_r = p2_generic(&u2_r_r, &cr.r2_r, &cr.x2_r);
    let v2_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v2_r = p2_generic(&v2_r_r, &cr.sigma2_r, &cr.t2_r);

    let u3_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let u3_r = p2_generic(&u3_r_r, &cr.r3_r, &cr.x3_r);
    let v3_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
    let v3_r = p2_generic(&v3_r_r, &cr.sigma3_r, &cr.t3_r);

    // u4
    let u4_r_r = BigInt::sample(params.dv_params.vpk_n_bitlen() as usize);
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
               lang: &dv::DVLang,
               inst: &dv::DVInst,
               com: &DVRCom,
               ch: &DVRChallenge,
               resp: &DVRResp,
               query_ix: usize) -> bool {

    let mut ch_active_bits: Vec<usize> = vec![];
    for i in 0..(params.lambda() as usize) {
        if ch.0.test_bit(i) { ch_active_bits.push(i); }
    }

    let ch_raw: BigInt =
        &vsk.chs()[(params.lambda() as usize) + query_ix] +
        ch_active_bits.iter()
        .map(|&i| &vsk.chs()[i])
        .fold(BigInt::from(0), |acc,x| acc + x );

    // λ 2^{4λ+Q} R + λ 2^{3λ+Q} R = λ 2^{3λ+Q} R (2^λ + 1)
    let ui_range = &BigInt::from(params.lambda()) *
                   &BigInt::pow(&BigInt::from(2),3 * params.lambda() + params.dv_params.crs_uses) *
                   &params.range *
                   &(&BigInt::pow(&BigInt::from(2),params.lambda()) + &BigInt::from(1));

    let u_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u_m)).0.into_owned();
    // Perform the _m checks
    {
        let v_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v_m)).0.into_owned();
        let u1_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u1_m)).0.into_owned();
        let v1_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v1_m)).0.into_owned();
        let u2_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u2_m)).0.into_owned();
        let v2_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v2_m)).0.into_owned();
        let u3_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u3_m)).0.into_owned();
        let v3_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v3_m)).0.into_owned();
        let u4_m_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u4_m)).0.into_owned();

        let eq1_lhs =
            BigInt::mod_mul(
                &com.beta_m,
                &BigInt::mod_pow(
                    &(&BigInt::mod_pow(&com.com_m,&BigInt::from(-1),&vpk.n) *
                      &BigInt::mod_pow(&vpk.g,&params.range,&vpk.n)),
                    &ch_raw,
                    &vpk.n),
                &vpk.n);
        let eq1_rhs = pedersen_commit(&vpk, &u_m_plain, &v_m_plain);
        if eq1_lhs != eq1_rhs { return false; }

        let eq21_lhs = BigInt::mod_mul(&com.beta1_m,
                                       &BigInt::mod_pow(&com.com_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq21_rhs = pedersen_commit(&vpk, &u1_m_plain, &v1_m_plain);
        if eq21_lhs != eq21_rhs { return false; }

        let eq22_lhs = BigInt::mod_mul(&com.beta2_m,
                                       &BigInt::mod_pow(&com.com_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq22_rhs = pedersen_commit(&vpk, &u2_m_plain, &v2_m_plain);
        if eq22_lhs != eq22_rhs { return false; }

        let eq23_lhs = BigInt::mod_mul(&com.beta3_m,
                                       &BigInt::mod_pow(&com.com_m,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq23_rhs = pedersen_commit(&vpk, &u3_m_plain, &v3_m_plain);
        if eq23_lhs != eq23_rhs { return false; }

        let eq3_lhs =
            BigInt::mod_mul(
                &com.beta4_m,
                &([&BigInt::mod_pow(&com.com1_m,&u1_m_plain,&vpk.n),
                   &BigInt::mod_pow(&com.com2_m,&u2_m_plain,&vpk.n),
                   &BigInt::mod_pow(&com.com3_m,&u3_m_plain,&vpk.n),
                ].iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n))),
                &vpk.n);
        let eq3_rhs = pedersen_commit(&vpk, &ch_raw, &u4_m_plain);
        if eq3_lhs != eq3_rhs { return false; }

        if !u::bigint_in_range_sym(&ui_range,&u1_m_plain) ||
            !u::bigint_in_range_sym(&ui_range,&u2_m_plain) ||
            !u::bigint_in_range_sym(&ui_range,&u3_m_plain) {
                return false;
            }
    }

    // Perform the _r checks
    let u_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u_r)).0.into_owned();
    {
        let v_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v_r)).0.into_owned();
        let u1_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u1_r)).0.into_owned();
        let v1_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v1_r)).0.into_owned();
        let u2_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u2_r)).0.into_owned();
        let v2_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v2_r)).0.into_owned();
        let u3_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u3_r)).0.into_owned();
        let v3_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.v3_r)).0.into_owned();
        let u4_r_plain = Paillier::decrypt(vsk.sk(),RawCiphertext::from(&resp.u4_r)).0.into_owned();

        let eq1_lhs =
            BigInt::mod_mul(
                &com.beta_r,
                &BigInt::mod_pow(
                    &(&BigInt::mod_pow(&com.com_r,&BigInt::from(-1),&vpk.n) *
                      &BigInt::mod_pow(&vpk.g,&params.range,&vpk.n)),
                    &ch_raw,
                    &vpk.n),
                &vpk.n);
        let eq1_rhs = pedersen_commit(&vpk, &u_r_plain, &v_r_plain);
        if eq1_lhs != eq1_rhs { return false; }

        let eq21_lhs = BigInt::mod_mul(&com.beta1_r,
                                       &BigInt::mod_pow(&com.com_r,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq21_rhs = pedersen_commit(&vpk, &u1_r_plain, &v1_r_plain);
        if eq21_lhs != eq21_rhs { return false; }

        let eq22_lhs = BigInt::mod_mul(&com.beta2_r,
                                       &BigInt::mod_pow(&com.com_r,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq22_rhs = pedersen_commit(&vpk, &u2_r_plain, &v2_r_plain);
        if eq22_lhs != eq22_rhs { return false; }

        let eq23_lhs = BigInt::mod_mul(&com.beta3_r,
                                       &BigInt::mod_pow(&com.com_r,&ch_raw,&vpk.n),
                                       &vpk.n);
        let eq23_rhs = pedersen_commit(&vpk, &u3_r_plain, &v3_r_plain);
        if eq23_lhs != eq23_rhs { return false; }

        let eq3_lhs =
            BigInt::mod_mul(
                &com.beta4_r,
                &([&BigInt::mod_pow(&com.com1_r,&u1_r_plain,&vpk.n),
                   &BigInt::mod_pow(&com.com2_r,&u2_r_plain,&vpk.n),
                   &BigInt::mod_pow(&com.com3_r,&u3_r_plain,&vpk.n),
                ].iter().fold(BigInt::from(1), |x,y| BigInt::mod_mul(&x, y, &vpk.n))),
                &vpk.n);
        let eq3_rhs = pedersen_commit(&vpk, &ch_raw, &u4_r_plain);
        if eq3_lhs != eq3_rhs { return false; }

        if !u::bigint_in_range_sym(&ui_range,&u1_r_plain) ||
            !u::bigint_in_range_sym(&ui_range,&u2_r_plain) ||
            !u::bigint_in_range_sym(&ui_range,&u3_r_plain) {
                return false;
            }
    }

    // perform the alpha check

    {
        let pe::PECiphertext{ct1:rhs_1,ct2:rhs_2} =
            pe::encrypt_with_randomness(&lang.pk, &u_m_plain, &u_r_plain);

        // FIXME: what should be R for the randomness?...
        // Currently it's 0 but it probably won't work
        let pe::PECiphertext{ct1:psi_range_1,ct2:psi_range_2} =
            pe::encrypt_with_randomness(&lang.pk, &params.range, &BigInt::from(0));

        let lhs_1 =
            BigInt::mod_mul(&com.alpha1,
                            &BigInt::mod_pow(
                                &BigInt::mod_mul(
                                    &BigInt::mod_pow(&inst.ct.ct1,&BigInt::from(-1),&lang.pk.n2),
                                    &psi_range_1,
                                    &lang.pk.n2),
                                &ch_raw,
                                &lang.pk.n2),
                            &lang.pk.n2);

        if lhs_1 != rhs_1 { return false; }

        let lhs_2 =
            BigInt::mod_mul(&com.alpha2,
                            &BigInt::mod_pow(
                                &BigInt::mod_mul(
                                    &BigInt::mod_pow(&inst.ct.ct2,&BigInt::from(-1),&lang.pk.n2),
                                    &psi_range_2,
                                    &lang.pk.n2),
                                &ch_raw,
                                &lang.pk.n2),
                            &lang.pk.n2);

        if lhs_2 != rhs_2 { return false; }

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
    fn test_correctness_keygen() {
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams { dv_params: dv::DVParams::new(1024, 32, 5, false, false),
                                 range: range };

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }

    #[test]
    fn test_correctness() {
        let queries:usize = 5;
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams { dv_params: dv::DVParams::new(256, 16, queries as u32, false, false),
                                 range: range };

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
