use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation};
use curv::BigInt;
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration, Encrypt, Decrypt, RawCiphertext,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};
use std::fmt;
use std::iter;
use std::time::{SystemTime, UNIX_EPOCH};
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
    pub range: BigInt
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
}

////////////////////////////////////////////////////////////////////////////
// Keygen
////////////////////////////////////////////////////////////////////////////


#[derive(Clone, Debug)]
pub struct VSK {
    /// Internal DV VSK
    pub dv_vsk: dv::VSK,
    /// The secret exponent
    pub f: BigInt
}

impl VSK {
    pub fn sk(&self) -> &DecryptionKey { &self.dv_vsk.sk }
    pub fn chs(&self) -> &Vec<BigInt> { &self.dv_vsk.chs }
}

#[derive(Clone, Debug)]
pub struct VPK {
    /// Internal DV VPK
    pub dv_vpk: dv::VPK,

    /// Generator w.r.t. N
    pub g: BigInt,
    /// Second generator w.r.t. N, h = g^f mod N, where f is secret.
    pub h: BigInt,
    /// Schnorr proof of g/h
    pub nizk_gen: se::FSProof,
}

impl VPK {
    pub fn n(&self) -> &BigInt { &self.dv_vpk.pk.n }
    pub fn pk(&self) -> &EncryptionKey { &self.dv_vpk.pk }
    pub fn cts(&self) -> &Vec<BigInt> { &self.dv_vpk.cts }
    pub fn nizk_gcd(&self) -> &n_gcd::Proof { &self.dv_vpk.nizk_gcd }
    pub fn nizks_ct(&self) -> &Vec<spb::FSProof> { &self.dv_vpk.nizks_ct }
}


pub fn keygen(params: &DVRParams) -> (VPK, VSK) {
    let (dv_vpk, dv_vsk) = dv::keygen(&params.dv_params);
    let p = &dv_vsk.sk.p;
    let q = &dv_vsk.sk.q;
    // FIXME: not sure g in Z_N or in Z_{N^2}
    let h = BigInt::sample_below(&dv_vpk.pk.n);
    let phi = (p-1) * (q-1);
    let f = BigInt::sample_below(&phi);
    let g = BigInt::mod_pow(&h, &f, &dv_vpk.pk.n);
    let nizk_gen = se::fs_prove(
        &params.nizk_se_params(),
        &se::Lang{n: dv_vpk.pk.n.clone(), h: h.clone()},
        &se::Inst{g: g.clone()},
        &se::Wit{x: f.clone()});

    if !se::fs_verify(&params.nizk_se_params(),
                      &se::Lang{n: dv_vpk.pk.n.clone(), h: h.clone()},
                      &se::Inst{g: g.clone()},
                      &se::VerifierPrecomp(None),
                      &nizk_gen) { panic!("DVRange keygen"); }


    let vsk = VSK{dv_vsk, f};
    let vpk = VPK{dv_vpk, g, h, nizk_gen};
    (vpk,vsk)
}

pub fn verify_vpk(params: &DVRParams, vpk: &VPK) -> bool {
    if !dv::verify_vpk(&params.dv_params, &vpk.dv_vpk) { return false; }
    if !se::fs_verify(&params.nizk_se_params(),
                      &se::Lang{n: vpk.dv_vpk.pk.n.clone(), h: vpk.h.clone()},
                      &se::Inst{g: vpk.g.clone()},
                      &se::VerifierPrecomp(None),
                      &vpk.nizk_gen) { return false; }
    true
}


////////////////////////////////////////////////////////////////////////////
// Interactive part
////////////////////////////////////////////////////////////////////////////

pub struct DVRCom { }

pub struct DVRComRand { }

pub fn pedersen_commit(vpk: &VPK, msg: &BigInt, r: &BigInt) -> BigInt {
    // FIXME over Z_N, right? Or Z_N^2?
    BigInt::mod_mul(
        &BigInt::mod_pow(&vpk.g, msg, vpk.n()),
        &BigInt::mod_pow(&vpk.h, r, vpk.n()),
        vpk.n())
}


pub fn prove1(params: &DVRParams, vpk: &VPK, lang: &dv::DVLang, wit: &dv::DVWit) -> (DVRCom,DVRComRand) {
    // For the message first
    {
        // 2^{λ-1}N
        let t_m = u::bigint_sample_below_sym(
            &(&BigInt::pow(&BigInt::from(2),params.dv_params.lambda - 1) * vpk.n()));
        // FIXME over Z_N, right? Or Z_N^2?
        let com_m = pedersen_commit(&vpk, &wit.m, &t_m);

        // λ 2^{4λ+Q} R
        let r_m = u::bigint_sample_below_sym(
            &(&BigInt::from(params.lambda()) *
              &BigInt::pow(&BigInt::from(2),4 * params.lambda() + params.dv_params.crs_uses) *
              &params.range));
        // λ 2^{5λ+Q - 1} N
        let sigma_m = u::bigint_sample_below_sym(
            &(&BigInt::from(params.lambda()) *
              &BigInt::pow(&BigInt::from(2),5 * params.lambda() + params.dv_params.crs_uses - 1) *
              vpk.n()));
        let beta_m = pedersen_commit(&vpk, &r_m, &sigma_m);

    }

    let t_r = u::bigint_sample_below_sym(
        &(&BigInt::pow(&BigInt::from(2),params.dv_params.lambda - 1) * vpk.n()));
    // FIXME over Z_N, right? Or Z_N^2?
    let com_r = pedersen_commit(&vpk, &wit.r, &t_r);


    unimplemented!()
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
        let params = DVRParams { dv_params: dv::DVParams::new(1024, 32, 5, false),
                                 range: range };

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }
}
