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


#[derive(Clone, Debug)]
pub struct DVRParams {
    /// Internal DV Params
    pub dv_params: dv::DVParams,
    /// Range we're proving
    pub range: BigInt
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

}

impl VPK {
    pub fn pk(&self) -> &EncryptionKey { &self.dv_vpk.pk }
    pub fn cts(&self) -> &Vec<BigInt> { &self.dv_vpk.cts }
    pub fn nizk_gcd(&self) -> &n_gcd::Proof { &self.dv_vpk.nizk_gcd }
    pub fn nizks_ct(&self) -> &Vec<spb::FSProof> { &self.dv_vpk.nizks_ct }
}


pub fn keygen(params: &DVRParams) -> (VPK, VSK) {
    let (dv_vpk, dv_vsk) = dv::keygen(&params.dv_params);
    let p = &dv_vsk.sk.p;
    let q = &dv_vsk.sk.q;
    let phi = p * q * (p-1) * (q-1);
    // FIXME: not sure g in Z_N or in Z_{N^2}
    let g = BigInt::sample_below(&dv_vpk.pk.n);
    let f = BigInt::sample_below(&phi);
    let h = BigInt::mod_pow(&g, &f, &dv_vpk.pk.n);
    let vsk = VSK{dv_vsk, f};
    let vpk = VPK{dv_vpk, g, h};
    // FIXME: add schnorr proof for g/f
    (vpk,vsk)
}

pub fn verify_vpk(params: &DVRParams, vpk: &VPK) -> bool {
    if !dv::verify_vpk(&params.dv_params, &vpk.dv_vpk) { return false; }
    // FIXME: add schnorr proof for g/f
    true
}
