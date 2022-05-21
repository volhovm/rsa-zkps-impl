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
    let nizk_gen = se::fs_prove(
        &params.nizk_se_params(),
        &se::Lang{n: dv_vpk.pk.n.clone(), h: h.clone()},
        &se::Inst{g: g.clone()},
        &se::Wit{x: f.clone()});
          
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


#[cfg(test)]
mod tests {

    use crate::protocols::designated::*;

    #[test]
    fn test_correctness_keygen() {
        let range = BigInt::pow(&BigInt::from(2), 256);
        let params = DVRParams { dv_params: DVRParams::new(1024, 32, 5, false),
                                 range: range };

        let (vpk,_vsk) = keygen(&params);
        assert!(verify_vpk(&params,&vpk));
    }

}
