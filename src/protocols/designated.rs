use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::{Paillier, EncryptionKey, DecryptionKey,
               KeyGeneration, Encrypt, Decrypt, RawCiphertext,
               Randomness, RawPlaintext, Keypair, EncryptWithChosenRandomness};
use std::fmt;
use std::iter;
use std::time::{SystemTime, UNIX_EPOCH};
use rand::distributions::{Distribution, Uniform};

use super::utils as u;
use super::schnorr_paillier_batched as spb;
use super::n_gcd as n_gcd;
use super::paillier_elgamal as pe;


#[derive(Clone, Debug)]
pub struct DVParams {
    /// N of the prover, bit length
    pub n_bitlen: u32,
    /// Security parameter
    pub lambda: u32,
    /// The number of CRS reuses
    pub crs_uses: u32,
    /// Whether malicious setup (that introduces VPK proofs) is enabled
    pub malicious_setup: bool
}

impl DVParams {
    pub fn new(n_bitlen: u32, lambda: u32, crs_uses: u32, malicious_setup: bool) -> DVParams {
        DVParams{n_bitlen, lambda, crs_uses, malicious_setup}
    }

    /// Range slack of the batched range proof.
    pub fn range_slack_bitlen(&self) -> u32 {
        2 * self.lambda + u::log2ceil(self.lambda) - 1
    }

    /// The actual size of generated challenges.
    fn ch_small_bitlen(&self) -> u32 { self.lambda }

    // @volhovm: FIXME shouldn't it account for the batched range
    // proof slack? I suspect not, because big ciphertext blinding is
    // needed for soundness (for the oracle not to reveal the CRS),
    // and thus for soundness we can assume trusted setup?
    fn ch_big_bitlen(&self) -> u32 { 2 * self.lambda + u::log2ceil(self.lambda) } 

    /// Maximum size of the summed-up challenge, real.
    pub fn max_ch_bitlen(&self) -> u32 {
        if self.crs_uses == 0 {
            self.lambda + u::log2ceil(self.lambda)
        } else {
            2 * self.lambda + u::log2ceil(self.lambda) // FIXME, shouldn't it be a bit more?
        }
    }

    /// Maximum size of the summed-up challenge
    pub fn max_ch_proven_bitlen(&self) -> u32 {
        if self.crs_uses == 0 {
            // sum of lambda (small challenges with slack)
            (self.ch_small_bitlen() + self.range_slack_bitlen())
                + u::log2ceil(self.lambda)
        } else {
            // a single big challenge with slack
            self.ch_big_bitlen() + self.range_slack_bitlen() + 1
        }
    }

    pub fn rand_m_bitlen(&self) -> u32 {
        // r should be lambda bits more than c * w, where c is maximum
        // sum-challenge according to what is known (in the trusted
        // case) or proven by the batched protocol (in the malicious
        // setup case).
        self.n_bitlen + self.max_ch_proven_bitlen() + self.lambda
    }

    pub fn rand_r_bitlen(&self) -> u32 {
        // @volhovm FIXME: which randomness we use here depends on
        // what randomness is used for Paillier on Prover's side. It
        // can either be randomness from N or from N^2.
        
        self.n_bitlen + self.max_ch_proven_bitlen() + self.lambda
        //2 * self.n_bitlen + self.max_ch_proven_bitlen() + self.lambda
    }

    // M should be bigger than r + cw, but r should hide cw perfectly;
    // so cw is always negligibly smaller than r. We could just take M
    // to be n and achieve statistical completeness in this respect,
    // but adding one extra bit will give us perfect completeness,
    // because now r + cw < 2 r.
    pub fn vpk_n_bitlen(&self) -> u32 {
        std::cmp::max(self.rand_m_bitlen(),self.rand_r_bitlen()) + 1
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
        n_gcd::ProofParams{ n_bitlen: self.n_bitlen as usize,
                            lambda: self.lambda,
                            pmax: 10000 }
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

        let params = if i == 0 { params.nizk_ct_params_1() }
                     else { params.nizk_ct_params_2() };
        let inst = spb::Inst{cts: cts_inst};
        let wit = spb::Wit{ms: ms_wit, rs: rs_wit};

        nizks_ct.push(spb::fs_prove(&params, &lang, &inst, &wit));
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

        let params =
            if i == 0 { params.nizk_ct_params_1() }
            else { params.nizk_ct_params_2() };
        let inst = spb::Lang{ pk: vpk.pk.clone() };
        let wit = spb::Inst{ cts: cts_w };

        let res2 = spb::fs_verify(&params, &inst, &wit, &vpk.nizks_ct[i as usize]);
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
    let (pk,_sk) = pe::keygen(params.n_bitlen as usize);
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
pub struct DVComRand {
    pub rm_m: BigInt,
    pub rm_r: BigInt,
    pub rr_m: BigInt,
    pub rr_r: BigInt,
    pub tm1: BigInt,
    pub tm2: BigInt,
    pub tm3: BigInt,
    pub tr1: BigInt,
    pub tr2: BigInt,
    pub tr3: BigInt,
}

#[derive(Clone, Debug)]
pub struct DVChallenge1(Vec<usize>);
#[derive(Clone, Debug)]
pub struct DVChallenge2(BigInt);

#[derive(Clone, Debug)]
pub struct DVResp1{
    pub sm: BigInt,
    pub sr: BigInt,
    pub tm: BigInt,
    pub tr: BigInt,
}

#[derive(Clone, Debug)]
pub struct DVResp2{
    pub um1: BigInt,
    pub um2: BigInt,
    pub um3: BigInt,
    pub ur1: BigInt,
    pub ur2: BigInt,
    pub ur3: BigInt,
}


pub fn prove1(params: &DVParams, lang: &DVLang) -> (DVCom,DVComRand) {
    // TODO it's broken here
    let rm_m = BigInt::sample(params.rand_m_bitlen() as usize);
    let rm_r = BigInt::sample(params.vpk_n_bitlen() as usize);

    let rr_m = BigInt::sample(params.rand_r_bitlen() as usize);
    let rr_r = BigInt::sample(params.vpk_n_bitlen() as usize);

    let tm1 = BigInt::sample(params.vpk_n_bitlen() as usize);
    let tm2 = BigInt::sample(params.vpk_n_bitlen() as usize);
    let tm3 = BigInt::sample(params.vpk_n_bitlen() as usize);

    let tr1 = BigInt::sample(params.vpk_n_bitlen() as usize);
    let tr2 = BigInt::sample(params.vpk_n_bitlen() as usize);
    let tr3 = BigInt::sample(params.vpk_n_bitlen() as usize);

    let a = pe::encrypt_with_randomness(&lang.pk,&rm_m,&rr_m);

    (DVCom{a}, DVComRand{rm_m, rm_r, rr_m, rr_r, tm1, tm2, tm3, tr1, tr2, tr3})
}

pub fn verify1(params: &DVParams) -> DVChallenge1 {
    let mut rng = rand::thread_rng();
    let gen = Uniform::from(0..(2 * (params.lambda as usize)));

    // There is a better way to do it.
    use std::collections::HashSet;
    let mut ix: HashSet<usize> = HashSet::new();

    while ix.len() < params.lambda as usize {
        let i = gen.sample(&mut rng);
        if !ix.contains(&i) { ix.insert(i); }
    }

    DVChallenge1(ix.into_iter().collect())
}

pub fn prove2(vpk: &VPK,
              cr: &DVComRand,
              wit: &DVWit,
              ch: &DVChallenge1) -> DVResp1 {
    let n2: &BigInt = &vpk.pk.nn;

    let ct =
        ch.0.iter()
        .map(|&i| &vpk.cts[i])
        .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, n2));

    let sm_ct = Paillier::encrypt_with_chosen_randomness(
                  &vpk.pk,
                  RawPlaintext::from(&cr.rm_m),
                  &Randomness::from(&cr.rm_r)).0.into_owned();
    let sm = BigInt::mod_mul(&BigInt::mod_pow(&ct, &wit.m, n2),
                             &sm_ct,
                             n2);

    let sr_ct = Paillier::encrypt_with_chosen_randomness(
                  &vpk.pk,
                  RawPlaintext::from(&cr.rr_m),
                  &Randomness::from(&cr.rr_r)).0.into_owned();
    let sr = BigInt::mod_mul(&BigInt::mod_pow(&ct, &wit.r, n2),
                             &sr_ct,
                             n2);

    let tm_ct = Paillier::encrypt_with_chosen_randomness(
                  &vpk.pk,
                  RawPlaintext::from(&cr.tm2),
                  &Randomness::from(&cr.tm3)).0.into_owned();
    let tm = BigInt::mod_mul(&BigInt::mod_pow(&ct, &cr.tm1, n2),
                             &tm_ct,
                             n2);

    let tr_ct = Paillier::encrypt_with_chosen_randomness(
                  &vpk.pk,
                  RawPlaintext::from(&cr.tr2),
                  &Randomness::from(&cr.tr3)).0.into_owned();
    let tr = BigInt::mod_mul(&BigInt::mod_pow(&ct, &cr.tr1, n2),
                             &tr_ct,
                             n2);

    DVResp1{sm, sr, tm, tr}
}

pub fn verify2(params: &DVParams) -> DVChallenge2 {
    let d = BigInt::sample(params.lambda as usize);
    DVChallenge2(d)
}

pub fn prove3(vpk: &VPK,
              cr: &DVComRand,
              wit: &DVWit,
              ch: &DVChallenge2) -> DVResp2 {
    let n2: &BigInt = &vpk.pk.nn;
    let d: &BigInt = &ch.0;

    let um1 = BigInt::mod_add(&BigInt::mod_mul(&wit.m, d, n2), &cr.tm1, n2);
    let um2 = BigInt::mod_add(&BigInt::mod_mul(&cr.rm_m, d, n2), &cr.tm2, n2);
    let um3 = BigInt::mod_mul(&BigInt::mod_pow(&cr.rm_r, d, n2), &cr.tm3, n2);

    let ur1 = BigInt::mod_add(&BigInt::mod_mul(&wit.r, d, n2), &cr.tr1, n2);
    let ur2 = BigInt::mod_add(&BigInt::mod_mul(&cr.rr_m, d, n2), &cr.tr2, n2);
    let ur3 = BigInt::mod_mul(&BigInt::mod_pow(&cr.rr_r, d, n2), &cr.tr3, n2);

    DVResp2{um1, um2, um3, ur1, ur2, ur3}
}

pub fn verify3(vsk: &VSK,
               vpk: &VPK,
               lang: &DVLang,
               inst: &DVInst,
               com: &DVCom,
               ch1: &DVChallenge1,
               ch2: &DVChallenge2,
               resp1: &DVResp1,
               resp2: &DVResp2) -> bool {
    let ch1_ct =
        ch1.0.iter()
        .map(|&i| &vpk.cts[i])
        .fold(BigInt::from(1), |ct,cti| BigInt::mod_mul(&ct, cti, &vpk.pk.nn));

    let ch1_raw: BigInt =
        ch1.0.iter()
        .map(|&i| &vsk.chs[i])
        .fold(BigInt::from(0), |acc,x| acc + x );

    let sr = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp1.sr)).0.into_owned();
    let sm = Paillier::decrypt(&vsk.sk,RawCiphertext::from(&resp1.sm)).0.into_owned();

    // a Y^c = Enc_psi(s_m,s_r)
    {
        let pe::PECiphertext{ct1:x1,ct2:x2} =
            pe::encrypt_with_randomness(&lang.pk, &sm, &sr);

        let tmp1 =
            BigInt::mod_mul(
                &BigInt::mod_pow(&inst.ct.ct1, &ch1_raw, &lang.pk.n2),
                &com.a.ct1,
                &lang.pk.n2);
        if tmp1 != x1 { return false; }

        let tmp2 =
            BigInt::mod_mul(
                &BigInt::mod_pow(&inst.ct.ct2, &ch1_raw, &lang.pk.n2),
                &com.a.ct2,
                &lang.pk.n2);
        if tmp2 != x2 { return false; }
    }

    {
        let ct = Paillier::encrypt_with_chosen_randomness(
                &vpk.pk,
                RawPlaintext::from(&resp2.um2),
                &Randomness::from(&resp2.um3)).0.into_owned();
        let rhs = &BigInt::mod_mul(&BigInt::mod_pow(&ch1_ct, &resp2.um1, &vpk.pk.nn), &ct, &vpk.pk.nn);
        let lhs = &BigInt::mod_mul(&BigInt::mod_pow(&resp1.sm, &ch2.0, &vpk.pk.nn), &resp1.tm, &vpk.pk.nn);
        if lhs != rhs { return false; }
    }

    {
        let ct = Paillier::encrypt_with_chosen_randomness(
                &vpk.pk,
                RawPlaintext::from(&resp2.ur2),
                &Randomness::from(&resp2.ur3)).0.into_owned();
        let rhs = &BigInt::mod_mul(&BigInt::mod_pow(&ch1_ct, &resp2.ur1, &vpk.pk.nn), &ct, &vpk.pk.nn);
        let lhs = &BigInt::mod_mul(&BigInt::mod_pow(&resp1.sr, &ch2.0, &vpk.pk.nn), &resp1.tr, &vpk.pk.nn);
        if lhs != rhs { return false; }
    }

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
