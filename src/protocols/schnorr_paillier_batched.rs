use curv::arithmetic::traits::{Modulo, Samplable, BasicOps, BitManipulation};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, DecryptionKey, Randomness, RawPlaintext, Keypair};
use paillier::*;
use serde::{Serialize};
use std::time::{SystemTime, UNIX_EPOCH};
use std::fmt;

use super::utils::PROFILE_SPB;
use super::paillier::paillier_enc_opt;


// Common parameters for the proof system.
#[derive(Clone, PartialEq, Debug)]
pub struct ProofParams {
    /// Bitlength of the RSA modulus.
    pub n_bitlen: u32,
    /// Security parameter, also.
    pub lambda: u32,
    /// Number of repeats n, equal to the number of instances, usually =lambda
    pub reps_n: u32,
    /// m = 2 * n - 1
    pub reps_m: u32,
    /// Challenge space, 2^n = 2^reps
    pub ch_space: BigInt,
    /// Range of the original message value, R
    pub range: BigInt,
    /// 2^{λ-1} R n
    pub rand_range: BigInt,
}

impl ProofParams {
    pub fn new(n_bitlen: u32, lambda: u32, reps_n: u32, range_bits: u32) -> Self {
        let range = BigInt::pow(&BigInt::from(2), range_bits);
        let rand_range =
            BigInt::pow(&BigInt::from(2), lambda - 1) * &range * BigInt::from(reps_n);
        let ch_space = BigInt::pow(&BigInt::from(2), reps_n);
        let reps_m = reps_n * 2 - 1;
        return ProofParams { n_bitlen, lambda, reps_n, reps_m,
                             range, rand_range, ch_space };
    }

}

impl fmt::Display for ProofParams {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ProofParams ( logN: {}, lambda: {}, reps: {}, range: {} )",
               self.n_bitlen,
               self.lambda,
               self.reps_n,
               self.range)
    }
}



#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Lang {
    /// Public key that is used to generate instances.
    pub pk: EncryptionKey,
    /// Optional decryption key. If present, speeds up proving and verification.
    pub sk: Option<DecryptionKey>,
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Inst {
    /// The encryption ciphertext
    pub cts: Vec<BigInt>
}

#[derive(Clone, PartialEq, Debug)]
pub struct Wit {
    pub ms: Vec<BigInt>,
    pub rs: Vec<BigInt>,
}

pub fn sample_lang(params: &ProofParams) -> Lang {
    let (pk,sk) = Paillier::keypair_with_modulus_size(params.n_bitlen as usize).keys();
    Lang { pk: pk, sk: Some(sk) }
}

pub fn to_public(lang: &Lang) -> Lang {
    let mut other = lang.clone();
    other.sk = None;
    other
}

pub fn sample_inst(params: &ProofParams, lang: &Lang) -> (Inst,Wit) {
    let ms: Vec<BigInt> =
        (0..params.reps_n).map(|_|
          BigInt::sample_below(&params.range) - &params.range/2).collect();

    let rs: Vec<BigInt> =
        (0..params.reps_n).map(|_| BigInt::sample_below(&lang.pk.n)).collect();
    let cts: Vec<BigInt> =
        ms.iter().zip(rs.iter())
        .map(|(m,r)|
            paillier_enc_opt(&lang.pk, lang.sk.as_ref(), m, r))
        .collect();

    let inst = Inst { cts };
    let wit = Wit { ms, rs };

    return (inst,wit);
}

pub fn sample_liw(params: &ProofParams) -> (Lang,Inst,Wit) {
    let lang = sample_lang(params);
    let (inst,wit) = sample_inst(params, &lang);
    (lang,inst,wit)
}

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Commitment(Vec<BigInt>);

#[derive(Clone, PartialEq, Debug)]
pub struct ComRand(Vec<BigInt>,Vec<BigInt>);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Challenge(BigInt);

#[derive(Clone, PartialEq, Debug, Serialize)]
pub struct Response(Vec<BigInt>,Vec<BigInt>);



pub fn prove1(params: &ProofParams, lang: &Lang) -> (Commitment,ComRand) {
    let n: &BigInt = &lang.pk.n;

    let rand_m_v: Vec<_> =
        (0..params.reps_m).map(|_| BigInt::sample_below(&params.rand_range)).collect();
    let rand_r_v: Vec<_> = (0..params.reps_m).map(|_| BigInt::sample_below(n)).collect();
    let com_v: Vec<_> =
        rand_m_v.iter().zip(rand_r_v.iter()).map(|(rm,rr)|
            paillier_enc_opt(&lang.pk, lang.sk.as_ref(), rm, rr)).collect();

    (Commitment(com_v),ComRand(rand_m_v,rand_r_v))
}


pub fn verify1(params: &ProofParams) -> Challenge {
    //Challenge(BigInt::from(128))
    Challenge(BigInt::sample_below(&params.ch_space))
}

fn challenge_e_mat(reps_m: usize, reps_n: usize, e: &BigInt) -> Vec<Vec<BigInt>> {
    let mut e_mat: Vec<Vec<BigInt>> =
        vec![vec![BigInt::from(0);reps_n];reps_m];
    for i in 0..reps_m {
        for j in 0..reps_n {
            if (i < reps_n && j <= i) ||
               (i >= reps_n && j >= i - reps_n) {
                e_mat[i][j] = BigInt::from(e.test_bit(reps_n - 1 + i - j) as u32);
            }
        }
    }
    e_mat
}

pub fn prove2(params: &ProofParams,
              lang: &Lang,
              wit: &Wit,
              ch: &Challenge,
              cr: &ComRand) -> Response {

    let reps_n = params.reps_n as usize;
    let reps_m = params.reps_m as usize;

    let e_mat = challenge_e_mat(reps_m,reps_n,&ch.0);

    let sm: Vec<BigInt> = (0..reps_m).map(|i| {
        let em =
            (0..reps_n)
            .map(|j| &e_mat[i][j] * &wit.ms[j])
            .fold(BigInt::from(0), |acc,x| acc + x );
        em + &cr.0[i]
    }).collect();

    // TODO This can be optimised when factorization of n is known.
    // It's very much not a bottleneck though.
    let sr: Vec<BigInt> = (0..reps_m).map(|i| {
        let em =
            (0..reps_n)
            .map(|j| BigInt::mod_pow(&wit.rs[j], &e_mat[i][j], &lang.pk.n))
            .fold(BigInt::from(1), |acc,x| BigInt::mod_mul(&acc,  &x, &lang.pk.n));
        BigInt::mod_mul(&em, &cr.1[i], &lang.pk.n)
    }).collect();

    Response(sm, sr)
}

pub fn verify2(params: &ProofParams,
               lang: &Lang,
               inst: &Inst,
               com: &Commitment,
               ch: &Challenge,
               resp: &Response) -> bool {
    let t_1 = SystemTime::now();

    let reps_n = params.reps_n as usize;
    let reps_m = params.reps_m as usize;
    let e_mat = challenge_e_mat(reps_m,reps_n,&ch.0);

    let t_2 = SystemTime::now();
    let t_3 = SystemTime::now();
    let t_4 = SystemTime::now();


    let mut t_delta2 = t_3.duration_since(t_2).unwrap();
    let mut t_delta3 = t_4.duration_since(t_3).unwrap();
    for i in 0..(params.reps_m as usize) {
        let a = &com.0[i];
        let s_m = &resp.0[i];
        let s_r = &resp.1[i];

        if s_m >= &params.rand_range { return false; }

        let t_2 = SystemTime::now();
        let ct_e =
                (0..params.reps_n as usize)
                .map(|j| BigInt::mod_pow(&inst.cts[j], &e_mat[i][j], &lang.pk.nn))
                .fold(BigInt::from(1), |acc,x| BigInt::mod_mul(&acc, &x, &lang.pk.nn));
        let lhs = BigInt::mod_mul(&a, &ct_e, &lang.pk.nn);
        let t_3 = SystemTime::now();

        let rhs = paillier_enc_opt(&lang.pk, lang.sk.as_ref(), s_m, s_r);
        let t_4 = SystemTime::now();
//        let rhs_doublecheck =
//            BigInt::mod_mul(
//                &BigInt::mod_pow(&(&lang.pk.n + 1), &s_m, &lang.pk.nn),
//                &BigInt::mod_pow(s_r, &lang.pk.n, &lang.pk.nn),
//                &lang.pk.nn);
//
//        assert!(rhs == rhs_doublecheck);

        t_delta2 = t_delta2 + t_3.duration_since(t_2).unwrap();
        t_delta3 = t_delta3 + t_4.duration_since(t_3).unwrap();


        if lhs != rhs {
            return false; }
    }
    let t_5 = SystemTime::now();

    let t_total = t_5.duration_since(t_1).unwrap();

    if PROFILE_SPB {
        println!("Sch batched verify2 (total {:?}):
  lhs        total {:?}
  rhs (enc)  total {:?}",
                 t_total, t_delta2, t_delta3);
    }


    return true;
}





#[derive(Clone, Debug, Serialize)]
pub struct FSProof {
    fs_com : Commitment,
    fs_ch : Challenge,
    fs_resp : Response
}

fn fs_compute_challenge(len: usize, lang: &Lang, inst:&Inst, fs_com: &Commitment) -> Challenge {
    use blake2::*;
    let x: Vec<u8> = rmp_serde::to_vec(&(fs_com, inst, lang)).unwrap();
    // Use Digest::digest, but it asks for a fixed-sized slice?
    let mut hasher: Blake2b = Digest::new();
    hasher.update(&x);
    let mut res = BigInt::from(0);
    let r0 = hasher.finalize();
    for i in 0..len {
        for j in 0..8 {
            res.set_bit(i, &(r0.as_slice())[i/8] & (0b0000_0001 << j) == 1);
        }
    }
    Challenge(res)
}

pub fn fs_prove(params: &ProofParams,
                lang: &Lang,
                inst: &Inst,
                wit: &Wit) -> FSProof {
    let t_start = SystemTime::now();
    let (fs_com,cr) = prove1(&params,&lang);
    let t_p1 = SystemTime::now();
    let fs_ch = fs_compute_challenge(params.reps_n as usize,lang,inst,&fs_com);
    let t_p2 = SystemTime::now();
    let fs_resp = prove2(&params,&lang,&wit,&fs_ch,&cr);

    let t_p3 = SystemTime::now();

    let _t_delta1 = t_p1.duration_since(t_start).expect("error1");
    let _t_delta2 = t_p2.duration_since(t_p1).expect("error2");
    let _t_delta3 = t_p3.duration_since(t_p2).expect("error2");
    let _t_total = t_p3.duration_since(t_start).expect("error2");
    //println!("schnorr batched fs_prove time (total {:?}): prove1: {:?}, compute_ch {:?}; resp: {:?}",t_total, t_delta1, t_delta2, t_delta3);


    FSProof{ fs_com, fs_ch, fs_resp }
}

pub fn fs_verify(params: &ProofParams,
                 lang: &Lang,
                 inst: &Inst,
                 proof: &FSProof) -> bool {
    let fs_ch_own = fs_compute_challenge(params.reps_n as usize,lang,inst,&proof.fs_com);
    if fs_ch_own != proof.fs_ch { return false; }

    verify2(&params,&lang,&inst,&proof.fs_com,&proof.fs_ch,&proof.fs_resp)
}


#[cfg(test)]
pub mod tests {
    use crate::protocols::schnorr_paillier_batched::*;

    #[test]
    fn test_correctness() {
        for _i in 0..1 {
            let params = ProofParams::new(1024, 128, 128, 32);
            let (lang,inst,wit) = sample_liw(&params);

            let (com,cr) = prove1(&params,&lang);
            let ch = verify1(&params);

            let resp = prove2(&params,&lang,&wit,&ch,&cr);
            assert!(verify2(&params,&lang,&inst,&com,&ch,&resp));
        }
    }

    #[test]
    fn test_correctness_fs() {
        let params = ProofParams::new(1024, 128, 128, 32);
        let (lang,inst,wit) = sample_liw(&params);

        let proof = fs_prove(&params,&lang,&inst,&wit);
        assert!(fs_verify(&params,&lang,&inst,&proof));
    }


}
