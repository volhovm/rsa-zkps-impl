#![allow(dead_code)]

use get_size::GetSize;

use serde::ser::{Serialize};
use std::time::{SystemTime};

use rsazkps::bigint::*;

use rsazkps::protocols::paillier as p;

use rsazkps::protocols::schnorr_generic as sch;
use rsazkps::protocols::schnorr_paillier as sp;
use rsazkps::protocols::schnorr_paillier_elgamal as spe;
use rsazkps::protocols::schnorr_paillier_batched as spb;
use rsazkps::protocols::schnorr_exp as se;

use rsazkps::protocols::designated as dv;
use rsazkps::protocols::designated_range as dvr;


fn to_vec_opt<T:Serialize>(x: &T) -> Result<Vec<u8>,rmp_serde::encode::Error> {
    let mut wr = Vec::with_capacity(128);
    let mut serializer = rmp_serde::encode::Serializer::new(&mut wr).with_binary();
    x.serialize(&mut serializer)?;
    Ok(wr)
}

fn estimate_size<T: GetSize>(x: &T) -> f64 {
    (x.get_heap_size() as f64) / 1024.0
    //let x: Vec<u8> = rmp_serde::to_vec(x).unwrap();

   //// println!("serialized: {:?}",x);
    //(x.len() as f64) / 1024.0
}


fn debug_bignum_size() {
    let (pk,_sk) = p::keygen(4096);
    let n = pk.n;
    println!("n.bit_length: {}", n.bit_length());
    println!("n.to_bytes.len: {}", n.to_bytes().len());
    println!("serialized len: {}", rmp_serde::to_vec(&n).unwrap().len());
    println!("to_vec_opt len: {}", to_vec_opt(&n).unwrap().len());

    let stupid: Vec<u8> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    println!("stupid len: {}", stupid.len());
    println!("to_vec_opt stupid: {}", to_vec_opt(&stupid).unwrap().len());
    println!("stupid get_size: {}", (&stupid).get_heap_size());

    let nbytes: Vec<u8> = n.to_bytes();
    println!("nbytes len: {}", nbytes.len());
    println!("to_vec_opt nbytes: {}", to_vec_opt(&nbytes).unwrap().len());
    println!("nbytes get_size: {}", (&nbytes).get_heap_size());
    //println!("estimate_size: {:.2} KB", estimate_size(&n));
}

fn estimate_size_designated(params: &dv::DVParams) {
    print!("DV FS, malicious {:?}, GGM {:?}. ",
             params.malicious_setup, params.ggm_mode);

    let (vpk,vsk) = dv::keygen(&params);
    //println!("vpk_n_bitlen: {}", params.vpk_n_bitlen());
    //println!("VPK.cts[0]: {:.2} KB, VPK.cts[0].len: {}, to_bytes.len: {}",
    //         estimate_size(&vpk.cts[0]),
    //         vpk.cts[0].bit_length(),
    //         vpk.cts[0].to_bytes().len());
    ////assert!(false);
    //println!("VPK.pk: {:.2} KB, VPK.cts: {:.2} KB",
    //         estimate_size(&vpk.pk),
    //         estimate_size(&vpk.cts));

    dv::verify_vpk(&params, &vpk);
    let (lang,inst,wit) = dv::sample_liw(params);
    let proof = dv::fs_prove(params,&vpk,&lang,&inst,&wit,0);
    println!("VPK: {:.2} KB, VSK: {:.2} KB, proof: {:.2} KB",
             estimate_size(&vpk),
             estimate_size(&vsk),
             estimate_size(&proof))
}

fn estimate_size_designated_range(params: &dvr::DVRParams) {
    print!("DVRange FS, malicious {:?}, GGM {:?}. ",
             params.malicious_setup, params.ggm_mode);

    let (vpk,vsk) = dvr::keygen(&params);
    let (lang,inst,wit) = dvr::sample_liw(params);
    let proof = dvr::fs_prove(params,&vpk,&lang,&inst,&wit,0);

    println!("VPK: {:.2} KB, VSK: {:.2} KB, proof: {:.2} KB",
             estimate_size(&vpk),
             estimate_size(&vsk),
             estimate_size(&proof))
}

fn estimate_size_schnorr<L: sch::Lang>(params: &sch::ProofParams, lparams: &L::LangParams) {
    print!("Schnorr FS, {:?} {:?}. ", params, lparams);

    let (lang,inst,wit) = L::sample_liw(lparams);
    let proof = sch::fs_prove(&params,&lang,&inst,&wit);

    println!("proof: {:.2} KB",
             estimate_size(&proof))
}

fn estimate_proof_sizes() {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries = 128;
    let range_bitlen = 256;

    println!("Estimating proof sizes; log(N) = {}, lambda = {}, queries = {}, log(Range) = {}",
             n_bitlen, lambda, queries, range_bitlen);

    estimate_size_schnorr::<sp::PLang>(
        &sch::ProofParams::new_range(lambda),
        &sp::PLangParams{ n_bitlen, range: Some(BigInt::pow(&BigInt::from(2),range_bitlen))});

    for ch_space_bitlen in [1,16,19,22,26] {
        estimate_size_schnorr::<sp::PLang>(
            &sch::ProofParams::new(lambda, ch_space_bitlen),
            &sp::PLangParams{ n_bitlen, range: None });
    }

    //estimate_size_schnorr::<spe::PELang>(
    //    &sch::ProofParams::new(lambda, 1),
    //    &n_bitlen);
    //estimate_size_schnorr::<spe::PELang>(
    //    &sch::ProofParams::new(lambda, 22),
    //    &n_bitlen);


    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, false, true));
    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, true, true));
    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, false, false));
    estimate_size_designated(&dv::DVParams::new(n_bitlen, lambda, queries, true, false));

    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, false, true));
    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, true, true));
    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, false, false));
    estimate_size_designated_range(&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, true, false));

}



fn profile_schnorr_generic<L: sch::Lang>(params: &sch::ProofParams, lparams: &L::LangParams) {
    let (lang,inst,wit) = L::sample_liw(lparams);

    let t_1 = SystemTime::now();
    let (com,cr) = sch::prove1(params,&lang);
    let t_2 = SystemTime::now();
    let ch = sch::verify1(params);
    let t_3 = SystemTime::now();
    let resp = sch::prove2(params,&lang,&wit,&ch,&cr);
    let t_4 = SystemTime::now();
    sch::verify2(params,&lang.to_public(),&inst,&com,&ch,&resp);
    let t_5 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_total = t_5.duration_since(t_1).unwrap();


    println!("Schnorr (total {:?}):
prove1   {:?}
verify1  {:?}
prove2   {:?}
verify2  {:?}",
             t_total,t_delta1, t_delta2, t_delta3, t_delta4);

}

fn profile_schnorr() {
    let n_bitlen = 2048;
    let lambda = 128;
    let ch_space_bitlen = 16;

    profile_schnorr_generic::<sp::PLang>(
        &sch::ProofParams::new(lambda, ch_space_bitlen),
        &sp::PLangParams{ n_bitlen, range: None });

    profile_schnorr_generic::<spe::PELang>(
        &sch::ProofParams::new(lambda, ch_space_bitlen),
        &n_bitlen);

    profile_schnorr_generic::<se::ExpNLang>(
        &sch::ProofParams::new(lambda, ch_space_bitlen),
        &n_bitlen);
}

fn profile_schnorr_batched() {
    let n_bitlen = 2700;
    let lambda = 128;
    let range_bits = 256;
    let reps_number = 128;
    let params = spb::ProofParams::new(n_bitlen,lambda,reps_number,range_bits);

    let (lang,inst,wit) = spb::sample_liw(&params);

    // This difference is
    //let range_bits = lambda;
    //let range_bits = 2 * lambda + utils::log2ceil(lambda);

    let t_1 = SystemTime::now();
    let (com,cr) = spb::prove1(&params,&lang);
    let t_2 = SystemTime::now();
    let ch = spb::verify1(&params);

    let t_3 = SystemTime::now();
    let resp = spb::prove2(&params,&lang,&wit,&ch,&cr);
    let t_4 = SystemTime::now();
    assert!(spb::verify2(&params,&spb::to_public(&lang),&inst,&com,&ch,&resp));
    let t_5 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_total = t_5.duration_since(t_1).unwrap();

    println!("Schnorr Paillier Batched (total {:?}):
prove1   {:?}
verify1  {:?}
prove2   {:?}
verify2  {:?}",
             t_total,t_delta1, t_delta2, t_delta3, t_delta4);


}

fn profile_dv() {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries: usize = 128;
    let malicious_setup = true;
    let ggm_mode = true;
    let params = dv::DVParams::new(n_bitlen, lambda, queries as u32, malicious_setup, ggm_mode);

    println!("n_bitlen: {}, vpk_n_bitlen: {}", n_bitlen, params.vpk_n_bitlen());
    println!("max_ch_bitlen {}, max_ch_proven_bitlen {}",
             params.max_ch_bitlen(),
             params.max_ch_proven_bitlen());

    let (vpk,vsk) = dv::keygen(&params);

    assert!(dv::verify_vpk(&params,&vpk));

    for query_ix in 0..1 {
    let (lang,inst,wit) = dv::sample_liw(&params);

    let t_1 = SystemTime::now();
    let (com,cr) = dv::prove1(&params,&vpk,&lang);
    let t_2 = SystemTime::now();
    let ch1 = dv::verify1(&params);
    let t_3 = SystemTime::now();
    let resp1 = dv::prove2(&params,&vpk,&cr,&wit,&ch1,query_ix);
    let t_4 = SystemTime::now();
    let ch2 = dv::verify2(&params);
    let t_5 = SystemTime::now();
    let resp2 = dv::prove3(&params,&vpk,&cr,&wit,ch2.as_ref());
    let t_6 = SystemTime::now();

    dv::verify3(&params,&vsk,&vpk,&lang,&inst,
            &com,&ch1,ch2.as_ref(),&resp1,resp2.as_ref(),query_ix);
    let t_7 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_delta5 = t_6.duration_since(t_5).unwrap();
    let t_delta6 = t_7.duration_since(t_6).unwrap();
    let t_total = t_7.duration_since(t_1).unwrap();
    println!("DV (total {:?}):
  prove1   {:?}
  verify1  {:?}
  prove2   {:?}
  verify2  {:?}
  prove3   {:?}
  verify3  {:?}",
             t_total,t_delta1, t_delta2, t_delta3, t_delta4, t_delta5, t_delta6);

    }
}

fn profile_dv_range() {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries: usize = 128;
    let range_bitlen = 256;
    let malicious_setup = false;
    let ggm_mode = false;
    let params = dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, malicious_setup, ggm_mode);

    println!("n_bitlen: {}, vpk_n_bitlen: {}", n_bitlen, params.vpk_n_bitlen);
    println!("max_ch_bitlen {}, max_ch_proven_bitlen {}",
             params.max_ch_bitlen,
             params.max_ch_proven_bitlen);
    println!("tau range: {}", params.tau_range_bitlen);

    let (vpk,vsk) = dvr::keygen(&params);

    assert!(dvr::verify_vpk(&params,&vpk));

    for query_ix in 0..1 {
    let (lang,inst,wit) = dvr::sample_liw(&params);

    let t_1 = SystemTime::now();
    let (com,cr) = dvr::prove1(&params,&vpk,&lang,&wit);
    let t_2 = SystemTime::now();
    let ch1 = dvr::verify1(&params);
    let t_3 = SystemTime::now();
    let (resp1,resp1rand) = dvr::prove2(&params,&vpk,&wit,&ch1,&cr,query_ix);
    let t_4 = SystemTime::now();
    let ch2 = dvr::verify2(&params);
    let t_5 = SystemTime::now();
    let resp2 = dvr::prove3(&params,&vpk,&wit,&ch1,&cr,&resp1rand,ch2.as_ref(),query_ix);
    let t_6 = SystemTime::now();

    dvr::verify3(&params,&vsk,&vpk,&lang,&inst,
            &com,&ch1,&resp1,ch2.as_ref(),resp2.as_ref(),query_ix);
    let t_7 = SystemTime::now();

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_delta4 = t_5.duration_since(t_4).unwrap();
    let t_delta5 = t_6.duration_since(t_5).unwrap();
    let t_delta6 = t_7.duration_since(t_6).unwrap();
    let t_total = t_7.duration_since(t_1).unwrap();
    println!("DV Range (total {:?}):
  prove1   {:?}
  verify1  {:?}
  prove2   {:?}
  verify2  {:?}
  prove3   {:?}
  verify3  {:?}",
             t_total,t_delta1, t_delta2, t_delta3, t_delta4, t_delta5, t_delta6);

    }
}

fn main() {
    //rsazkps::protocols::designated_range::test_keygen_correctness();
    estimate_proof_sizes();
    //profile_schnorr();
    //profile_schnorr_batched();
    //profile_dv();
    //profile_dv_range();
    //debug_bignum_size();
}
