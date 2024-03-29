#![allow(dead_code)]

use criterion::{criterion_group, criterion_main, Criterion, BatchSize};
use std::time::Duration;

use rsazkps::bigint::*;

use rsazkps::protocols::paillier as p;
use rsazkps::protocols::paillier_elgamal as pe;
use rsazkps::protocols::paillier_cramer_shoup as pcs;

use rsazkps::protocols::schnorr_generic as sch;
use rsazkps::protocols::schnorr_batched_generic as schb;
use rsazkps::protocols::schnorr_paillier as sp;
use rsazkps::protocols::schnorr_paillier_elgamal as spe;
use rsazkps::protocols::schnorr_paillier_cramer_shoup as spcs;
use rsazkps::protocols::designated as dv;
use rsazkps::protocols::designated_range as dvr;

////////////////////////////////////////////////////////////////////////////
// Paillier (-Elgamal)
////////////////////////////////////////////////////////////////////////////


fn bench_paillier(c: &mut Criterion) {
    let n_bitlen = 2048;
    let mut grp = c.benchmark_group(format!("Paillier log(N)={}", n_bitlen));


    grp.bench_function("keygen", |b| b.iter(|| p::keygen(n_bitlen as usize)));

    grp.bench_function("encrypt_crt", |b| {
        b.iter_batched(|| { let (pk,sk) = p::keygen(n_bitlen as usize);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            (pk,sk,m,r) },
                       |(pk,sk,m,r)| p::encrypt(&pk,Some(&sk),&m,&r),
                       BatchSize::LargeInput);
    });

    grp.bench_function("encrypt_naive", |b| {
        b.iter_batched(|| { let (pk,_) = p::keygen(n_bitlen as usize);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            (pk,m,r) },
                       |(pk,m,r)| p::encrypt(&pk,None,&m,&r),
                       BatchSize::LargeInput);
    });

    grp.bench_function("decrypt", |b| {
        b.iter_batched(|| { let (pk,sk) = p::keygen(n_bitlen as usize);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            let ct = p::encrypt(&pk,Some(&sk),&m,&r);
                            (sk,ct) },
                       |(sk,ct)| p::decrypt(&sk,&ct),
                       BatchSize::LargeInput);
    });
}

fn bench_paillier_elgamal(c: &mut Criterion) {
    let n_bitlen = 2048;
    let mut grp = c.benchmark_group(format!("Paillier-Elgamal log(N)={}", n_bitlen));

    grp.bench_function("keygen", |b| b.iter(|| pe::keygen(n_bitlen as usize)));

    grp.bench_function("encrypt_crt", |b| {
        b.iter_batched(|| { let (pk,sk) = pe::keygen(n_bitlen as usize);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            (pk,sk,m,r) },
                       |(pk,sk,m,r)| pe::encrypt_with_randomness_opt(&pk,Some(&sk),&m,&r),
                       BatchSize::LargeInput);
    });

    grp.bench_function("encrypt_naive", |b| {
        b.iter_batched(|| { let (pk,_) = pe::keygen(n_bitlen as usize);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            (pk,m,r) },
                       |(pk,m,r)| pe::encrypt_with_randomness_opt(&pk,None,&m,&r),
                       BatchSize::LargeInput);
    });
}

fn bench_paillier_cramer_shoup(c: &mut Criterion) {
    let n_bitlen = 2048;
    let mut grp = c.benchmark_group(format!("Paillier-Cramer-Shoup log(N)={}", n_bitlen));


    grp.bench_function("keygen", |b| b.iter(|| pcs::keygen(n_bitlen as usize)));

    grp.bench_function("encrypt_crt", |b| {
        b.iter_batched(|| { let (pk,sk) = pcs::keygen(n_bitlen);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            (pk,sk,m,r) },
                       |(pk,sk,m,r)| pcs::encrypt(&pk,Some(&sk),&m,&r),
                       BatchSize::LargeInput);
    });

    grp.bench_function("encrypt_naive", |b| {
        b.iter_batched(|| { let (pk,_) = pcs::keygen(n_bitlen);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            (pk,m,r) },
                       |(pk,m,r)| pcs::encrypt(&pk,None,&m,&r),
                       BatchSize::LargeInput);
    });

    grp.bench_function("decrypt", |b| {
        b.iter_batched(|| { let (pk,sk) = pcs::keygen(n_bitlen);
                            let m = BigInt::sample_below(&pk.n);
                            let r = BigInt::sample_below(&pk.n);
                            let ct = pcs::encrypt(&pk,Some(&sk),&m,&r);
                            (pk,sk,ct) },
                       |(pk,sk,ct)| pcs::decrypt(&pk,&sk,&ct),
                       BatchSize::LargeInput);
    });
}


////////////////////////////////////////////////////////////////////////////
// Schnorr generic
////////////////////////////////////////////////////////////////////////////

fn format_params(params: &sch::ProofParams) -> String {
    format!("λ={} log(Ch)={} reps={}, {}",
            params.lambda,
            params.ch_space_bitlen,
            params.reps,
            (if params.range_mode { "+range" } else { "norange" }))
}

fn bench_schnorr<L: sch::SchnorrLang>(c: &mut Criterion,
                               params: &sch::ProofParams,
                               lparams: &L::LangParams) {
    let mut grp = c.benchmark_group(format!("Sch {} {:?}", format_params(params), lparams));

    //grp.measurement_time(Duration::from_secs(120));

    grp.bench_function("lang_verify", |b| {
        b.iter_batched(|| L::sample_lang(lparams),
                       |lang| lang.pre_verify(params),
                       BatchSize::LargeInput);
    });

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| L::sample_liw(lparams).0,
                       |lang| sch::prove1(params,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| sch::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = L::sample_liw(lparams);
                 let (_,cr) = sch::prove1(params,&lang);
                 let ch = sch::verify1(params);
                 (lang,wit,ch,cr) },
            |(lang,wit,ch,cr)| sch::prove2(params,&lang,&wit,&ch,&cr),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = L::sample_liw(lparams);
                 let (com,cr) = sch::prove1(params,&lang);
                 let ch = sch::verify1(params);
                 let resp = sch::prove2(params,&lang,&wit,&ch,&cr);
                 return (lang.to_public(),inst,com,ch,resp); },
            |(lang,inst,com,ch,resp)| sch::verify2(params,&lang,&inst,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

fn bench_schnorr_fs<L: sch::SchnorrLang>(c: &mut Criterion,
                                  params: &sch::ProofParams,
                                  lparams: &L::LangParams) {
    let mut grp = c.benchmark_group(format!("Sch FS {} {:?}", format_params(params), lparams));
    //grp.sample_size(10);


    grp.bench_function("fs_prove", |b| {
        b.iter_batched(|| L::sample_liw(lparams),
                       |(lang,inst,wit)| sch::fs_prove(params,&lang,&inst,&wit),
                       BatchSize::LargeInput);
    });

    grp.bench_function("lang_verify", |b| {
        b.iter_batched(|| L::sample_lang(lparams),
                       |lang| lang.pre_verify(params),
                       BatchSize::LargeInput);
    });

    grp.bench_function("fs_verify", |b| {
        b.iter_batched(|| { let (lang,inst,wit) = L::sample_liw(lparams);
                            let proof = sch::fs_prove(params,&lang,&inst,&wit);
                            (params,lang.to_public(),inst,proof) },
                       |(params,lang,inst,proof)| sch::fs_verify(params,&lang,&inst,&proof),
                       BatchSize::LargeInput);
    });

    grp.finish();
}


////////////////////////////////////////////////////////////////////////////
// Schnorr Paillier Batched
////////////////////////////////////////////////////////////////////////////

fn format_schb_params(params: &schb::ProofParams) -> String {
    format!("λ={} inst_num={}",
            params.lambda,
            params.reps_n)
}

fn bench_schnorr_batched<L: schb::SchnorrBatchedLang>(
    c: &mut Criterion,
    params: &schb::ProofParams,
    lparams: &L::LangParams)
{
    let mut grp =
        c.benchmark_group(format!("Sch batched {}, {:?}",
                                  format_schb_params(params),
                                  lparams
        ));

    //grp.sample_size(10);
    //grp.measurement_time(Duration::from_secs(30));

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| L::sample_liw(params,lparams).0,
                       |lang| schb::prove1(params,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| schb::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = L::sample_liw(params,lparams);
                 let (_,cr) = schb::prove1(params,&lang);
                 let ch = schb::verify1(params);
                 return (lang,wit,ch,cr); },
            |(lang,wit,ch,cr)| schb::prove2(params,&lang,&wit,&ch,&cr),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = L::sample_liw(params,lparams);
                 let (com,cr) = schb::prove1(params,&lang);
                 let ch = schb::verify1(params);
                 let resp = schb::prove2(params,&lang,&wit,&ch,&cr);
                 return (L::to_public(&lang),inst,com,ch,resp); },
            |(lang,inst,com,ch,resp)| schb::verify2(params,&lang,&inst,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

fn bench_schnorr_batched_fs<L: schb::SchnorrBatchedLang>(
    c: &mut Criterion,
    params: &schb::ProofParams,
    lparams: &L::LangParams)
{
    let mut grp =
        c.benchmark_group(format!("Sch batched FS {}",
                                  format_schb_params(params),
        ));

    //grp.sample_size(10);

    grp.bench_function("fs_prove", |b| {
        b.iter_batched(|| L::sample_liw(params,lparams),
                       |(lang,inst,wit)| schb::fs_prove(params,&lang,&inst,&wit),
                       BatchSize::LargeInput);
    });

    grp.bench_function("fs_verify", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = L::sample_liw(params,lparams);
                 let proof = schb::fs_prove(params,&lang,&inst,&wit);
                 return (lang,inst,proof); },
            |(lang,inst,proof)| schb::fs_verify(params,&L::to_public(&lang),&inst,&proof),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

////////////////////////////////////////////////////////////////////////////
// DV
////////////////////////////////////////////////////////////////////////////


fn bench_designated_vpk(c: &mut Criterion, params: &dv::DVParams) {
//    let mut grp = c.benchmark_group(format!("Group 3: Batched Schnorr Paillier for {}", params));
    let mut grp = c.benchmark_group(format!("DV VPK lam = {:?}, malicious {:?}", params.lambda, params.malicious_setup));

    //grp.measurement_time(Duration::from_secs(30));
    //grp.sample_size(10);

    grp.bench_function("keygen", |b| b.iter(|| dv::keygen(params)));

    if params.malicious_setup {
        grp.bench_function("verify_vpk", |b| {
            b.iter_batched(|| dv::keygen(params).0,
                           |vpk| dv::verify_vpk(params,&vpk),
                           BatchSize::LargeInput);
        });
    }
}


fn bench_designated(c: &mut Criterion, params: &dv::DVParams) {
//    let mut grp = c.benchmark_group(format!("Group 3: Batched Schnorr Paillier for {}", params));
    let mut grp = c.benchmark_group(format!("DV lam = {:?}", params.lambda));

    //grp.measurement_time(Duration::from_secs(30));
    //grp.sample_size(2);

    // This could be precomputed for each benchmark, but it's quite expensive?...
    let (vpk,vsk) = dv::keygen(&params);

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| dv::sample_liw(params).0,
                       |lang| dv::prove1(params,&vpk,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| dv::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = dv::sample_liw(params);
                 let (_,cr) = dv::prove1(params,&vpk,&lang);
                 let ch = dv::verify1(params);
                 return (wit,ch,cr); },
            |(wit,ch,cr)| dv::prove2(params,&vpk,&cr,&wit,&ch,0),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| b.iter(|| dv::verify2(params)));

    grp.bench_function("prove3", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = dv::sample_liw(params);
                 let (_,cr) = dv::prove1(params,&vpk,&lang);
                 let ch2 = dv::verify2(params);
                 return (wit,cr,ch2); },
            |(wit,cr,ch2)| dv::prove3(params,&vpk,&cr,&wit,ch2.as_ref()),
            BatchSize::LargeInput
        );
    });


    grp.bench_function("verify3", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = dv::sample_liw(params);
                 let (com,cr) = dv::prove1(params,&vpk,&lang);
                 let ch1 = dv::verify1(params);
                 let resp1 = dv::prove2(params,&vpk,&cr,&wit,&ch1,0);
                 let ch2 = dv::verify2(params);
                 let resp2 = dv::prove3(params,&vpk,&cr,&wit,ch2.as_ref());
                 return (lang,inst,com,ch1,ch2,resp1,resp2); },
            |(lang,inst,com,ch1,ch2,resp1,resp2)|
            dv::verify3(params,&vsk,&vpk,&lang,&inst,
                        &com,&ch1,ch2.as_ref(),&resp1,resp2.as_ref(),0),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

fn bench_designated_fs(c: &mut Criterion, params: &dv::DVParams) {
//    let mut grp = c.benchmark_group(format!("Group 3: Batched Schnorr Paillier for {}", params));
    let mut grp = c.benchmark_group(format!("DV FS lam = {:?}, malicious {:?}, GGM {:?}", params.lambda, params.malicious_setup, params.ggm_mode));

    // This could be precomputed for each benchmark, but it's quite expensive?...
    let (vpk,vsk) = dv::keygen(&params);

    grp.bench_function("fs_prove", |b| {
        b.iter_batched(|| dv::sample_liw(params),
                       |(lang,inst,wit)|
                       dv::fs_prove(params,&vpk,&lang,&inst,&wit,0),
                       BatchSize::LargeInput);
    });

    grp.bench_function("fs_verify", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = dv::sample_liw(params);
                 let proof = dv::fs_prove(params,&vpk,&lang,&inst,&wit,0);
                 return (lang,inst,proof); },
            |(lang,inst,proof)|
            dv::fs_verify(params,&vsk,&vpk,&lang,&inst,0,&proof),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}



////////////////////////////////////////////////////////////////////////////
// DVRange
////////////////////////////////////////////////////////////////////////////


fn bench_designated_range_vpk(c: &mut Criterion, params: &dvr::DVRParams) {
//    let mut grp = c.benchmark_group(format!("Group 3: Batched Schnorr Paillier for {}", params));
    let mut grp = c.benchmark_group(format!("DVR VPK malicious {:?}, GGM {:?}", params.malicious_setup, params.ggm_mode));

    //grp.measurement_time(Duration::from_secs(30));
    //grp.sample_size(10);

    grp.bench_function("keygen", |b| b.iter(|| dvr::keygen(params)));


    if params.malicious_setup {
    grp.bench_function("verify_vpk", |b| {
        b.iter_batched(|| dvr::keygen(params).0,
                       |vpk| dvr::verify_vpk(params,&vpk),
                       BatchSize::LargeInput);
    });
    }
}


fn bench_designated_range_fs(c: &mut Criterion, params: &dvr::DVRParams) {
//    let mut grp = c.benchmark_group(format!("Group 3: Batched Schnorr Paillier for {}", params));
    let mut grp = c.benchmark_group(format!("DVRange FS malicious {:?}, GGM {:?}", params.malicious_setup, params.ggm_mode));

    // This could be precomputed for each benchmark, but it's quite expensive?...
    let (vpk,vsk) = dvr::keygen(&params);

    grp.bench_function("fs_prove", |b| {
        b.iter_batched(|| dvr::sample_liw(params),
                       |(lang,inst,wit)|
                       dvr::fs_prove(params,&vpk,&lang,&inst,&wit,0),
                       BatchSize::LargeInput);
    });

    grp.bench_function("fs_verify", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = dvr::sample_liw(params);
                 let proof = dvr::fs_prove(params,&vpk,&lang,&inst,&wit,0);
                 return (lang,inst,proof); },
            |(lang,inst,proof)|
            dvr::fs_verify(params,&vsk,&vpk,&lang,&inst,0,&proof),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}


////////////////////////////////////////////////////////////////////////////
// All
////////////////////////////////////////////////////////////////////////////



fn bench_schnorr_all(c: &mut Criterion) {
    let lambda = 128;
    let n_bitlen = 2048;

    // q = 128, 8, 7, 6, 5
    for i in [1, 16, 19, 22, 26] {
        let params = sch::ProofParams::new(lambda,i);
        bench_schnorr_fs::<sp::PLang>(c, &params, &sp::PLangParams{ n_bitlen, range: None });
        bench_schnorr_fs::<spe::PELang>(c, &params, &spe::PELangParams{n_bitlen, range:None });
    }

    let range_bitlen = 256;
    let range = BigInt::pow(&BigInt::from(2),range_bitlen);

    bench_schnorr_fs::<sp::PLang>(c, &sch::ProofParams::new_range(lambda), &sp::PLangParams{ n_bitlen, range:Some(range.clone()) });
    bench_schnorr_fs::<spe::PELang>(c, &sch::ProofParams::new_range(lambda), &spe::PELangParams{ n_bitlen, range:Some(range.clone()) });


    //let reps_n = 128;
    //bench_schnorr_batched_fs::<spcs::PCSLang>(
    //    c,
    //    &schb::ProofParams::new(lambda,reps_n),
    //    &spcs::PCSLangParams{n_bitlen, range_bitlen});
    //bench_schnorr_batched_fs::<sp::PLang>(
    //    c,
    //    &schb::ProofParams::new(lambda,reps_n),
    //    &sp::PLangParams{n_bitlen, range: Some(range.clone())});

}


fn bench_designated_all(c: &mut Criterion) {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries = 128;

    bench_designated_vpk(c,&dv::DVParams::new(n_bitlen, lambda, queries, true, false));
    bench_designated_vpk(c,&dv::DVParams::new(n_bitlen, lambda, queries, false, false));

    bench_designated_fs(c,&dv::DVParams::new(n_bitlen, lambda, queries, true, false));
    bench_designated_fs(c,&dv::DVParams::new(n_bitlen, lambda, queries, false, false));
    bench_designated_fs(c,&dv::DVParams::new(n_bitlen, lambda, queries, true, true));
    bench_designated_fs(c,&dv::DVParams::new(n_bitlen, lambda, queries, false, true));
}

fn bench_designated_range_all(c: &mut Criterion) {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries = 128;
    let range_bitlen = 256;

    bench_designated_range_vpk(c,&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, false, false));
    bench_designated_range_vpk(c,&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries as u32, true, false));

    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries, true, false));
    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries, false, false));
    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries, true, true));
    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range_bitlen, queries, false, true));
}


//criterion_group!(benches, bench_designated_all, bench_designated_range_all, bench_schnorr_all);
//criterion_group!(benches, bench_designated_all);
//criterion_group!(benches, bench_designated_range_all);
//criterion_group!(benches, bench_schnorr_all);
criterion_group!(benches, bench_paillier, bench_paillier_elgamal, bench_paillier_cramer_shoup);
//criterion_group!(benches, bench_paillier_cramer_shoup);
criterion_main!(benches);
