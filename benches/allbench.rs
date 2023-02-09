#![allow(dead_code)]

use curv::arithmetic::traits::BasicOps;
use curv::BigInt;
use criterion::{criterion_group, criterion_main, Criterion, BatchSize};
use std::time::Duration;

use rsazkps::protocols::schnorr_generic as sch;
use rsazkps::protocols::schnorr_paillier as sp;
use rsazkps::protocols::schnorr_paillier_elgamal as spe;
use rsazkps::protocols::schnorr_paillier_batched as spb;
use rsazkps::protocols::designated as dv;
use rsazkps::protocols::designated_range as dvr;

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

fn bench_schnorr<L: sch::Lang>(c: &mut Criterion,
                               params: &sch::ProofParams,
                               lparams: &L::LangParams) {
    let mut grp = c.benchmark_group(format!("Sch {} {:?}", format_params(params), lparams));

    grp.measurement_time(Duration::from_secs(120));

    grp.bench_function("lang_verify", |b| {
        b.iter_batched(|| L::sample_lang(lparams),
                       |lang| lang.verify(params),
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

fn bench_schnorr_fs<L: sch::Lang>(c: &mut Criterion,
                                  params: &sch::ProofParams,
                                  lparams: &L::LangParams) {
    let mut grp = c.benchmark_group(format!("Sch FS {} {:?}", format_params(params), lparams));
    grp.sample_size(10);


    grp.bench_function("fs_prove", |b| {
        b.iter_batched(|| L::sample_liw(lparams),
                       |(lang,inst,wit)| sch::fs_prove(params,&lang,&inst,&wit),
                       BatchSize::LargeInput);
    });

    grp.bench_function("lang_verify", |b| {
        b.iter_batched(|| L::sample_lang(lparams),
                       |lang| lang.verify(params),
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

fn bench_schnorr_paillier_batched(c: &mut Criterion, params: &spb::ProofParams) {
    let mut grp = c.benchmark_group(format!("Batched S-P {:?}", params));

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| spb::sample_liw(params).0,
                       |lang| spb::prove1(params,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| spb::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = spb::sample_liw(params);
                 let (_,cr) = spb::prove1(params,&lang);
                 let ch = spb::verify1(params);
                 return (lang,wit,ch,cr); },
            |(lang,wit,ch,cr)| spb::prove2(params,&lang,&wit,&ch,&cr),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = spb::sample_liw(params);
                 let (com,cr) = spb::prove1(params,&lang);
                 let ch = spb::verify1(params);
                 let resp = spb::prove2(params,&lang,&wit,&ch,&cr);
                 let mut lang2 = lang.clone();
                 lang2.sk = None;
                 return (lang2,inst,com,ch,resp); },
            |(lang,inst,com,ch,resp)| spb::verify2(params,&lang,&inst,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

fn bench_schnorr_paillier_batched_fs(c: &mut Criterion, params: &spb::ProofParams) {
    let mut grp = c.benchmark_group(format!("Batched S-P FS {:?}", params));

    grp.bench_function("fs_prove", |b| {
        b.iter_batched(|| spb::sample_liw(params),
                       |(lang,inst,wit)| spb::fs_prove(params,&lang,&inst,&wit),
                       BatchSize::LargeInput);
    });

    grp.bench_function("fs_verify", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = spb::sample_liw(params);
                 let proof = spb::fs_prove(params,&lang,&inst,&wit);
                 return (lang,inst,proof); },
            |(lang,inst,proof)| spb::fs_verify(params,&lang,&inst,&proof),
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
    grp.sample_size(10);

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
                       |lang| dv::prove1(params,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| dv::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = dv::sample_liw(params);
                 let (_,cr) = dv::prove1(params,&lang);
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
                 let (_,cr) = dv::prove1(params,&lang);
                 let ch2 = dv::verify2(params);
                 return (wit,cr,ch2); },
            |(wit,cr,ch2)| dv::prove3(params,&vpk,&cr,&wit,ch2.as_ref()),
            BatchSize::LargeInput
        );
    });


    grp.bench_function("verify3", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = dv::sample_liw(params);
                 let (com,cr) = dv::prove1(params,&lang);
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
    grp.sample_size(10);

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



fn bench_schnorr_paillier_all(c: &mut Criterion) {
    let lambda = 128;
    let n_bitlen = 2048;

    // q = 128, 8, 7, 6, 5
    for i in [1, 16, 19, 22, 26] {
        let params = sch::ProofParams::new(lambda,i);
        let lparams = sp::PLangParams{ n_bitlen, range: None };
        bench_schnorr_fs::<sp::PLang>(c, &params, &lparams);

        bench_schnorr_fs::<spe::PELang>(c, &params, &n_bitlen);
        //bench_schnorr::<spe::PELang>(c, &params, &n_bitlen);
    }

    let range_bits = 128;
    let params = spb::ProofParams::new(n_bitlen,lambda,lambda,range_bits);
    bench_schnorr_paillier_batched_fs(c, &params);
}


fn bench_designated_all(c: &mut Criterion) {
    let n_bitlen = 2048;
    let lambda = 128;
    let queries = 32;

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
    let queries = 32;
    let range = BigInt::pow(&BigInt::from(2), 256);

    bench_designated_range_vpk(c,&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries as u32, false, false));
    bench_designated_range_vpk(c,&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries as u32, true, false));

    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries, true, false));
    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries, false, false));
    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries, true, true));
    bench_designated_range_fs(c,&dvr::DVRParams::new(n_bitlen, lambda, range.clone(), queries, false, true));
}


//criterion_group!(benches, bench_designated_all, bench_designated_range_all);
criterion_group!(benches, bench_designated_all);
//criterion_group!(benches, bench_designated_range_all);
//criterion_group!(benches, bench_schnorr_paillier_all);
criterion_main!(benches);
