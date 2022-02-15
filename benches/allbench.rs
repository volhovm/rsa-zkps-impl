use criterion::{criterion_group, criterion_main, Criterion, BatchSize};
use std::time::Duration;
use rsazkps::protocols::schnorr_paillier as sp;
use rsazkps::protocols::schnorr_paillier_batched as spb;
use rsazkps::protocols::designated as dv;


// TODO the public modulus is not randomized. Should it be?
fn bench_schnorr_paillier_raw(c: &mut Criterion, params: &sp::ProofParams) {
    let mut grp = c.benchmark_group(format!("S-P, {}", params));

    grp.measurement_time(Duration::from_secs(120));

    grp.bench_function("verify0", |b| {
        b.iter_batched(|| sp::sample_liw(params).0,
                       |lang| sp::verify0(params,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| sp::sample_liw(params).0,
                       |lang| sp::prove1(params,&lang),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| sp::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (lang,_,wit) = sp::sample_liw(params);
                 let (_,cr) = sp::prove1(params,&lang);
                 let ch = sp::verify1(params);
                 return (lang,wit,ch,cr); },
            |(lang,wit,ch,cr)| sp::prove2(params,&lang,&wit,&ch,&cr),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| {
        b.iter_batched(
            || { let (lang,inst,wit) = sp::sample_liw(params);
                 let (_,precomp) = sp::verify0(params,&lang);
                 let (com,cr) = sp::prove1(params,&lang);
                 let ch = sp::verify1(params);
                 let resp = sp::prove2(params,&lang,&wit,&ch,&cr);
                 return (lang,inst,precomp,com,ch,resp); },
            |(lang,inst,precomp,com,ch,resp)| sp::verify2(params,&lang,&inst,&precomp,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

fn bench_schnorr_paillier_fs(c: &mut Criterion, params: &sp::ProofParams) {
    let mut grp = c.benchmark_group(format!("S-P FS {}", params));

    grp.bench_function("FS prove", |b| {
        b.iter_batched(|| sp::sample_liw(params),
                       |(lang,inst,wit)| sp::fs_prove(params,&lang,&inst,&wit),
                       BatchSize::LargeInput);
    });

    grp.bench_function("FS verify 0", |b| {
        b.iter_batched(|| sp::sample_lang(params),
                       |lang| sp::fs_verify0(params,&lang).0,
                       BatchSize::LargeInput);
    });

    grp.bench_function("FS verify", |b| {
        b.iter_batched(|| { let (lang,inst,wit) = sp::sample_liw(params);
                            let (_,precomp) = sp::fs_verify0(params,&lang);
                            let proof = sp::fs_prove(params,&lang,&inst,&wit);
                            (params,lang,inst,precomp,proof) },
                       |(params,lang,inst,precomp,proof)| sp::fs_verify(params,&lang,&inst,&precomp,&proof),
                       BatchSize::LargeInput);
    });

    grp.finish();
}

// TODO the public modulus is not randomized. Should it be?
fn bench_schnorr_paillier_batched(c: &mut Criterion, params: &spb::ProofParams) {
    let mut grp = c.benchmark_group(format!("Batched S-P {:?}", params));
//    let mut grp = c.benchmark_group("Batched S-P");

//    grp.measurement_time(Duration::from_secs(30));
//    grp.sample_size(100);

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
                 return (lang,inst,com,ch,resp); },
            |(lang,inst,com,ch,resp)| spb::verify2(params,&lang,&inst,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}


fn bench_designated(c: &mut Criterion, params: &dv::DVParams) {
//    let mut grp = c.benchmark_group(format!("Group 3: Batched Schnorr Paillier for {}", params));
    let mut grp = c.benchmark_group(format!("DV lam = {:?}", params.lambda));

    //grp.measurement_time(Duration::from_secs(30));
    //grp.sample_size(2);

    grp.bench_function("keygen", |b| b.iter(|| dv::keygen(params)));


    grp.bench_function("verify_vpk", |b| {
        b.iter_batched(|| dv::keygen(params).0,
                       |vpk| dv::verify_vpk(params,&vpk),
                       BatchSize::LargeInput);
    });


    //// This could be precomputed for each benchmark, but it's quite expensive?...
    //let (vpk,vsk) = dv::keygen(&params);

    //grp.bench_function("prove1", |b| {
    //    b.iter_batched(|| dv::sample_liw(params).0,
    //                   |lang| dv::prove1(params,&lang),
    //                   BatchSize::LargeInput);
    //});

    //grp.bench_function("verify1", |b| b.iter(|| dv::verify1(params)));

    //grp.bench_function("prove2", |b| {
    //    b.iter_batched(
    //        || { let (lang,_,wit) = dv::sample_liw(params);
    //             let (_,cr) = dv::prove1(params,&lang);
    //             let ch = dv::verify1(params);
    //             return (wit,ch,cr); },
    //        |(wit,ch,cr)| dv::prove2(&vpk,&cr,&wit,&ch),
    //        BatchSize::LargeInput
    //    );
    //});

    //grp.bench_function("verify2", |b| {
    //    b.iter_batched(
    //        || { let (lang,inst,wit) = dv::sample_liw(params);
    //             let (com,cr) = dv::prove1(params,&lang);
    //             let ch = dv::verify1(params);
    //             let resp = dv::prove2(&vpk,&cr,&wit,&ch);
    //             return (lang,inst,com,ch,resp); },
    //        |(lang,inst,com,ch,resp)| dv::verify2(&vsk,&lang,&inst,&com,&ch,&resp),
    //        BatchSize::LargeInput
    //    );
    //});

    grp.finish();
}



fn bench_schnorr_paillier(c: &mut Criterion) {

    let params1 = sp::ProofParams::new(2048,256,15);
    bench_schnorr_paillier_raw(c, &params1);
    bench_schnorr_paillier_fs(c, &params1);

    // Not checking for small primes
    let params2 = sp::ProofParams::new(2048,128,1);
    bench_schnorr_paillier_raw(c, &params2);
    bench_schnorr_paillier_fs(c, &params2);

    let params3 = spb::ProofParams::new(2048,128,128,128);
    bench_schnorr_paillier_batched(c, &params3);
}


fn bench_designated_all(c: &mut Criterion) {
//    bench_designated(c,&dv::DVParams::new(1024, 32));
    bench_designated(c,&dv::DVParams::new(2048, 128));
}


//criterion_group!(benches, bench_schnorr_paillier, bench_designated_all);
criterion_group!(benches, bench_designated_all);
criterion_main!(benches);
