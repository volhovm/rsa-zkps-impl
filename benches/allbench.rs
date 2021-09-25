use criterion::{criterion_group, criterion_main, Criterion, BatchSize};
use std::time::Duration;
use rsazkps::protocols::schnorr_paillier as sp;


// TODO the public modulus is not randomized. Should it be?
fn bench_schnorr_paillier_raw(c: &mut Criterion, params: &sp::ProofParams) {
    let mut grp = c.benchmark_group(format!("Group 1: Schnorr Paillier for {}", params));

    grp.measurement_time(Duration::from_secs(120));

    grp.bench_function("verify0", |b| {
        b.iter_batched(|| sp::lang_sample(params).0,
                       |inst| sp::verify0(params,&inst),
                       BatchSize::LargeInput);
    });

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| sp::lang_sample(params).0,
                       |inst| sp::prove1(params,&inst),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| sp::verify1(params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (inst,wit) = sp::lang_sample(params);
                 let (_,cr) = sp::prove1(params,&inst);
                 let ch = sp::verify1(params);
                 return (inst,wit,ch,cr); },
            |(inst,wit,ch,cr)| sp::prove2(params,&inst,&wit,&ch,&cr),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| {
        b.iter_batched(
            || { let (inst,wit) = sp::lang_sample(params);
                 let (_,precomp) = sp::verify0(params,&inst);
                 let (com,cr) = sp::prove1(params,&inst);
                 let ch = sp::verify1(params);
                 let resp = sp::prove2(params,&inst,&wit,&ch,&cr);
                 return (inst,precomp,com,ch,resp); },
            |(inst,precomp,com,ch,resp)| sp::verify2(params,&inst,&precomp,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}


fn bench_schnorr_paillier(c: &mut Criterion) {

    let params1 = sp::ProofParams::new(2048,256,15);
    bench_schnorr_paillier_raw(c, &params1);

    // Not checking for small primes
    let params2 = sp::ProofParams::new(2048,256,1);
    bench_schnorr_paillier_raw(c, &params2);
}

criterion_group!(benches, bench_schnorr_paillier);
criterion_main!(benches);
