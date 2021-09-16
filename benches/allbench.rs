use criterion::{black_box, criterion_group, criterion_main,
                Criterion, ParameterizedBenchmark, BatchSize};
use std::time::Duration;
use rsazkps::protocols::schnorr_paillier as sp;

fn bench_schnorr_paillier(c: &mut Criterion) {
    let mut grp = c.benchmark_group("Group 1: Schnorr Paillier");

    grp.measurement_time(Duration::from_secs(120));

    // 2^23 small primes check, 12 reps, 12*23=276
    let params = sp::ProofParams { q: 8388608 , reps: 12 };

    grp.bench_function("verify0", |b| {
        b.iter_batched(|| sp::lang_sample(2048).0,
                       |inst| sp::verify0(&params,&inst),
                       BatchSize::LargeInput);
    });

    grp.bench_function("prove1", |b| {
        b.iter_batched(|| sp::lang_sample(2048).0,
                       |inst| sp::prove1(&params,&inst),
                       BatchSize::LargeInput);
    });

    grp.bench_function("verify1", |b| b.iter(|| sp::verify1(&params)));

    grp.bench_function("prove2", |b| {
        b.iter_batched(
            || { let (inst,wit) = sp::lang_sample(2048);
                 let (_,cr) = sp::prove1(&params,&inst);
                 let ch = sp::verify1(&params);
                 return (inst,wit,ch,cr); },
            |(inst,wit,ch,cr)| sp::prove2(&params,&inst,&wit,&ch,&cr),
            BatchSize::LargeInput
        );
    });

    grp.bench_function("verify2", |b| {
        b.iter_batched(
            || { let (inst,wit) = sp::lang_sample(2048);
                 let (com,cr) = sp::prove1(&params,&inst);
                 let ch = sp::verify1(&params);
                 let resp = sp::prove2(&params,&inst,&wit,&ch,&cr);
                 return (inst,com,ch,resp); },
            |(inst,com,ch,resp)| sp::verify2(&params,&inst,&com,&ch,&resp),
            BatchSize::LargeInput
        );
    });

    grp.finish();
}

criterion_group!(benches, bench_schnorr_paillier);
criterion_main!(benches);
