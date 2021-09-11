use curv::arithmetic::traits::{Modulo, Samplable, BasicOps};
use curv::BigInt;
use paillier::EncryptWithChosenRandomness;
use paillier::Paillier;
use paillier::{EncryptionKey, Randomness, RawPlaintext, Keypair};

use criterion::{criterion_group, criterion_main, Criterion, ParameterizedBenchmark};

fn schnorr_paillier() {
    let x = 1u64;
}


fn criterion_benchmark(c: &mut Criterion) {
    c.bench(
        "Schnorr Paillier",
        ParameterizedBenchmark::new("few", |b, _| b.iter(schnorr_paillier), vec![0]).sample_size(20),
    );
}


criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
