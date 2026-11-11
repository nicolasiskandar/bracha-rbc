use brb_simulator::scenarios;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

fn bench_scenario_a(c: &mut Criterion) {
    let mut group = c.benchmark_group("scenario_a_honest");
    for &n in &[4usize, 7, 10, 13] {
        let f = (n - 1) / 3;
        group.bench_with_input(BenchmarkId::new("n", n), &(n, f), |b, &(n, f)| {
            b.iter(|| {
                let mut net = scenarios::scenario_a_generic(n, f, 42);
                net.run_until_quiescent(10_000);
                assert!(net.safety_holds());
            });
        });
    }
    group.finish();
}

fn bench_message_complexity(c: &mut Criterion) {
    let mut group = c.benchmark_group("message_complexity");
    for &n in &[4usize, 7, 10, 13] {
        let f = (n - 1) / 3;
        group.bench_with_input(BenchmarkId::new("n", n), &(n, f), |b, &(n, f)| {
            b.iter(|| {
                let mut net = scenarios::scenario_a_generic(n, f, 0);
                net.run_until_quiescent(10_000);
                net.trace.len()
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_scenario_a, bench_message_complexity);
criterion_main!(benches);
