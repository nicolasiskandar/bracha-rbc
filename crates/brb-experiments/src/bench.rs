use brb_simulator::scenarios;
use serde::Serialize;
use std::path::Path;

#[derive(Serialize)]
struct BenchResult {
    n: usize,
    f: usize,
    seed: u64,
    safety: bool,
    deliveries: usize,
    ticks: u64,
    message_count: usize,
}

pub fn run_bench(sizes: &str, rounds: u32, output: &Path) {
    std::fs::create_dir_all(output).ok();
    let ns: Vec<usize> = sizes
        .split(',')
        .filter_map(|s| s.trim().parse().ok())
        .collect();
    let mut results = Vec::new();

    for &n in &ns {
        let f = (n - 1) / 3;
        if n <= 3 * f {
            continue;
        }
        println!("Benchmarking n={n} f={f}...");
        for seed in 0..rounds as u64 {
            let mut net = scenarios::scenario_a_generic(n, f, seed);
            net.run_until_quiescent(10_000);
            results.push(BenchResult {
                n,
                f,
                seed,
                safety: net.safety_holds(),
                deliveries: net.deliveries.len(),
                ticks: net.tick,
                message_count: net.trace.len(),
            });
        }
    }

    let json = serde_json::to_string_pretty(&results).unwrap_or_default();
    let path = output.join("bench_results.json");
    std::fs::write(&path, json).ok();
    println!("Benchmark results → {}", path.display());
    let violations: usize = results.iter().filter(|r| !r.safety).count();
    println!("Total safety violations: {violations}/{}", results.len());
}
