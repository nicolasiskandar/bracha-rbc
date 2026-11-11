use brb_simulator::scenarios;
use std::path::Path;

pub fn run_scenario(scenario: &str, seed: u64, output: &Path, reps: u32) {
    std::fs::create_dir_all(output).ok();

    for rep in 0..reps {
        let rep_seed = seed.wrapping_add(rep as u64);
        let (trace, safety, delivered_count) = match scenario.to_lowercase().as_str() {
            "a" => {
                let mut net = scenarios::scenario_a(rep_seed);
                net.run_until_quiescent(1000);
                (
                    net.export_trace_json(),
                    net.safety_holds(),
                    net.deliveries.len(),
                )
            }
            "b" => {
                let mut net = scenarios::scenario_b(rep_seed);
                net.run_until_quiescent(1000);
                (
                    net.export_trace_json(),
                    net.safety_holds(),
                    net.deliveries.len(),
                )
            }
            "c" => {
                let mut net = scenarios::scenario_c(rep_seed);
                net.run_until_quiescent(1000);
                (
                    net.export_trace_json(),
                    net.safety_holds(),
                    net.deliveries.len(),
                )
            }
            "d" => {
                let (_partitioned, mut recovered) = scenarios::scenario_d(rep_seed);
                recovered.run_until_quiescent(1000);
                (
                    recovered.export_trace_json(),
                    recovered.safety_holds(),
                    recovered.deliveries.len(),
                )
            }
            "e" => {
                let mut net = scenarios::scenario_e(rep_seed);
                net.run_until_quiescent(1000);
                (
                    net.export_trace_json(),
                    net.safety_holds(),
                    net.deliveries.len(),
                )
            }
            _ => {
                eprintln!("Unknown scenario: {scenario}. Use a, b, c, d, or e.");
                return;
            }
        };

        let filename = output.join(format!(
            "scenario_{scenario}_rep{rep:04}_seed{rep_seed}.json"
        ));
        std::fs::write(&filename, &trace).ok();
        println!(
            "Scenario {scenario} rep={rep} seed={rep_seed}: safety={safety} deliveries={delivered_count} → {}",
            filename.display()
        );
        if !safety {
            eprintln!("⚠ SAFETY VIOLATION in scenario {scenario} rep={rep}!");
            std::process::exit(1);
        }
    }
}
