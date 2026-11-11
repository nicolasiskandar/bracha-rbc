use clap::{Parser, Subcommand};
use std::path::PathBuf;

mod bench;
mod run;

#[derive(Parser)]
#[command(name = "brb-experiments")]
#[command(about = "Bracha RBC adversarial scenarios and performance benchmarks")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Run {
        #[arg(short, long)]
        scenario: String,
        #[arg(long, default_value = "42")]
        seed: u64,
        #[arg(short, long, default_value = "results")]
        output: PathBuf,
        #[arg(short, long, default_value = "1")]
        reps: u32,
    },

    Bench {
        #[arg(long, default_value = "4,7,10,13")]
        sizes: String,
        #[arg(long, default_value = "20")]
        rounds: u32,
        #[arg(short, long, default_value = "results")]
        output: PathBuf,
    },
}

fn main() {
    tracing_subscriber::fmt::init();
    let cli = Cli::parse();
    match cli.command {
        Commands::Run {
            scenario,
            seed,
            output,
            reps,
        } => {
            run::run_scenario(&scenario, seed, &output, reps);
        }
        Commands::Bench {
            sizes,
            rounds,
            output,
        } => {
            bench::run_bench(&sizes, rounds, &output);
        }
    }
}
