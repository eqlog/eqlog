use std::hint::black_box;
#[cfg(not(feature = "allocations"))]
use std::time::Instant;

use clap::{error::ErrorKind, CommandFactory, Parser};
use eqlog_bench::{case, Config, Engine, Family, Metrics, Workload};

#[cfg(feature = "allocations")]
mod allocations;

#[derive(Parser)]
#[command(about = "Compare one native Eqlog closure with one Rust COW topological sweep")]
struct Arguments {
    /// Cases to run; omitting this runs every family.
    #[arg(long = "case", value_delimiter = ',')]
    cases: Vec<Family>,
    /// Omit to run both engines on the same input, alternating their order.
    #[arg(long)]
    engine: Option<Engine>,
    #[command(flatten)]
    config: Config,
    #[arg(long, default_value_t = 5)]
    samples: usize,
    #[arg(long, hide = true)]
    bench: bool,
}

#[cfg(not(feature = "allocations"))]
fn measure(workload: &mut dyn Workload) -> String {
    let start = Instant::now();
    black_box(workload).close();
    let elapsed = start.elapsed().as_nanos();
    elapsed.to_string()
}

#[cfg(feature = "allocations")]
fn measure(workload: &mut dyn Workload) -> String {
    let (count, bytes) = allocations::measure(|| black_box(workload).close());
    format!("{count},{bytes}")
}

fn main() {
    let mut args = Arguments::parse();
    match args.config.validate() {
        Ok(()) => {}
        Err(message) => Arguments::command()
            .error(ErrorKind::ValueValidation, message)
            .exit(),
    }
    if args.samples == 0 {
        Arguments::command()
            .error(ErrorKind::ValueValidation, "samples must be positive")
            .exit();
    }
    if args.cases.is_empty() {
        args.cases.extend(Family::ALL);
    }
    #[cfg(not(feature = "allocations"))]
    let columns = "close_ns";
    #[cfg(feature = "allocations")]
    let columns = "allocations,allocated_bytes";
    println!("case,engine,seed,seed_mask,worlds,morphisms,parents,width,members,owned_elements,local_size,sample,{columns},checksum");
    for family in args.cases {
        let name = family.name();
        let fixture = case(family, &args.config);
        let mut expected = None;
        for sample in 0..args.samples {
            let engines = match args.engine {
                Some(engine) => vec![engine],
                None => {
                    if sample % 2 == 0 {
                        vec![Engine::Native, Engine::Cow]
                    } else {
                        vec![Engine::Cow, Engine::Native]
                    }
                }
            };
            for engine in engines {
                let mut workload = fixture.prepare(engine);
                let measurement = measure(workload.as_mut());
                let metrics = workload.verify();
                if let Some(previous) = &expected {
                    assert_eq!(&metrics, previous, "{name}: engines or samples disagree");
                } else {
                    expected = Some(metrics.clone());
                }
                let Metrics {
                    worlds,
                    morphisms,
                    owned_elements,
                    local_size,
                    checksum,
                } = metrics;
                let Config {
                    seed,
                    seed_mask,
                    parents,
                    width,
                    members,
                    ..
                } = args.config;
                let engine = engine.name();
                println!("{name},{engine},{seed},{seed_mask},{worlds},{morphisms},{parents},{width},{members},{owned_elements},{local_size},{sample},{measurement},{checksum}");
            }
        }
    }
}
