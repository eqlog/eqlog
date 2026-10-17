use std::env;
use std::hint::black_box;
#[cfg(not(feature = "allocations"))]
use std::time::Instant;

use eqlog_bench::{cases, Phase, Workload};

#[cfg(feature = "allocations")]
mod allocations;

fn setting(name: &str, default: usize) -> usize {
    env::var_os(name)
        .map(|value| {
            value
                .to_str()
                .expect("setting must be UTF-8")
                .parse()
                .expect("setting must be an integer")
        })
        .unwrap_or(default)
}

#[cfg(not(feature = "allocations"))]
fn measure(workload: &mut dyn Workload) -> (u128, u128) {
    let start = Instant::now();
    black_box(workload).close();
    (start.elapsed().as_nanos(), 0)
}

#[cfg(feature = "allocations")]
fn measure(workload: &mut dyn Workload) -> (u128, u128) {
    allocations::measure(|| black_box(workload).close())
}

fn main() {
    let samples = setting("EQLOG_BENCH_SAMPLES", 15);
    let warmup = setting("EQLOG_BENCH_WARMUP", 2);
    let scale = setting("EQLOG_BENCH_SCALE", 8);
    assert!(samples > 0 && scale > 0);
    let filter = env::var_os("EQLOG_BENCH_FILTER");
    let cases: Vec<_> = cases()
        .into_iter()
        .filter(|case| filter.as_ref().is_none_or(|filter| case.name == filter))
        .collect();
    assert!(!cases.is_empty(), "no matching workloads");
    #[cfg(not(feature = "allocations"))]
    println!("case,phase,scale,samples,median_ns,p10_ns,p90_ns");
    #[cfg(feature = "allocations")]
    println!("case,phase,scale,samples,median_allocations,median_allocated_bytes");
    for phase in [Phase::Initial, Phase::Incremental, Phase::Unchanged] {
        let mut results = vec![Vec::with_capacity(samples); cases.len()];
        for sample in 0..warmup + samples {
            for offset in 0..cases.len() {
                // Reverse order on alternate samples to distribute warm-cache and drift effects.
                let i = if sample % 2 == 0 {
                    offset
                } else {
                    cases.len() - 1 - offset
                };
                let case = &cases[i];
                let mut workload = (case.prepare)(scale, phase);
                let result = measure(workload.as_mut());
                workload.check();
                if sample >= warmup {
                    results[i].push(result);
                }
            }
        }
        for (case, mut results) in cases.iter().zip(results) {
            results.sort_unstable();
            let name = case.name;
            let phase = phase.name();
            let median = results[samples / 2].0;
            #[cfg(not(feature = "allocations"))]
            {
                let p10 = results[(samples - 1) / 10].0;
                let p90 = results[(samples - 1) * 9 / 10].0;
                println!("{name},{phase},{scale},{samples},{median},{p10},{p90}");
            }
            #[cfg(feature = "allocations")]
            {
                let mut bytes: Vec<_> = results.iter().map(|result| result.1).collect();
                bytes.sort_unstable();
                let bytes = bytes[samples / 2];
                println!("{name},{phase},{scale},{samples},{median},{bytes}");
            }
        }
    }
}
