use std::hint::black_box;
#[cfg(not(feature = "allocations"))]
use std::time::Instant;

use clap::{Parser, ValueEnum};
use eqlog_bench::{carrier, graph::Graph};

#[cfg(feature = "allocations")]
#[path = "../../benches/allocations.rs"]
mod allocations;

#[cfg(not(feature = "allocations"))]
type Measurement = u128;
#[cfg(feature = "allocations")]
type Measurement = (u128, u128);

#[derive(Clone, Copy, ValueEnum)]
enum Shape {
    Chain,
    Merge,
}

#[derive(Parser)]
struct Arguments {
    #[arg(long, value_delimiter = ',', default_value = "32,64,128")]
    vertices: Vec<usize>,
    #[arg(long, value_delimiter = ',', default_value = "4")]
    members: Vec<usize>,
    #[arg(long, value_delimiter = ',', default_value = "chain")]
    shape: Vec<Shape>,
    #[arg(long, default_value_t = 9)]
    samples: usize,
    #[arg(long, default_value_t = 17)]
    seed: u64,
    #[arg(long, hide = true)]
    bench: bool,
}

fn eqlog_sample(parents: &[Vec<usize>], members: usize) -> Measurement {
    let mut model = carrier::new_eqlog(parents, members);
    #[cfg(not(feature = "allocations"))]
    let measured = {
        let start = Instant::now();
        black_box(&mut model).close();
        start.elapsed().as_nanos()
    };
    #[cfg(feature = "allocations")]
    let measured = allocations::measure(|| black_box(&mut model).close());
    black_box(&model);
    measured
}

fn cow_sample(parents: &[Vec<usize>], members: usize) -> Measurement {
    let mut worlds = carrier::new_cow(parents.len(), members);
    #[cfg(not(feature = "allocations"))]
    let measured = {
        let start = Instant::now();
        carrier::close_cow(black_box(parents), black_box(&mut worlds));
        start.elapsed().as_nanos()
    };
    #[cfg(feature = "allocations")]
    let measured =
        allocations::measure(|| carrier::close_cow(black_box(parents), black_box(&mut worlds)));
    black_box(&worlds);
    measured
}

fn main() -> Result<(), &'static str> {
    let args = Arguments::parse();
    if args.samples == 0 || args.vertices.contains(&0) || args.members.contains(&0) {
        return Err("sizes and sample count must be positive");
    }
    #[cfg(not(feature = "allocations"))]
    println!("shape,vertices,members,seed,sample,eqlog_ns,cow_ns");
    #[cfg(feature = "allocations")]
    println!("shape,vertices,members,seed,sample,eqlog_allocations,cow_allocations,eqlog_allocated_bytes,cow_allocated_bytes");
    for shape in args.shape {
        for &vertices in &args.vertices {
            let (name, graph) = match shape {
                Shape::Chain => ("chain", Graph::chain(vertices)),
                Shape::Merge => ("merge", Graph::merge(vertices, args.seed)),
            };
            for &members in &args.members {
                for sample in 0..args.samples {
                    let (eqlog, cow) = if sample % 2 == 0 {
                        let eqlog = eqlog_sample(&graph.parents, members);
                        let cow = cow_sample(&graph.parents, members);
                        (eqlog, cow)
                    } else {
                        let cow = cow_sample(&graph.parents, members);
                        let eqlog = eqlog_sample(&graph.parents, members);
                        (eqlog, cow)
                    };
                    let seed = args.seed;
                    #[cfg(not(feature = "allocations"))]
                    println!("{name},{vertices},{members},{seed},{sample},{eqlog},{cow}");
                    #[cfg(feature = "allocations")]
                    {
                        let (eqlog_count, eqlog_bytes) = eqlog;
                        let (cow_count, cow_bytes) = cow;
                        println!("{name},{vertices},{members},{seed},{sample},{eqlog_count},{cow_count},{eqlog_bytes},{cow_bytes}");
                    }
                }
            }
        }
    }
    Ok(())
}
