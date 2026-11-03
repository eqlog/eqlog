use std::collections::BTreeMap;
use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use eqlog_bench::{ambient, chain, congruence, dag, graph::Graph, join, propagation};

mod runner;
use runner::{Label, Options, Result, Runner};

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
enum Shape {
    Chain,
    Merge,
    Sparse,
    Dense,
    Cycle,
    Fanout,
    Overlap,
    Split,
    Diamonds,
    Layered,
    Comb,
    Wide,
}

impl Shape {
    fn name(self) -> String {
        self.to_possible_value().unwrap().get_name().to_owned()
    }

    fn graph(self, vertices: usize, parents: usize, seed: u64) -> Graph {
        match self {
            Self::Chain => Graph::chain(vertices),
            Self::Merge => Graph::merge(vertices, seed),
            Self::Sparse => Graph::sparse(vertices, parents, seed),
            Self::Dense => Graph::dense(vertices),
            Self::Cycle => Graph::cycle(vertices),
            Self::Fanout
            | Self::Overlap
            | Self::Split
            | Self::Diamonds
            | Self::Layered
            | Self::Comb
            | Self::Wide => unreachable!("case owns this graph"),
        }
    }
}

const PROPAGATION: &str =
    "O(N+E+NK log(2+NK)) upper bound; shared chunks can cost less; setup excluded";
const AMBIENT: &str =
    "O((N+E) log(2+N)+NK log(2+NK)+U), U=nonshared parent-union work; SCCs share finite closure";
const CONGRUENCE: &str = "O(NK log(2+NK)) for one-step shared-key merges";
const RECURSIVE: &str = "O(NK(D+1) log(2+NK(D+1))) for K shared keys and D function successors";
const JOB_CHAIN: &str = "O(N log(2+N))";
const JOB_EQUATION: &str =
    "O(N log^2(2+N)) upper; persistent union-find lookups use historical origins";
const JOB_DAG: &str = "O(N+E+(N+EM) log(2+M)) upper; M<=N+8, shared ancestry can cost less";
const MEMBER_JOIN: &str = "O(N+E+(L+E(M+P)) log(2+L)) upper; L=local rows, M=max carrier, P=max logical pairs; suffix sharing can cost less";

struct Declaration {
    name: &'static str,
    shapes: &'static [Shape],
    bound: &'static str,
    slow: bool,
}

const CASES: &[Declaration] = &[
    Declaration {
        name: "carrier",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "member-predicate",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "mixed-predicate",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "from-ambient",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "to-ambient",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "member-function",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "marking",
        shapes: &[Shape::Chain, Shape::Merge],
        bound: PROPAGATION,
        slow: false,
    },
    Declaration {
        name: "ambient-predicate",
        shapes: &[
            Shape::Chain,
            Shape::Merge,
            Shape::Sparse,
            Shape::Dense,
            Shape::Cycle,
        ],
        bound: AMBIENT,
        slow: false,
    },
    Declaration {
        name: "ambient-marking",
        shapes: &[
            Shape::Chain,
            Shape::Merge,
            Shape::Sparse,
            Shape::Dense,
            Shape::Cycle,
        ],
        bound: AMBIENT,
        slow: false,
    },
    Declaration {
        name: "congruence",
        shapes: &[Shape::Chain],
        bound: CONGRUENCE,
        slow: false,
    },
    Declaration {
        name: "recursive-congruence",
        shapes: &[Shape::Chain],
        bound: RECURSIVE,
        slow: false,
    },
    Declaration {
        name: "job-chain",
        shapes: &[Shape::Chain],
        bound: JOB_CHAIN,
        slow: true,
    },
    Declaration {
        name: "job-equation",
        shapes: &[Shape::Chain],
        bound: JOB_EQUATION,
        slow: true,
    },
    Declaration {
        name: "job-dag",
        shapes: &[
            Shape::Chain,
            Shape::Sparse,
            Shape::Layered,
            Shape::Comb,
            Shape::Wide,
        ],
        bound: JOB_DAG,
        slow: true,
    },
    Declaration {
        name: "member-join",
        shapes: &[
            Shape::Chain,
            Shape::Fanout,
            Shape::Overlap,
            Shape::Split,
            Shape::Diamonds,
            Shape::Layered,
            Shape::Comb,
        ],
        bound: MEMBER_JOIN,
        slow: true,
    },
];

#[derive(Parser)]
#[command(
    about = "Paired native Eqlog and Rust COW closure benchmarks",
    after_help = "Each comma-separated size list is swept independently in a Cartesian grid. Construction and full verification are outside the timer. --list describes cases and COW bounds. Examples: --case from-ambient --vertices 32,64,128 --members 4,16; --case ambient-predicate --shape sparse,cycle; --case member-join --shape overlap. --output writes raw paired observations and growth factors as JSON. Performance checks require a baseline for this host/compiler and at least seven samples; faster results also fail. Run on an otherwise idle pinned CPU. Expectation intervals assume independent samples; no outliers are discarded."
)]
struct Arguments {
    /// Omit to run the small isolated cases. Repeat or comma-separate names.
    #[arg(long = "case", value_delimiter = ',')]
    cases: Vec<String>,
    #[arg(long, value_delimiter = ',', default_value = "chain")]
    shape: Vec<Shape>,
    #[arg(long, value_delimiter = ',', default_value = "32,64,128")]
    vertices: Vec<usize>,
    #[arg(long, value_delimiter = ',', default_value = "4")]
    members: Vec<usize>,
    #[arg(long, value_delimiter = ',', default_value = "4")]
    keys: Vec<usize>,
    #[arg(long, value_delimiter = ',', default_value = "8")]
    depth: Vec<usize>,
    #[arg(long, default_value_t = 2)]
    parents: usize,
    #[arg(long, default_value_t = 8)]
    width: usize,
    #[arg(long, default_value_t = 17)]
    seed: u64,
    #[arg(long, default_value_t = 255)]
    seed_mask: u32,
    #[arg(long, default_value_t = 9)]
    samples: usize,
    /// Include the older compound stress cases when --case is omitted.
    #[arg(long)]
    slow: bool,
    #[arg(long)]
    list: bool,
    #[arg(long)]
    output: Option<PathBuf>,
    #[arg(long)]
    baseline: Option<PathBuf>,
    #[arg(long)]
    check: bool,
    /// Fail if the Eqlog/COW ratio grows too quickly across the size sweep.
    #[arg(long)]
    check_scaling: bool,
    /// Allowed growth in the Eqlog/COW ratio per doubling of a size parameter.
    #[arg(long, default_value_t = 1.25)]
    max_ratio_growth: f64,
    #[arg(long)]
    update_baseline: bool,
    #[arg(long, default_value_t = 0.2)]
    tolerance: f64,
    #[arg(long, hide = true)]
    bench: bool,
}

fn parameters(values: &[(&str, usize)], seed: u64) -> BTreeMap<String, u64> {
    values
        .iter()
        .map(|&(name, value)| (name.to_owned(), u64::try_from(value).unwrap()))
        .chain([("seed".to_owned(), seed)])
        .collect()
}

fn run_case(
    runner: &mut Runner,
    declaration: &Declaration,
    shape: Shape,
    vertices: usize,
    args: &Arguments,
) -> Result<()> {
    let label = |parameters| Label {
        case: declaration.name.to_owned(),
        shape: shape.name(),
        parameters,
        cow_bound: declaration.bound,
    };
    match declaration.name {
        "carrier" | "member-predicate" | "mixed-predicate" | "from-ambient" | "to-ambient"
        | "member-function" | "marking" => {
            for &members in &args.members {
                let params = propagation::Params {
                    vertices,
                    members,
                    seed: args.seed,
                };
                let graph = shape.graph(vertices, args.parents, args.seed);
                let label = label(parameters(
                    &[("vertices", vertices), ("members", members)],
                    args.seed,
                ));
                match declaration.name {
                    "carrier" => runner.run(label, propagation::carrier(&params, graph))?,
                    "member-predicate" => {
                        runner.run(label, propagation::member_predicate(&params, graph))?
                    }
                    "mixed-predicate" => {
                        runner.run(label, propagation::mixed_predicate(&params, graph))?
                    }
                    "from-ambient" => {
                        runner.run(label, propagation::from_ambient(&params, graph))?
                    }
                    "to-ambient" => runner.run(label, propagation::to_ambient(&params, graph))?,
                    "member-function" => {
                        runner.run(label, propagation::member_function(&params, graph))?
                    }
                    "marking" => runner.run(label, propagation::marking(&params, graph))?,
                    _ => unreachable!(),
                }
            }
        }
        "ambient-predicate" | "ambient-marking" => {
            for &members in &args.members {
                let params = ambient::Params { vertices, members };
                let graph = shape.graph(vertices, args.parents, args.seed);
                let label = label(parameters(
                    &[
                        ("vertices", vertices),
                        ("members", members),
                        ("parents", args.parents),
                    ],
                    args.seed,
                ));
                if declaration.name == "ambient-predicate" {
                    runner.run(label, ambient::propagation(&params, graph))?;
                } else {
                    runner.run(label, ambient::marking(&params, graph))?;
                }
            }
        }
        "congruence" => {
            for &keys in &args.keys {
                let params = congruence::one_step::Params { vertices, keys };
                runner.run(
                    label(parameters(
                        &[("vertices", vertices), ("keys", keys)],
                        args.seed,
                    )),
                    congruence::one_step::case(&params),
                )?;
            }
        }
        "recursive-congruence" => {
            for &keys in &args.keys {
                for &depth in &args.depth {
                    let params = congruence::recursive::Params {
                        vertices,
                        keys,
                        depth,
                    };
                    runner.run(
                        label(parameters(
                            &[("vertices", vertices), ("keys", keys), ("depth", depth)],
                            args.seed,
                        )),
                        congruence::recursive::case(&params),
                    )?;
                }
            }
        }
        "job-chain" | "job-equation" => {
            let params = chain::Params {
                vertices,
                seed: args.seed,
                seed_mask: args.seed_mask,
            };
            let label = label(parameters(
                &[
                    ("vertices", vertices),
                    ("seed_mask", args.seed_mask as usize),
                ],
                args.seed,
            ));
            if declaration.name == "job-chain" {
                runner.run(label, chain::plain(&params))?;
            } else {
                runner.run(label, chain::equation(&params))?;
            }
        }
        "job-dag" => {
            let variant = match shape {
                Shape::Chain => dag::Variant::Chain,
                Shape::Sparse => dag::Variant::Forward,
                Shape::Layered => dag::Variant::Layered,
                Shape::Comb => dag::Variant::Comb,
                Shape::Wide => dag::Variant::Wide,
                Shape::Merge
                | Shape::Dense
                | Shape::Cycle
                | Shape::Fanout
                | Shape::Overlap
                | Shape::Split
                | Shape::Diamonds => unreachable!(),
            };
            let params = dag::Params {
                vertices,
                parents: args.parents,
                width: args.width,
                seed: args.seed,
                seed_mask: args.seed_mask,
            };
            runner.run(
                label(parameters(
                    &[
                        ("vertices", vertices),
                        ("parents", args.parents),
                        ("width", args.width),
                        ("seed_mask", args.seed_mask as usize),
                    ],
                    args.seed,
                )),
                dag::case(&params, variant),
            )?;
        }
        "member-join" => {
            let variant = match shape {
                Shape::Chain => join::Variant::Chain,
                Shape::Fanout => join::Variant::Fanout,
                Shape::Overlap => join::Variant::Overlap,
                Shape::Split => join::Variant::Split,
                Shape::Diamonds => join::Variant::Diamonds,
                Shape::Layered => join::Variant::Layered,
                Shape::Comb => join::Variant::Comb,
                Shape::Merge | Shape::Sparse | Shape::Dense | Shape::Cycle | Shape::Wide => {
                    unreachable!()
                }
            };
            for &members in &args.members {
                let params = join::Params {
                    vertices,
                    parents: args.parents,
                    width: args.width,
                    members,
                    seed: args.seed,
                };
                runner.run(
                    label(parameters(
                        &[
                            ("vertices", vertices),
                            ("parents", args.parents),
                            ("width", args.width),
                            ("members", members),
                        ],
                        args.seed,
                    )),
                    join::case(&params, variant),
                )?;
            }
        }
        _ => unreachable!("registered case"),
    }
    Ok(())
}

fn main() -> Result<()> {
    let mut args = Arguments::parse();
    if args.list {
        for case in CASES {
            let shapes = case
                .shapes
                .iter()
                .map(|shape| shape.name())
                .collect::<Vec<_>>()
                .join(",");
            let slow = if case.slow { " (opt-in)" } else { "" };
            println!("{}{}\t{}\t{}", case.name, slow, shapes, case.bound);
        }
        return Ok(());
    }
    for sizes in [
        &mut args.vertices,
        &mut args.members,
        &mut args.keys,
        &mut args.depth,
    ] {
        if sizes.is_empty() || sizes.contains(&0) {
            return Err("size axes must be nonempty and positive".into());
        }
        sizes.sort_unstable();
        sizes.dedup();
    }
    if args.parents == 0 || args.width == 0 || args.seed_mask > 255 {
        return Err("invalid parent count, width or seed mask".into());
    }
    if args.cases.is_empty() {
        args.cases = CASES
            .iter()
            .filter(|case| args.slow || !case.slow)
            .map(|case| case.name.to_owned())
            .collect();
    }
    let selected = args
        .cases
        .iter()
        .map(|name| {
            CASES
                .iter()
                .find(|case| case.name == name)
                .ok_or_else(|| format!("unknown case {name}; use --list"))
        })
        .collect::<std::result::Result<Vec<_>, _>>()?;
    for case in &selected {
        for shape in &args.shape {
            if !case.shapes.contains(shape) {
                return Err(format!(
                    "{} does not support {}; use --list",
                    case.name,
                    shape.name()
                )
                .into());
            }
        }
    }
    let mut runner = Runner::new(Options {
        samples: args.samples,
        output: args.output.clone(),
        baseline: args.baseline.clone(),
        check: args.check,
        update: args.update_baseline,
        tolerance: args.tolerance,
        check_scaling: args.check_scaling,
        max_ratio_growth: args.max_ratio_growth,
    })?;
    for case in selected {
        for &shape in &args.shape {
            for &vertices in &args.vertices {
                run_case(&mut runner, case, shape, vertices, &args)?;
            }
        }
    }
    runner.finish()
}
