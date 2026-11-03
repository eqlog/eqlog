use std::collections::BTreeMap;
use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use eqlog_bench::{ambient, chain, congruence, dag, graph::Graph, join, propagation, Case};

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

    fn graph(self, vertices: usize, parents: usize, seed: u64) -> Result<Graph> {
        match self {
            Self::Chain => Ok(Graph::chain(vertices)),
            Self::Merge => Ok(Graph::merge(vertices, seed)),
            Self::Sparse => Ok(Graph::sparse(vertices, parents, seed)),
            Self::Dense => Ok(Graph::dense(vertices)),
            Self::Cycle => Ok(Graph::cycle(vertices)),
            Self::Fanout
            | Self::Overlap
            | Self::Split
            | Self::Diamonds
            | Self::Layered
            | Self::Comb
            | Self::Wide => Err("case requires its own graph generator".into()),
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
enum Scenario {
    Carrier,
    MemberPredicate,
    MixedPredicate,
    FromAmbient,
    ToAmbient,
    MemberFunction,
    Marking,
    AmbientPredicate,
    AmbientMarking,
    Congruence,
    RecursiveCongruence,
    JobChain,
    JobEquation,
    JobDag,
    MemberJoin,
}

struct Declaration {
    shapes: &'static [Shape],
    bound: &'static str,
    slow: bool,
}

impl Scenario {
    fn name(self) -> String {
        self.to_possible_value().unwrap().get_name().to_owned()
    }

    fn declaration(self) -> Declaration {
        let (shapes, bound, slow): (&'static [Shape], &'static str, bool) = match self {
            Self::Carrier
            | Self::MemberPredicate
            | Self::MixedPredicate
            | Self::FromAmbient
            | Self::ToAmbient
            | Self::MemberFunction
            | Self::Marking => (&[Shape::Chain, Shape::Merge], PROPAGATION, false),
            Self::AmbientPredicate | Self::AmbientMarking => (
                &[
                    Shape::Chain,
                    Shape::Merge,
                    Shape::Sparse,
                    Shape::Dense,
                    Shape::Cycle,
                ],
                AMBIENT,
                false,
            ),
            Self::Congruence => (&[Shape::Chain], CONGRUENCE, false),
            Self::RecursiveCongruence => (&[Shape::Chain], RECURSIVE, false),
            Self::JobChain => (&[Shape::Chain], JOB_CHAIN, true),
            Self::JobEquation => (&[Shape::Chain], JOB_EQUATION, true),
            Self::JobDag => (
                &[
                    Shape::Chain,
                    Shape::Sparse,
                    Shape::Layered,
                    Shape::Comb,
                    Shape::Wide,
                ],
                JOB_DAG,
                true,
            ),
            Self::MemberJoin => (
                &[
                    Shape::Chain,
                    Shape::Fanout,
                    Shape::Overlap,
                    Shape::Split,
                    Shape::Diamonds,
                    Shape::Layered,
                    Shape::Comb,
                ],
                MEMBER_JOIN,
                true,
            ),
        };
        Declaration {
            shapes,
            bound,
            slow,
        }
    }

    fn label(self, shape: Shape, values: &[(&str, usize)], seed: u64) -> Label {
        let parameters: BTreeMap<_, _> = values
            .iter()
            .map(|&(name, value)| (name.to_owned(), u64::try_from(value).unwrap()))
            .chain([("seed".to_owned(), seed)])
            .collect();
        Label {
            case: self.name(),
            shape: shape.name(),
            parameters,
            cow_bound: self.declaration().bound,
        }
    }

    fn run(
        self,
        runner: &mut Runner,
        shape: Shape,
        vertices: usize,
        args: &Arguments,
    ) -> Result<()> {
        let label = |values: &[(&str, usize)]| self.label(shape, values, args.seed);
        match self {
            Self::Carrier => {
                run_propagation(runner, self, shape, vertices, args, propagation::carrier)
            }
            Self::MemberPredicate => run_propagation(
                runner,
                self,
                shape,
                vertices,
                args,
                propagation::member_predicate,
            ),
            Self::MixedPredicate => run_propagation(
                runner,
                self,
                shape,
                vertices,
                args,
                propagation::mixed_predicate,
            ),
            Self::FromAmbient => run_propagation(
                runner,
                self,
                shape,
                vertices,
                args,
                propagation::from_ambient,
            ),
            Self::ToAmbient => {
                run_propagation(runner, self, shape, vertices, args, propagation::to_ambient)
            }
            Self::MemberFunction => run_propagation(
                runner,
                self,
                shape,
                vertices,
                args,
                propagation::member_function,
            ),
            Self::Marking => {
                run_propagation(runner, self, shape, vertices, args, propagation::marking)
            }
            Self::AmbientPredicate => {
                run_ambient(runner, self, shape, vertices, args, ambient::propagation)
            }
            Self::AmbientMarking => {
                run_ambient(runner, self, shape, vertices, args, ambient::marking)
            }
            Self::Congruence => {
                for &keys in &args.keys {
                    let params = congruence::one_step::Params { vertices, keys };
                    runner.run(
                        label(&[("vertices", vertices), ("keys", keys)]),
                        congruence::one_step::case(&params),
                    )?;
                }
                Ok(())
            }
            Self::RecursiveCongruence => {
                for &keys in &args.keys {
                    for &depth in &args.depth {
                        let params = congruence::recursive::Params {
                            vertices,
                            keys,
                            depth,
                        };
                        runner.run(
                            label(&[("vertices", vertices), ("keys", keys), ("depth", depth)]),
                            congruence::recursive::case(&params),
                        )?;
                    }
                }
                Ok(())
            }
            Self::JobChain => run_chain(runner, self, shape, vertices, args, chain::plain),
            Self::JobEquation => run_chain(runner, self, shape, vertices, args, chain::equation),
            Self::JobDag => {
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
                    | Shape::Diamonds => return Err("unsupported job-dag shape".into()),
                };
                let params = dag::Params {
                    vertices,
                    parents: args.parents,
                    width: args.width,
                    seed: args.seed,
                    seed_mask: args.seed_mask,
                };
                runner.run(
                    label(&[
                        ("vertices", vertices),
                        ("parents", args.parents),
                        ("width", args.width),
                        ("seed_mask", args.seed_mask as usize),
                    ]),
                    dag::case(&params, variant),
                )
            }
            Self::MemberJoin => {
                let variant = match shape {
                    Shape::Chain => join::Variant::Chain,
                    Shape::Fanout => join::Variant::Fanout,
                    Shape::Overlap => join::Variant::Overlap,
                    Shape::Split => join::Variant::Split,
                    Shape::Diamonds => join::Variant::Diamonds,
                    Shape::Layered => join::Variant::Layered,
                    Shape::Comb => join::Variant::Comb,
                    Shape::Merge | Shape::Sparse | Shape::Dense | Shape::Cycle | Shape::Wide => {
                        return Err("unsupported member-join shape".into())
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
                        label(&[
                            ("vertices", vertices),
                            ("parents", args.parents),
                            ("width", args.width),
                            ("members", members),
                        ]),
                        join::case(&params, variant),
                    )?;
                }
                Ok(())
            }
        }
    }
}

fn run_propagation<C: Case>(
    runner: &mut Runner,
    scenario: Scenario,
    shape: Shape,
    vertices: usize,
    args: &Arguments,
    make: impl Fn(&propagation::Params, Graph) -> C,
) -> Result<()> {
    for &members in &args.members {
        let params = propagation::Params {
            vertices,
            members,
            seed: args.seed,
        };
        let graph = shape.graph(vertices, args.parents, args.seed)?;
        let label = scenario.label(
            shape,
            &[("vertices", vertices), ("members", members)],
            args.seed,
        );
        runner.run(label, make(&params, graph))?;
    }
    Ok(())
}

fn run_ambient<C: Case>(
    runner: &mut Runner,
    scenario: Scenario,
    shape: Shape,
    vertices: usize,
    args: &Arguments,
    make: impl Fn(&ambient::Params, Graph) -> C,
) -> Result<()> {
    for &members in &args.members {
        let params = ambient::Params { vertices, members };
        let graph = shape.graph(vertices, args.parents, args.seed)?;
        let label = scenario.label(
            shape,
            &[
                ("vertices", vertices),
                ("members", members),
                ("parents", args.parents),
            ],
            args.seed,
        );
        runner.run(label, make(&params, graph))?;
    }
    Ok(())
}

fn run_chain<C: Case>(
    runner: &mut Runner,
    scenario: Scenario,
    shape: Shape,
    vertices: usize,
    args: &Arguments,
    make: impl Fn(&chain::Params) -> C,
) -> Result<()> {
    let params = chain::Params {
        vertices,
        seed: args.seed,
        seed_mask: args.seed_mask,
    };
    let label = scenario.label(
        shape,
        &[
            ("vertices", vertices),
            ("seed_mask", args.seed_mask as usize),
        ],
        args.seed,
    );
    runner.run(label, make(&params))
}

#[derive(Parser)]
#[command(
    about = "Paired native Eqlog and Rust COW closure benchmarks",
    after_help = "Size lists form a Cartesian grid. Only close() is measured; construction and verification are excluded. Run on an idle pinned CPU. Ratio intervals assume independent samples; no outliers are discarded. Example: --case from-ambient --vertices 32,64,128 --members 4,16."
)]
struct Arguments {
    #[arg(
        long = "case",
        value_delimiter = ',',
        help = "Cases to run; defaults to the isolated cases"
    )]
    cases: Vec<Scenario>,
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
    #[arg(long, help = "Include compound stress cases in the default selection")]
    slow: bool,
    #[arg(long, help = "List cases, supported shapes and COW bounds")]
    list: bool,
    #[arg(long, help = "Write raw pairs and growth comparisons as JSON")]
    output: Option<PathBuf>,
    #[arg(long)]
    baseline: Option<PathBuf>,
    #[arg(
        long,
        help = "Check host/compiler-specific ratio bands; speedups also fail"
    )]
    check: bool,
    #[arg(
        long,
        help = "Check ratio growth across sizes; requires at least seven samples"
    )]
    check_scaling: bool,
    #[arg(
        long,
        default_value_t = 1.25,
        help = "Maximum ratio growth per doubling of a size parameter"
    )]
    max_ratio_growth: f64,
    #[arg(long)]
    update_baseline: bool,
    #[arg(long, default_value_t = 0.2)]
    tolerance: f64,
    #[arg(long, hide = true)]
    bench: bool,
}

fn main() -> Result<()> {
    let mut args = Arguments::parse();
    if args.list {
        for &scenario in Scenario::value_variants() {
            let declaration = scenario.declaration();
            let shapes = declaration
                .shapes
                .iter()
                .map(|shape| shape.name())
                .collect::<Vec<_>>()
                .join(",");
            let slow = if declaration.slow { " (opt-in)" } else { "" };
            let name = scenario.name();
            let bound = declaration.bound;
            println!("{name}{slow}\t{shapes}\t{bound}");
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
        args.cases = Scenario::value_variants()
            .iter()
            .copied()
            .filter(|scenario| args.slow || !scenario.declaration().slow)
            .collect();
    }
    for &scenario in &args.cases {
        for shape in &args.shape {
            if !scenario.declaration().shapes.contains(shape) {
                return Err(format!(
                    "{} does not support {}; use --list",
                    scenario.name(),
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
    for &scenario in &args.cases {
        for &shape in &args.shape {
            for &vertices in &args.vertices {
                scenario.run(&mut runner, shape, vertices, &args)?;
            }
        }
    }
    runner.finish()
}
