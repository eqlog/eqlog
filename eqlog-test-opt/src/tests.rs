use std::env;
use std::fs;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::path::PathBuf;
use std::sync::OnceLock;

use eqlog_runtime::{
    find_isomorphism, find_isomorphism_under, CompiledModel, Element, Fuel, Model, ModelHom,
    Relation, RelationId, RelationKind, Signature, Type, TypeId, TypeKind,
};

#[path = "trace.rs"]
mod trace;
use trace::{Op, State};

trait Evaluator: CompiledModel {
    fn close_bounded(&mut self);
    fn canonicalize_compiled(&mut self);
}

trait Execution {
    fn apply(&mut self, op: &Op);
    fn copy_state(&self) -> State;
}

struct CompiledState<M> {
    model: M,
    handles: Vec<Element>,
}

impl<M: Evaluator> Execution for CompiledState<M> {
    fn apply(&mut self, op: &Op) {
        let elements = |slots: &[usize]| {
            slots
                .iter()
                .map(|&slot| self.handles[slot])
                .collect::<Vec<_>>()
        };
        let signature = M::dynamic_signature();
        match op {
            Op::New { type_, parents } => {
                let type_ = signature.type_named(type_).unwrap();
                let element = self.model.new_element(type_, &elements(parents)).unwrap();
                self.handles.push(element);
            }
            Op::Insert {
                relation,
                arguments,
            } => {
                let relation = signature.relation_named(relation).unwrap();
                self.model.insert(relation, &elements(arguments)).unwrap();
            }
            Op::Define {
                function,
                arguments,
            } => {
                let function = signature.relation_named(function).unwrap();
                let element = self.model.define(function, &elements(arguments)).unwrap();
                self.handles.push(element);
            }
            Op::Equate {
                parents,
                left,
                right,
            } => {
                self.model
                    .equate(
                        &elements(parents),
                        self.handles[*left],
                        self.handles[*right],
                    )
                    .unwrap();
            }
            Op::Canonicalize => self.model.canonicalize_compiled(),
            Op::Close => self.model.close_bounded(),
        }
    }

    fn copy_state(&self) -> State {
        let mut model = self.model.to_dynamic();
        model.canonicalize();
        State {
            model,
            handles: self.handles.clone(),
        }
    }
}

fn create<M: Evaluator + 'static>() -> Box<dyn Execution> {
    Box::new(CompiledState {
        model: M::from_dynamic(&Model::new(M::dynamic_signature())).unwrap(),
        handles: Vec::new(),
    })
}

struct Variant {
    name: &'static str,
    create: fn() -> Box<dyn Execution>,
    signature: &'static Signature,
}

struct Case {
    name: &'static str,
    source: &'static str,
    variants: [Variant; 4],
}

include!(concat!(env!("OUT_DIR"), "/cases.rs"));

#[cfg(not(eqlog_opt_replay))]
#[path = "authored.rs"]
mod authored;

fn setting(name: &str, default: u64) -> u64 {
    env::var_os(name)
        .map(|value| {
            value
                .to_str()
                .expect("setting must be UTF-8")
                .parse()
                .expect("setting must be a u64")
        })
        .unwrap_or(default)
}

fn compare(base: &State, left: &State, right: &State) {
    assert_eq!(base.handles.len(), left.handles.len());
    assert_eq!(base.handles.len(), right.handles.len());
    let to_left = ModelHom::new(
        &base.model,
        &left.model,
        base.handles
            .iter()
            .copied()
            .zip(left.handles.iter().copied()),
    )
    .unwrap();
    let to_right = ModelHom::new(
        &base.model,
        &right.model,
        base.handles
            .iter()
            .copied()
            .zip(right.handles.iter().copied()),
    )
    .unwrap();
    let fuel = setting("EQLOG_OPT_FUEL", 50_000_000);
    let iso = find_isomorphism_under(&to_left, &to_right, Fuel::Finite(fuel)).unwrap();
    assert!(
        iso.is_some(),
        "closures are not isomorphic under the supplied inputs"
    );
}

fn run(case: &Case, trace: &[Op]) {
    assert!(
        trace.last().is_some_and(|op| match op {
            Op::Close => true,
            Op::New { .. }
            | Op::Insert { .. }
            | Op::Define { .. }
            | Op::Equate { .. }
            | Op::Canonicalize => false,
        }),
        "a trace must end with a closure comparison"
    );
    let mut base = State::new(case.variants[0].signature);
    let mut states: Vec<_> = case
        .variants
        .iter()
        .map(|variant| {
            assert_eq!(base.model.signature(), variant.signature);
            (variant.create)()
        })
        .collect();
    for (step, op) in trace.iter().enumerate() {
        base.apply(op);
        for (variant, state) in case.variants.iter().zip(&mut states) {
            let name = variant.name;
            eprintln!("step {step}, {name}: {op:?}");
            state.apply(op);
        }
        match op {
            Op::Close => {
                let copies: Vec<_> = states.iter().map(|state| state.copy_state()).collect();
                for (variant, state) in case.variants.iter().zip(&copies).skip(1) {
                    let name = variant.name;
                    eprintln!("compare at step {step}: Naive/Desugared vs {name}");
                    compare(&base, &copies[0], state);
                }
            }
            Op::New { .. }
            | Op::Insert { .. }
            | Op::Define { .. }
            | Op::Equate { .. }
            | Op::Canonicalize => {}
        }
    }
}

#[test]
fn optimization_equivalence() {
    let cases = cases();
    let replay = env::var_os("EQLOG_OPT_TRACE").map(|path| {
        assert_eq!(cases.len(), 1, "use EQLOG_OPT_CASE with EQLOG_OPT_TRACE");
        serde_json::from_slice::<Vec<Op>>(&fs::read(path).unwrap()).unwrap()
    });
    let seed = setting("EQLOG_OPT_INPUT_SEED", 0);
    let count = if replay.is_some() {
        1
    } else {
        setting("EQLOG_OPT_TRACES", 4)
    };
    let rounds = setting("EQLOG_OPT_ROUNDS", 5) as usize;
    assert!(
        count > 0 && rounds > 0,
        "the optimization suite must exercise inputs"
    );
    for case in &cases {
        for offset in 0..count {
            let seed = seed.wrapping_add(offset);
            let name = case.name;
            eprintln!("case {name}, input seed {seed}");
            let trace = replay
                .clone()
                .unwrap_or_else(|| trace::generate(case.variants[0].signature, seed, rounds));
            run_checked(case, &seed.to_string(), &trace);
        }
    }
}

fn run_checked(case: &Case, label: &str, trace: &[Op]) {
    match catch_unwind(AssertUnwindSafe(|| run(case, trace))) {
        Ok(()) => {}
        Err(panic) => {
            let name = case.name;
            let directory = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../target/eqlog-opt-failures")
                .join(format!("{name}_{label}"));
            fs::create_dir_all(&directory).unwrap();
            fs::write(directory.join("case.eql"), case.source).unwrap();
            fs::write(
                directory.join("trace.json"),
                serde_json::to_vec_pretty(trace).unwrap(),
            )
            .unwrap();
            let directory = directory.canonicalize().unwrap();
            let directory = directory.display();
            eprintln!("Replay: EQLOG_OPT_CASE={directory}/case.eql EQLOG_OPT_TRACE={directory}/trace.json cargo test -p eqlog-test-opt optimization_equivalence");
            resume_unwind(panic);
        }
    }
}

fn oracle_input() -> State {
    static SIGNATURE: OnceLock<Signature> = OnceLock::new();
    let signature = SIGNATURE.get_or_init(|| {
        Signature::new(
            vec![Type {
                name: "El".into(),
                kind: TypeKind::Plain,
                parents: Vec::new(),
            }],
            vec![Relation {
                name: "marked".into(),
                kind: RelationKind::Predicate,
                arity: vec![TypeId(0)],
                parents: Vec::new(),
            }],
        )
        .unwrap()
    });
    let mut state = State::new(signature);
    for _ in 0..2 {
        state.apply(&Op::New {
            type_: "El".into(),
            parents: Vec::new(),
        });
    }
    state
}

#[test]
#[should_panic(expected = "closures are not isomorphic under the supplied inputs")]
fn oracle_rejects_swapped_inputs_even_when_unanchored_isomorphism_exists() {
    let base = oracle_input();
    let mut left = oracle_input();
    let mut right = oracle_input();
    left.model
        .insert(RelationId(0), &[left.handles[0]])
        .unwrap();
    right
        .model
        .insert(RelationId(0), &[right.handles[1]])
        .unwrap();
    assert!(
        find_isomorphism(&left.model, &right.model, Fuel::Finite(10_000))
            .unwrap()
            .is_some()
    );
    compare(&base, &left, &right);
}

#[test]
#[should_panic(expected = "closures are not isomorphic under the supplied inputs")]
fn oracle_rejects_a_missing_derived_fact() {
    let base = oracle_input();
    let mut left = oracle_input();
    let right = oracle_input();
    left.model
        .insert(RelationId(0), &[left.handles[0]])
        .unwrap();
    compare(&base, &left, &right);
}

#[test]
fn oracle_accepts_different_allocations_and_equality_representatives() {
    let base = oracle_input();
    let mut left = oracle_input();
    let mut right = oracle_input();
    let extra_right = right.handles[0];
    right.handles[0] = right.model.new_element(TypeId(0), &[]).unwrap();
    let extra_left = left.model.new_element(TypeId(0), &[]).unwrap();
    left.model.insert(RelationId(0), &[extra_left]).unwrap();
    right.model.insert(RelationId(0), &[extra_right]).unwrap();
    left.model
        .equate(&[], left.handles[0], left.handles[1])
        .unwrap();
    right
        .model
        .equate(&[], right.handles[1], right.handles[0])
        .unwrap();
    left.model.canonicalize();
    right.model.canonicalize();
    compare(&base, &left, &right);
}
