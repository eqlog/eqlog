use std::collections::{BTreeMap, BTreeSet};

use eqlog_runtime::{CompiledModel, Element, RelationId};

mod workloads;

#[derive(Clone, Copy, Debug)]
pub enum Phase {
    Initial,
    Incremental,
    Unchanged,
}

impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Initial => "initial",
            Self::Incremental => "incremental",
            Self::Unchanged => "unchanged",
        }
    }
}

pub trait Workload {
    fn close(&mut self);
    fn check(&self);
}

pub struct Case {
    pub name: &'static str,
    pub mode: &'static str,
    pub prepare: fn(usize, Phase) -> Box<dyn Workload>,
}

trait Evaluator: CompiledModel + 'static {
    fn new() -> Self;
    fn close(&mut self);
}

struct Fixture<M> {
    model: M,
    expected: BTreeMap<RelationId, Vec<Vec<Element>>>,
}

impl<M: Evaluator> Fixture<M> {
    fn new() -> Self {
        Self {
            model: M::new(),
            expected: BTreeMap::new(),
        }
    }

    fn elements(&mut self, name: &str, parents: &[Element], count: usize) -> Vec<Element> {
        let type_ = M::dynamic_signature().type_named(name).unwrap();
        (0..count)
            .map(|_| self.model.new_element(type_, parents).unwrap())
            .collect()
    }

    fn insert(&mut self, name: &str, row: &[Element]) {
        let relation = M::dynamic_signature().relation_named(name).unwrap();
        self.model.insert(relation, row).unwrap();
    }

    fn expect(&mut self, name: &str, rows: impl IntoIterator<Item = Vec<Element>>) {
        let relation = M::dynamic_signature().relation_named(name).unwrap();
        self.expected.entry(relation).or_default().extend(rows);
    }

    fn settle(&mut self, phase: Phase) {
        match phase {
            Phase::Initial => {}
            Phase::Incremental | Phase::Unchanged => {
                self.close();
            }
        }
    }
}

impl<M: Evaluator> Workload for Fixture<M> {
    fn close(&mut self) {
        self.model.close();
    }

    fn check(&self) {
        let snapshot = self.model.to_dynamic();
        for (&relation, expected) in &self.expected {
            let expected: BTreeSet<_> = expected
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|&element| snapshot.root(element).unwrap())
                        .collect::<Vec<_>>()
                })
                .collect();
            let actual: BTreeSet<_> = snapshot.tuples(relation).unwrap().collect();
            let name = &snapshot.signature().relation(relation).unwrap().name;
            assert_eq!(actual, expected, "incorrect {name} closure");
        }
    }
}

include!(concat!(env!("OUT_DIR"), "/cases.rs"));
