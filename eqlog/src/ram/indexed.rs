use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::algebra::signature::{Signature, TypeId};
use crate::flat_eqlog::{
    FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection, IndexSpec, QuerySpec, RuleSchedule,
    Schedule,
};

use super::RamFunction;

pub struct TableIndex {
    pub rel: FlatInRel,
    pub order: Arc<[usize]>,
    pub columns: Vec<usize>,
    pub equalities: Vec<(usize, usize)>,
    pub viewed: bool,
}

pub struct IndexedTablePlan {
    pub arity: usize,
    pub functional: bool,
    pub indices: Vec<TableIndex>,
}

pub struct IndexedStratum {
    pub groups: Vec<usize>,
    pub sources: Vec<FlatInRel>,
    pub reads: Vec<((FlatInRel, IndexSpec), usize)>,
    pub buffers: Vec<(usize, FlatOutRel)>,
    pub producers: BTreeMap<FlatOutRel, Vec<usize>>,
    pub deltas: Vec<usize>,
}

pub enum IndexedStmt {
    Loop(Vec<IndexedStmt>),
    WhenChanged {
        stratum: usize,
        body: Vec<IndexedStmt>,
    },
    InitializeChanges(usize),
    MarkChanged(usize),
    BreakUnlessChanged(usize),
    CheckCondition,
}

pub struct IndexedPlan {
    pub tables: BTreeMap<FlatInRel, IndexedTablePlan>,
    pub function_codomains: BTreeSet<TypeId>,
    pub strata: Vec<IndexedStratum>,
    pub body: Vec<IndexedStmt>,
}

fn source_relation(rel: &FlatInRel) -> FlatInRel {
    match rel {
        FlatInRel::RelWithDiagonals { rel, .. } => FlatInRel::Rel(*rel),
        FlatInRel::Rel(_) | FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => rel.clone(),
    }
}

fn lower_schedule(schedule: &Schedule, active: Option<usize>, depth: usize) -> Vec<IndexedStmt> {
    match schedule {
        Schedule::Sequence(children) | Schedule::Independent(children) => children
            .iter()
            .flat_map(|child| lower_schedule(child, active, depth))
            .collect(),
        Schedule::Rules(id) => {
            let mut body = Vec::new();
            if let Some(active) = active {
                body.push(IndexedStmt::MarkChanged(active));
            }
            body.push(IndexedStmt::CheckCondition);
            vec![IndexedStmt::WhenChanged {
                stratum: id.0,
                body,
            }]
        }
        Schedule::Saturate(body) => {
            let mut lowered = vec![IndexedStmt::InitializeChanges(depth)];
            lowered.extend(lower_schedule(body, Some(depth), depth + 1));
            lowered.push(IndexedStmt::BreakUnlessChanged(depth));
            if let Some(active) = active {
                lowered.push(IndexedStmt::MarkChanged(active));
            }
            vec![IndexedStmt::Loop(lowered)]
        }
        Schedule::ModelComponents { .. } => {
            unreachable!("desugared models have no model-scoped strata")
        }
    }
}

impl IndexedPlan {
    pub fn new(
        modules: &[RamFunction],
        schedule: &RuleSchedule,
        selection: &IndexSelection,
        signature: &Signature,
    ) -> Self {
        let viewed: BTreeSet<_> = modules
            .iter()
            .flat_map(RamFunction::input_indices)
            .filter(|(_, index)| match index.age {
                IndexAge::Old | IndexAge::All => true,
                IndexAge::New => false,
            })
            .map(|(rel, index)| (rel, index.order))
            .chain(signature.iter_funcs().map(|func| {
                let rel = FlatInRel::Rel(FlatRel::Func(func));
                let query = QuerySpec::eval_func(func, signature);
                let order = selection.current_query(&rel, query).order.clone();
                (rel, order)
            }))
            .collect();
        let mut tables: BTreeMap<FlatInRel, IndexedTablePlan> = BTreeMap::new();
        for (rel, index) in selection.current_indices() {
            let source = source_relation(rel);
            let functional = match source {
                FlatInRel::Rel(FlatRel::Func(_)) => true,
                FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::ModelMember(_))
                | FlatInRel::TypeSet(_) => false,
                FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) => {
                    unreachable!("only relations and types have tables")
                }
            };
            let arity = source.arity(signature).len();
            let table = tables.entry(source).or_insert_with(|| IndexedTablePlan {
                arity,
                functional,
                indices: Vec::new(),
            });
            if table
                .indices
                .iter()
                .any(|other| other.rel == *rel && other.order == index.order)
            {
                continue;
            }
            let (columns, equalities) = match rel {
                FlatInRel::Rel(_) | FlatInRel::TypeSet(_) => (index.order.to_vec(), Vec::new()),
                FlatInRel::RelWithDiagonals { equalities, .. } => {
                    let kept: Vec<_> = equalities
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &j)| (i == j).then_some(i))
                        .collect();
                    let columns = index.order.iter().map(|&column| kept[column]).collect();
                    let equalities = equalities
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &j)| (i != j).then_some((i, j)))
                        .collect();
                    (columns, equalities)
                }
                FlatInRel::Equality(_) => unreachable!("equalities have no tuple indices"),
            };
            table.indices.push(TableIndex {
                rel: rel.clone(),
                order: index.order.clone(),
                columns,
                equalities,
                viewed: viewed.contains(&(rel.clone(), index.order.clone())),
            });
        }
        let strata = schedule
            .strata
            .iter()
            .map(|stratum| {
                let reads: BTreeSet<_> = stratum
                    .groups
                    .iter()
                    .flat_map(|&m| modules[m].input_indices())
                    .collect();
                let sources: Vec<_> = reads
                    .iter()
                    .map(|(rel, _)| source_relation(rel))
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
                let reads: Vec<_> = reads
                    .into_iter()
                    .map(|(rel, index)| {
                        let source = sources
                            .binary_search(&source_relation(&rel))
                            .expect("sources contain every read relation");
                        ((rel, index), source)
                    })
                    .collect();
                let deltas = reads
                    .iter()
                    .enumerate()
                    .filter_map(|(i, ((_, index), _))| match index.age {
                        IndexAge::New => Some(i),
                        IndexAge::Old | IndexAge::All => None,
                    })
                    .collect();
                let buffers: Vec<_> = stratum
                    .groups
                    .iter()
                    .enumerate()
                    .flat_map(|(i, &m)| {
                        modules[m]
                            .interface
                            .outputs
                            .iter()
                            .map(move |&rel| (i, rel))
                    })
                    .collect();
                let mut producers: BTreeMap<_, Vec<_>> = BTreeMap::new();
                for &(i, rel) in &buffers {
                    producers.entry(rel).or_default().push(i);
                }
                IndexedStratum {
                    groups: stratum.groups.clone(),
                    sources,
                    reads,
                    buffers,
                    producers,
                    deltas,
                }
            })
            .collect();
        Self {
            tables,
            function_codomains: signature
                .iter_funcs()
                .map(|func| signature.func(func).codomain)
                .collect(),
            strata,
            body: lower_schedule(&schedule.body, None, 0),
        }
    }

    pub fn position(&self, rel: &FlatInRel, order: &[usize]) -> usize {
        self.tables[&source_relation(rel)]
            .indices
            .iter()
            .position(|index| index.rel == *rel && &index.order[..] == order)
            .expect("every selected index belongs to a table")
    }
}
