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

pub struct IndexedRead {
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub source: usize,
    pub position: usize,
}

pub struct IndexedCall {
    pub function: usize,
    pub producer: usize,
    pub inputs: Vec<usize>,
    pub outputs: Vec<FlatOutRel>,
}

pub enum IndexedOperation {
    SnapshotCursors,
    ReturnUnlessChanged,
    SaveCursors,
    SyncTables,
    ComputeWork,
    AllocateDelta(usize),
    Block(Vec<IndexedOperation>),
    InitializeTasks {
        capacity: Option<usize>,
    },
    WhenAdvanced {
        source: usize,
        body: Vec<IndexedOperation>,
    },
    QueueDelta(usize),
    RunTasks,
    TakeOutput {
        producer: usize,
        rel: FlatOutRel,
    },
    QueueCall(IndexedCall),
    ApplyEquality {
        producer: usize,
        typ: TypeId,
    },
    CanonicalizeEqualities(Vec<TypeId>),
    Insert {
        producer: usize,
        rel: FlatRel,
        arity: usize,
    },
    AppendPending {
        producer: usize,
        rel: FlatOutRel,
    },
    RestoreOutput {
        producer: usize,
        rel: FlatOutRel,
    },
    NormalizeFunctions,
    ReturnChanged,
}

pub enum IndexedCondition {
    Closed,
    NoAllocationOrNormalization,
    NoPendingEqualities,
    AnyUprooted(Vec<TypeId>),
}

pub enum IndexedLifecycle {
    SetDeferred(bool),
    CallDeferredClose,
    ReturnResult,
    CanonicalizeRelations,
    NormalizeFunctions,
    CheckConditionBeforeDelta,
    TakeDelta,
    ClearAllocated,
    ApplyDeferredFunctions,
    RecordNormalized,
    SaveDelta,
    Canonicalize,
    MarkClosed,
    ReturnFalse,
    ReturnCondition,
    InitializeNormalization,
    InitializePending,
    MarkNormalizationChanged,
    ReturnNormalizationChanged,
}

pub struct IndexedStratum {
    pub sources: Vec<FlatInRel>,
    pub reads: Vec<IndexedRead>,
    pub buffers: Vec<(usize, FlatOutRel)>,
    pub body: Vec<IndexedOperation>,
}

pub enum IndexedStmt {
    When {
        condition: IndexedCondition,
        body: Vec<IndexedStmt>,
    },
    Lifecycle(IndexedLifecycle),
    ApplyFunctionalEqualities(TypeId),
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
    pub wrapper: Vec<IndexedStmt>,
    pub normalize: Vec<IndexedStmt>,
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

fn lower_stratum(
    groups: &[usize],
    sources: Vec<FlatInRel>,
    reads: Vec<IndexedRead>,
    buffers: Vec<(usize, FlatOutRel)>,
    producers: BTreeMap<FlatOutRel, Vec<usize>>,
    modules: &[RamFunction],
    signature: &Signature,
) -> IndexedStratum {
    let mut body = vec![
        IndexedOperation::SnapshotCursors,
        IndexedOperation::ReturnUnlessChanged,
        IndexedOperation::SaveCursors,
        IndexedOperation::SyncTables,
        IndexedOperation::ComputeWork,
    ];
    let deltas: Vec<_> = reads
        .iter()
        .enumerate()
        .filter_map(|(id, read)| match read.index.age {
            IndexAge::New => Some(id),
            IndexAge::Old | IndexAge::All => None,
        })
        .collect();
    body.extend(deltas.iter().copied().map(IndexedOperation::AllocateDelta));
    if !deltas.is_empty() {
        let mut tasks = vec![IndexedOperation::InitializeTasks { capacity: None }];
        tasks.extend(deltas.iter().map(|&id| IndexedOperation::WhenAdvanced {
            source: reads[id].source,
            body: vec![IndexedOperation::QueueDelta(id)],
        }));
        tasks.push(IndexedOperation::RunTasks);
        body.push(IndexedOperation::Block(tasks));
    }
    body.extend(
        buffers
            .iter()
            .map(|&(producer, rel)| IndexedOperation::TakeOutput { producer, rel }),
    );
    let mut tasks = vec![IndexedOperation::InitializeTasks {
        capacity: Some(groups.len()),
    }];
    tasks.extend(groups.iter().enumerate().map(|(producer, &function)| {
        let module = &modules[function];
        let inputs = module
            .input_indices()
            .into_iter()
            .map(|(rel, index)| {
                reads
                    .iter()
                    .position(|read| read.rel == rel && read.index == index)
                    .expect("stratum inputs contain function inputs")
            })
            .collect();
        IndexedOperation::QueueCall(IndexedCall {
            function,
            producer,
            inputs,
            outputs: module.interface.outputs.iter().copied().collect(),
        })
    }));
    tasks.push(IndexedOperation::RunTasks);
    body.push(IndexedOperation::Block(tasks));
    let mut equalities = Vec::new();
    for (output, producers) in &producers {
        match output {
            FlatOutRel::Equality(typ) => {
                body.extend(
                    producers
                        .iter()
                        .map(|&producer| IndexedOperation::ApplyEquality {
                            producer,
                            typ: *typ,
                        }),
                );
                equalities.push(*typ);
            }
            FlatOutRel::Rel(_) | FlatOutRel::FuncDomain(_) => {}
        }
    }
    if !equalities.is_empty() {
        body.push(IndexedOperation::CanonicalizeEqualities(equalities));
    }
    for (output, producers) in &producers {
        match output {
            FlatOutRel::Rel(rel) => {
                body.extend(producers.iter().map(|&producer| IndexedOperation::Insert {
                    producer,
                    rel: *rel,
                    arity: rel.arity(signature).len(),
                }))
            }
            FlatOutRel::FuncDomain(_) => {
                body.extend(
                    producers
                        .iter()
                        .map(|&producer| IndexedOperation::AppendPending {
                            producer,
                            rel: *output,
                        }),
                )
            }
            FlatOutRel::Equality(_) => {}
        }
    }
    body.extend(
        buffers
            .iter()
            .map(|&(producer, rel)| IndexedOperation::RestoreOutput { producer, rel }),
    );
    body.extend([
        IndexedOperation::NormalizeFunctions,
        IndexedOperation::ReturnChanged,
    ]);
    IndexedStratum {
        sources,
        reads,
        buffers,
        body,
    }
}

fn normalize_body(codomains: &BTreeSet<TypeId>) -> Vec<IndexedStmt> {
    let mut body = vec![IndexedStmt::Lifecycle(IndexedLifecycle::InitializePending)];
    body.extend(
        codomains
            .iter()
            .copied()
            .map(IndexedStmt::ApplyFunctionalEqualities),
    );
    body.push(IndexedStmt::When {
        condition: IndexedCondition::NoPendingEqualities,
        body: vec![IndexedStmt::Lifecycle(
            IndexedLifecycle::ReturnNormalizationChanged,
        )],
    });
    body.push(IndexedStmt::When {
        condition: IndexedCondition::AnyUprooted(codomains.iter().copied().collect()),
        body: vec![
            IndexedStmt::Lifecycle(IndexedLifecycle::MarkNormalizationChanged),
            IndexedStmt::Lifecycle(IndexedLifecycle::CanonicalizeRelations),
        ],
    });
    vec![
        IndexedStmt::Lifecycle(IndexedLifecycle::InitializeNormalization),
        IndexedStmt::Loop(body),
    ]
}

fn close_body(schedule: Vec<IndexedStmt>) -> Vec<IndexedStmt> {
    let mut iteration = schedule;
    iteration.extend([
        IndexedStmt::Lifecycle(IndexedLifecycle::ClearAllocated),
        // Deferred function definitions evaluate through current table views.
        IndexedStmt::Lifecycle(IndexedLifecycle::SetDeferred(false)),
        IndexedStmt::Lifecycle(IndexedLifecycle::ApplyDeferredFunctions),
        IndexedStmt::Lifecycle(IndexedLifecycle::SetDeferred(true)),
        IndexedStmt::Lifecycle(IndexedLifecycle::RecordNormalized),
        IndexedStmt::When {
            condition: IndexedCondition::NoAllocationOrNormalization,
            body: vec![
                IndexedStmt::Lifecycle(IndexedLifecycle::SaveDelta),
                IndexedStmt::Lifecycle(IndexedLifecycle::Canonicalize),
                IndexedStmt::Lifecycle(IndexedLifecycle::MarkClosed),
                IndexedStmt::Lifecycle(IndexedLifecycle::ReturnFalse),
            ],
        },
        IndexedStmt::Lifecycle(IndexedLifecycle::CanonicalizeRelations),
        IndexedStmt::Lifecycle(IndexedLifecycle::NormalizeFunctions),
    ]);
    vec![
        IndexedStmt::When {
            condition: IndexedCondition::Closed,
            body: vec![IndexedStmt::Lifecycle(IndexedLifecycle::ReturnCondition)],
        },
        IndexedStmt::Lifecycle(IndexedLifecycle::CanonicalizeRelations),
        IndexedStmt::Lifecycle(IndexedLifecycle::NormalizeFunctions),
        IndexedStmt::Lifecycle(IndexedLifecycle::CheckConditionBeforeDelta),
        IndexedStmt::Lifecycle(IndexedLifecycle::TakeDelta),
        IndexedStmt::Loop(iteration),
    ]
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
                        let position = tables[&source_relation(&rel)]
                            .indices
                            .iter()
                            .position(|candidate| {
                                candidate.rel == rel && candidate.order == index.order
                            })
                            .expect("selected input belongs to a table");
                        IndexedRead {
                            rel,
                            index,
                            source,
                            position,
                        }
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
                lower_stratum(
                    &stratum.groups,
                    sources,
                    reads,
                    buffers,
                    producers,
                    modules,
                    signature,
                )
            })
            .collect();
        let function_codomains: BTreeSet<_> = signature
            .iter_funcs()
            .map(|func| signature.func(func).codomain)
            .collect();
        let normalize = normalize_body(&function_codomains);
        Self {
            tables,
            function_codomains,
            strata,
            normalize,
            wrapper: vec![
                IndexedStmt::Lifecycle(IndexedLifecycle::SetDeferred(true)),
                IndexedStmt::Lifecycle(IndexedLifecycle::CallDeferredClose),
                IndexedStmt::Lifecycle(IndexedLifecycle::SetDeferred(false)),
                IndexedStmt::Lifecycle(IndexedLifecycle::ReturnResult),
            ],
            body: close_body(lower_schedule(&schedule.body, None, 0)),
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
