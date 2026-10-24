use std::collections::{BTreeMap, BTreeSet};

use super::{
    CompactPlan, IndexPreparation, NativeIndexPreparation, NativePreparation, RamFunction,
};
use crate::algebra::signature::{Signature, TypeId};
use crate::flat_eqlog::{
    FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection, IndexSpec, RuleSchedule, Schedule,
    Stratum,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InputStorage {
    Relation(usize),
    Index(usize),
    Native(usize),
}

pub enum InheritedRows {
    MemberDomain(TypeId),
    CompactIndex(usize),
    Global,
}

pub struct InheritedInput {
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub arity: usize,
    pub rows: InheritedRows,
}

pub struct ScopedHistory {
    pub storage: InputStorage,
    pub owners: Vec<TypeId>,
    pub arity: usize,
}

pub struct TransportBaseline {
    pub relations: Vec<FlatInRel>,
    pub maps: Vec<(FlatInRel, IndexSpec)>,
    pub relation_maps: Vec<Vec<usize>>,
}

pub struct OutputConversion {
    pub output: FlatOutRel,
    pub pending: bool,
    pub columns: Vec<(usize, TypeId)>,
}

pub enum CanonicalInput {
    Global,
    CompactOwner,
    CompactMembers,
}

pub enum ProofRows {
    Direct,
    RestrictOwner { suffix: usize },
    RestoreOwners { prefix: usize, arity: usize },
}

pub struct CallInput {
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub storage: InputStorage,
    pub version: Option<IndexAge>,
    pub proof_rows: ProofRows,
}

pub struct EvaluationCall {
    pub module: usize,
    pub inputs: Vec<CallInput>,
    pub canonical: BTreeMap<TypeId, CanonicalInput>,
}

pub struct StratumEvaluation {
    pub model: Option<TypeId>,
    pub stable_inputs: BTreeSet<FlatInRel>,
    pub inputs: BTreeSet<FlatInRel>,
    pub outputs: BTreeSet<FlatOutRel>,
    pub possible_inputs: Option<BTreeSet<BTreeSet<usize>>>,
    pub output_conversions: Vec<OutputConversion>,
    pub calls: Vec<EvaluationCall>,
    pub diagonal_inputs: BTreeSet<FlatInRel>,
    pub stable_fields: BTreeMap<InputStorage, FlatInRel>,
    pub inherited: Option<BTreeMap<InputStorage, InheritedInput>>,
}

#[derive(Clone, Copy)]
pub enum RetainedOwners {
    None,
    Always,
    Component(usize),
}

pub enum EvaluationIteration {
    Components,
    ComponentObjects,
    IncomingObjects,
}

pub enum EvaluationCondition {
    StratumChanged {
        stratum: usize,
        scoped: bool,
        stable: bool,
        retain: Option<RetainedOwners>,
    },
    IncomingPresent,
    IncomingForObject,
    IncomingAbsent,
}

pub enum TransportEdges {
    Incoming,
    Internal,
    Outgoing,
}

pub enum EvaluationStmt {
    Block(Vec<EvaluationStmt>),
    Loop(Vec<EvaluationStmt>),
    ForEach {
        iteration: EvaluationIteration,
        body: Vec<EvaluationStmt>,
    },
    When {
        condition: EvaluationCondition,
        body: Vec<EvaluationStmt>,
    },
    AllocateStable(usize),
    InitializeChanges(usize),
    MarkChanged(usize),
    PropagateChanges {
        source: usize,
        target: usize,
    },
    BreakUnlessChanged {
        id: usize,
        require_internal: bool,
    },
    CheckCondition,
    SetParents {
        from_owners: bool,
    },
    SetOwners {
        parent_count: usize,
    },
    RefreshConsumers,
    RecomputeModelIndices(usize),
    PrepareIndex {
        rel: FlatInRel,
        index: IndexSpec,
    },
    PrepareNative(usize),
    CaptureBaseline {
        model: TypeId,
    },
    ComputeComponents {
        model: TypeId,
    },
    StageFrontier {
        model: TypeId,
        root: TypeId,
        retain: RetainedOwners,
    },
    ComputeIncoming {
        model: TypeId,
    },
    DefineRetention {
        id: usize,
        parent: RetainedOwners,
    },
    Transport {
        model: TypeId,
        root: TypeId,
        edges: TransportEdges,
        retain: RetainedOwners,
        changed: Option<usize>,
    },
    SaveFrontier {
        model: TypeId,
        root: TypeId,
    },
}

#[derive(Default)]
pub struct EvaluationPlan {
    pub models: BTreeMap<TypeId, usize>,
    pub inputs: BTreeMap<FlatInRel, usize>,
    pub indices: BTreeMap<(FlatInRel, IndexSpec), usize>,
    pub old_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    pub strata: Vec<StratumEvaluation>,
    pub transport_baselines: BTreeMap<TypeId, TransportBaseline>,
    pub scoped_histories: Vec<ScopedHistory>,
    pub tracked_owners: BTreeSet<TypeId>,
    pub body: Vec<EvaluationStmt>,
}

pub fn input_key(rel: FlatInRel, mut index: IndexSpec) -> (FlatInRel, IndexSpec) {
    index.age = IndexAge::Old;
    (rel, index)
}

fn source_relation(rel: &FlatInRel) -> FlatInRel {
    match rel {
        FlatInRel::RelWithDiagonals { rel, .. } => FlatInRel::Rel(*rel),
        FlatInRel::Rel(_) | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => rel.clone(),
    }
}

pub fn scope_prefix(rel: &FlatInRel, model: TypeId, signature: &Signature) -> usize {
    let parent = match rel {
        FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => {
            rel.parent_model_type(signature)
        }
        FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => None,
    };
    parent.map_or(0, |parent| {
        assert!(
            parent == model
                || signature.type_(model).parents.contains(&parent)
                || signature.type_(parent).parents.contains(&model)
        );
        (signature.type_(parent).parents.len() + 1).min(signature.type_(model).parents.len() + 1)
    })
}

fn native_index(
    native_indices: &[NativeIndexPreparation],
    rel: &FlatInRel,
    index: &IndexSpec,
) -> Option<usize> {
    native_indices
        .iter()
        .position(|plan| plan.rel == *rel && plan.index.order == index.order)
}

fn diagonal_input(
    stratum: &Stratum,
    source: &FlatInRel,
    modules: &[RamFunction],
    selection: &IndexSelection,
) -> bool {
    if stratum.model.is_some() {
        return false;
    }
    let primary = selection.current_primary(source);
    let [first, second, ..] = primary.order.as_ref() else {
        return false;
    };
    let mut used = false;
    for &module in &stratum.groups {
        for routine in &modules[module].rules {
            for (rel, _) in routine.input_indices() {
                if source_relation(&rel) != *source {
                    continue;
                }
                used = true;
                let constrained = match rel {
                    FlatInRel::RelWithDiagonals { equalities, .. } => {
                        equalities[*first] == equalities[*second]
                    }
                    FlatInRel::Rel(_) | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => false,
                };
                if !constrained {
                    return false;
                }
            }
        }
    }
    used
}

fn transport_baseline(
    model: TypeId,
    preparation: &NativePreparation,
    selection: &IndexSelection,
    signature: &Signature,
    compact: &CompactPlan,
) -> Option<TransportBaseline> {
    if !signature.type_(model).parents.is_empty()
        || signature
            .iter_model_decls()
            .any(|(_, ids)| signature.type_(ids.type_).parents.last() == Some(&model))
    {
        return None;
    }
    let plan = &preparation.propagation;
    let relations: Vec<_> = selection
        .indices
        .keys()
        .filter(|rel| compact.shared_indices(rel))
        .filter(|rel| match rel {
            FlatInRel::Rel(rel) => {
                plan.relations.contains(rel) && rel.parent_model_type(signature) == Some(model)
            }
            FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
                false
            }
        })
        .cloned()
        .collect();
    if relations
        .iter()
        .any(|rel| selection.current_primary(rel).order.first() != Some(&0))
    {
        return None;
    }
    let maps: Vec<_> = relations
        .iter()
        .flat_map(|rel| plan.map_indices.get(&(model, rel.clone())))
        .flatten()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let relation_maps = relations
        .iter()
        .map(|rel| {
            plan.map_indices
                .get(&(model, rel.clone()))
                .into_iter()
                .flatten()
                .map(|map| maps.binary_search(map).unwrap())
                .collect()
        })
        .collect();
    Some(TransportBaseline {
        relations,
        maps,
        relation_maps,
    })
}

fn inherited_input(
    rel: &FlatInRel,
    index: &IndexSpec,
    model: TypeId,
    signature: &Signature,
    compact: &CompactPlan,
) -> Option<InheritedInput> {
    let rows = match rel {
        FlatInRel::Rel(FlatRel::ModelMember(typ)) => {
            if !compact.supports_member(*typ)
                || signature.type_(*typ).parents.as_slice() != [model]
                || index.order.as_ref() != [0, 1]
            {
                return None;
            }
            InheritedRows::MemberDomain(*typ)
        }
        FlatInRel::Rel(FlatRel::Pred(_) | FlatRel::Func(_)) => {
            InheritedRows::CompactIndex(compact.inherited_slot(rel, index, model)?)
        }
        FlatInRel::TypeSet(typ) => {
            if *typ != model || index.order.as_ref() != [0] {
                return None;
            }
            InheritedRows::Global
        }
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::Equality(_) => return None,
    };
    Some(InheritedInput {
        rel: rel.clone(),
        index: index.clone(),
        arity: rel.arity(signature).len() - scope_prefix(rel, model, signature),
        rows,
    })
}

fn inherited_plan(
    stratum: &Stratum,
    modules: &[RamFunction],
    preparation: &IndexPreparation,
    inputs: &BTreeMap<FlatInRel, usize>,
    indices: &BTreeMap<(FlatInRel, IndexSpec), usize>,
    native_indices: &[NativeIndexPreparation],
    selection: &IndexSelection,
    signature: &Signature,
    compact: &CompactPlan,
) -> Option<BTreeMap<InputStorage, InheritedInput>> {
    let model = stratum.model?;
    if !compact.supports_model(model) {
        return None;
    }
    for &module in &stratum.groups {
        for routine in &modules[module].rules {
            let owner = routine.flat_rule.scope.owners().first()?;
            for stmt in &routine.flat_rule.premise {
                match &stmt.rel {
                    FlatInRel::TypeSet(typ) => {
                        if *typ != model || stmt.args.len() != 1 || &stmt.args[0] != owner {
                            return None;
                        }
                    }
                    FlatInRel::RelWithDiagonals { .. } => return None,
                    FlatInRel::Rel(_) | FlatInRel::Equality(_) => {}
                }
            }
            // Transport changes the owner prefix, but leaves owners stored as ordinary data unchanged.
            if routine
                .flat_rule
                .premise
                .iter()
                .any(|stmt| stmt.args.iter().skip(1).any(|arg| arg == owner))
                || routine
                    .flat_rule
                    .conclusion
                    .iter()
                    .any(|stmt| stmt.args.iter().skip(1).any(|arg| arg == owner))
            {
                return None;
            }
        }
    }
    let mut fields = BTreeMap::new();
    for rel in preparation
        .indices
        .iter()
        .map(|(rel, _)| source_relation(rel))
        .collect::<BTreeSet<_>>()
    {
        let input = inherited_input(
            &rel,
            selection.current_primary(&rel),
            model,
            signature,
            compact,
        )?;
        fields.insert(InputStorage::Relation(inputs[&rel]), input);
    }
    if fields.is_empty() {
        return None;
    }
    for (rel, index) in &preparation.indices {
        let input = inherited_input(rel, index, model, signature, compact)?;
        let storage = if let Some(id) = native_index(native_indices, rel, index) {
            Some(InputStorage::Native(id))
        } else if !selection.is_primary(rel, index) {
            Some(InputStorage::Index(
                indices[&input_key(rel.clone(), index.clone())],
            ))
        } else {
            None
        };
        if let Some(storage) = storage {
            fields.insert(storage, input);
        }
    }
    Some(fields)
}

fn output_conversions(
    outputs: &BTreeSet<FlatOutRel>,
    model: Option<TypeId>,
    signature: &Signature,
    compact: &CompactPlan,
) -> Vec<OutputConversion> {
    let Some(model) = model else {
        return Vec::new();
    };
    outputs
        .iter()
        .filter_map(|output| {
            let relation = match output {
                FlatOutRel::Rel(rel) => Some((*rel, false)),
                FlatOutRel::FuncDomain(func) => Some((FlatRel::Func(*func), true)),
                FlatOutRel::Equality(typ) => {
                    return (compact.supports_member(*typ)
                        && signature.type_(*typ).parents.first() == Some(&model))
                    .then(|| OutputConversion {
                        output: output.clone(),
                        pending: false,
                        columns: vec![(0, *typ), (1, *typ)],
                    });
                }
            };
            let (relation, pending) = relation.unwrap();
            let columns: Vec<_> = output
                .arity(signature)
                .into_iter()
                .enumerate()
                .filter(|&(column, typ)| {
                    compact.supports_member(typ)
                        && relation.column_maps_under(signature, column, model)
                })
                .collect();
            (!columns.is_empty()).then(|| OutputConversion {
                output: output.clone(),
                pending,
                columns,
            })
        })
        .collect()
}

fn evaluation_calls(
    stratum: &Stratum,
    modules: &[RamFunction],
    inputs: &BTreeMap<FlatInRel, usize>,
    indices: &BTreeMap<(FlatInRel, IndexSpec), usize>,
    old_indices: &BTreeSet<(FlatInRel, IndexSpec)>,
    native_indices: &[NativeIndexPreparation],
    selection: &IndexSelection,
    signature: &Signature,
    compact: &CompactPlan,
) -> Vec<EvaluationCall> {
    stratum
        .groups
        .iter()
        .map(|&module| {
            let function = &modules[module];
            let inputs = function
                .input_indices()
                .into_iter()
                .map(|(rel, index)| {
                    let key = input_key(rel.clone(), index.clone());
                    let (storage, version) =
                        if let Some(id) = native_index(native_indices, &rel, &index) {
                            (InputStorage::Native(id), Some(index.age))
                        } else if selection.is_primary(&rel, &index) {
                            (
                                InputStorage::Relation(inputs[&source_relation(&rel)]),
                                Some(index.age),
                            )
                        } else {
                            (
                                InputStorage::Index(indices[&key]),
                                old_indices.contains(&key).then_some(index.age),
                            )
                        };
                    let prefix = stratum
                        .model
                        .map_or(0, |model| scope_prefix(&rel, model, signature));
                    let arity = rel.arity(signature).len();
                    let proof_rows = if function.interface.proof_owner_prefix {
                        if prefix == 0 {
                            ProofRows::RestrictOwner { suffix: arity - 1 }
                        } else {
                            ProofRows::Direct
                        }
                    } else {
                        ProofRows::RestoreOwners { prefix, arity }
                    };
                    CallInput {
                        rel,
                        index,
                        storage,
                        version,
                        proof_rows,
                    }
                })
                .collect();
            let canonical = function
                .interface
                .canonical_types
                .iter()
                .map(|&typ| {
                    let source = if !compact.supports_member(typ) {
                        CanonicalInput::Global
                    } else if stratum.model == signature.type_(typ).parents.first().copied() {
                        CanonicalInput::CompactOwner
                    } else {
                        CanonicalInput::CompactMembers
                    };
                    (typ, source)
                })
                .collect();
            EvaluationCall {
                module,
                inputs,
                canonical,
            }
        })
        .collect()
}

fn loop_inputs(schedule: &Schedule, strata: &[StratumEvaluation], result: &mut Vec<usize>) {
    match schedule {
        Schedule::Rules(id) => {
            if !strata[id.0].stable_fields.is_empty() {
                result.push(id.0);
            }
        }
        Schedule::Sequence(children) | Schedule::Independent(children) => {
            for child in children {
                loop_inputs(child, strata, result);
            }
        }
        Schedule::Saturate(_) | Schedule::ModelComponents { .. } => {}
    }
}

struct ScheduleLowering<'a> {
    strata: &'a [Stratum],
    plans: &'a [StratumEvaluation],
    preparations: &'a [IndexPreparation],
    model_preparations: &'a BTreeMap<TypeId, NativePreparation>,
    native_indices: &'a [NativeIndexPreparation],
    baselines: &'a BTreeMap<TypeId, TransportBaseline>,
    signature: &'a Signature,
    compact: &'a CompactPlan,
}

impl ScheduleLowering<'_> {
    fn lower(
        &self,
        schedule: &Schedule,
        active: Option<usize>,
        depth: usize,
        root: Option<TypeId>,
        retain: RetainedOwners,
    ) -> Vec<EvaluationStmt> {
        match schedule {
            Schedule::Sequence(children) | Schedule::Independent(children) => children
                .iter()
                .flat_map(|child| self.lower(child, active, depth, root, retain))
                .collect(),
            Schedule::Rules(id) => {
                let mut body = Vec::new();
                if let Some(target) = active {
                    body.push(EvaluationStmt::MarkChanged(target));
                }
                body.push(EvaluationStmt::CheckCondition);
                vec![EvaluationStmt::When {
                    condition: EvaluationCondition::StratumChanged {
                        stratum: id.0,
                        scoped: self.strata[id.0].model.is_some(),
                        stable: !self.plans[id.0].stable_fields.is_empty(),
                        retain: self.preparations[id.0]
                            .reads_descendants()
                            .then_some(retain),
                    },
                    body,
                }]
            }
            Schedule::Saturate(body) => {
                let mut stable_inputs = Vec::new();
                loop_inputs(body, self.plans, &mut stable_inputs);
                let mut block: Vec<_> = stable_inputs
                    .into_iter()
                    .map(EvaluationStmt::AllocateStable)
                    .collect();
                let mut loop_body = vec![EvaluationStmt::InitializeChanges(depth)];
                loop_body.extend(self.lower(body, Some(depth), depth + 1, root, retain));
                loop_body.push(EvaluationStmt::BreakUnlessChanged {
                    id: depth,
                    require_internal: false,
                });
                if let Some(target) = active {
                    loop_body.push(EvaluationStmt::MarkChanged(target));
                }
                block.push(EvaluationStmt::Loop(loop_body));
                vec![EvaluationStmt::Block(block)]
            }
            Schedule::ModelComponents { model, body } => {
                self.model_components(*model, body, active, depth, root, retain)
            }
        }
    }

    fn model_components(
        &self,
        model: TypeId,
        body: &Schedule,
        active: Option<usize>,
        depth: usize,
        root: Option<TypeId>,
        retain: RetainedOwners,
    ) -> Vec<EvaluationStmt> {
        let outermost = root.is_none();
        let root = root.unwrap_or(model);
        let plan = &self.model_preparations[&root];
        let mut block = Vec::new();
        if outermost {
            block.push(EvaluationStmt::RefreshConsumers);
            block.push(EvaluationStmt::SetParents { from_owners: false });
            if !self.baselines.contains_key(&model) {
                let id = self
                    .model_preparations
                    .keys()
                    .position(|&candidate| candidate == model)
                    .unwrap();
                block.push(EvaluationStmt::RecomputeModelIndices(id));
            }
            block.extend(plan.support_indices.iter().map(|(rel, index)| {
                EvaluationStmt::PrepareIndex {
                    rel: rel.clone(),
                    index: index.clone(),
                }
            }));
            block.extend(
                plan.native_indices
                    .iter()
                    .filter(|&&id| !self.native_indices[id].from_primary)
                    .map(|&id| EvaluationStmt::PrepareNative(id)),
            );
            if let Some(baseline) = self.baselines.get(&model) {
                block.extend(baseline.maps.iter().map(|(rel, index)| {
                    EvaluationStmt::PrepareIndex {
                        rel: rel.clone(),
                        index: index.clone(),
                    }
                }));
                // Owner equality can invalidate another owner's inputs during this traversal.
                block.push(EvaluationStmt::CaptureBaseline { model });
            }
        } else {
            block.push(EvaluationStmt::SetParents { from_owners: true });
        }
        block.extend(
            plan.propagation
                .graph_indices
                .get(&model)
                .into_iter()
                .flatten()
                .map(|(rel, index)| EvaluationStmt::PrepareIndex {
                    rel: rel.clone(),
                    index: index.clone(),
                }),
        );
        block.push(EvaluationStmt::ComputeComponents { model });
        if self.baselines.contains_key(&root) {
            block.push(EvaluationStmt::StageFrontier {
                model,
                root,
                retain,
            });
        }
        let compact = self.compact.supports_model(model);
        if compact {
            block.push(EvaluationStmt::ComputeIncoming { model });
        }
        let mut component_body = Vec::new();
        if compact {
            component_body.push(EvaluationStmt::When {
                condition: EvaluationCondition::IncomingPresent,
                body: vec![EvaluationStmt::ForEach {
                    iteration: EvaluationIteration::IncomingObjects,
                    body: vec![EvaluationStmt::When {
                        condition: EvaluationCondition::IncomingForObject,
                        body: vec![EvaluationStmt::Transport {
                            model,
                            root,
                            edges: TransportEdges::Incoming,
                            retain,
                            changed: active,
                        }],
                    }],
                }],
            });
        }
        component_body.push(EvaluationStmt::DefineRetention {
            id: depth,
            parent: retain,
        });
        let mut object_body = vec![EvaluationStmt::SetOwners {
            parent_count: self.signature.type_(model).parents.len(),
        }];
        object_body.extend(self.lower(
            body,
            Some(depth),
            depth + 1,
            Some(root),
            RetainedOwners::Component(depth),
        ));
        let mut component_loop = vec![
            EvaluationStmt::InitializeChanges(depth),
            EvaluationStmt::ForEach {
                iteration: EvaluationIteration::ComponentObjects,
                body: object_body,
            },
            EvaluationStmt::Transport {
                model,
                root,
                edges: TransportEdges::Internal,
                retain: RetainedOwners::Always,
                changed: Some(depth),
            },
        ];
        if let Some(target) = active {
            component_loop.push(EvaluationStmt::PropagateChanges {
                source: depth,
                target,
            });
        }
        component_loop.push(EvaluationStmt::BreakUnlessChanged {
            id: depth,
            require_internal: true,
        });
        component_body.push(EvaluationStmt::Loop(component_loop));
        let outgoing = EvaluationStmt::Transport {
            model,
            root,
            edges: TransportEdges::Outgoing,
            retain,
            changed: active,
        };
        if compact {
            // Materialized transport must retain graph order for deferred work.
            component_body.push(EvaluationStmt::When {
                condition: EvaluationCondition::IncomingAbsent,
                body: vec![outgoing],
            });
        } else {
            component_body.push(outgoing);
        }
        block.push(EvaluationStmt::ForEach {
            iteration: EvaluationIteration::Components,
            body: component_body,
        });
        if self.baselines.contains_key(&root) {
            block.push(EvaluationStmt::SaveFrontier { model, root });
        }
        vec![EvaluationStmt::Block(block)]
    }
}

pub fn plan_evaluation(
    modules: &[RamFunction],
    schedule: &RuleSchedule,
    preparations: &[IndexPreparation],
    model_preparations: &BTreeMap<TypeId, NativePreparation>,
    native_indices: &[NativeIndexPreparation],
    selection: &IndexSelection,
    signature: &Signature,
    compact: &CompactPlan,
) -> EvaluationPlan {
    let all_indices: BTreeSet<_> = preparations
        .iter()
        .flat_map(|plan| plan.indices.iter().cloned())
        .collect();
    let old_indices: BTreeSet<_> = all_indices
        .iter()
        .filter(|(_, index)| index.age == IndexAge::Old)
        .cloned()
        .collect();
    let inputs: BTreeMap<_, _> = all_indices
        .iter()
        .map(|(rel, _)| source_relation(rel))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(i, key)| (key, i))
        .collect();
    let indices: BTreeMap<_, _> = all_indices
        .into_iter()
        .map(|(rel, index)| input_key(rel, index))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .enumerate()
        .map(|(i, key)| (key, i))
        .collect();
    let mut histories = BTreeMap::new();
    let strata: Vec<_> = schedule
        .strata
        .iter()
        .zip(preparations)
        .map(|(stratum, preparation)| {
            let stratum_inputs: BTreeSet<_> = preparation
                .indices
                .iter()
                .map(|(rel, _)| source_relation(rel))
                .collect();
            let diagonal_inputs = stratum_inputs
                .iter()
                .filter(|rel| diagonal_input(stratum, rel, modules, selection))
                .cloned()
                .collect();
            let mut stable_fields = BTreeMap::new();
            for (rel, index) in &preparation.indices {
                let source = source_relation(rel);
                let primary = InputStorage::Relation(inputs[&source]);
                let derived = if let Some(id) = native_index(native_indices, rel, index) {
                    Some(InputStorage::Native(id))
                } else if !selection.is_primary(rel, index)
                    && old_indices.contains(&input_key(rel.clone(), index.clone()))
                {
                    Some(InputStorage::Index(
                        indices[&input_key(rel.clone(), index.clone())],
                    ))
                } else {
                    None
                };
                if stratum.stable_inputs.contains(&source) {
                    stable_fields.insert(primary, source.clone());
                    if let Some(storage) = derived {
                        stable_fields.insert(storage, rel.clone());
                    }
                }
                if let Some(model) = stratum.model {
                    let count = scope_prefix(&source, model, signature);
                    if count == 0 {
                        continue;
                    }
                    let owners: Vec<_> = signature
                        .type_(model)
                        .parents
                        .iter()
                        .copied()
                        .chain(std::iter::once(model))
                        .take(count)
                        .collect();
                    histories.insert(
                        (primary, count),
                        ScopedHistory {
                            storage: primary,
                            owners: owners.clone(),
                            arity: source.arity(signature).len() - count,
                        },
                    );
                    if let Some(storage) = derived {
                        histories.insert(
                            (storage, count),
                            ScopedHistory {
                                storage,
                                owners,
                                arity: rel.arity(signature).len()
                                    - scope_prefix(rel, model, signature),
                            },
                        );
                    }
                }
            }
            let inherited = inherited_plan(
                stratum,
                modules,
                preparation,
                &inputs,
                &indices,
                native_indices,
                selection,
                signature,
                compact,
            );
            let outputs: BTreeSet<_> = stratum
                .groups
                .iter()
                .flat_map(|&module| modules[module].interface.outputs.iter().cloned())
                .collect();
            let possible: BTreeSet<BTreeSet<usize>> = stratum
                .groups
                .iter()
                .flat_map(|&module| &modules[module].rules)
                .map(|routine| {
                    routine
                        .input_indices()
                        .iter()
                        .map(|(rel, _)| inputs[&source_relation(rel)])
                        .collect()
                })
                .collect();
            let possible_inputs = (!possible.iter().any(BTreeSet::is_empty)).then_some(possible);
            let output_conversions =
                output_conversions(&outputs, stratum.model, signature, compact);
            let calls = evaluation_calls(
                stratum,
                modules,
                &inputs,
                &indices,
                &old_indices,
                native_indices,
                selection,
                signature,
                compact,
            );
            StratumEvaluation {
                model: stratum.model,
                stable_inputs: stratum.stable_inputs.clone(),
                inputs: stratum_inputs,
                outputs,
                possible_inputs,
                output_conversions,
                calls,
                diagonal_inputs,
                stable_fields,
                inherited,
            }
        })
        .collect();
    let transport_baselines = model_preparations
        .iter()
        .filter_map(|(&model, plan)| {
            transport_baseline(model, plan, selection, signature, compact).map(|plan| (model, plan))
        })
        .collect();
    let body = ScheduleLowering {
        strata: &schedule.strata,
        plans: &strata,
        preparations,
        model_preparations,
        native_indices,
        baselines: &transport_baselines,
        signature,
        compact,
    }
    .lower(&schedule.body, None, 0, None, RetainedOwners::None);
    EvaluationPlan {
        models: model_preparations
            .keys()
            .copied()
            .enumerate()
            .map(|(i, model)| (model, i))
            .collect(),
        inputs,
        indices,
        old_indices,
        strata,
        transport_baselines,
        scoped_histories: histories.into_values().collect(),
        tracked_owners: schedule
            .strata
            .iter()
            .filter_map(|stratum| stratum.model)
            .flat_map(|model| {
                signature
                    .type_(model)
                    .parents
                    .iter()
                    .copied()
                    .chain(std::iter::once(model))
            })
            .collect(),
        body,
    }
}
