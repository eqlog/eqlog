use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::{MorphismMemberTypes, Signature, TypeId, TypeKind};
use crate::flat_eqlog::{iter_flat_rels, FlatInRel, FlatRel, IndexSelection, IndexSpec};
use crate::options::ModelMode;
use crate::ram::{
    CompactPlan, IndexPreparation, NativeIndexPreparation, NativePreparation, PropagationPlan,
};

#[derive(Clone)]
pub struct TransportRead {
    pub rel: FlatInRel,
    pub index: IndexSpec,
    pub parents: usize,
}

#[derive(Clone, Copy)]
enum MorphismIndexColumnKind {
    OuterParent(usize),
    Parent,
    Member(TypeId),
    Copy,
}

#[derive(Clone)]
pub enum TransportValue {
    Parent(usize),
    Domain,
    Codomain,
    Column(usize),
    Image(usize),
}

pub enum TransportSuffix {
    Copy,
    Mapped(Vec<Option<usize>>),
}

pub enum TransportWalk {
    Restrict {
        position: usize,
        source: TransportValue,
        body: Box<TransportWalk>,
    },
    ForEachSource {
        position: usize,
        body: Box<TransportWalk>,
    },
    ForEachImage {
        position: usize,
        body: Box<TransportWalk>,
    },
    Emit {
        target: Vec<TransportValue>,
        suffix: TransportSuffix,
    },
}

pub enum TransportApplication {
    Rows,
    SinglePrefix,
    NestedPrefix,
}

pub struct TransportMapDelta {
    pub map: usize,
    pub column: usize,
    pub subtract: bool,
}

pub struct TransportIndexPlan {
    pub arity: usize,
    pub prefix: usize,
    pub suffix: usize,
    pub owners: usize,
    pub maps: Vec<(usize, TransportRead)>,
    pub walk: TransportWalk,
    pub checkpoint: Option<TransportWalk>,
    pub map_deltas: Vec<TransportMapDelta>,
    pub application: TransportApplication,
}

pub struct TransportCheckpointPlan {
    pub rel: FlatInRel,
    pub maps: Vec<TransportRead>,
    pub suffix: usize,
}

pub struct TransportGraph {
    pub dom: TransportRead,
    pub cod: TransportRead,
    pub objects: TransportRead,
}

pub struct TransportModelPlan {
    pub parents: Vec<TypeId>,
    pub graph: TransportGraph,
    pub checkpoints: Vec<TransportCheckpointPlan>,
    pub frontier: bool,
    pub key_types: Vec<TypeId>,
}

pub enum TransportIteration {
    Components,
    Objects,
    Internal,
    Outgoing,
}

#[derive(Clone, Copy)]
pub enum TransportChanges {
    All,
    Component,
}

#[derive(Clone, Copy)]
pub enum TransportRetention {
    Outer,
    Component,
}

pub enum TransportInstruction {
    PrepareGraph,
    ComputeComponents,
    CompactGraph,
    PrepareFrontier,
    ReturnUnlessWork,
    InitializeChanges(TransportChanges),
    ForEach {
        iteration: TransportIteration,
        body: Vec<TransportInstruction>,
    },
    Loop(Vec<TransportInstruction>),
    RetainComponent,
    CallChild {
        model: TypeId,
    },
    SelectRelations,
    ContinueUnlessActive,
    InitializeInserted,
    CallMorphism {
        changes: TransportChanges,
        retain: TransportRetention,
    },
    MarkWorkChanged,
    AccumulateChanges,
    BreakUnlessCyclicChanged,
    FinishFrontier,
    ReturnChanged,
}

pub struct TransportFrontierPlan {
    pub prepare_maps: BTreeSet<(FlatInRel, IndexSpec)>,
}

pub struct ModelPropagation {
    pub relations: Vec<FlatInRel>,
    pub frontier: Option<TransportFrontierPlan>,
    pub graph_indices: BTreeSet<(FlatInRel, IndexSpec)>,
    pub body: Vec<TransportInstruction>,
}

struct PropagationKey {
    relations: BTreeSet<FlatRel>,
    models: BTreeSet<TypeId>,
    graph_indices: BTreeMap<TypeId, BTreeSet<(FlatInRel, IndexSpec)>>,
    map_indices: BTreeMap<(TypeId, FlatInRel), BTreeSet<(FlatInRel, IndexSpec)>>,
}

impl PropagationKey {
    fn new(plan: &PropagationPlan) -> Self {
        Self {
            relations: plan.relations.clone(),
            models: plan.models.clone(),
            graph_indices: plan.graph_indices.clone(),
            map_indices: plan.map_indices.clone(),
        }
    }

    fn matches(&self, plan: &PropagationPlan) -> bool {
        self.relations == plan.relations
            && self.models == plan.models
            && self.graph_indices == plan.graph_indices
            && self.map_indices == plan.map_indices
    }
}

pub struct TransportPropagation {
    key: Option<PropagationKey>,
    pub models: BTreeMap<TypeId, ModelPropagation>,
    pub order: Vec<TypeId>,
    pub roots: Vec<TypeId>,
    pub invalidated: Vec<FlatRel>,
}

#[derive(Default)]
pub struct TransportPlan {
    pub models: BTreeMap<TypeId, TransportModelPlan>,
    pub model_order: Vec<TypeId>,
    indices: BTreeMap<(FlatInRel, Vec<usize>, TypeId), TransportIndexPlan>,
    groups: Vec<TransportPropagation>,
    pub native_bodies: BTreeMap<(usize, usize), Vec<TransportInstruction>>,
    rewrite_scopes: BTreeMap<FlatRel, (BTreeSet<TypeId>, BTreeSet<TypeId>)>,
}

fn parent_prefix_len(rel: &FlatInRel, signature: &Signature) -> usize {
    match rel {
        FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => match rel {
            FlatRel::Pred(pred) => signature.pred(*pred).parents.len(),
            FlatRel::Func(func) => signature.func(*func).parents.len(),
            FlatRel::ModelMember(typ) => signature.type_(*typ).parents.len(),
        },
        FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => 0,
    }
}

fn column_kind(
    rel: FlatRel,
    model: TypeId,
    column: usize,
    signature: &Signature,
) -> MorphismIndexColumnKind {
    if column < signature.type_(model).parents.len() {
        return MorphismIndexColumnKind::OuterParent(column);
    }
    let typ = rel.arity(signature)[column];
    if column < parent_prefix_len(&FlatInRel::Rel(rel), signature) && typ == model {
        return MorphismIndexColumnKind::Parent;
    }
    if rel.column_maps_under(signature, column, model) {
        return MorphismIndexColumnKind::Member(typ);
    }
    MorphismIndexColumnKind::Copy
}

fn read(
    rel: FlatInRel,
    order: Vec<usize>,
    selection: &IndexSelection,
    parents: usize,
) -> TransportRead {
    let index = selection.indices[&rel]
        .iter()
        .find(|index| index.order.as_ref() == order.as_slice())
        .unwrap_or_else(|| panic!("missing index with order {order:?}"))
        .clone();
    TransportRead {
        rel,
        index,
        parents,
    }
}

fn member_map(
    model: TypeId,
    member: TypeId,
    signature: &Signature,
    selection: &IndexSelection,
) -> TransportRead {
    let morphism_type = signature.ids_for_model_type(model).unwrap().mor;
    let app = signature
        .mor_app_func(MorphismMemberTypes {
            morphism_type,
            member_type: member,
        })
        .expect("mor_app_func should be defined for member types");
    let parents = signature.func(app).parents.len();
    read(
        FlatInRel::Rel(FlatRel::Func(app)),
        (0..parents + 3).collect(),
        selection,
        parents,
    )
}

fn walk(
    columns: &[MorphismIndexColumnKind],
    position: usize,
    prefix: usize,
    mut target: Vec<TransportValue>,
) -> TransportWalk {
    if position == prefix {
        let maps: Vec<_> = columns[position..]
            .iter()
            .enumerate()
            .map(|(offset, column)| match column {
                MorphismIndexColumnKind::Member(_) => Some(position + offset),
                MorphismIndexColumnKind::Copy => None,
                MorphismIndexColumnKind::OuterParent(_) | MorphismIndexColumnKind::Parent => {
                    unreachable!("parents belong to the prefix")
                }
            })
            .collect();
        let suffix = if maps.iter().any(Option::is_some) {
            TransportSuffix::Mapped(maps)
        } else {
            TransportSuffix::Copy
        };
        return TransportWalk::Emit { target, suffix };
    }
    match columns[position] {
        MorphismIndexColumnKind::OuterParent(parent) => {
            target.push(TransportValue::Parent(parent));
            TransportWalk::Restrict {
                position,
                source: TransportValue::Parent(parent),
                body: Box::new(walk(columns, position + 1, prefix, target)),
            }
        }
        MorphismIndexColumnKind::Parent => {
            target.push(TransportValue::Codomain);
            TransportWalk::Restrict {
                position,
                source: TransportValue::Domain,
                body: Box::new(walk(columns, position + 1, prefix, target)),
            }
        }
        MorphismIndexColumnKind::Member(_) => {
            target.push(TransportValue::Image(position));
            TransportWalk::ForEachSource {
                position,
                body: Box::new(TransportWalk::ForEachImage {
                    position,
                    body: Box::new(walk(columns, position + 1, prefix, target)),
                }),
            }
        }
        MorphismIndexColumnKind::Copy => {
            target.push(TransportValue::Column(position));
            TransportWalk::ForEachSource {
                position,
                body: Box::new(walk(columns, position + 1, prefix, target)),
            }
        }
    }
}

fn index_plan(
    rel: FlatRel,
    index: &IndexSpec,
    model: TypeId,
    signature: &Signature,
    selection: &IndexSelection,
) -> TransportIndexPlan {
    let arity = rel.arity(signature).len();
    let columns: Vec<_> = index
        .order
        .iter()
        .map(|&column| column_kind(rel, model, column, signature))
        .collect();
    let prefix = columns
        .iter()
        .rposition(|column| match column {
            MorphismIndexColumnKind::OuterParent(_) | MorphismIndexColumnKind::Parent => true,
            MorphismIndexColumnKind::Member(_) | MorphismIndexColumnKind::Copy => false,
        })
        .expect("index over a parented relation should contain the parent")
        + 1;
    let owners = signature.type_(model).parents.len() + 1;
    let maps: Vec<_> = columns
        .iter()
        .enumerate()
        .filter_map(|(column, kind)| match kind {
            MorphismIndexColumnKind::Member(member) => {
                Some((column, member_map(model, *member, signature, selection)))
            }
            MorphismIndexColumnKind::OuterParent(_)
            | MorphismIndexColumnKind::Parent
            | MorphismIndexColumnKind::Copy => None,
        })
        .collect();
    let checkpoint = index
        .order
        .iter()
        .take(owners)
        .copied()
        .eq(0..owners)
        .then(|| {
            let target = (0..owners - 1)
                .map(TransportValue::Parent)
                .chain(std::iter::once(TransportValue::Codomain))
                .collect();
            walk(&columns, owners, prefix, target)
        });
    let map_deltas = maps
        .iter()
        .enumerate()
        .map(|(map, (column, _))| TransportMapDelta {
            map,
            column: *column,
            subtract: map + 1 < maps.len(),
        })
        .collect();
    TransportIndexPlan {
        arity,
        prefix,
        suffix: arity - prefix,
        owners,
        maps,
        walk: walk(&columns, 0, prefix, Vec::new()),
        checkpoint,
        map_deltas,
        application: if arity == prefix {
            TransportApplication::Rows
        } else if prefix == 1 {
            TransportApplication::SinglePrefix
        } else {
            TransportApplication::NestedPrefix
        },
    }
}

fn edge_body(
    changes: TransportChanges,
    retain: TransportRetention,
    work: bool,
) -> Vec<TransportInstruction> {
    let mut body = Vec::new();
    if work {
        body.extend([
            TransportInstruction::SelectRelations,
            TransportInstruction::ContinueUnlessActive,
            TransportInstruction::InitializeInserted,
        ]);
    }
    body.push(TransportInstruction::CallMorphism { changes, retain });
    if work {
        body.push(TransportInstruction::MarkWorkChanged);
    }
    body
}

fn driver(children: Vec<TypeId>, work: bool) -> Vec<TransportInstruction> {
    let mut body = vec![TransportInstruction::ComputeComponents];
    if work {
        body.insert(0, TransportInstruction::PrepareGraph);
        body.extend([
            TransportInstruction::CompactGraph,
            TransportInstruction::PrepareFrontier,
            TransportInstruction::ReturnUnlessWork,
        ]);
    }
    body.extend([
        TransportInstruction::InitializeChanges(TransportChanges::All),
        TransportInstruction::ForEach {
            iteration: TransportIteration::Components,
            body: vec![
                TransportInstruction::RetainComponent,
                TransportInstruction::Loop(vec![
                    TransportInstruction::InitializeChanges(TransportChanges::Component),
                    TransportInstruction::ForEach {
                        iteration: TransportIteration::Objects,
                        body: children
                            .into_iter()
                            .map(|model| TransportInstruction::CallChild { model })
                            .collect(),
                    },
                    TransportInstruction::ForEach {
                        iteration: TransportIteration::Internal,
                        body: edge_body(
                            TransportChanges::Component,
                            TransportRetention::Component,
                            work,
                        ),
                    },
                    TransportInstruction::AccumulateChanges,
                    TransportInstruction::BreakUnlessCyclicChanged,
                ]),
                TransportInstruction::ForEach {
                    iteration: TransportIteration::Outgoing,
                    body: edge_body(TransportChanges::All, TransportRetention::Outer, work),
                },
            ],
        },
    ]);
    if work {
        body.push(TransportInstruction::FinishFrontier);
    }
    body.push(TransportInstruction::ReturnChanged);
    body
}

impl TransportPlan {
    pub fn new(
        signature: &Signature,
        selection: &IndexSelection,
        mode: ModelMode,
        compact: &CompactPlan,
        preparations: &[IndexPreparation],
        model_preparations: &BTreeMap<TypeId, NativePreparation>,
        native: &[NativeIndexPreparation],
    ) -> Self {
        let mut result = Self::default();
        match mode {
            ModelMode::Desugared => return result,
            ModelMode::Native => {}
        }
        result.model_order = signature
            .iter_model_decls()
            .map(|(_, ids)| ids.type_)
            .collect();
        for &model in &result.model_order {
            let ids = signature.ids_for_model_type(model).unwrap();
            let parents = signature.type_(model).parents.clone();
            let n = parents.len();
            let mut dom_order: Vec<_> = (0..n).collect();
            dom_order.extend([n + 1, n]);
            let graph = TransportGraph {
                dom: read(
                    FlatInRel::Rel(FlatRel::Func(ids.dom)),
                    dom_order,
                    selection,
                    n,
                ),
                cod: read(
                    FlatInRel::Rel(FlatRel::Func(ids.cod)),
                    (0..n + 2).collect(),
                    selection,
                    n,
                ),
                objects: read(
                    if n == 0 {
                        FlatInRel::TypeSet(model)
                    } else {
                        FlatInRel::Rel(FlatRel::ModelMember(model))
                    },
                    (0..n + 1).collect(),
                    selection,
                    n,
                ),
            };
            let mut checkpoints = Vec::new();
            for (input, index) in selection.current_indices() {
                if !compact.shared_indices(input) || !selection.is_primary(input, index) {
                    continue;
                }
                let rel = match input {
                    FlatInRel::Rel(rel) => *rel,
                    FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::TypeSet(_)
                    | FlatInRel::Equality(_) => continue,
                };
                let Some(owner) = rel.parent_model_type(signature) else {
                    continue;
                };
                if owner != model && !signature.type_(owner).parents.contains(&model) {
                    continue;
                }
                let plan = index_plan(rel, index, model, signature, selection);
                if plan.checkpoint.is_some() {
                    checkpoints.push(TransportCheckpointPlan {
                        rel: input.clone(),
                        maps: plan.maps.iter().map(|(_, read)| read.clone()).collect(),
                        suffix: rel.arity(signature).len() - n - 1,
                    });
                }
                result
                    .indices
                    .insert((input.clone(), index.order.to_vec(), model), plan);
            }
            let frontier = !signature
                .iter_model_decls()
                .any(|(_, ids)| signature.type_(ids.type_).parents.last() == Some(&model));
            let key_types = parents
                .iter()
                .copied()
                .chain(
                    checkpoints
                        .first()
                        .into_iter()
                        .flat_map(|_| [ids.mor, model, model]),
                )
                .collect();
            result.models.insert(
                model,
                TransportModelPlan {
                    parents,
                    graph,
                    checkpoints,
                    frontier,
                    key_types,
                },
            );
        }
        for (id, plan) in native.iter().enumerate() {
            let rel = match plan.rel {
                FlatInRel::Rel(rel) => rel,
                FlatInRel::RelWithDiagonals { .. }
                | FlatInRel::TypeSet(_)
                | FlatInRel::Equality(_) => unreachable!("native transport uses full relations"),
            };
            for (level, &model) in plan.models.iter().enumerate() {
                result
                    .indices
                    .entry((plan.rel.clone(), plan.index.order.to_vec(), model))
                    .or_insert_with(|| index_plan(rel, &plan.index, model, signature, selection));
                result.native_bodies.insert(
                    (id, level),
                    driver(
                        plan.models.get(level + 1).copied().into_iter().collect(),
                        false,
                    ),
                );
            }
        }
        result.add_group(None, signature, selection, compact);
        for preparation in preparations {
            result.add_group(
                Some(&preparation.native.propagation),
                signature,
                selection,
                compact,
            );
            if let Some(stable) = &preparation.stable {
                result.add_group(Some(&stable.propagation), signature, selection, compact);
            }
        }
        for preparation in model_preparations.values() {
            result.add_group(
                Some(&preparation.propagation),
                signature,
                selection,
                compact,
            );
        }
        for rel in iter_flat_rels(signature) {
            let index = selection.current_primary(&FlatInRel::Rel(rel));
            if index.order.first() != Some(&0) {
                continue;
            }
            let arity = rel.arity(signature);
            let Some(&owner) = arity.first() else {
                continue;
            };
            match signature.type_(owner).kind {
                TypeKind::Model => {}
                TypeKind::Plain | TypeKind::Enum | TypeKind::Mor(_) => continue,
            }
            if !signature.type_(owner).parents.is_empty() {
                continue;
            }
            let mut members = BTreeSet::new();
            let mut unrestricted = BTreeSet::from([owner]);
            for (column, &typ) in arity.iter().enumerate().skip(1) {
                if rel.column_maps_under(signature, column, owner) {
                    members.insert(typ);
                } else {
                    unrestricted.insert(typ);
                }
            }
            if !members.is_empty() {
                result.rewrite_scopes.insert(rel, (members, unrestricted));
            }
        }
        result
    }

    fn add_group(
        &mut self,
        plan: Option<&PropagationPlan>,
        signature: &Signature,
        selection: &IndexSelection,
        compact: &CompactPlan,
    ) {
        if self.groups.iter().any(|group| match (&group.key, plan) {
            (None, None) => true,
            (Some(key), Some(plan)) => key.matches(plan),
            (None, Some(_)) | (Some(_), None) => false,
        }) {
            return;
        }
        let order: Vec<_> = self
            .model_order
            .iter()
            .copied()
            .filter(|model| plan.is_none_or(|plan| plan.models.contains(model)))
            .collect();
        let roots = order
            .iter()
            .copied()
            .filter(|&model| signature.type_(model).parents.is_empty())
            .collect();
        let invalidated = iter_flat_rels(signature)
            .filter(|rel| {
                compact.shared_indices(&FlatInRel::Rel(*rel))
                    && plan.is_none_or(|plan| plan.relations.contains(rel))
            })
            .collect();
        let mut models = BTreeMap::new();
        for &model in &order {
            let relations: Vec<_> = selection
                .indices
                .keys()
                .filter(|input| compact.shared_indices(input))
                .filter(|input| match input {
                    FlatInRel::Rel(rel) => {
                        plan.is_none_or(|plan| plan.relations.contains(rel))
                            && rel.parent_model_type(signature).is_some_and(|owner| {
                                owner == model || signature.type_(owner).parents.contains(&model)
                            })
                    }
                    FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::TypeSet(_)
                    | FlatInRel::Equality(_) => false,
                })
                .cloned()
                .collect();
            let model_plan = &self.models[&model];
            let frontier = (model_plan.frontier
                && relations.iter().all(|rel| {
                    model_plan
                        .checkpoints
                        .iter()
                        .any(|checkpoint| checkpoint.rel == *rel)
                }))
            .then(|| TransportFrontierPlan {
                prepare_maps: plan
                    .into_iter()
                    .flat_map(|plan| {
                        relations
                            .iter()
                            .flat_map(|rel| plan.map_indices.get(&(model, rel.clone())))
                            .flatten()
                    })
                    .cloned()
                    .collect(),
            });
            let children = self
                .model_order
                .iter()
                .copied()
                .filter(|&child| {
                    signature.type_(child).parents.last() == Some(&model)
                        && plan.is_none_or(|plan| plan.models.contains(&child))
                })
                .collect();
            models.insert(
                model,
                ModelPropagation {
                    relations,
                    frontier,
                    graph_indices: plan
                        .and_then(|plan| plan.graph_indices.get(&model))
                        .cloned()
                        .unwrap_or_default(),
                    body: driver(children, true),
                },
            );
        }
        self.groups.push(TransportPropagation {
            key: plan.map(PropagationKey::new),
            models,
            order,
            roots,
            invalidated,
        });
    }

    pub fn index(&self, rel: &FlatInRel, index: &IndexSpec, model: TypeId) -> &TransportIndexPlan {
        &self.indices[&(rel.clone(), index.order.to_vec(), model)]
    }

    pub fn group(&self, plan: Option<&PropagationPlan>) -> &TransportPropagation {
        self.groups
            .iter()
            .find(|group| match (&group.key, plan) {
                (None, None) => true,
                (Some(key), Some(plan)) => key.matches(plan),
                (None, Some(_)) | (Some(_), None) => false,
            })
            .expect("transport dependency group has a RAM plan")
    }

    pub fn rewrite_scopes(&self, rel: FlatRel) -> Option<&(BTreeSet<TypeId>, BTreeSet<TypeId>)> {
        self.rewrite_scopes.get(&rel)
    }
}
