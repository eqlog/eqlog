mod eligibility;
mod keys;

use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::{Signature, TypeId, TypeKind};
use crate::flat_eqlog::{
    iter_flat_rels, FlatInRel, FlatRel, IndexSelection, IndexSpec, RuleSchedule,
};
use crate::options::ModelMode;
use crate::ram::{NativeIndexPreparation, RamFunction};

pub enum CompactRejection {
    NativeRequired,
    NotModel(TypeId),
    EnclosingCoordinates(TypeId),
    UnsupportedMember { model: TypeId, member: TypeId },
    NoMembers(TypeId),
    ForeignColumn { rel: FlatRel, column: usize },
    OutsideOwner { rel: FlatRel, model: TypeId },
    IncompleteIndex(FlatRel),
    NonleadingIndex(FlatRel),
    DiagonalIndex(FlatRel),
    RuleScope { name: String, model: TypeId },
    ExecutionScope(String),
    ReadScope(String),
    WriteScope(String),
    InputIndex(String),
}

#[derive(Clone, Copy)]
pub enum CompactView {
    Owned(TypeId),
    Membership(TypeId),
    Morphism { model: TypeId, member: TypeId },
}

pub struct CompactRelationLayout {
    pub rel: FlatRel,
    pub relation: usize,
    pub member_types: Vec<Option<usize>>,
    pub slots: Vec<(Vec<usize>, usize)>,
}

impl CompactRelationLayout {
    pub fn slot(&self, order: &[usize]) -> usize {
        self.slots
            .iter()
            .find_map(|(candidate, slot)| (candidate == order).then_some(*slot))
            .expect("selected compact permutation has a storage slot")
    }

    pub fn signature_slot(&self) -> usize {
        self.slot(&(0..self.member_types.len()).collect::<Vec<_>>())
    }
}

pub struct CompactModelPlan {
    pub layouts: Vec<CompactRelationLayout>,
    pub keys: Vec<(FlatRel, usize)>,
    pub rejection: Option<CompactRejection>,
    pub owner_leading: bool,
}

pub struct CompactPlan {
    member_types: BTreeSet<TypeId>,
    model_members: BTreeMap<TypeId, Vec<TypeId>>,
    policy_models: Vec<TypeId>,
    models: BTreeMap<TypeId, CompactModelPlan>,
    owners: BTreeMap<FlatRel, TypeId>,
    shared_relations: BTreeSet<FlatRel>,
    views: BTreeMap<FlatRel, CompactView>,
    inherited_slots: BTreeMap<(TypeId, FlatInRel, Vec<usize>), usize>,
    member_columns: BTreeMap<(FlatRel, usize), TypeId>,
}

fn supports_member(signature: &Signature, mode: ModelMode, typ: TypeId) -> bool {
    match mode {
        ModelMode::Native => match signature.type_(typ).kind {
            TypeKind::Plain => signature.type_(typ).parents.len() == 1,
            TypeKind::Enum | TypeKind::Model | TypeKind::Mor(_) => false,
        },
        ModelMode::Desugared => false,
    }
}

impl CompactPlan {
    pub fn new(
        modules: &[RamFunction],
        schedule: &RuleSchedule,
        selection: &IndexSelection,
        signature: &Signature,
        mode: ModelMode,
        native_indices: &[NativeIndexPreparation],
    ) -> Self {
        let member_types: BTreeSet<_> = signature
            .iter_types()
            .filter(|&typ| supports_member(signature, mode, typ))
            .collect();
        let model_members: BTreeMap<_, Vec<_>> = signature
            .iter_model_decls()
            .map(|(_, ids)| {
                let members = member_types
                    .iter()
                    .copied()
                    .filter(|&typ| signature.type_(typ).parents.as_slice() == [ids.type_])
                    .collect();
                (ids.type_, members)
            })
            .collect();
        let supported_models: BTreeSet<_> = model_members
            .iter()
            .filter(|(model, members)| {
                signature.type_(**model).parents.is_empty() && !members.is_empty()
            })
            .map(|(&model, _)| model)
            .collect();
        let policy_models = signature
            .iter_model_decls()
            .map(|(_, ids)| ids.type_)
            .filter(|model| !model_members[model].is_empty())
            .collect();
        let owners: BTreeMap<_, _> = iter_flat_rels(signature)
            .filter_map(|rel| match rel {
                FlatRel::Pred(_) | FlatRel::Func(_) => rel
                    .parent_model_type(signature)
                    .filter(|model| supported_models.contains(model))
                    .map(|model| (rel, model)),
                FlatRel::ModelMember(_) => None,
            })
            .collect();
        let shared_relations = iter_flat_rels(signature)
            .filter(|rel| match mode {
                ModelMode::Native => {
                    !rel.is_model_membership_relation()
                        && rel.parent_model_type(signature).is_some()
                }
                ModelMode::Desugared => false,
            })
            .collect();
        let mut models = BTreeMap::new();
        let mut inherited_slots = BTreeMap::new();
        let mut member_columns = BTreeMap::new();
        for model in supported_models {
            let members = &model_members[&model];
            let layouts = layouts(model, members, &owners, selection, signature);
            let owner_leading = layouts.iter().all(|layout| {
                selection
                    .current_primary(&FlatInRel::Rel(layout.rel))
                    .order
                    .first()
                    == Some(&0)
            }) && native_indices.iter().all(|plan| {
                let owner = match &plan.rel {
                    FlatInRel::Rel(rel) => owners.get(rel).copied(),
                    FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::TypeSet(_)
                    | FlatInRel::Equality(_) => None,
                };
                owner != Some(model) || plan.index.order.first() == Some(&0)
            });
            for layout in &layouts {
                for (column, member) in layout.member_types.iter().enumerate() {
                    if let Some(member) = member {
                        member_columns.insert((layout.rel, column + 1), members[*member]);
                    }
                }
                for (order, slot) in &layout.slots {
                    let mut permutation = order.clone();
                    permutation.sort_unstable();
                    if !permutation.into_iter().eq(0..layout.member_types.len()) {
                        continue;
                    }
                    let order = std::iter::once(0)
                        .chain(order.iter().map(|column| column + 1))
                        .collect();
                    inherited_slots.insert((model, FlatInRel::Rel(layout.rel), order), *slot);
                }
            }
            models.insert(
                model,
                CompactModelPlan {
                    layouts,
                    keys: keys::invariant_keys(model, modules, signature, mode),
                    rejection: eligibility::rejection_reason(
                        model, modules, schedule, selection, signature, mode,
                    ),
                    owner_leading,
                },
            );
        }
        let views = iter_flat_rels(signature)
            .filter_map(|rel| {
                let view = match rel {
                    FlatRel::ModelMember(member) => member_types
                        .contains(&member)
                        .then_some(CompactView::Membership(member)),
                    FlatRel::Func(func) => {
                        if let Some(types) = signature.types_for_mor_app_func(func) {
                            let model = types.model_type(signature);
                            (member_types.contains(&types.member_type)
                                && models.contains_key(&model))
                            .then_some(CompactView::Morphism {
                                model,
                                member: types.member_type,
                            })
                        } else {
                            owners.get(&rel).copied().map(CompactView::Owned)
                        }
                    }
                    FlatRel::Pred(_) => owners.get(&rel).copied().map(CompactView::Owned),
                };
                view.map(|view| (rel, view))
            })
            .collect();
        Self {
            member_types,
            model_members,
            policy_models,
            models,
            owners,
            shared_relations,
            views,
            inherited_slots,
            member_columns,
        }
    }

    pub fn supports_member(&self, typ: TypeId) -> bool {
        self.member_types.contains(&typ)
    }

    pub fn supports_model(&self, model: TypeId) -> bool {
        self.models.contains_key(&model)
    }

    pub fn members(&self, model: TypeId) -> &[TypeId] {
        self.model_members.get(&model).map_or(&[], Vec::as_slice)
    }

    pub fn policy_models(&self) -> &[TypeId] {
        &self.policy_models
    }

    pub fn member_column(&self, rel: FlatRel, column: usize) -> Option<TypeId> {
        self.member_columns.get(&(rel, column)).copied()
    }

    pub fn model(&self, model: TypeId) -> Option<&CompactModelPlan> {
        self.models.get(&model)
    }

    pub fn owner(&self, rel: &FlatInRel) -> Option<TypeId> {
        match rel {
            FlatInRel::Rel(rel) => self.owners.get(rel).copied(),
            FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
                None
            }
        }
    }

    pub fn shared_indices(&self, rel: &FlatInRel) -> bool {
        match rel {
            FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => {
                self.shared_relations.contains(rel)
            }
            FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => false,
        }
    }

    pub fn view(&self, rel: FlatRel) -> Option<CompactView> {
        self.views.get(&rel).copied()
    }

    pub fn inherited_slot(
        &self,
        rel: &FlatInRel,
        index: &IndexSpec,
        model: TypeId,
    ) -> Option<usize> {
        self.inherited_slots
            .get(&(model, rel.clone(), index.order.to_vec()))
            .copied()
    }
}

fn layouts(
    model: TypeId,
    members: &[TypeId],
    owners: &BTreeMap<FlatRel, TypeId>,
    selection: &IndexSelection,
    signature: &Signature,
) -> Vec<CompactRelationLayout> {
    let mut next_slot = 0;
    iter_flat_rels(signature)
        .filter(|rel| owners.get(rel) == Some(&model))
        .enumerate()
        .map(|(relation, rel)| {
            let arity = rel.arity(signature);
            let member_types = arity[1..]
                .iter()
                .enumerate()
                .map(|(column, typ)| {
                    rel.column_maps_under(signature, column + 1, model)
                        .then(|| members.iter().position(|member| member == typ))
                        .flatten()
                })
                .collect();
            let mut orders = BTreeSet::from([(0..arity.len() - 1).collect::<Vec<_>>()]);
            for index in &selection.indices[&FlatInRel::Rel(rel)] {
                assert_eq!(index.order.len(), arity.len());
                orders.insert(
                    index
                        .order
                        .iter()
                        .copied()
                        .filter(|&column| column != 0)
                        .map(|column| column - 1)
                        .collect(),
                );
            }
            let slots = orders
                .into_iter()
                .map(|order| {
                    let slot = next_slot;
                    next_slot += 1;
                    (order, slot)
                })
                .collect();
            CompactRelationLayout {
                rel,
                relation,
                member_types,
                slots,
            }
        })
        .collect()
}
