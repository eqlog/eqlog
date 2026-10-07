use std::collections::{BTreeMap, BTreeSet};

use super::{IndexPreparation, NativeIndexPreparation, PropagationPlan, RamModule, RamStmt};
use crate::algebra::signature::{MorphismMemberTypes, Signature, TypeId};
use crate::flat_eqlog::{
    morphism_preservation_rules, FlatInRel, FlatOutRel, FlatRel, IndexAge, IndexSelection,
    IndexSpec, RuleSchedule, Schedule, Stratum,
};
use crate::options::ModelMode;

fn propagation_plan(
    inputs: &BTreeSet<(FlatInRel, IndexSpec)>,
    signature: &Signature,
    indices: &IndexSelection,
    mode: ModelMode,
) -> PropagationPlan {
    let mut plan = PropagationPlan::default();
    match mode {
        ModelMode::Desugared => return plan,
        ModelMode::Native => {}
    }
    let mut pending: Vec<_> = inputs.iter().map(|(rel, _)| rel.clone()).collect();
    let preservation = morphism_preservation_rules(signature);
    while let Some(input) = pending.pop() {
        let rel = match input {
            FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => rel,
            FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => continue,
        };
        if rel.is_model_membership_relation() {
            continue;
        }
        let Some(parent) = rel.parent_model_type(signature) else {
            continue;
        };
        if !plan.relations.insert(rel) {
            continue;
        }
        plan.models.insert(parent);
        plan.models
            .extend(signature.type_(parent).parents.iter().copied());
        // An inherited graph edge or application can itself depend on an outer
        // morphism, so preparation includes the transitive transport inputs.
        for rule in &preservation {
            let produces = rule.conclusion.iter().any(|output| match output.rel {
                FlatOutRel::Rel(output) => output == rel,
                FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {
                    unreachable!("preservation only transports tuples")
                }
            });
            if produces {
                pending.extend(rule.premise.iter().map(|stmt| stmt.rel.clone()));
            }
        }
    }
    for &model in &plan.models {
        let ids = signature.ids_for_model_type(model).unwrap();
        for &rel in &plan.relations {
            let parent = rel.parent_model_type(signature).unwrap();
            if parent != model && !signature.type_(parent).parents.contains(&model) {
                continue;
            }
            for (input, index) in
                support_indices(&FlatInRel::Rel(rel), &[model], signature, indices)
            {
                let is_graph = match &input {
                    FlatInRel::Rel(FlatRel::Func(func)) => *func == ids.dom || *func == ids.cod,
                    FlatInRel::Rel(FlatRel::ModelMember(_)) | FlatInRel::TypeSet(_) => true,
                    FlatInRel::Rel(FlatRel::Pred(_))
                    | FlatInRel::RelWithDiagonals { .. }
                    | FlatInRel::Equality(_) => {
                        unreachable!("transport inputs are graph operations or applications")
                    }
                };
                let target = if is_graph {
                    plan.graph_indices.entry(model).or_default()
                } else {
                    plan.map_indices
                        .entry((model, FlatInRel::Rel(rel)))
                        .or_default()
                };
                target.insert((input, index));
            }
        }
    }
    plan
}

fn support_indices(
    rel: &FlatInRel,
    models: &[TypeId],
    signature: &Signature,
    indices: &IndexSelection,
) -> BTreeSet<(FlatInRel, IndexSpec)> {
    let mut result = BTreeSet::new();
    let mut add = |rel: FlatInRel, order: Vec<usize>| {
        for age in [IndexAge::Old, IndexAge::New] {
            let index = indices.indices[&rel]
                .iter()
                .find(|index| index.age == age && index.order.as_ref() == order.as_slice())
                .expect("native graph queries must have selected their indices");
            result.insert((rel.clone(), index.clone()));
        }
    };
    let arity = rel.arity(signature);
    let parent_cols = match rel {
        FlatInRel::Rel(rel) => rel
            .parent_model_type(signature)
            .map_or(0, |model| signature.type_(model).parents.len() + 1),
        FlatInRel::RelWithDiagonals { .. } | FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => {
            unreachable!("transport plans use full member relations")
        }
    };
    for &model in models {
        let ids = signature.ids_for_model_type(model).unwrap();
        let parent_len = signature.type_(model).parents.len();
        let mut dom_order: Vec<_> = (0..parent_len).collect();
        dom_order.extend([parent_len + 1, parent_len]);
        add(FlatInRel::Rel(FlatRel::Func(ids.dom)), dom_order);
        add(
            FlatInRel::Rel(FlatRel::Func(ids.cod)),
            (0..parent_len + 2).collect(),
        );
        let objects = if parent_len == 0 {
            FlatInRel::TypeSet(model)
        } else {
            FlatInRel::Rel(FlatRel::ModelMember(model))
        };
        add(objects, (0..parent_len + 1).collect());
        for (column, &typ) in arity.iter().enumerate() {
            if column < parent_len
                || (column < parent_cols && typ == model)
                || !signature.type_(typ).parents.contains(&model)
            {
                continue;
            }
            let app = signature
                .mor_app_func(MorphismMemberTypes {
                    morphism_type: ids.mor,
                    member_type: typ,
                })
                .unwrap();
            let app_parent_len = signature.func(app).parents.len();
            add(
                FlatInRel::Rel(FlatRel::Func(app)),
                (0..app_parent_len + 3).collect(),
            );
        }
    }
    result
}

#[derive(Clone, Default)]
struct ModelGroups {
    groups: Vec<usize>,
    traversals: BTreeSet<TypeId>,
}

fn model_groups(
    schedule: &Schedule,
    strata: &[Stratum],
    nested: bool,
    models: &mut BTreeMap<TypeId, ModelGroups>,
) -> ModelGroups {
    match schedule {
        Schedule::Rules(id) => ModelGroups {
            groups: strata[id.0].groups.clone(),
            traversals: BTreeSet::new(),
        },
        Schedule::Sequence(children) => {
            let mut result = ModelGroups::default();
            for child in children {
                let child = model_groups(child, strata, nested, models);
                result.groups.extend(child.groups);
                result.traversals.extend(child.traversals);
            }
            result
        }
        Schedule::Saturate(body) => model_groups(body, strata, nested, models),
        Schedule::ModelComponents { model, body } => {
            let mut groups = model_groups(body, strata, true, models);
            groups.traversals.insert(*model);
            if !nested {
                assert!(models.insert(*model, groups.clone()).is_none());
            }
            groups
        }
    }
}

pub fn plan_index_preparation(
    modules: &[RamModule],
    schedule: &RuleSchedule,
    indices: &IndexSelection,
    signature: &Signature,
    mode: ModelMode,
) -> (
    Vec<IndexPreparation>,
    BTreeMap<TypeId, IndexPreparation>,
    Vec<NativeIndexPreparation>,
) {
    let groups: Vec<(Option<TypeId>, ModelGroups)> = match schedule {
        RuleSchedule::Simultaneous => vec![(
            None,
            ModelGroups {
                groups: (0..modules.len()).collect(),
                traversals: BTreeSet::new(),
            },
        )],
        RuleSchedule::Stratified(plan) => {
            let mut groups: Vec<_> = plan
                .strata
                .iter()
                .map(|stratum| {
                    (
                        None,
                        ModelGroups {
                            groups: stratum.groups.clone(),
                            traversals: BTreeSet::new(),
                        },
                    )
                })
                .collect();
            let mut models = BTreeMap::new();
            model_groups(&plan.body, &plan.strata, false, &mut models);
            groups.extend(
                models
                    .into_iter()
                    .map(|(model, groups)| (Some(model), groups)),
            );
            groups
        }
    };
    let mut native = Vec::new();
    let mut native_ids = BTreeMap::new();
    let mut preparations = Vec::new();
    let mut model_preparations = BTreeMap::new();
    for (model, ModelGroups { groups, traversals }) in groups {
        let mut inputs: BTreeSet<_> = groups
            .iter()
            .flat_map(|&i| modules[i].input_indices())
            .collect();
        if model.is_some() {
            for stmt in groups
                .iter()
                .flat_map(|&i| &modules[i].routines)
                .flat_map(|routine| &routine.stmts)
            {
                match stmt {
                    RamStmt::Insert(stmt) => match stmt.rel {
                        FlatOutRel::Rel(rel) => {
                            let rel = FlatInRel::Rel(rel);
                            for age in [IndexAge::Old, IndexAge::New] {
                                inputs.insert((rel.clone(), indices.primary(&rel, age).clone()));
                            }
                        }
                        FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {}
                    },
                    RamStmt::DefineSet(_) | RamStmt::Iter(_) | RamStmt::GuardInhabited(_) => {}
                }
            }
        }
        for &model in &traversals {
            let ids = signature.ids_for_model_type(model).unwrap();
            for func in [ids.dom, ids.cod] {
                let rel = FlatInRel::Rel(crate::flat_eqlog::FlatRel::Func(func));
                for age in [IndexAge::Old, IndexAge::New] {
                    inputs.insert((rel.clone(), indices.primary(&rel, age).clone()));
                }
            }
        }
        let mut required_native = BTreeSet::new();
        for (rel, index) in &inputs {
            match mode {
                ModelMode::Desugared => continue,
                ModelMode::Native => {}
            }
            if indices.is_primary(rel, index) {
                continue;
            }
            let relation = match rel {
                FlatInRel::Rel(rel) => rel,
                FlatInRel::RelWithDiagonals { .. }
                | FlatInRel::TypeSet(_)
                | FlatInRel::Equality(_) => continue,
            };
            if relation.is_model_membership_relation() {
                continue;
            }
            let Some(parent) = relation.parent_model_type(signature) else {
                continue;
            };
            let index = IndexSpec {
                age: IndexAge::Old,
                order: index.order.clone(),
            };
            let key = (rel.clone(), index.clone());
            let id = *native_ids.entry(key).or_insert_with(|| {
                let id = native.len();
                let mut models = signature.type_(parent).parents.clone();
                models.push(parent);
                let support_indices = support_indices(rel, &models, signature, indices);
                native.push(NativeIndexPreparation {
                    rel: rel.clone(),
                    index,
                    models,
                    support_indices,
                });
                id
            });
            required_native.insert(id);
        }
        let prepared_support = required_native
            .iter()
            .flat_map(|&id| native[id].support_indices.iter().cloned())
            .collect();
        let mut propagation = propagation_plan(&inputs, signature, indices, mode);
        for &model in &traversals {
            propagation.models.insert(model);
            propagation
                .models
                .extend(signature.type_(model).parents.iter().copied());
            let dom = signature.ids_for_model_type(model).unwrap().dom;
            propagation
                .graph_indices
                .entry(model)
                .or_default()
                .extend(support_indices(
                    &FlatInRel::Rel(crate::flat_eqlog::FlatRel::Func(dom)),
                    &[model],
                    signature,
                    indices,
                ));
        }
        let plan = IndexPreparation {
            indices: inputs,
            native_indices: required_native,
            support_indices: prepared_support,
            propagation,
            descendants: BTreeSet::new(),
        };
        match model {
            Some(model) => {
                model_preparations.insert(model, plan);
            }
            None => preparations.push(plan),
        }
    }
    match schedule {
        RuleSchedule::Simultaneous => {}
        RuleSchedule::Stratified(plan) => {
            for (stratum, preparation) in plan.strata.iter().zip(&mut preparations) {
                let Some(model) = stratum.model else {
                    continue;
                };
                let depth = signature.type_(model).parents.len() + 1;
                for (input, _) in &preparation.indices {
                    let rel = match input {
                        FlatInRel::Rel(rel) | FlatInRel::RelWithDiagonals { rel, .. } => rel,
                        FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => continue,
                    };
                    if rel.is_model_membership_relation() {
                        continue;
                    }
                    let Some(parent) = rel.parent_model_type(signature) else {
                        continue;
                    };
                    if signature.type_(parent).parents.contains(&model) {
                        let child = signature
                            .type_(parent)
                            .parents
                            .get(depth)
                            .copied()
                            .unwrap_or(parent);
                        preparation.descendants.insert(child);
                    }
                }
            }
        }
    }
    (preparations, model_preparations, native)
}
