use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::{Signature, TypeId};
use crate::flat_eqlog::{
    iter_flat_rels, morphism_preservation_rules, FlatInRel, FlatOutRel, FlatRuleGroup, RuleScope,
};
use crate::options::{ModelMode, SchedulingMode};

pub enum RuleSchedule {
    Simultaneous,
    Stratified(StratifiedPlan),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StratumId(pub usize);

pub struct StratifiedPlan {
    pub strata: Vec<Stratum>,
    pub body: Schedule,
}

pub enum Schedule {
    Sequence(Vec<Schedule>),
    Rules(StratumId),
    Saturate(Box<Schedule>),
    ModelComponents {
        models: Vec<TypeId>,
        body: Box<Schedule>,
    },
}

pub struct Stratum {
    pub groups: Vec<usize>,
    pub model: Option<TypeId>,
}

pub fn schedule_rule_groups(
    groups: &mut [FlatRuleGroup],
    signature: &Signature,
    model_mode: ModelMode,
    scheduling_mode: SchedulingMode,
) -> RuleSchedule {
    let scoped = scheduling_mode == SchedulingMode::Stratified && model_mode == ModelMode::Native;
    if !scoped {
        for rule in groups.iter_mut().flat_map(|group| &mut group.rules) {
            rule.scope = RuleScope::Global;
        }
    }
    match scheduling_mode {
        SchedulingMode::Simultaneous => RuleSchedule::Simultaneous,
        SchedulingMode::Stratified => {
            RuleSchedule::Stratified(strata(groups, signature, model_mode))
        }
    }
}

fn resource(rel: &FlatInRel) -> FlatInRel {
    match rel {
        FlatInRel::RelWithDiagonals { rel, .. } => FlatInRel::Rel(*rel),
        FlatInRel::Rel(_) | FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => rel.clone(),
    }
}

fn strata(
    groups: &mut [FlatRuleGroup],
    signature: &Signature,
    model_mode: ModelMode,
) -> StratifiedPlan {
    let resources: Vec<_> = iter_flat_rels(signature)
        .map(FlatInRel::Rel)
        .chain(signature.iter_types().map(FlatInRel::TypeSet))
        .collect();
    let reads: Vec<BTreeSet<_>> = groups
        .iter()
        .map(|group| {
            group
                .rules
                .iter()
                .flat_map(|rule| rule.premise.iter().map(|stmt| resource(&stmt.rel)))
                .collect()
        })
        .collect();
    let mut propagation: BTreeMap<FlatInRel, BTreeSet<FlatInRel>> = BTreeMap::new();
    match model_mode {
        ModelMode::Desugared => {}
        ModelMode::Native => {
            // Native transport has the same dependencies as its materialized
            // preservation rules, even though it does not appear in the RAM.
            for rule in morphism_preservation_rules(signature) {
                for input in rule.premise {
                    for output in &rule.conclusion {
                        match output.rel {
                            FlatOutRel::Rel(rel) => {
                                propagation
                                    .entry(resource(&input.rel))
                                    .or_default()
                                    .insert(FlatInRel::Rel(rel));
                            }
                            FlatOutRel::Equality(_) | FlatOutRel::FuncDomain(_) => {
                                unreachable!("preservation only transports tuples")
                            }
                        }
                    }
                }
            }
        }
    }
    let mut edges = vec![Vec::new(); groups.len()];
    for (source, group) in groups.iter().enumerate() {
        let mut writes = BTreeSet::new();
        for output in group.rules.iter().flat_map(|rule| &rule.conclusion) {
            match output.rel {
                FlatOutRel::Rel(rel) => {
                    writes.insert(FlatInRel::Rel(rel));
                }
                FlatOutRel::Equality(typ) => {
                    writes.extend(
                        resources
                            .iter()
                            .filter(|rel| rel.arity(signature).contains(&typ))
                            .cloned(),
                    );
                    writes.insert(FlatInRel::Equality(typ));
                }
                // Allocation feeds the enclosing loop after immediate closure.
                FlatOutRel::FuncDomain(_) => {}
            }
        }
        let mut pending: Vec<_> = writes.iter().cloned().collect();
        while let Some(input) = pending.pop() {
            if let Some(outputs) = propagation.get(&input) {
                for output in outputs {
                    if writes.insert(output.clone()) {
                        pending.push(output.clone());
                    }
                }
            }
        }
        for (target, reads) in reads.iter().enumerate() {
            if !writes.is_disjoint(reads) {
                edges[source].push(target);
            }
        }
    }
    let strata: Vec<_> = components(&edges)
        .into_iter()
        .map(|members| {
            let model = groups[members[0]]
                .rules
                .first()
                .and_then(|rule| rule.scope.model());
            let model = model.filter(|model| {
                members.iter().all(|&i| {
                    groups[i]
                        .rules
                        .iter()
                        .all(|rule| rule.scope.model() == Some(*model))
                })
            });
            if model.is_none() {
                for &i in &members {
                    for rule in &mut groups[i].rules {
                        rule.scope = RuleScope::Global;
                    }
                }
            }
            Stratum {
                groups: members,
                model,
            }
        })
        .collect();
    let mut plan = StratifiedPlan {
        strata,
        body: Schedule::Sequence(Vec::new()),
    };
    nest_model_components(&mut plan, groups, &edges, signature);
    plan
}

fn nest_model_components(
    plan: &mut StratifiedPlan,
    groups: &mut [FlatRuleGroup],
    edges: &[Vec<usize>],
    signature: &Signature,
) {
    let mut stratum_of = vec![0; groups.len()];
    for (s, stratum) in plan.strata.iter().enumerate() {
        for &group in &stratum.groups {
            stratum_of[group] = s;
        }
    }
    loop {
        let mut units = BTreeMap::new();
        for (s, stratum) in plan.strata.iter().enumerate() {
            let key = (stratum.model, if stratum.model.is_some() { 0 } else { s });
            units.entry(key).or_insert_with(Vec::new).push(s);
        }
        let units: Vec<Vec<usize>> = units.into_values().collect();
        let mut unit_of = vec![0; plan.strata.len()];
        for (u, strata) in units.iter().enumerate() {
            for &s in strata {
                unit_of[s] = u;
            }
        }
        let mut unit_edges = vec![Vec::new(); units.len()];
        for (source, targets) in edges.iter().enumerate() {
            let source = unit_of[stratum_of[source]];
            for &target in targets {
                let target = unit_of[stratum_of[target]];
                if source != target {
                    unit_edges[source].push(target);
                }
            }
        }
        let components = components(&unit_edges);
        let mut retry = false;
        for component in &components {
            if component.len() == 1 {
                continue;
            }
            // Contracting all rules for a model must not hide ambient feedback.
            for &unit in component {
                for &s in &units[unit] {
                    if plan.strata[s].model.take().is_some() {
                        retry = true;
                        for &group in &plan.strata[s].groups {
                            for rule in &mut groups[group].rules {
                                rule.scope = RuleScope::Global;
                            }
                        }
                    }
                }
            }
        }
        if retry {
            continue;
        }
        let leaf = |s: usize| {
            let members = &plan.strata[s].groups;
            let node = Schedule::Rules(StratumId(s));
            if members.len() > 1 || edges[members[0]].contains(&members[0]) {
                Schedule::Saturate(Box::new(node))
            } else {
                node
            }
        };
        plan.body = Schedule::Sequence(
            components
                .into_iter()
                .map(|component| {
                    assert_eq!(component.len(), 1, "uncontracted rule strata form a DAG");
                    let members = &units[component[0]];
                    match plan.strata[members[0]].model {
                        Some(model) => Schedule::ModelComponents {
                            models: signature
                                .type_(model)
                                .parents
                                .iter()
                                .copied()
                                .chain(std::iter::once(model))
                                .collect(),
                            body: Box::new(Schedule::Sequence(
                                members.iter().map(|&s| leaf(s)).collect(),
                            )),
                        },
                        None => {
                            assert_eq!(members.len(), 1);
                            leaf(members[0])
                        }
                    }
                })
                .collect(),
        );
        return;
    }
}

fn components(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let mut incoming = vec![Vec::new(); edges.len()];
    for (source, targets) in edges.iter().enumerate() {
        for &target in targets {
            incoming[target].push(source);
        }
    }
    let mut visited = vec![false; edges.len()];
    let mut finished = Vec::new();
    for start in 0..edges.len() {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        let mut stack = vec![(start, 0)];
        while let Some((node, next)) = stack.last_mut() {
            if let Some(&target) = edges[*node].get(*next) {
                *next += 1;
                if !visited[target] {
                    visited[target] = true;
                    stack.push((target, 0));
                }
            } else {
                finished.push(*node);
                stack.pop();
            }
        }
    }
    visited.fill(false);
    let mut components = Vec::new();
    for start in finished.into_iter().rev() {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        let mut component = Vec::new();
        let mut stack = vec![start];
        while let Some(node) = stack.pop() {
            component.push(node);
            for &source in &incoming[node] {
                if !visited[source] {
                    visited[source] = true;
                    stack.push(source);
                }
            }
        }
        component.sort_unstable();
        components.push(component);
    }
    components
}
