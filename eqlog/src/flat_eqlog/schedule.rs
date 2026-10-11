use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::{Signature, TypeId};
use crate::flat_eqlog::{
    infer_rule_scopes, iter_flat_rels, morphism_preservation_rules, FlatInRel, FlatOutRel,
    FlatRuleGroup, RuleScope,
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
    // Children have no write-to-read dependencies; shared inputs and outputs are allowed.
    Independent(Vec<Schedule>),
    Rules(StratumId),
    Saturate(Box<Schedule>),
    ModelComponents { model: TypeId, body: Box<Schedule> },
}

pub struct Stratum {
    pub groups: Vec<usize>,
    pub model: Option<TypeId>,
    pub stable_inputs: BTreeSet<FlatInRel>,
}

struct Dependencies {
    reads: Vec<BTreeSet<FlatInRel>>,
    writes: Vec<BTreeSet<FlatInRel>>,
    edges: Vec<Vec<usize>>,
}

pub fn schedule_rule_groups(
    groups: &mut [FlatRuleGroup],
    signature: &Signature,
    model_mode: ModelMode,
    scheduling_mode: SchedulingMode,
) -> RuleSchedule {
    let scoped = scheduling_mode == SchedulingMode::Stratified && model_mode == ModelMode::Native;
    if scoped {
        infer_rule_scopes(groups, signature);
    } else {
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
    let mut effective_writes = Vec::new();
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
        effective_writes.push(writes);
    }
    let dependencies = Dependencies {
        reads,
        writes: effective_writes,
        edges,
    };
    for group in groups.iter_mut() {
        let model = group.rules.first().and_then(|rule| rule.scope.model());
        if group.rules.iter().any(|rule| rule.scope.model() != model) {
            for rule in &mut group.rules {
                rule.scope = RuleScope::Global;
            }
        }
    }
    let members: Vec<_> = (0..groups.len()).collect();
    loop {
        let mut strata = Vec::new();
        match schedule_scope(
            None,
            &members,
            groups,
            &dependencies,
            signature,
            &mut strata,
        ) {
            Ok(body) => return StratifiedPlan { strata, body },
            Err(fallback) => {
                // Ambient feedback cannot be closed with one owner bound.
                for group in fallback {
                    for rule in &mut groups[group].rules {
                        rule.scope = RuleScope::Global;
                    }
                }
            }
        }
    }
}

fn schedule_scope(
    scope: Option<TypeId>,
    members: &[usize],
    groups: &[FlatRuleGroup],
    dependencies: &Dependencies,
    signature: &Signature,
    strata: &mut Vec<Stratum>,
) -> Result<Schedule, Vec<usize>> {
    let edges = &dependencies.edges;
    let depth = scope.map_or(0, |model| signature.type_(model).parents.len() + 1);
    let mut units = BTreeMap::new();
    for &group in members {
        let model = groups[group]
            .rules
            .first()
            .and_then(|rule| rule.scope.model());
        let child = model.filter(|model| Some(*model) != scope).map(|model| {
            signature
                .type_(model)
                .parents
                .get(depth)
                .copied()
                .unwrap_or(model)
        });
        let key = (child, if child.is_some() { 0 } else { group });
        units.entry(key).or_insert_with(Vec::new).push(group);
    }
    let units: Vec<_> = units
        .into_iter()
        .map(|((model, _), groups)| (model, groups))
        .collect();
    let unit_of: BTreeMap<_, _> = units
        .iter()
        .enumerate()
        .flat_map(|(u, (_, groups))| groups.iter().map(move |&group| (group, u)))
        .collect();
    let mut unit_edges = vec![Vec::new(); units.len()];
    for &source in members {
        let source_unit = unit_of[&source];
        for target in &edges[source] {
            if let Some(&target_unit) = unit_of.get(target) {
                if source_unit != target_unit || units[source_unit].0.is_none() {
                    unit_edges[source_unit].push(target_unit);
                }
            }
        }
    }
    let components = components(&unit_edges);
    if scope.is_none() {
        let mut fallback = Vec::new();
        for component in components.iter().filter(|component| component.len() > 1) {
            for &unit in component {
                if units[unit].0.is_none() {
                    continue;
                }
                for &source in &units[unit].1 {
                    if edges[source].iter().any(|target| {
                        let target = unit_of[target];
                        target != unit && component.contains(&target)
                    }) {
                        fallback.push(source);
                    }
                }
            }
        }
        if !fallback.is_empty() {
            return Err(fallback);
        }
    }
    let mut bodies = Vec::new();
    for component in &components {
        let recursive = component.len() > 1 || unit_edges[component[0]].contains(&component[0]);
        let writes: BTreeSet<_> = component
            .iter()
            .flat_map(|&unit| &units[unit].1)
            .flat_map(|&group| dependencies.writes[group].iter().cloned())
            .collect();
        let traverses_models = component.iter().any(|&unit| units[unit].0.is_some());
        let mut children = Vec::new();
        let mut rules: Vec<usize> = Vec::new();
        for &unit in component {
            let (model, members) = &units[unit];
            match model {
                Some(model) => {
                    let body = schedule_scope(
                        Some(*model),
                        members,
                        groups,
                        dependencies,
                        signature,
                        strata,
                    )?;
                    children.push(Schedule::ModelComponents {
                        model: *model,
                        body: Box::new(body),
                    });
                }
                None => rules.extend(members),
            }
        }
        if !rules.is_empty() {
            rules.sort_unstable();
            let stable_inputs = rules
                .iter()
                .flat_map(|&group| dependencies.reads[group].iter())
                .filter(|rel| recursive && !writes.contains(*rel))
                .filter(|rel| {
                    // A traversal may expose inherited tuples even if no rule
                    // in this component writes their relation directly.
                    !traverses_models
                        || match rel {
                            FlatInRel::Rel(rel) => rel.parent_model_type(signature).is_none(),
                            FlatInRel::TypeSet(_) | FlatInRel::Equality(_) => true,
                            FlatInRel::RelWithDiagonals { .. } => {
                                unreachable!("resources are normalized")
                            }
                        }
                })
                .cloned()
                .collect();
            let id = StratumId(strata.len());
            strata.push(Stratum {
                groups: rules,
                model: scope,
                stable_inputs,
            });
            children.insert(0, Schedule::Rules(id));
        }
        let body = sequence(children);
        bodies.push(Some(if recursive {
            Schedule::Saturate(Box::new(body))
        } else {
            body
        }));
    }
    let mut component_of = vec![0; units.len()];
    for (i, component) in components.iter().enumerate() {
        for &unit in component {
            component_of[unit] = i;
        }
    }
    let mut incoming = vec![BTreeSet::new(); components.len()];
    let mut adjacent = vec![BTreeSet::new(); components.len()];
    for (unit, targets) in unit_edges.iter().enumerate() {
        let source = component_of[unit];
        for &target in targets {
            let target = component_of[target];
            if source != target {
                incoming[target].insert(source);
                adjacent[source].insert(target);
                adjacent[target].insert(source);
            }
        }
    }
    Ok(order_components(&incoming, &adjacent, &mut bodies))
}

fn sequence(mut children: Vec<Schedule>) -> Schedule {
    if children.len() == 1 {
        children.pop().unwrap()
    } else {
        Schedule::Sequence(children)
    }
}

fn independent(mut children: Vec<Schedule>) -> Schedule {
    if children.len() == 1 {
        children.pop().unwrap()
    } else {
        Schedule::Independent(children)
    }
}

fn order_components(
    incoming: &[BTreeSet<usize>],
    adjacent: &[BTreeSet<usize>],
    bodies: &mut [Option<Schedule>],
) -> Schedule {
    let mut unseen: BTreeSet<_> = (0..bodies.len()).collect();
    let mut visited = vec![false; bodies.len()];
    let incoming: Vec<Vec<_>> = incoming
        .iter()
        .map(|set| set.iter().copied().collect())
        .collect();
    let mut branches = Vec::new();
    while let Some(start) = unseen.pop_first() {
        let mut region = BTreeSet::new();
        let mut pending = vec![start];
        while let Some(node) = pending.pop() {
            region.insert(node);
            for &next in &adjacent[node] {
                if unseen.remove(&next) {
                    pending.push(next);
                }
            }
        }
        // Visiting a consumer's prerequisites depth first keeps producer
        // pipelines together. An explicit stack also handles long chains.
        let mut ordered = Vec::new();
        for start in region.into_iter().rev() {
            if visited[start] {
                continue;
            }
            visited[start] = true;
            let mut stack = vec![(start, 0)];
            while let Some((node, next)) = stack.last_mut() {
                if let Some(&source) = incoming[*node].get(*next) {
                    *next += 1;
                    if !visited[source] {
                        visited[source] = true;
                        stack.push((source, 0));
                    }
                } else {
                    ordered.push(*node);
                    stack.pop();
                }
            }
        }
        let mut steps = Vec::new();
        let mut batch = BTreeSet::new();
        let mut children = Vec::new();
        for node in ordered {
            if incoming[node].iter().any(|source| batch.contains(source)) {
                steps.push(independent(std::mem::take(&mut children)));
                batch.clear();
            }
            batch.insert(node);
            children.push(bodies[node].take().unwrap());
        }
        steps.push(independent(children));
        branches.push(sequence(steps));
    }
    independent(branches)
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
