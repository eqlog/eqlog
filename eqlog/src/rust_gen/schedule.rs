use std::collections::{BTreeMap, BTreeSet};

use crate::algebra::signature::Signature;
use crate::flat_eqlog::{iter_flat_rels, morphism_preservation_rules, FlatInRel, FlatOutRel};
use crate::options::ModelMode;
use crate::ram::RamModule;

pub struct Stratum {
    pub modules: Vec<usize>,
    pub recursive: bool,
}

fn resource(rel: &FlatInRel) -> FlatInRel {
    match rel {
        FlatInRel::RelWithDiagonals { rel, .. } => FlatInRel::Rel(*rel),
        FlatInRel::Rel(_) | FlatInRel::Equality(_) | FlatInRel::TypeSet(_) => rel.clone(),
    }
}

pub fn strata(modules: &[RamModule], signature: &Signature, model_mode: ModelMode) -> Vec<Stratum> {
    let resources: Vec<_> = iter_flat_rels(signature)
        .map(FlatInRel::Rel)
        .chain(signature.iter_types().map(FlatInRel::TypeSet))
        .collect();
    let reads: Vec<BTreeSet<_>> = modules
        .iter()
        .map(|module| {
            module
                .routines
                .iter()
                .flat_map(|routine| {
                    routine
                        .flat_rule
                        .premise
                        .iter()
                        .map(|stmt| resource(&stmt.rel))
                })
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
    let mut edges = vec![Vec::new(); modules.len()];
    for (source, module) in modules.iter().enumerate() {
        let mut writes = BTreeSet::new();
        for output in module.routines.iter().flat_map(|r| &r.flat_rule.conclusion) {
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
    components(&edges)
        .into_iter()
        .map(|modules| {
            let recursive = modules.len() > 1 || edges[modules[0]].contains(&modules[0]);
            Stratum { modules, recursive }
        })
        .collect()
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
