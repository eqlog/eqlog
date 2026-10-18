use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Deref;
use std::rc::Rc;

use crate::lazy_index::IndexSeed;
use crate::versions::SnapshotSet;
use crate::{PrefixTree1, PrefixTree2};

#[derive(Clone, Debug)]
pub struct MorphismWithSignature {
    pub morph: u32,
    pub dom: u32,
    pub cod: u32,
}

#[derive(Clone, Debug, Default)]
pub struct MorphismComponent {
    pub objects: Vec<u32>,
    pub internal: Vec<MorphismWithSignature>,
    pub outgoing: Vec<MorphismWithSignature>,
}

/// All relations using this topology share its sorted edge signatures.
#[derive(Debug)]
pub struct MorphismGraph {
    components: Vec<MorphismComponent>,
    pub(crate) signatures: Rc<[(u32, u32, u32, bool)]>,
}

impl Deref for MorphismGraph {
    type Target = [MorphismComponent];

    fn deref(&self) -> &Self::Target {
        &self.components
    }
}

fn edge_signatures(graph: &[MorphismComponent]) -> Vec<(u32, u32, u32, bool)> {
    let mut edges: Vec<_> = graph
        .iter()
        .flat_map(|component| {
            component
                .internal
                .iter()
                .map(|morphism| (morphism, true))
                .chain(component.outgoing.iter().map(|morphism| (morphism, false)))
        })
        .map(|(morphism, internal)| (morphism.morph, morphism.dom, morphism.cod, internal))
        .collect();
    edges.sort_unstable();
    edges
}

struct GraphSnapshot {
    dom: PrefixTree2,
    cod: PrefixTree2,
    objects: PrefixTree1,
    graph_objects: PrefixTree1,
    dom_by_morphism: IndexSeed<PrefixTree2, PrefixTree2>,
    positions: BTreeMap<u32, usize>,
    connectivity: BTreeMap<(u32, u32), usize>,
    conflicting_codomain_targets: BTreeSet<u32>,
    components: Rc<MorphismGraph>,
}

impl GraphSnapshot {
    fn update_edges(&mut self, dom: &PrefixTree2, cod: &PrefixTree2) -> Option<Rc<MorphismGraph>> {
        let mut changed = BTreeSet::new();
        dom.visit_difference(&self.dom, &mut |[_, morphism]| {
            changed.insert(morphism);
        });
        self.dom.visit_difference(dom, &mut |[_, morphism]| {
            changed.insert(morphism);
        });
        cod.visit_difference(&self.cod, &mut |[morphism, _]| {
            changed.insert(morphism);
        });
        self.cod.visit_difference(cod, &mut |[morphism, _]| {
            changed.insert(morphism);
        });
        let domains = self
            .dom_by_morphism
            .update(dom, |[owner, morphism]| Some([morphism, owner]));
        let mut connectivity_delta = BTreeMap::<(u32, u32), isize>::new();
        let mut affected = BTreeSet::new();
        let mut additions = Vec::new();
        let old = &self.components.signatures;
        for &morphism in &changed {
            let first = old.partition_point(|edge| edge.0 < morphism);
            let end = old.partition_point(|edge| edge.0 <= morphism);
            for &(_, dom, cod, _) in &old[first..end] {
                *connectivity_delta.entry((dom, cod)).or_default() -= 1;
                affected.insert(self.positions[&dom]);
            }
            if let Some(domains) = domains.get(morphism) {
                if let Some(codomains) = cod.get(morphism) {
                    for [dom] in domains.iter() {
                        for [cod] in codomains.iter() {
                            let source = self.positions[&dom];
                            let target = self.positions[&cod];
                            if source > target {
                                return None;
                            }
                            *connectivity_delta.entry((dom, cod)).or_default() += 1;
                            affected.insert(source);
                            additions.push((morphism, dom, cod, source == target));
                        }
                    }
                }
            }
        }
        for (&(dom, cod), &delta) in &connectivity_delta {
            let count = self.connectivity.get(&(dom, cod)).copied().unwrap_or(0);
            let remaining = count
                .checked_add_signed(delta)
                .expect("edge multiplicities must stay nonnegative");
            // Removing the last internal connection can split an SCC. Outgoing
            // deletions and additions respecting its order preserve the partition.
            if remaining == 0 && dom != cod && self.positions[&dom] == self.positions[&cod] {
                return None;
            }
        }
        let mut signatures: Vec<_> = old
            .iter()
            .copied()
            .filter(|edge| !changed.contains(&edge.0))
            .collect();
        signatures.extend(additions.iter().copied());
        signatures.sort_unstable();
        if signatures.as_slice() == old.as_ref() {
            return Some(Rc::clone(&self.components));
        }
        let mut components = self.components.components.clone();
        for source in affected {
            components[source]
                .internal
                .retain(|edge| !changed.contains(&edge.morph));
            components[source]
                .outgoing
                .retain(|edge| !changed.contains(&edge.morph));
        }
        for (morph, dom, cod, internal) in additions {
            let component = &mut components[self.positions[&dom]];
            let edges = if internal {
                &mut component.internal
            } else {
                &mut component.outgoing
            };
            edges.push(MorphismWithSignature { morph, dom, cod });
        }
        for (pair, delta) in connectivity_delta {
            let count = self.connectivity.get(&pair).copied().unwrap_or(0);
            let remaining = count.checked_add_signed(delta).unwrap();
            if remaining == 0 {
                self.connectivity.remove(&pair);
            } else {
                self.connectivity.insert(pair, remaining);
            }
        }
        Some(Rc::new(MorphismGraph {
            components,
            signatures: signatures.into(),
        }))
    }
}

/// Reuses graph topology across relations and strata with the same inputs.
pub struct MorphismGraphCache<const N: usize> {
    owners: RefCell<BTreeMap<[u32; N], GraphSnapshot>>,
    ownership_known: bool,
}

impl<const N: usize> MorphismGraphCache<N> {
    pub fn new() -> Self {
        Self {
            owners: RefCell::new(BTreeMap::new()),
            ownership_known: true,
        }
    }

    /// Graph observations cannot certify the dependent ownership of imported facts.
    pub fn mark_ownership_unknown(&mut self) {
        self.ownership_known = false;
    }

    pub fn components(
        &self,
        parents: [u32; N],
        dom: &PrefixTree2,
        cod: &PrefixTree2,
        objects: &PrefixTree1,
    ) -> Rc<MorphismGraph> {
        let mut owners = self.owners.borrow_mut();
        if let Some(previous) = owners.get(&parents) {
            if previous.dom.shares_root(dom)
                && previous.cod.shares_root(cod)
                && previous.objects.shares_root(objects)
            {
                return Rc::clone(&previous.components);
            }
        }
        let mut conflicting_codomain_targets =
            owners.get(&parents).map_or_else(BTreeSet::new, |previous| {
                previous.conflicting_codomain_targets.clone()
            });
        let previous_cod = owners
            .get(&parents)
            .map(|previous| &previous.cod)
            .unwrap_or_else(|| PrefixTree2::empty());
        for (_, targets, _) in cod.map.difference_entries(&previous_cod.map) {
            if targets.iter().nth(1).is_some() {
                conflicting_codomain_targets.extend(targets.iter().map(|[target]| target));
            }
        }
        let mut graph_objects = objects.clone();
        if N > 0 {
            // Propagated endpoints can precede parent equalities. Include
            // them in the graph without asserting additional membership.
            for [object, _] in dom.iter() {
                graph_objects.insert([object]);
            }
            for [_, object] in cod.iter() {
                graph_objects.insert([object]);
            }
        }
        if let Some(previous) = owners.get_mut(&parents) {
            if graph_objects.is_subset(&previous.graph_objects)
                && previous.graph_objects.is_subset(&graph_objects)
            {
                if let Some(components) = previous.update_edges(dom, cod) {
                    previous.dom = dom.clone();
                    previous.cod = cod.clone();
                    previous.objects = objects.clone();
                    previous.graph_objects = graph_objects;
                    previous.conflicting_codomain_targets = conflicting_codomain_targets;
                    previous.components = Rc::clone(&components);
                    return components;
                }
            }
        }
        let components = morphism_components(dom, cod, &graph_objects);
        let positions = components
            .iter()
            .enumerate()
            .flat_map(|(i, component)| component.objects.iter().map(move |&object| (object, i)))
            .collect();
        let signatures = edge_signatures(&components);
        let mut connectivity = BTreeMap::new();
        for &(_, dom, cod, _) in &signatures {
            *connectivity.entry((dom, cod)).or_default() += 1;
        }
        let signatures = if let Some(previous) = owners
            .get(&parents)
            .filter(|previous| previous.components.signatures.as_ref() == signatures.as_slice())
        {
            Rc::clone(&previous.components.signatures)
        } else {
            signatures.into()
        };
        let components = Rc::new(MorphismGraph {
            components,
            signatures,
        });
        let mut dom_by_morphism = IndexSeed::new();
        dom_by_morphism.update(dom, |[owner, morphism]| Some([morphism, owner]));
        owners.insert(
            parents,
            GraphSnapshot {
                dom: dom.clone(),
                cod: cod.clone(),
                objects: objects.clone(),
                graph_objects,
                dom_by_morphism,
                positions,
                connectivity,
                conflicting_codomain_targets,
                components: Rc::clone(&components),
            },
        );
        components
    }

    /// Conflicting codomains can transport member facts outside their declared owner.
    /// Keep those owners after conflicts disappear, since inherited facts survive.
    /// `None` means history is absent or cannot certify imported facts.
    pub fn conflicting_codomain_targets(&self, parents: [u32; N]) -> Option<Vec<u32>> {
        if !self.ownership_known {
            return None;
        }
        self.owners.borrow().get(&parents).map(|snapshot| {
            snapshot
                .conflicting_codomain_targets
                .iter()
                .copied()
                .collect()
        })
    }

    pub fn retain_owners(&mut self, mut retain: impl FnMut(&[u32; N]) -> bool) {
        self.owners.get_mut().retain(|owners, _| retain(owners));
    }
}

/// Groups mutually reachable objects in topological order.
///
/// Internal morphisms need fixed-point propagation; outgoing morphisms can run
/// once after their source component is closed. Isolated objects are included
/// because they can contain nested morphism graphs.
///
/// Domains use (object, morphism) order and codomains use (morphism, object)
/// order. Incomplete morphisms are omitted.
pub fn morphism_components(
    dom_order_1_0: &PrefixTree2,
    cod_order_0_1: &PrefixTree2,
    obj_order_0: &PrefixTree1,
) -> Vec<MorphismComponent> {
    let objects: Vec<_> = obj_order_0.iter().map(|[object]| object).collect();
    let indices: BTreeMap<_, _> = objects
        .iter()
        .enumerate()
        .map(|(index, &object)| (object, index))
        .collect();
    let mut outgoing = vec![Vec::new(); objects.len()];
    let mut incoming = vec![Vec::new(); objects.len()];
    let mut morphisms = Vec::new();
    for [dom, morph] in dom_order_1_0.iter() {
        let cods = cod_order_0_1.get(morph);
        let Some(cods) = cods else {
            continue;
        };
        let source = indices[&dom];
        // Conflicting results still contribute edges until functionality merges
        // them; dropping an edge could discard the last owned support of a fact.
        for [cod] in cods.iter() {
            let target = indices[&cod];
            outgoing[source].push(target);
            incoming[target].push(source);
            morphisms.push(MorphismWithSignature { morph, dom, cod });
        }
    }

    // Explicit DFS stacks also support long chains without using the call stack.
    let mut visited = vec![false; objects.len()];
    let mut finished = Vec::new();
    for start in 0..objects.len() {
        if visited[start] {
            continue;
        }
        visited[start] = true;
        let mut stack = vec![(start, 0)];
        while let Some((object, next)) = stack.last_mut() {
            if let Some(&target) = outgoing[*object].get(*next) {
                *next += 1;
                if !visited[target] {
                    visited[target] = true;
                    stack.push((target, 0));
                }
            } else {
                finished.push(*object);
                stack.pop();
            }
        }
    }

    let mut component_of = vec![None; objects.len()];
    let mut components = Vec::new();
    for start in finished.into_iter().rev() {
        if component_of[start].is_some() {
            continue;
        }
        let index = components.len();
        let mut component = MorphismComponent::default();
        let mut stack = vec![start];
        component_of[start] = Some(index);
        while let Some(object) = stack.pop() {
            component.objects.push(objects[object]);
            for &source in &incoming[object] {
                if component_of[source].is_none() {
                    component_of[source] = Some(index);
                    stack.push(source);
                }
            }
        }
        components.push(component);
    }

    for morphism in morphisms {
        let source = component_of[indices[&morphism.dom]].unwrap();
        let target = component_of[indices[&morphism.cod]].unwrap();
        if source == target {
            components[source].internal.push(morphism);
        } else {
            assert!(source < target);
            components[source].outgoing.push(morphism);
        }
    }
    components
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn components_separate_cycles_from_incoming_and_outgoing_morphisms() {
        let mut dom = PrefixTree2::new();
        let mut cod = PrefixTree2::new();
        let mut objects = PrefixTree1::new();
        for object in 0..7 {
            objects.insert([object]);
        }
        for (morph, (source, target)) in [(0, 1), (1, 2), (2, 1), (2, 3), (3, 3), (4, 5), (1, 2)]
            .into_iter()
            .enumerate()
        {
            let morph = morph as u32;
            dom.insert([source, morph]);
            cod.insert([morph, target]);
        }
        dom.insert([3, 100]);
        cod.insert([101, 0]);
        let components = morphism_components(&dom, &cod, &objects);
        let positions: BTreeMap<_, _> = components
            .iter()
            .enumerate()
            .flat_map(|(i, component)| component.objects.iter().map(move |&obj| (obj, i)))
            .collect();
        assert_eq!(positions.len(), 7);
        assert_eq!(components.len(), 6);
        assert_eq!(positions[&1], positions[&2]);
        for (source, target) in [(0, 1), (2, 3), (4, 5)] {
            assert!(positions[&source] < positions[&target]);
        }
        assert_eq!(components[positions[&1]].internal.len(), 3);
        assert_eq!(components[positions[&3]].internal.len(), 1);
        assert_eq!(components[positions[&6]].objects, vec![6]);
        assert_eq!(
            components
                .iter()
                .map(|c| c.internal.len() + c.outgoing.len())
                .sum::<usize>(),
            7
        );
    }

    #[test]
    fn empty_graph() {
        assert!(morphism_components(
            PrefixTree2::empty(),
            PrefixTree2::empty(),
            PrefixTree1::empty(),
        )
        .is_empty());
    }

    #[test]
    fn long_chain() {
        let mut dom = PrefixTree2::new();
        let mut cod = PrefixTree2::new();
        let mut objects = PrefixTree1::new();
        for object in 0..10_000 {
            objects.insert([object]);
            if object > 0 {
                dom.insert([object - 1, object]);
                cod.insert([object, object]);
            }
        }
        let components = morphism_components(&dom, &cod, &objects);
        assert_eq!(components.len(), 10_000);
        for (i, component) in components.iter().enumerate() {
            assert_eq!(component.objects, vec![i as u32]);
            assert!(component.internal.is_empty());
            assert_eq!(component.outgoing.len(), usize::from(i < 9_999));
        }
    }
}
