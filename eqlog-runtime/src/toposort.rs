use std::collections::BTreeMap;

use crate::{PrefixTree1, PrefixTree2};

#[derive(Debug)]
pub struct MorphismWithSignature {
    pub morph: u32,
    pub dom: u32,
    pub cod: u32,
}

#[derive(Debug, Default)]
pub struct MorphismComponent {
    pub objects: Vec<u32>,
    pub internal: Vec<MorphismWithSignature>,
    pub outgoing: Vec<MorphismWithSignature>,
}

/// Groups mutually reachable objects in topological order.
///
/// Internal morphisms need fixed-point propagation; outgoing morphisms can run
/// once after their source component is closed. Isolated objects are included
/// because they can contain nested morphism graphs.
///
/// Inputs are disjoint old/new sets. Domains use (object, morphism) order and
/// codomains use (morphism, object) order. Incomplete morphisms are omitted.
pub fn morphism_components(
    dom_new_order_1_0: &PrefixTree2,
    dom_old_order_1_0: &PrefixTree2,
    cod_new_order_0_1: &PrefixTree2,
    cod_old_order_0_1: &PrefixTree2,
    obj_old_order_0: &PrefixTree1,
    obj_new_order_0: &PrefixTree1,
) -> Vec<MorphismComponent> {
    let objects: Vec<_> = obj_old_order_0
        .union(obj_new_order_0)
        .iter()
        .map(|[object]| object)
        .collect();
    let indices: BTreeMap<_, _> = objects
        .iter()
        .enumerate()
        .map(|(index, &object)| (object, index))
        .collect();
    let mut outgoing = vec![Vec::new(); objects.len()];
    let mut incoming = vec![Vec::new(); objects.len()];
    let mut morphisms = Vec::new();
    for [dom, morph] in dom_new_order_1_0.iter().chain(dom_old_order_1_0.iter()) {
        let cods = cod_new_order_0_1
            .get(morph)
            .or_else(|| cod_old_order_0_1.get(morph));
        let Some(cods) = cods else {
            continue;
        };
        let [cod] = cods.iter().next().unwrap();
        let source = indices[&dom];
        let target = indices[&cod];
        outgoing[source].push(target);
        incoming[target].push(source);
        morphisms.push(MorphismWithSignature { morph, dom, cod });
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
        let mut dom_new = PrefixTree2::new();
        let mut dom_old = PrefixTree2::new();
        let mut cod_new = PrefixTree2::new();
        let mut cod_old = PrefixTree2::new();
        let mut objects = PrefixTree1::new();
        for object in 0..7 {
            objects.insert([object]);
        }
        for (morph, (source, target)) in [(0, 1), (1, 2), (2, 1), (2, 3), (3, 3), (4, 5), (1, 2)]
            .into_iter()
            .enumerate()
        {
            let morph = morph as u32;
            if morph % 2 == 0 {
                dom_new.insert([source, morph]);
                cod_old.insert([morph, target]);
            } else {
                dom_old.insert([source, morph]);
                cod_new.insert([morph, target]);
            }
        }
        dom_new.insert([3, 100]);
        cod_new.insert([101, 0]);
        let components = morphism_components(
            &dom_new,
            &dom_old,
            &cod_new,
            &cod_old,
            &objects,
            PrefixTree1::empty(),
        );
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
            PrefixTree2::empty(),
            PrefixTree2::empty(),
            PrefixTree1::empty(),
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
        let components = morphism_components(
            &dom,
            PrefixTree2::empty(),
            &cod,
            PrefixTree2::empty(),
            &objects,
            PrefixTree1::empty(),
        );
        assert_eq!(components.len(), 10_000);
        for (i, component) in components.iter().enumerate() {
            assert_eq!(component.objects, vec![i as u32]);
            assert!(component.internal.is_empty());
            assert_eq!(component.outgoing.len(), usize::from(i < 9_999));
        }
    }
}
