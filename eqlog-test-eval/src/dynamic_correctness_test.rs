use std::collections::BTreeSet;

use eqlog_runtime::{CompiledModel, Element, Model};

use crate::morphism_preservation::MorphismPreservation;

fn normalized_rows(model: &Model) -> Vec<BTreeSet<Vec<Element>>> {
    let normalize = |element: Element| {
        (0..=element.index)
            .map(|index| Element { index, ..element })
            .find(|&other| model.are_equal(element, other).unwrap())
            .unwrap()
    };
    model
        .signature()
        .relations()
        .map(|(relation, _)| {
            model
                .tuples(relation)
                .unwrap()
                .map(|row| row.into_iter().map(normalize).collect())
                .collect()
        })
        .collect()
}

fn random(state: &mut u64, bound: u32) -> u32 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state % u64::from(bound)) as u32
}

#[test]
fn dynamic_conversion_preserves_random_morphism_closures() {
    for seed in 1..=16 {
        let mut state = seed;
        let mut compiled = MorphismPreservation::new();
        let worlds: Vec<_> = (0..4).map(|_| compiled.new_world()).collect();
        let elements: Vec<_> = worlds
            .iter()
            .map(|&world| (0..3).map(|_| compiled.new_el(world)).collect::<Vec<_>>())
            .collect();
        let ambient: Vec<_> = (0..4).map(|_| compiled.new_ambient()).collect();
        for _ in 0..4 {
            let source = random(&mut state, 4) as usize;
            let target = random(&mut state, 4) as usize;
            let map = compiled.new_world_mor();
            compiled.insert_world_mor_dom(map, worlds[source]);
            compiled.insert_world_mor_cod(map, worlds[target]);
            for i in 0..3 {
                compiled.insert_el_mor_app(map, elements[source][i], elements[target][i]);
            }
        }
        for step in 0..50 {
            let world = random(&mut state, 4) as usize;
            let first = random(&mut state, 3) as usize;
            let second = random(&mut state, 3) as usize;
            let label = random(&mut state, 4) as usize;
            match random(&mut state, 6) {
                0 => compiled.insert_ready(worlds[world]),
                1 => compiled.insert_tagged(worlds[world], elements[world][first], ambient[label]),
                2 => compiled.insert_edge(
                    worlds[world],
                    elements[world][first],
                    elements[world][second],
                ),
                3 => compiled.equate_el(
                    worlds[world],
                    elements[world][first],
                    elements[world][second],
                ),
                4 => compiled.equate_ambient(ambient[label], ambient[(label + 1) % 4]),
                5 => compiled.close(),
                _ => unreachable!(),
            }
            let before = compiled.to_dynamic();
            let mut converted = MorphismPreservation::from_dynamic(&before).unwrap();
            converted.close();
            compiled.close();
            assert_eq!(
                normalized_rows(&converted.to_dynamic()),
                normalized_rows(&compiled.to_dynamic()),
                "seed {seed}, step {step}"
            );
        }
    }
}
