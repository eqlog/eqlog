use std::collections::{BTreeMap, BTreeSet};

use eqlog_bench::{carrier, graph::Graph};

#[test]
fn carrier_propagation_is_a_disjoint_union_of_local_and_inherited_members() {
    for vertices in [1, 2, 9, 65] {
        for members in [1, 3] {
            for graph in [Graph::chain(vertices), Graph::merge(vertices, 91)] {
                let ancestors = graph.ancestors();
                let mut model = carrier::new_eqlog(&graph.parents, members);
                let mut local = vec![BTreeSet::new(); vertices];
                for (world, element) in model.iter_world_member_el() {
                    assert!(local[world.0 as usize].insert(element));
                }
                for elements in &local {
                    assert_eq!(elements.len(), members);
                }
                model.close();
                let mut worlds: Vec<_> = model.iter_world().collect();
                worlds.sort_unstable();
                assert_eq!(worlds.len(), vertices);
                let mut arrows: Vec<_> = model.iter_world_mor().collect();
                arrows.sort_unstable();
                assert_eq!(arrows.len(), graph.edges.len());
                let domains: Vec<_> = model.iter_world_mor_dom().collect();
                assert_eq!(domains.len(), arrows.len());
                assert_eq!(
                    domains.into_iter().collect::<BTreeSet<_>>(),
                    graph
                        .edges
                        .iter()
                        .enumerate()
                        .map(|(i, &(source, _))| (arrows[i], worlds[source]))
                        .collect::<BTreeSet<_>>()
                );
                let codomains: Vec<_> = model.iter_world_mor_cod().collect();
                assert_eq!(codomains.len(), arrows.len());
                assert_eq!(
                    codomains.into_iter().collect::<BTreeSet<_>>(),
                    graph
                        .edges
                        .iter()
                        .enumerate()
                        .map(|(i, &(_, target))| (arrows[i], worlds[target]))
                        .collect::<BTreeSet<_>>()
                );
                let mut member_rows: Vec<_> = model.iter_world_member_el().collect();
                member_rows.sort_unstable();
                let mut carriers = vec![BTreeSet::new(); vertices];
                let mut all = BTreeSet::new();
                for &(world, element) in &member_rows {
                    assert!(carriers[world.0 as usize].insert(element));
                    assert!(all.insert(element), "owners must have distinct identities");
                }
                let mut globals: Vec<_> = model.iter_el().collect();
                globals.sort_unstable();
                assert_eq!(globals.len(), all.len());
                assert_eq!(globals.iter().copied().collect::<BTreeSet<_>>(), all);
                for (owner, carrier) in carriers.iter().enumerate() {
                    assert_eq!(carrier.len(), ancestors[owner].len() * members);
                }
                let mut image_rows: Vec<_> = model.iter_el_mor_app().collect();
                image_rows.sort_unstable();
                let mut images = vec![BTreeMap::new(); arrows.len()];
                for &(arrow, source, target) in &image_rows {
                    assert!(images[arrow.0 as usize].insert(source, target).is_none());
                }
                let mut inherited = vec![BTreeSet::new(); vertices];
                for (edge, &(source, target)) in graph.edges.iter().enumerate() {
                    assert_eq!(
                        images[edge].keys().copied().collect::<BTreeSet<_>>(),
                        carriers[source]
                    );
                    for &image in images[edge].values() {
                        assert!(carriers[target].contains(&image));
                        assert!(
                            inherited[target].insert(image),
                            "incoming images must be disjoint"
                        );
                    }
                }
                for owner in 0..vertices {
                    assert_eq!(
                        carriers[owner]
                            .difference(&inherited[owner])
                            .copied()
                            .collect::<BTreeSet<_>>(),
                        local[owner]
                    );
                }
                model.close();
                let mut members_again: Vec<_> = model.iter_world_member_el().collect();
                members_again.sort_unstable();
                assert_eq!(members_again, member_rows);
                let mut globals_again: Vec<_> = model.iter_el().collect();
                globals_again.sort_unstable();
                assert_eq!(globals_again, globals);
                let mut images_again: Vec<_> = model.iter_el_mor_app().collect();
                images_again.sort_unstable();
                assert_eq!(images_again, image_rows);

                let mut cow = carrier::new_cow(vertices, members);
                carrier::close_cow(&graph.parents, &mut cow);
                let cow_rows: Vec<Vec<_>> = cow.iter().map(|tree| tree.iter().collect()).collect();
                for (owner, rows) in cow_rows.iter().enumerate() {
                    let expected: Vec<_> = ancestors[owner]
                        .iter()
                        .flat_map(|&source| {
                            (source * members..(source + 1) * members)
                                .map(|origin| [u32::try_from(origin).unwrap()])
                        })
                        .collect();
                    assert_eq!(*rows, expected);
                }
                carrier::close_cow(&graph.parents, &mut cow);
                let cow_again: Vec<Vec<_>> = cow.iter().map(|tree| tree.iter().collect()).collect();
                assert_eq!(cow_again, cow_rows);
            }
        }
    }
}
