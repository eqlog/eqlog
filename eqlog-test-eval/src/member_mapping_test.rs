use std::collections::BTreeSet;

use eqlog_runtime::CompiledModel;

use crate::member_mapping::*;

#[test]
fn member_transport_handles_chunks_late_images_and_quotients() {
    for (chunk, reverse) in [(32, false), (8, false), (8, true)] {
        let mut model = MemberMapping::new();
        let source = model.new_world();
        let target = model.new_world();
        let other = model.new_world();
        let mut members = Vec::new();
        let mut images = Vec::new();
        let mut labels = Vec::new();
        for _ in 0..32 / chunk {
            for _ in 0..chunk {
                members.push(model.new_el(source));
                labels.push(model.new_label());
            }
            for _ in 0..chunk {
                images.push(model.new_el(target));
            }
            model.new_el(other);
        }
        if reverse {
            images.reverse();
        }
        let morphism = model.new_world_mor();
        model.insert_world_mor_dom(morphism, source);
        model.insert_world_mor_cod(morphism, target);
        model.insert_reached(source, members[0]);
        model.insert_request(target);
        for i in 0..32 {
            model.insert_tagged(source, members[i], labels[i]);
            if i + 1 < 32 {
                model.insert_edge(source, members[i], members[i + 1]);
            }
            if i % 2 == 0 {
                model.insert_el_mor_app(morphism, members[i], images[i]);
            }
        }
        model.close();
        assert_eq!(
            model.iter_edge().filter(|(w, _, _)| *w == target).count(),
            0
        );
        for i in 0..32 {
            assert_eq!(model.observed(target, labels[i]), i % 2 == 0);
        }

        for i in (1..32).step_by(2) {
            model.insert_el_mor_app(morphism, members[i], images[i]);
        }
        model.close();
        for i in 0..31 {
            assert!(model.edge(target, images[i], images[i + 1]));
        }
        for &label in &labels {
            assert!(model.observed(target, label));
        }

        model.equate_el(target, images[31], images[0]);
        model.equate_el(source, members[9], members[8]);
        let late = model.new_label();
        model.insert_tagged(source, members[0], late);
        model.insert_edge(source, members[31], members[0]);
        model.close();
        assert!(model.are_equal_el(images[8], images[9]));
        assert!(model.observed(target, late));
        let expected: BTreeSet<_> = (0..32)
            .map(|i| {
                (
                    model.root_el(images[i]),
                    model.root_el(images[(i + 1) % 32]),
                )
            })
            .collect();
        let actual: BTreeSet<_> = model
            .iter_edge()
            .filter_map(|(w, x, y)| (w == target).then_some((x, y)))
            .collect();
        assert_eq!(actual, expected);
        assert!(model
            .iter_edge()
            .all(|(_, x, y)| model.root_el(x) == x && model.root_el(y) == y));
        model.close();
        assert_eq!(
            model.iter_edge().filter(|(w, _, _)| *w == target).count(),
            expected.len()
        );
    }
}

#[test]
fn multi_column_member_transport_composes_and_canonicalizes() {
    let mut model = MemberMapping::new();
    let source = model.new_world();
    let target = model.new_world();
    let destination = model.new_world();
    let members: Vec<_> = (0..24).map(|_| model.new_el(source)).collect();
    let images: Vec<_> = (0..24).map(|_| model.new_el(target)).collect();
    let final_images: Vec<_> = (0..24).map(|_| model.new_el(destination)).collect();
    let labels: Vec<_> = (0..3).map(|_| model.new_label()).collect();
    let first = model.new_world_mor();
    model.insert_world_mor_dom(first, source);
    model.insert_world_mor_cod(first, target);
    let second = model.new_world_mor();
    model.insert_world_mor_dom(second, target);
    model.insert_world_mor_cod(second, destination);
    for i in 0..24 {
        model.insert_el_mor_app(first, members[i], images[i]);
        model.insert_el_mor_app(second, images[i], final_images[i]);
    }
    let mut source_rows = Vec::new();
    for i in 0..24 {
        for &label in &labels {
            for j in 0..24 {
                source_rows.push((i, label, j));
                model.insert_labelled_edge(source, members[i], label, members[j]);
            }
        }
    }
    model.close();

    // Leave inherited rows unread until equality repair has visited the mapped roots.
    model.equate_el(source, members[2], members[1]);
    model.equate_el(target, images[22], images[21]);
    model.equate_el(destination, final_images[14], final_images[13]);
    model.equate_label(labels[2], labels[0]);
    let late_label = model.new_label();
    source_rows.push((23, late_label, 0));
    model.insert_labelled_edge(source, members[23], late_label, members[0]);
    model.insert_labelled_edge(target, images[20], late_label, images[1]);
    model.insert_labelled_edge(destination, final_images[19], late_label, final_images[2]);
    for world in [target, destination] {
        for label in [labels[0], labels[1], late_label] {
            model.insert_request_label(world, label);
        }
    }
    model.close();

    assert!(model.are_equal_el(images[2], images[1]));
    assert!(model.are_equal_el(final_images[2], final_images[1]));
    assert!(model.are_equal_el(final_images[22], final_images[21]));
    let mut inherited_rows = source_rows;
    inherited_rows.push((20, late_label, 1));
    for (world, elements) in [(target, &images), (destination, &final_images)] {
        let mut expected: BTreeSet<_> = inherited_rows
            .iter()
            .map(|&(i, label, j)| {
                (
                    model.root_el(elements[i]),
                    model.root_label(label),
                    model.root_el(elements[j]),
                )
            })
            .collect();
        if world == destination {
            expected.insert((
                model.root_el(final_images[19]),
                late_label,
                model.root_el(final_images[2]),
            ));
        }
        let transported: BTreeSet<_> = model
            .iter_labelled_edge()
            .filter_map(|(w, x, label, y)| (w == world).then_some((x, label, y)))
            .collect();
        let matched: BTreeSet<_> = model
            .iter_matched_labelled_edge()
            .filter_map(|(w, x, label, y)| (w == world).then_some((x, label, y)))
            .collect();
        assert_eq!(transported, expected);
        assert_eq!(matched, expected);
    }
    assert!(model.iter_labelled_edge().all(|(_, x, label, y)| {
        model.root_el(x) == x && model.root_label(label) == label && model.root_el(y) == y
    }));
    let count = model.iter_labelled_edge().count();
    model.close();
    assert_eq!(model.iter_labelled_edge().count(), count);
}

#[test]
fn multi_column_member_transport_filters_partial_maps_and_merges_images() {
    for reverse in [false, true] {
        let mut model = MemberMapping::new();
        let source = model.new_world();
        let target = model.new_world();
        let members: Vec<_> = (0..24).map(|_| model.new_el(source)).collect();
        let mut images: Vec<_> = (0..24).map(|_| model.new_el(target)).collect();
        if reverse {
            images.reverse();
        }
        let labels: Vec<_> = (0..3).map(|_| model.new_label()).collect();
        let morphism = model.new_world_mor();
        model.insert_world_mor_dom(morphism, source);
        model.insert_world_mor_cod(morphism, target);
        for i in 0..12 {
            model.insert_el_mor_app(morphism, members[i], images[i]);
        }
        let mut source_rows = Vec::new();
        for i in 0..24 {
            let successors = if i < 8 { 12..24 } else { 0..12 };
            for j in successors {
                let label = labels[i % labels.len()];
                source_rows.push((i, label, j));
                model.insert_labelled_edge(source, members[i], label, members[j]);
            }
        }
        for &label in &labels {
            model.insert_request_label(target, label);
        }
        model.close();

        let expected: BTreeSet<_> = source_rows
            .iter()
            .filter_map(|&(i, label, j)| {
                (i < 12 && j < 12).then_some((images[i], label, images[j]))
            })
            .collect();
        let transported: BTreeSet<_> = model
            .iter_labelled_edge()
            .filter_map(|(w, x, label, y)| (w == target).then_some((x, label, y)))
            .collect();
        let matched: BTreeSet<_> = model
            .iter_matched_labelled_edge()
            .filter_map(|(w, x, label, y)| (w == target).then_some((x, label, y)))
            .collect();
        assert_eq!(transported, expected);
        assert_eq!(matched, expected);

        for i in 12..24 {
            model.insert_el_mor_app(morphism, members[i], images[i]);
        }
        model.insert_el_mor_app(morphism, members[0], images[1]);
        source_rows.push((23, labels[0], 23));
        model.insert_labelled_edge(source, members[23], labels[0], members[23]);
        model.canonicalize();
        model.close();

        assert!(model.are_equal_el(images[0], images[1]));
        let expected: BTreeSet<_> = source_rows
            .iter()
            .map(|&(i, label, j)| (model.root_el(images[i]), label, model.root_el(images[j])))
            .collect();
        let transported: BTreeSet<_> = model
            .iter_labelled_edge()
            .filter_map(|(w, x, label, y)| (w == target).then_some((x, label, y)))
            .collect();
        let matched: BTreeSet<_> = model
            .iter_matched_labelled_edge()
            .filter_map(|(w, x, label, y)| (w == target).then_some((x, label, y)))
            .collect();
        assert_eq!(transported, expected);
        assert_eq!(matched, expected);
        model.close();
        assert_eq!(
            model
                .iter_labelled_edge()
                .filter(|(w, _, _, _)| *w == target)
                .count(),
            expected.len()
        );
    }
}

#[test]
fn member_transport_can_move_inherited_rows_outside_the_original_image() {
    let mut model = MemberMapping::new();
    let source = model.new_world();
    let target = model.new_world();
    let other = model.new_world();
    let members: Vec<_> = (0..24).map(|_| model.new_el(source)).collect();
    let images: Vec<_> = (0..24).map(|_| model.new_el(target)).collect();
    let representative = model.new_el(other);
    let labels: Vec<_> = (0..128).map(|_| model.new_label()).collect();
    let morphism = model.new_world_mor();
    model.insert_world_mor_dom(morphism, source);
    model.insert_world_mor_cod(morphism, target);
    for i in 0..24 {
        model.insert_el_mor_app(morphism, members[i], images[i]);
        for j in 0..24 {
            if (i + j) % 3 != 0 {
                model.insert_labelled_edge(source, members[i], labels[i % 2], members[j]);
            }
        }
    }
    for &label in &labels {
        model.insert_tagged(other, representative, label);
    }
    model.close();

    // Own facts make the representative win even though its ID is outside the image.
    model.equate_world(target, other);
    model.equate_el(target, images[17], representative);
    model.canonicalize();
    model.canonicalize();
    assert_eq!(model.root_el(images[17]), representative);
    model.insert_labelled_edge(source, members[17], labels[2], members[17]);
    for label in &labels[..3] {
        model.insert_request_label(other, *label);
    }
    model.close();

    let target = model.root_world(target);
    let mut expected = BTreeSet::new();
    for i in 0..24 {
        for j in 0..24 {
            if (i + j) % 3 != 0 {
                expected.insert((
                    model.root_el(images[i]),
                    labels[i % 2],
                    model.root_el(images[j]),
                ));
            }
        }
    }
    expected.insert((representative, labels[2], representative));
    for actual in [
        model
            .iter_labelled_edge()
            .filter_map(|(world, x, label, y)| (world == target).then_some((x, label, y)))
            .collect::<BTreeSet<_>>(),
        model
            .iter_matched_labelled_edge()
            .filter_map(|(world, x, label, y)| (world == target).then_some((x, label, y)))
            .collect(),
    ] {
        assert_eq!(actual, expected);
    }
    assert!(model.iter_labelled_edge().all(|(world, x, label, y)| {
        model.root_world(world) == world
            && model.root_el(x) == x
            && model.root_label(label) == label
            && model.root_el(y) == y
    }));
    let snapshot = model.to_dynamic();
    assert!(snapshot.is_canonical());
    let mut restored = MemberMapping::from_dynamic(&snapshot).unwrap();
    restored.close();
    assert_eq!(
        restored.iter_labelled_edge().collect::<BTreeSet<_>>(),
        model.iter_labelled_edge().collect()
    );
}

#[test]
fn overlapping_owned_and_inherited_rows_survive_partial_images_and_cycles() {
    let mut model = MemberMapping::new();
    let source = model.new_world();
    let target = model.new_world();
    let x0 = model.new_el(source);
    let x1 = model.new_el(source);
    let y0 = model.new_el(target);
    let y1 = model.new_el(target);
    let common = model.new_label();
    let owned = model.new_label();
    for world in [source, target] {
        for label in [common, owned] {
            model.insert_request_label(world, label);
        }
    }
    model.insert_labelled_edge(source, x0, common, x1);
    model.insert_labelled_edge(target, y0, common, y1);
    model.insert_labelled_edge(target, y1, owned, y0);
    let forward = model.new_world_mor();
    model.insert_world_mor_dom(forward, source);
    model.insert_world_mor_cod(forward, target);
    model.insert_el_mor_app(forward, x0, y0);
    model.close();
    assert_eq!(model.iter_labelled_edge().count(), 3);
    assert_eq!(model.iter_matched_labelled_edge().count(), 3);

    model.insert_el_mor_app(forward, x1, y1);
    model.close();
    assert_eq!(model.iter_labelled_edge().count(), 3);
    assert_eq!(model.iter_matched_labelled_edge().count(), 3);

    model.insert_labelled_edge(source, x1, common, x0);
    model.close();
    assert!(model.labelled_edge(target, y1, common, y0));
    assert!(model.labelled_edge(target, y1, owned, y0));
    assert_eq!(model.iter_labelled_edge().count(), 5);
    assert_eq!(model.iter_matched_labelled_edge().count(), 5);

    let reverse = model.new_world_mor();
    model.insert_world_mor_dom(reverse, target);
    model.insert_world_mor_cod(reverse, source);
    model.insert_el_mor_app(reverse, y0, x0);
    model.insert_el_mor_app(reverse, y1, x1);
    for _ in 0..3 {
        model.canonicalize();
        model.close();
        assert!(model.labelled_edge(source, x1, owned, x0));
        assert_eq!(model.iter_labelled_edge().count(), 6);
        assert_eq!(model.iter_matched_labelled_edge().count(), 6);
    }
    model.equate_el(source, x0, x1);
    model.close();
    assert_eq!(model.iter_labelled_edge().count(), 4);
    assert_eq!(model.iter_matched_labelled_edge().count(), 4);
}
