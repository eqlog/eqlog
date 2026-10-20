use std::collections::BTreeSet;

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
