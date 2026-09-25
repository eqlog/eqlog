use crate::morphism_preservation::*;

#[test]
fn rule_insertions_can_precede_endpoint_equalities() {
    let mut model = MorphismPreservation::new();
    let world = model.new_world();
    let source0 = model.new_inner(world);
    let source1 = model.new_inner(world);
    let target = model.new_inner(world);
    let x0 = model.new_item(world, source0);
    let x1 = model.new_item(world, source1);
    let y = model.new_item(world, target);
    let f = model.new_inner_mor(world);
    model.insert_requested_map(world, f, source0, target);
    model.insert_requested_source(world, source0, f, x0);
    model.insert_requested_map(world, f, source1, target);
    model.insert_requested_source(world, source1, f, x1);
    model.insert_requested_target(world, target, f, y);

    model.close();

    assert!(model.are_equal_inner(source0, source1));
    assert_eq!(model.item_mor_app(world, f, x0), Some(y));
    assert_eq!(model.item_mor_app(world, f, x1), Some(y));
    assert_eq!(model.iter_item_mor_app().count(), 2);

    model.equate_item(world, source0, x0, x1);
    model.close();
    assert_eq!(model.item_mor_app(world, f, x0), Some(y));
    assert_eq!(model.iter_item_mor_app().count(), 1);
}

#[test]
fn preservation_waits_for_endpoints_and_images() {
    let mut model = MorphismPreservation::new();
    let source = model.new_world();
    let target = model.new_world();
    let x = model.new_el(source);
    let y = model.new_el(source);
    let label = model.new_ambient();
    model.insert_ready(source);
    model.insert_tagged(source, x, label);
    model.insert_edge(source, x, y);
    let h = model.new_world_mor();

    model.close();
    assert_eq!(model.world_mor_dom(h), None);
    assert_eq!(model.world_mor_cod(h), None);
    assert!(!model.ready(target));

    model.insert_world_mor_dom(h, source);
    model.close();
    assert_eq!(model.world_mor_cod(h), None);
    assert!(!model.ready(target));

    model.insert_world_mor_cod(h, target);
    model.close();
    assert!(model.ready(target));
    assert!(model.observed(target));
    assert_eq!(model.el_mor_app(h, x), None);
    assert_eq!(model.el_mor_app(h, y), None);
    assert_eq!(model.iter_el().count(), 2);

    let image_x = model.new_el(target);
    model.insert_el_mor_app(h, x, image_x);
    model.close();
    assert!(model.tagged(target, image_x, label));
    assert_eq!(model.edge(target, image_x), None);
    assert_eq!(model.el_mor_app(h, y), None);
    assert_eq!(model.iter_el().count(), 3);

    let image_y = model.new_el(target);
    model.insert_el_mor_app(h, y, image_y);
    model.close();
    assert_eq!(model.edge(target, image_x), Some(image_y));
    assert_eq!(model.iter_el().count(), 4);

    let late_label = model.new_ambient();
    model.insert_tagged(source, x, late_label);
    model.close();
    assert!(model.tagged(target, image_x, late_label));

    let other_result = model.new_el(target);
    model.insert_edge(target, image_x, other_result);
    model.close();
    assert!(model.are_equal_el(image_y, other_result));
    model.close();
    assert_eq!(model.iter_el().count(), 4);
}

#[test]
fn nested_preservation_does_not_create_images() {
    let mut model = MorphismPreservation::new();
    let source = model.new_world();
    let target = model.new_world();
    let inner = model.new_inner(source);
    let x = model.new_item(source, inner);
    model.insert_marked(source, inner, x);
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, source);
    model.insert_world_mor_cod(h, target);

    model.close();
    assert_eq!(model.inner_mor_app(h, inner), None);
    assert_eq!(model.world_item_mor_app(h, x), None);
    assert_eq!(model.iter_inner().count(), 1);
    assert_eq!(model.iter_item().count(), 1);

    let image_inner = model.new_inner(target);
    model.insert_inner_mor_app(h, inner, image_inner);
    model.close();
    assert_eq!(model.world_item_mor_app(h, x), None);
    assert_eq!(model.iter_item().count(), 1);

    let image_x = model.new_item(target, image_inner);
    assert!(!model.marked(target, image_inner, image_x));
    model.insert_world_item_mor_app(h, x, image_x);
    model.close();
    assert!(model.marked(target, image_inner, image_x));
    assert_eq!(model.iter_item().count(), 2);
}

#[test]
fn cyclic_morphisms_reach_a_fixed_point() {
    let mut model = MorphismPreservation::new();
    let a = model.new_world();
    let b = model.new_world();
    for (source, target) in [(a, b), (b, a), (b, b)] {
        let h = model.new_world_mor();
        model.insert_world_mor_dom(h, source);
        model.insert_world_mor_cod(h, target);
    }
    let label = model.new_ambient();
    model.insert_ready(a);
    model.insert_seen(a, label);
    model.close();
    assert!(model.observed(b));
    assert!(model.seen(b, label));

    let late_label = model.new_ambient();
    model.insert_seen(b, late_label);
    model.close();
    assert!(model.seen(a, late_label));
    assert_eq!(model.iter_seen().count(), 4);
    model.close();
    assert_eq!(model.iter_seen().count(), 4);

    model.equate_world(a, b);
    model.close();
    assert_eq!(model.iter_world().count(), 1);
    assert_eq!(model.iter_seen().count(), 2);
}

#[test]
fn preservation_respects_merged_parents() {
    let mut model = MorphismPreservation::new();
    let source = model.new_world();
    let target = model.new_world();
    let first = model.new_inner(source);
    let second = model.new_inner(source);
    let image_first = model.new_inner(target);
    let image_second = model.new_inner(target);
    let x = model.new_item(source, first);
    model.equate_inner(source, first, second);
    model.insert_inner_member_item(source, second, x);
    model.insert_marked(source, second, x);
    let image_x = model.new_item(target, image_first);
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, source);
    model.insert_world_mor_cod(h, target);
    model.insert_inner_mor_app(h, first, image_first);
    model.insert_inner_mor_app(h, second, image_second);
    model.insert_world_item_mor_app(h, x, image_x);

    assert!(!model.inner_member_item(target, image_second, image_x));
    model.close();
    assert!(model.inner_member_item(target, image_second, image_x));
    assert!(model.marked(target, image_second, image_x));
    assert!(model.are_equal_inner(image_first, image_second));
}

#[test]
fn nested_application_preservation_waits_for_parent_images() {
    let mut model = MorphismPreservation::new();
    let a = model.new_world();
    let b = model.new_world();
    let source = model.new_inner(a);
    let target = model.new_inner(a);
    let image_source = model.new_inner(b);
    let image_target = model.new_inner(b);
    let x = model.new_item(a, source);
    let y = model.new_item(a, target);
    let image_x = model.new_item(b, image_source);
    let image_y = model.new_item(b, image_target);
    let g = model.new_inner_mor(a);
    model.insert_inner_mor_dom(a, g, source);
    model.insert_inner_mor_cod(a, g, target);
    model.insert_item_mor_app(a, g, x, y);
    let image_g = model.new_inner_mor(b);
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, a);
    model.insert_world_mor_cod(h, b);
    model.insert_inner_mor_mor_app(h, g, image_g);

    model.close();
    assert_eq!(model.inner_mor_dom(b, image_g), None);
    assert_eq!(model.inner_mor_cod(b, image_g), None);
    assert_eq!(model.inner_mor_app(h, source), None);
    assert_eq!(model.inner_mor_app(h, target), None);

    model.insert_inner_mor_app(h, source, image_source);
    model.insert_inner_mor_app(h, target, image_target);
    model.insert_world_item_mor_app(h, x, image_x);
    model.insert_world_item_mor_app(h, y, image_y);
    model.close();
    assert_eq!(model.inner_mor_dom(b, image_g), Some(image_source));
    assert_eq!(model.inner_mor_cod(b, image_g), Some(image_target));
    assert_eq!(model.item_mor_app(b, image_g, image_x), Some(image_y));
}

#[test]
fn self_morphism_permutations_preserve_facts_across_rebuilds() {
    let mut model = MorphismPreservation::new();
    let world = model.new_world();
    let elements = [
        model.new_el(world),
        model.new_el(world),
        model.new_el(world),
    ];
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, world);
    model.insert_world_mor_cod(h, world);
    let label = model.new_ambient();
    model.insert_tagged(world, elements[0], label);
    model.insert_edge(world, elements[0], elements[1]);
    model.insert_el_mor_app(h, elements[0], elements[1]);
    model.close();
    assert!(model.tagged(world, elements[1], label));
    assert!(!model.tagged(world, elements[2], label));
    assert_eq!(model.edge(world, elements[1]), None);

    model.insert_el_mor_app(h, elements[1], elements[2]);
    model.insert_el_mor_app(h, elements[2], elements[0]);
    for _ in 0..3 {
        model.canonicalize();
        model.close();
        for i in 0..elements.len() {
            assert!(model.tagged(world, elements[i], label));
            assert_eq!(model.edge(world, elements[i]), Some(elements[(i + 1) % 3]));
        }
        assert_eq!(model.iter_el().count(), 3);
    }
}

#[test]
fn outer_cycles_retain_support_for_acyclic_inner_graphs() {
    let mut model = MorphismPreservation::new();
    let a = model.new_world();
    let b = model.new_world();
    let a0 = model.new_inner(a);
    let a1 = model.new_inner(a);
    let b0 = model.new_inner(b);
    let b1 = model.new_inner(b);
    let x0 = model.new_item(a, a0);
    let x1 = model.new_item(a, a1);
    let y0 = model.new_item(b, b0);
    let y1 = model.new_item(b, b1);
    for (world, source, target, x, y) in [(a, a0, a1, x0, x1), (b, b0, b1, y0, y1)] {
        let h = model.new_inner_mor(world);
        model.insert_inner_mor_dom(world, h, source);
        model.insert_inner_mor_cod(world, h, target);
        model.insert_item_mor_app(world, h, x, y);
    }
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, a);
    model.insert_world_mor_cod(h, b);
    model.insert_inner_mor_app(h, a0, b1);
    model.insert_inner_mor_app(h, a1, b0);
    model.insert_world_item_mor_app(h, x0, y1);
    model.insert_world_item_mor_app(h, x1, y0);
    let k = model.new_world_mor();
    model.insert_world_mor_dom(k, b);
    model.insert_world_mor_cod(k, a);
    model.insert_inner_mor_app(k, b0, a1);
    model.insert_inner_mor_app(k, b1, a0);
    model.insert_world_item_mor_app(k, y0, x1);

    model.insert_marked(a, a1, x1);
    model.close();
    assert!(!model.marked(a, a0, x0));
    assert!(model.marked(b, b1, y1));

    // The return map closes a path through both inner graphs. Its seed must
    // survive even though neither inner morphism graph contains a cycle.
    model.insert_world_item_mor_app(k, y1, x0);
    for _ in 0..3 {
        model.canonicalize();
        model.close();
        for (world, inner, item) in [(a, a0, x0), (a, a1, x1), (b, b0, y0), (b, b1, y1)] {
            assert!(model.marked(world, inner, item));
        }
        assert_eq!(model.iter_marked().count(), 4);
    }
}

#[test]
fn outer_transport_can_install_a_nested_cycle() {
    let mut model = MorphismPreservation::new();
    let a = model.new_world();
    let b = model.new_world();
    let a0 = model.new_inner(a);
    let a1 = model.new_inner(a);
    let b0 = model.new_inner(b);
    let b1 = model.new_inner(b);
    let x0 = model.new_item(a, a0);
    let x1 = model.new_item(a, a1);
    let y0 = model.new_item(b, b0);
    let y1 = model.new_item(b, b1);
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, a);
    model.insert_world_mor_cod(h, b);
    model.insert_inner_mor_app(h, a0, b0);
    model.insert_inner_mor_app(h, a1, b1);
    model.insert_world_item_mor_app(h, x0, y0);
    model.insert_world_item_mor_app(h, x1, y1);
    for (source, target, x, y) in [(a0, a1, x0, x1), (a1, a0, x1, x0)] {
        let g = model.new_inner_mor(a);
        model.insert_inner_mor_dom(a, g, source);
        model.insert_inner_mor_cod(a, g, target);
        model.insert_item_mor_app(a, g, x, y);
        let image_g = model.new_inner_mor(b);
        model.insert_inner_mor_mor_app(h, g, image_g);
    }
    model.close();
    model.insert_marked(b, b1, y1);
    for _ in 0..3 {
        model.close();
        assert!(model.marked(b, b0, y0));
        assert!(model.marked(b, b1, y1));
        assert!(!model.marked(a, a0, x0));
        assert!(!model.marked(a, a1, x1));
    }
}
