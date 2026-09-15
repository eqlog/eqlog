use crate::morphism_preservation::*;

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
#[cfg(feature = "desugared")]
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
fn preservation_derives_additional_membership_and_facts() {
    let mut model = MorphismPreservation::new();
    let source = model.new_world();
    let target = model.new_world();
    let first = model.new_inner(source);
    let second = model.new_inner(source);
    let image_first = model.new_inner(target);
    let image_second = model.new_inner(target);
    let x = model.new_item(source, first);
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
    assert!(!model.are_equal_inner(image_first, image_second));
}

#[test]
fn nested_application_preservation_keeps_endpoints_partial() {
    let mut model = MorphismPreservation::new();
    let a = model.new_world();
    let b = model.new_world();
    let source = model.new_inner(a);
    let target = model.new_inner(a);
    let alternate = model.new_inner(a);
    let image_alternate = model.new_inner(b);
    let x = model.new_item(a, source);
    let y = model.new_item(a, target);
    model.insert_inner_member_item(a, alternate, x);
    model.insert_inner_member_item(a, alternate, y);
    let image_x = model.new_item(b, image_alternate);
    let image_y = model.new_item(b, image_alternate);
    let g = model.new_inner_mor(a);
    model.insert_inner_mor_dom(a, g, source);
    model.insert_inner_mor_cod(a, g, target);
    model.insert_item_mor_app(a, g, x, y);
    let image_g = model.new_inner_mor(b);
    let h = model.new_world_mor();
    model.insert_world_mor_dom(h, a);
    model.insert_world_mor_cod(h, b);
    model.insert_inner_mor_app(h, alternate, image_alternate);
    model.insert_inner_mor_mor_app(h, g, image_g);
    model.insert_world_item_mor_app(h, x, image_x);
    model.insert_world_item_mor_app(h, y, image_y);

    model.close();
    assert_eq!(model.inner_mor_dom(b, image_g), None);
    assert_eq!(model.inner_mor_cod(b, image_g), None);
    assert!(model
        .iter_item_mor_app()
        .any(|row| row == (b, image_g, image_x, image_y)));

    model.equate_item(image_x, image_y);
    model.close();
    let image = model.root_item(image_x);
    assert!(model
        .iter_item_mor_app()
        .any(|row| row == (b, image_g, image, image)));
    assert_eq!(model.inner_mor_dom(b, image_g), None);
    assert_eq!(model.inner_mor_cod(b, image_g), None);
    assert_eq!(model.inner_mor_app(h, source), None);
    assert_eq!(model.inner_mor_app(h, target), None);
}
