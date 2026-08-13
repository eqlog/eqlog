use crate::nested::*;

#[test]
fn empty_model() {
    let mut model = Nested::new();
    model.close();
}

#[test]
fn create_nested_elements() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber = model.new_fiber(bundle);
    let x = model.new_el(fiber);

    assert!(model.bundle_member_fiber(bundle, fiber));
    assert!(model.fiber_member_el(fiber, x));
    model.close();
    assert!(model.bundle_member_fiber(bundle, fiber));
    assert!(model.fiber_member_el(fiber, x));

    assert_eq!(model.iter_bundle().count(), 1);
    assert_eq!(model.iter_fiber().count(), 1);
    // The inner tip() rule adjoins one more El.
    assert_eq!(model.iter_el().count(), 2);
    assert!(model.tip(fiber).is_some());
}

#[test]
fn inner_tip_is_a_member() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber = model.new_fiber(bundle);
    model.close();

    let tip = model.tip(fiber).unwrap();
    assert!(model.fiber_member_el(fiber, tip));
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn member_predicate_insert_rejects_wrong_fiber() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);
    let x = model.new_el(fiber0);

    model.insert_marked(fiber1, x);
}

#[test]
fn merge_fibers_merges_tips() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);
    model.close();

    assert_eq!(model.iter_fiber().count(), 2);
    assert_eq!(model.iter_el().count(), 2);

    model.equate_fiber(fiber0, fiber1);
    model.close();

    assert_eq!(model.iter_fiber().count(), 1);
    assert_eq!(model.iter_el().count(), 1);
}

#[test]
fn merge_bundles_does_not_merge_fibers() {
    let mut model = Nested::new();
    let bundle0 = model.new_bundle();
    let bundle1 = model.new_bundle();
    let fiber0 = model.new_fiber(bundle0);
    let fiber1 = model.new_fiber(bundle1);
    model.close();

    model.equate_bundle(bundle0, bundle1);
    model.close();

    assert_eq!(model.iter_bundle().count(), 1);
    assert_eq!(model.iter_fiber().count(), 2);
    assert!(!model.are_equal_fiber(fiber0, fiber1));
}

#[test]
fn fiber_morphism_maps_marked() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);
    let x = model.new_el(fiber0);

    let g = model.new_fiber_mor(bundle);
    model.insert_fiber_mor_dom(bundle, g, fiber0);
    model.insert_fiber_mor_cod(bundle, g, fiber1);
    model.insert_marked(fiber0, x);

    model.close();

    let y = model.el_mor_app(bundle, g, x).unwrap();
    assert!(model.fiber_member_el(fiber1, y));
    assert!(model.marked(fiber1, y));
}

#[test]
fn three_level_nesting() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b = model.new_b(a);
    let c = model.new_c(b);
    let t = model.new_t(c);

    assert!(model.a_member_b(a, b));
    assert!(model.b_member_c(b, c));
    assert!(model.c_member_t(c, t));
    model.close();
    assert!(model.a_member_b(a, b));
    assert!(model.b_member_c(b, c));
    assert!(model.c_member_t(c, t));
}

#[test]
fn bundle_morphism_maps_fibers() {
    let mut model = Nested::new();
    let bundle0 = model.new_bundle();
    let bundle1 = model.new_bundle();
    let fiber = model.new_fiber(bundle0);

    let h = model.new_bundle_mor();
    model.insert_bundle_mor_dom(h, bundle0);
    model.insert_bundle_mor_cod(h, bundle1);

    model.close();

    let image = model.fiber_mor_app(h, fiber).unwrap();
    assert!(model.bundle_member_fiber(bundle1, image));
    assert!(!model.are_equal_fiber(fiber, image));
}
