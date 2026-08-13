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
    assert!(model.apex(c).is_some());
    assert!(model.c_member_t(c, model.apex(c).unwrap()));
}

#[test]
fn four_level_nesting() {
    let mut model = Nested::new();
    let w = model.new_w();
    let x = model.new_x(w);
    let y = model.new_y(x);
    let z = model.new_z(y);
    let u = model.new_u(z);

    assert!(model.w_member_x(w, x));
    assert!(model.x_member_y(x, y));
    assert!(model.y_member_z(y, z));
    assert!(model.z_member_u(z, u));
    model.close();
    assert!(model.z_member_u(z, u));
}

#[test]
fn deep_c_morphism_maps_marked() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b = model.new_b(a);
    let c0 = model.new_c(b);
    let c1 = model.new_c(b);
    let x = model.new_t(c0);

    let g = model.new_c_mor(b);
    model.insert_c_mor_dom(b, g, c0);
    model.insert_c_mor_cod(b, g, c1);
    model.insert_tagged(c0, x);

    model.close();

    let y = model.t_mor_app(b, g, x).unwrap();
    assert!(model.c_member_t(c1, y));
    assert!(model.tagged(c1, y));
}

#[test]
fn deep_b_morphism_maps_c() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b0 = model.new_b(a);
    let b1 = model.new_b(a);
    let c = model.new_c(b0);

    let f = model.new_b_mor(a);
    model.insert_b_mor_dom(a, f, b0);
    model.insert_b_mor_cod(a, f, b1);

    model.close();

    let image = model.c_mor_app(a, f, c).unwrap();
    assert!(model.b_member_c(b1, image));
    assert!(!model.are_equal_c(c, image));
}

#[test]
fn deep_a_morphism_maps_b() {
    let mut model = Nested::new();
    let a0 = model.new_a();
    let a1 = model.new_a();
    let b = model.new_b(a0);

    let h = model.new_a_mor();
    model.insert_a_mor_dom(h, a0);
    model.insert_a_mor_cod(h, a1);

    model.close();

    let image = model.b_mor_app(h, b).unwrap();
    assert!(model.a_member_b(a1, image));
    assert!(!model.are_equal_b(b, image));
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
