use crate::nested::*;

struct NestedMorphismFixture {
    model: Nested,
    h: AMor,
    domain: A,
    codomain: A,
    target_b: B,
    target_c: C,
    x: T,
    y: T,
}

fn nested_morphism_fixture() -> NestedMorphismFixture {
    let mut model = Nested::new();
    let domain = model.new_a();
    let codomain = model.new_a();
    let source_b = model.new_b(domain);
    let source_c = model.new_c(domain, source_b);
    let x = model.new_t(domain, source_b, source_c);
    let target_b = model.new_b(codomain);
    let target_c = model.new_c(codomain, target_b);
    let y = model.new_t(codomain, target_b, target_c);
    let h = model.new_a_mor();
    model.insert_a_mor_dom(h, domain);
    model.insert_a_mor_cod(h, codomain);
    model.insert_b_mor_app(h, source_b, target_b);
    model.insert_a_c_mor_app(h, source_c, target_c);
    NestedMorphismFixture {
        model,
        h,
        domain,
        codomain,
        target_b,
        target_c,
        x,
        y,
    }
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn nested_mor_app_insert_rejects_wrong_domain() {
    let mut fixture = nested_morphism_fixture();
    fixture
        .model
        .insert_a_t_mor_app(fixture.h, fixture.y, fixture.y);
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn nested_mor_app_insert_rejects_wrong_codomain() {
    let mut fixture = nested_morphism_fixture();
    fixture
        .model
        .insert_a_t_mor_app(fixture.h, fixture.x, fixture.x);
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn nested_mor_app_insert_rejects_wrong_inner_parent() {
    let mut fixture = nested_morphism_fixture();
    let other_c = fixture.model.new_c(fixture.codomain, fixture.target_b);
    let other_y = fixture
        .model
        .new_t(fixture.codomain, fixture.target_b, other_c);
    fixture
        .model
        .insert_a_t_mor_app(fixture.h, fixture.x, other_y);
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn nested_mor_app_insert_rejects_wrong_intermediate_parent() {
    let mut fixture = nested_morphism_fixture();
    let other_b = fixture.model.new_b(fixture.codomain);
    fixture
        .model
        .insert_b_member_c(fixture.codomain, other_b, fixture.target_c);
    let other_y = fixture
        .model
        .new_t(fixture.codomain, other_b, fixture.target_c);
    fixture
        .model
        .insert_a_t_mor_app(fixture.h, fixture.x, other_y);
}

#[test]
#[should_panic(expected = "morphism application requires a defined domain")]
fn nested_mor_app_insert_requires_domain() {
    let mut fixture = nested_morphism_fixture();
    let h = fixture.model.new_a_mor();
    fixture.model.insert_a_mor_cod(h, fixture.codomain);
    fixture.model.insert_a_t_mor_app(h, fixture.x, fixture.y);
}

#[test]
#[should_panic(expected = "morphism application requires a defined codomain")]
fn nested_mor_app_insert_requires_codomain() {
    let mut fixture = nested_morphism_fixture();
    let h = fixture.model.new_a_mor();
    fixture.model.insert_a_mor_dom(h, fixture.domain);
    fixture.model.insert_a_t_mor_app(h, fixture.x, fixture.y);
}

#[test]
#[should_panic(expected = "nested morphism application requires defined parent images")]
fn nested_mor_app_insert_requires_parent_images() {
    let mut fixture = nested_morphism_fixture();
    let h = fixture.model.new_a_mor();
    fixture.model.insert_a_mor_dom(h, fixture.domain);
    fixture.model.insert_a_mor_cod(h, fixture.codomain);
    fixture.model.insert_a_t_mor_app(h, fixture.x, fixture.y);
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn nested_mor_app_insert_rejects_wrong_outer_parent() {
    let mut fixture = nested_morphism_fixture();
    let g = fixture.model.new_b_mor(fixture.codomain);
    fixture
        .model
        .insert_b_t_mor_app(fixture.domain, g, fixture.x, fixture.y);
}

#[test]
#[should_panic(expected = "morphism application argument is not a member of the morphism domain")]
fn nested_mor_app_query_rejects_wrong_domain() {
    let fixture = nested_morphism_fixture();
    fixture.model.a_t_mor_app(fixture.h, fixture.y);
}

#[test]
fn nested_mor_app_accepts_any_valid_source_membership() {
    let mut fixture = nested_morphism_fixture();
    let other_b = fixture.model.new_b(fixture.domain);
    let other_c = fixture.model.new_c(fixture.domain, other_b);
    fixture
        .model
        .insert_c_member_t(fixture.domain, other_b, other_c, fixture.x);

    // The original source parents have no images under h, so validation must
    // also consider the other membership of x.
    let h = fixture.model.new_a_mor();
    fixture.model.insert_a_mor_dom(h, fixture.domain);
    fixture.model.insert_a_mor_cod(h, fixture.codomain);
    fixture.model.insert_b_mor_app(h, other_b, fixture.target_b);
    fixture
        .model
        .insert_a_c_mor_app(h, other_c, fixture.target_c);
    assert_eq!(fixture.model.a_t_mor_app(h, fixture.x), None);
    fixture.model.insert_a_t_mor_app(h, fixture.x, fixture.y);
    assert_eq!(fixture.model.a_t_mor_app(h, fixture.x), Some(fixture.y));

    fixture.model.close();
    fixture.model.insert_a_t_mor_app(h, fixture.x, fixture.y);
    assert_eq!(fixture.model.a_t_mor_app(h, fixture.x), Some(fixture.y));
}

#[test]
fn nested_mor_app_accepts_inherited_source_membership() {
    let mut fixture = nested_morphism_fixture();
    fixture
        .model
        .insert_a_t_mor_app(fixture.h, fixture.x, fixture.y);
    fixture.model.close();

    // The first morphism supplies y's membership after closure. A second
    // morphism must be able to use that inherited membership as its source.
    let next_a = fixture.model.new_a();
    let next_b = fixture.model.new_b(next_a);
    let next_c = fixture.model.new_c(next_a, next_b);
    let z = fixture.model.new_t(next_a, next_b, next_c);
    let k = fixture.model.new_a_mor();
    fixture.model.insert_a_mor_dom(k, fixture.codomain);
    fixture.model.insert_a_mor_cod(k, next_a);
    fixture.model.insert_b_mor_app(k, fixture.target_b, next_b);
    fixture
        .model
        .insert_a_c_mor_app(k, fixture.target_c, next_c);
    fixture.model.insert_a_t_mor_app(k, fixture.y, z);
    assert_eq!(fixture.model.a_t_mor_app(k, fixture.y), Some(z));
    fixture.model.close();
    assert_eq!(fixture.model.a_t_mor_app(k, fixture.y), Some(z));
}

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
    let x = model.new_el(bundle, fiber);

    assert!(model.bundle_member_fiber(bundle, fiber));
    assert!(model.fiber_member_el(bundle, fiber, x));
    model.close();
    assert!(model.bundle_member_fiber(bundle, fiber));
    assert!(model.fiber_member_el(bundle, fiber, x));

    assert_eq!(model.iter_bundle().count(), 1);
    assert_eq!(model.iter_fiber().count(), 1);
    // The inner tip() rule adjoins one more El.
    assert_eq!(model.iter_el().count(), 2);
    assert!(model.tip(bundle, fiber).is_some());
}

#[test]
fn inner_tip_is_a_member() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber = model.new_fiber(bundle);
    model.close();

    let tip = model.tip(bundle, fiber).unwrap();
    assert!(model.fiber_member_el(bundle, fiber, tip));
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn member_predicate_insert_rejects_wrong_fiber() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);
    let x = model.new_el(bundle, fiber0);

    model.insert_marked(bundle, fiber1, x);
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
fn fiber_morphism_applies_to_tip() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);

    let g = model.new_fiber_mor(bundle);
    model.insert_fiber_mor_dom(bundle, g, fiber0);
    model.insert_fiber_mor_cod(bundle, g, fiber1);

    model.close();

    let tip0 = model.tip(bundle, fiber0).unwrap();
    let image = model.el_mor_app(bundle, g, tip0).unwrap();
    assert!(model.fiber_member_el(bundle, fiber1, image));
}

#[test]
fn fiber_morphism_image_found_by_rule() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);
    let x = model.new_el(bundle, fiber0);
    let y = model.new_el(bundle, fiber1);

    let g = model.new_fiber_mor(bundle);
    model.insert_fiber_mor_dom(bundle, g, fiber0);
    model.insert_fiber_mor_cod(bundle, g, fiber1);
    model.insert_el_mor_app(bundle, g, x, y);
    model.insert_marked(bundle, fiber1, y);

    model.close();

    assert!(model.reached_marked_image(bundle, fiber1));
    assert!(!model.reached_marked_image(bundle, fiber0));
}

#[test]
#[should_panic(expected = "invalid dependent argument")]
fn fiber_mor_app_rejects_el_from_other_bundle() {
    let mut model = Nested::new();
    let bundle0 = model.new_bundle();
    let bundle1 = model.new_bundle();
    let fiber0 = model.new_fiber(bundle0);
    let fiber1 = model.new_fiber(bundle0);
    let foreign = model.new_fiber(bundle1);
    let x = model.new_el(bundle1, foreign);

    let g = model.new_fiber_mor(bundle0);
    model.insert_fiber_mor_dom(bundle0, g, fiber0);
    model.insert_fiber_mor_cod(bundle0, g, fiber1);

    let _ = model.el_mor_app(bundle0, g, x);
}

#[test]
fn fiber_morphism_maps_marked() {
    let mut model = Nested::new();
    let bundle = model.new_bundle();
    let fiber0 = model.new_fiber(bundle);
    let fiber1 = model.new_fiber(bundle);
    let x = model.new_el(bundle, fiber0);

    let g = model.new_fiber_mor(bundle);
    model.insert_fiber_mor_dom(bundle, g, fiber0);
    model.insert_fiber_mor_cod(bundle, g, fiber1);
    model.insert_marked(bundle, fiber0, x);

    model.close();

    let y = model.el_mor_app(bundle, g, x).unwrap();
    assert!(model.fiber_member_el(bundle, fiber1, y));
    assert!(model.marked(bundle, fiber1, y));
}

#[test]
fn three_level_nesting() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b = model.new_b(a);
    let c = model.new_c(a, b);
    let t = model.new_t(a, b, c);

    assert!(model.a_member_b(a, b));
    assert!(model.b_member_c(a, b, c));
    assert!(model.c_member_t(a, b, c, t));
    model.close();
    assert!(model.a_member_b(a, b));
    assert!(model.b_member_c(a, b, c));
    assert!(model.c_member_t(a, b, c, t));
    assert!(model.apex(a, b, c).is_some());
    assert!(model.c_member_t(a, b, c, model.apex(a, b, c).unwrap()));
}

#[test]
fn four_level_nesting() {
    let mut model = Nested::new();
    let w = model.new_w();
    let x = model.new_x(w);
    let y = model.new_y(w, x);
    let z = model.new_z(w, x, y);
    let u = model.new_u(w, x, y, z);

    assert!(model.w_member_x(w, x));
    assert!(model.x_member_y(w, x, y));
    assert!(model.y_member_z(w, x, y, z));
    assert!(model.z_member_u(w, x, y, z, u));
    model.close();
    assert!(model.z_member_u(w, x, y, z, u));
}

#[test]
fn c_morphism_image_found_by_rule() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b = model.new_b(a);
    let c0 = model.new_c(a, b);
    let c1 = model.new_c(a, b);
    let x = model.new_t(a, b, c0);
    let y = model.new_t(a, b, c1);

    let g = model.new_c_mor(a, b);
    model.insert_c_mor_dom(a, b, g, c0);
    model.insert_c_mor_cod(a, b, g, c1);
    model.insert_t_mor_app(a, b, g, x, y);
    model.insert_tagged(a, b, c1, y);

    model.close();

    assert!(model.reached_tagged_image(a, b, c1));
    assert!(!model.reached_tagged_image(a, b, c0));
}

#[test]
fn outer_morphism_maps_deep_members() {
    let mut model = Nested::new();
    let a0 = model.new_a();
    let a1 = model.new_a();
    let b0 = model.new_b(a0);
    let c0 = model.new_c(a0, b0);
    let x = model.new_t(a0, b0, c0);
    let b1 = model.new_b(a1);
    let c1 = model.new_c(a1, b1);
    let y = model.new_t(a1, b1, c1);

    let h = model.new_a_mor();
    model.insert_a_mor_dom(h, a0);
    model.insert_a_mor_cod(h, a1);
    model.insert_b_mor_app(h, b0, b1);
    model.insert_a_c_mor_app(h, c0, c1);
    model.insert_a_t_mor_app(h, x, y);
    model.close();

    assert_eq!(model.b_mor_app(h, b0), Some(b1));
    assert_eq!(model.a_c_mor_app(h, c0), Some(c1));
    assert_eq!(model.a_t_mor_app(h, x), Some(y));
    assert!(model.a_member_b(a1, b1));
    assert!(model.b_member_c(a1, b1, c1));
    assert!(model.c_member_t(a1, b1, c1, y));
    assert!(model.recognized_deep_mor_app(h));
    assert!(model.recognized_deep_mor_app_from_source(h));
    assert!(model.recognized_deep_mor_app_with_later_types(h));
    assert!(model.recognized_deep_mor_app_in_branch(h));
    assert!(!model.are_equal_t(x, y));
    assert!(!model.are_equal_b(b0, b1));
    assert!(!model.are_equal_c(c0, c1));
}

#[test]
fn nested_morphism_inference_preserves_outer_parent() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b0 = model.new_b(a);
    let b1 = model.new_b(a);
    let c0 = model.new_c(a, b0);
    let c1 = model.new_c(a, b1);
    let x = model.new_t(a, b0, c0);
    let y = model.new_t(a, b1, c1);
    let f = model.new_b_mor(a);
    model.insert_b_mor_dom(a, f, b0);
    model.insert_b_mor_cod(a, f, b1);
    model.insert_c_mor_app(a, f, c0, c1);
    model.insert_b_t_mor_app(a, f, x, y);

    let other_a = model.new_a();
    let other_f = model.new_b_mor(other_a);
    model.close();

    assert!(model.recognized_mid_mor_app(a, f));
    assert!(!model.recognized_mid_mor_app(other_a, other_f));
    assert!(!model.are_equal_t(x, y));
    assert!(model.c_member_t(a, b0, c0, x));
    assert!(model.c_member_t(a, b1, c1, y));
}

#[test]
fn c_morphism_applies_to_apex() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b = model.new_b(a);
    let c0 = model.new_c(a, b);
    let c1 = model.new_c(a, b);

    let g = model.new_c_mor(a, b);
    model.insert_c_mor_dom(a, b, g, c0);
    model.insert_c_mor_cod(a, b, g, c1);

    model.close();

    let apex0 = model.apex(a, b, c0).unwrap();
    let image = model.t_mor_app(a, b, g, apex0).unwrap();
    assert!(model.c_member_t(a, b, c1, image));
}

#[test]
fn deep_c_morphism_maps_marked() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b = model.new_b(a);
    let c0 = model.new_c(a, b);
    let c1 = model.new_c(a, b);
    let x = model.new_t(a, b, c0);

    let g = model.new_c_mor(a, b);
    model.insert_c_mor_dom(a, b, g, c0);
    model.insert_c_mor_cod(a, b, g, c1);
    model.insert_tagged(a, b, c0, x);

    model.close();

    let y = model.t_mor_app(a, b, g, x).unwrap();
    assert!(model.c_member_t(a, b, c1, y));
    assert!(model.tagged(a, b, c1, y));
}

#[test]
fn deep_b_morphism_maps_c() {
    let mut model = Nested::new();
    let a = model.new_a();
    let b0 = model.new_b(a);
    let b1 = model.new_b(a);
    let c = model.new_c(a, b0);

    let f = model.new_b_mor(a);
    model.insert_b_mor_dom(a, f, b0);
    model.insert_b_mor_cod(a, f, b1);

    model.close();

    let image = model.c_mor_app(a, f, c).unwrap();
    assert!(model.b_member_c(a, b1, image));
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
